//! Shared machinery for the three bench files: the input corpus, the digest that
//! keeps a measurement honest, and the two-mode runner that guarantees the timed
//! code and the verified code are the *same* code.
//!
//! # The problem this module exists to solve
//!
//! A benchmark can be wrong in two ways that a green run will never show you.
//! It can measure less than it claims, because the optimizer deleted work whose
//! result nobody looked at. And it can measure the *wrong thing*, because the
//! "optimized" function no longer computes what the baseline computed. Both
//! failures make a number go down, which is exactly the direction that makes an
//! autonomous optimization loop believe it succeeded.
//!
//! So:
//!
//! * **Every case has exactly one body**, written once, and [`run`] either times
//!   it or digests its result. There is no separate "verification copy" that can
//!   drift away from the code that gets timed.
//! * **Every case ends in a digest** that depends on every output element and on
//!   its position. `case!` computes the digest for the current crate and for the
//!   frozen baseline and asserts they are equal *before* timing either. An
//!   optimization that changes an answer fails the bench run; it cannot be
//!   reported as a speedup.
//! * **Every input is opaque to the optimizer** ([`std::hint::black_box`]) and
//!   every output is consumed, so there is nothing to constant-fold and nothing
//!   dead to delete.
//!
//! # The corpus
//!
//! Inputs come from a seeded `SplitMix64`, so a case gets byte-identical inputs on
//! every run, on every machine, in both variants. Two things follow: run-to-run
//! comparisons are not confounded by input variation, and `now` vs `genesis` is
//! a comparison of code rather than of luck.
//!
//! Values are drawn from `[1, P)` — never zero. Zero is not a neutral input
//! here, and the direction is worth stating carefully because it is easy to get
//! backwards: `Ext4::is_zero` and `UnivariatePoly::trim` both stop at the first
//! **non-zero** coefficient, so an all-zero corpus is what runs them to
//! completion and a non-zero corpus is their fast exit. Excluding zero is
//! therefore not about keeping an `O(n)` measurement `O(n)`; it is about
//! keeping the *shape* of a case fixed. A zero top coefficient would make
//! `add` and `mul` trim their result to a different length, so a row's work
//! would depend on how many zeros its seed happened to produce.
//!
//! The cost is that `field/ext4_is_zero` measures the early exit rather than
//! the full four-coefficient compare — see its docstring. Cases that need
//! zeros (`trim`) place them deliberately.

#![allow(dead_code)] // each bench file uses a different subset of this module.

use std::time::Duration;

use criterion::Criterion;

/// The Hachi prime. Checked against the crate's own constant at compile time by
/// each bench file, so this copy can never silently disagree with the field it
/// is generating elements for.
pub const P: u64 = 4_294_967_197;

// ---------------------------------------------------------------------------
// Sizes
//
// One size where a second would only re-measure the same straight line, two
// where the shape of the algorithm is the thing under study (a schoolbook
// convolution and a basis-building evaluator have to be seen at more than one
// point to be seen at all).
// ---------------------------------------------------------------------------

/// Field ops are single-digit nanoseconds; they are measured a batch at a time.
pub const FIELD_N: usize = 1024;
/// Univariate `O(n)` operations.
pub const UNI_N: usize = 1024;
/// Univariate evaluation — small and large, because Horner's constant matters.
pub const UNI_EVAL_N: [usize; 2] = [64, 1024];
/// Univariate multiplication is `O(n^2)`; 1024 would cost minutes.
pub const UNI_MUL_N: [usize; 2] = [64, 256];
/// Multilinear arity for the flat `O(2^vars)` passes: one table of 4096 entries.
pub const ML_VARS: usize = 12;
/// Multilinear arity where the algorithm, not just the length, is under study.
pub const ML_VARS_2: [usize; 2] = [8, 12];
/// The A/B fairness control: one case, one size, once per bench binary.
///
/// It is a **sanity check on the run**, not a per-case error bar. Both variants
/// execute identical code (see [`control_workload`]), so whatever it reads is
/// the harness disagreeing with itself; `harness.py` takes the worst of the
/// three and refuses to report a run above `USABLE_BIAS_MAX`.
///
/// One size rather than several, because no small set of controls can cover this
/// suite: the real cases span roughly 0.2 us to 2 ms, four orders of magnitude.
/// Several would invite exactly the wrong inference — a per-case threshold
/// interpolated across them and applied to rows up to 100x longer than the
/// control it came from, which reads as rigour and is not.
///
/// 8192 lands near 19 us with a 64 KiB buffer: the duration and the memory
/// footprint of the polynomial rows the optimization loop actually acts on.
pub const CONTROL_N: usize = 8192;

// ---------------------------------------------------------------------------
// Deterministic corpus
// ---------------------------------------------------------------------------

/// `SplitMix64` — three lines, no dependency, and the same stream everywhere.
pub struct SplitMix64(u64);

impl SplitMix64 {
    #[must_use]
    pub fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// `n` field-sized words in `[1, P)`, drawn from the stream named by `tag`.
///
/// `tag` is part of the seed rather than a call counter, so a case's inputs do
/// not change when an unrelated case is added, removed, or reordered above it.
/// Two operands of the same operation must use different tags — `x * x` is a
/// squaring, and squaring is not what `mul` is for.
#[must_use]
pub fn words(tag: u64, n: usize) -> Vec<u64> {
    let mut rng = SplitMix64::new(0x_C0FF_EE00_0000_0000 ^ tag);
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(1 + rng.next_u64() % (P - 1));
    }
    out
}

// ---------------------------------------------------------------------------
// Digest
// ---------------------------------------------------------------------------

/// Fold one word into a running digest, sensitive to both value and position.
///
/// Runs **outside** every timed region — it is applied to a finished result, not
/// per element inside the loop — so it can afford to be a real mixing function
/// rather than an xor that would call a reversed vector equal to its original.
#[must_use]
pub fn mix(acc: u64, v: u64) -> u64 {
    let mut z = acc.rotate_left(17) ^ v.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

// ---------------------------------------------------------------------------
// The A/B fairness control
// ---------------------------------------------------------------------------

/// A fixed integer kernel with nothing to do with `cpoly`, used by the
/// `_control/*` cases as **both** the `now` and the `genesis` variant.
///
/// # Why the harness benchmarks something it does not care about
///
/// The "vs genesis" column compares two criterion benchmarks run one after the
/// other: `now` finishes completely before `genesis` starts. Anything that
/// changes about the machine across those few seconds — a core clocking up, a
/// fan spinning down, another process arriving — lands entirely on the second
/// one and looks exactly like a code change. Code layout can do the same thing
/// silently and permanently: the two variants are different symbols in
/// different crates, and a few bytes of alignment difference can be worth
/// several percent on a tight loop.
///
/// None of that can be reasoned away, so it is measured. Both variants of a
/// `_control` case call *this* function — the same symbol, in the bench crate,
/// with the same input — so their measured difference is the harness's own bias
/// and nothing else. `benches/harness.py` prints it and folds it into the
/// significance threshold, which means an optimization has to beat the harness's
/// error before it is called an improvement.
///
/// Sized to land in the same low-microsecond range as a typical case, so it is
/// subject to the same rounding and scheduling effects they are.
///
/// # Why it allocates
///
/// A tight integer loop over a borrowed slice is the quietest thing a CPU can
/// do, and a control that quiet flatters the harness: it would report a
/// fraction of the run-to-run spread the real cases — every one of which
/// builds and drops a `Vec` — actually show. That is worse than no control,
/// because the number it produces is used as the threshold real cases must
/// clear.
///
/// So this does what the majority of real cases do: allocate a result buffer,
/// fill it element by element, hand it back to be digested and dropped. The
/// allocator traffic and the page faults are the point, not an accident.
#[must_use]
pub fn control_workload(xs: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(xs.len());
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < xs.len() {
        acc = acc.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(xs[i]);
        acc ^= acc >> 29;
        out.push(acc);
        i += 1;
    }
    out
}

// ---------------------------------------------------------------------------
// The two-mode runner
// ---------------------------------------------------------------------------

/// What a case should do with its body: time it, or run it once and digest it.
pub enum Mode<'a, 'b> {
    /// Hand the body to criterion.
    Bench(&'a mut criterion::Bencher<'b>),
    /// Run the body once and return a digest of its result.
    Digest,
}

/// Time (or digest) a body that returns its result.
///
/// `Bencher::iter` black-boxes whatever the body returns, so the result cannot
/// be optimized away; the caller's job is only to make the *inputs* opaque.
pub fn run<R, F, D>(m: Mode<'_, '_>, mut body: F, digest: D) -> u64
where
    F: FnMut() -> R,
    D: Fn(&R) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter(&mut body);
            0
        }
        Mode::Digest => digest(&body()),
    }
}

/// Time (or digest) a body that writes into a caller-owned buffer.
///
/// For the field cases, where a returned value per element would cost as much as
/// the operation being measured. The buffer is re-blackboxed on every iteration
/// so the writes cannot be hoisted out of the loop or elided.
pub fn run_into<T, F, D>(m: Mode<'_, '_>, out: &mut [T], mut body: F, digest: D) -> u64
where
    F: FnMut(&mut [T]),
    D: Fn(&[T]) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter(|| body(std::hint::black_box(&mut *out)));
            std::hint::black_box(&*out);
            0
        }
        Mode::Digest => {
            body(out);
            digest(&*out)
        }
    }
}

/// Time (or digest) a body that consumes its input.
///
/// `iter_batched` builds the inputs and drops the outputs outside the timed
/// region (verified in criterion 0.7's `Bencher::iter_batched`, and 0.8's), which is
/// the only correct way to measure `trim`, `to_evals` and `to_coeffs`: each
/// needs a fresh owned value, and timing the clone that produces it would
/// measure `Vec::clone` rather than the transform.
pub fn run_batched<I, R, S, F, D>(m: Mode<'_, '_>, mut setup: S, mut body: F, digest: D) -> u64
where
    S: FnMut() -> I,
    F: FnMut(I) -> R,
    D: Fn(&R) -> u64,
{
    match m {
        Mode::Bench(b) => {
            b.iter_batched(&mut setup, &mut body, criterion::BatchSize::LargeInput);
            0
        }
        Mode::Digest => digest(&body(setup())),
    }
}

// ---------------------------------------------------------------------------
// Criterion configuration
// ---------------------------------------------------------------------------

/// The configuration `make run-bench` uses. There is exactly one; there is no
/// reduced-sampling mode, because a run that cannot be acted on is not worth the
/// minutes it still costs.
///
/// 100 samples is criterion's default and what its confidence intervals are
/// worth trusting at. The measurement window is 5s, up from criterion's 3s
/// default.
///
/// Why 5s and not more: criterion samples *linearly*, so sample `k` runs the
/// routine `k * d` times, and a longer window buys a larger `d`. For the slowest
/// rows here (~1 ms) `d = 1` up to about a 9s window, so the returns past 5s are
/// thin and the suite would double. What actually fixes the low-iteration
/// samples is discarding them, which `harness.py`'s `_robust` does.
///
/// What more sampling does **not** fix, and what nothing inside criterion can:
/// a machine that settles into a slower state for longer than an entire
/// measurement. Criterion's statistics describe the samples it took; they
/// cannot see a bias that is constant across every one of them. Only the
/// now-vs-genesis delta survives that, because it lands on both variants
/// equally — which is why that delta, and not the absolute time, is the
/// number this harness exists to produce.
#[must_use]
pub fn criterion_config() -> Criterion {
    Criterion::default()
        .sample_size(100)
        .warm_up_time(Duration::from_millis(1000))
        .measurement_time(Duration::from_secs(5))
        .noise_threshold(0.03)
}

// ---------------------------------------------------------------------------
// The case driver
// ---------------------------------------------------------------------------

/// Measure one case in both variants, after proving they agree.
///
/// The equality assertion is the load-bearing line. `now` and `genesis` are
/// different code compiled from different crates; if they disagree on a fixed
/// input, then whatever the timings say, they are not timings of the same
/// computation and the comparison is meaningless. Failing here is much cheaper
/// than shipping a "speedup" that changed an answer.
#[macro_export]
macro_rules! case {
    ($g:expr, $f:ident, $param:expr) => {{
        let p = $param;
        let d_now = now::$f($crate::support::Mode::Digest, p);
        let d_gen = genesis::$f($crate::support::Mode::Digest, p);
        assert_eq!(
            d_now, d_gen,
            "bench `{}` at {}: cpoly and the frozen genesis snapshot compute \
             DIFFERENT results. Either the current code is wrong, or it changed \
             semantics; either way the timings below would compare two different \
             functions. Fix the code, do not silence this.",
            stringify!($f),
            p
        );
        $g.bench_with_input(::criterion::BenchmarkId::new("now", p), &p, |b, &p| {
            now::$f($crate::support::Mode::Bench(b), p);
        });
        $g.bench_with_input(::criterion::BenchmarkId::new("genesis", p), &p, |b, &p| {
            genesis::$f($crate::support::Mode::Bench(b), p);
        });
    }};
}

/// One criterion group per operation, one case per size.
///
/// The group name is the `<module>/<op>` pair the report keys a case on, and
/// `// @covers` ties it to the item it measures — rename deliberately.
#[macro_export]
macro_rules! bench_case {
    ($c:expr, $name:literal, $f:ident, [$($p:expr),+ $(,)?]) => {{
        let mut g = $c.benchmark_group($name);
        $( $crate::case!(g, $f, $p); )+
        g.finish();
    }};
}
