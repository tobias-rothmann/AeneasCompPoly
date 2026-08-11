//! Benchmarks for [`cpoly::field`] — the base field `F_P` and its quartic
//! extension `Ext4`.
//!
//! # What a "field" number here means, exactly
//!
//! A single `Fp::add` is a handful of nanoseconds; a single `Fp::mul` is one
//! 64-bit multiply plus a reduction that LLVM turns into a multiply-and-shift.
//! At that scale the harness is not a bystander — a per-element accumulator
//! would cost as much as the operation it is accumulating. So these cases do
//! **not** time one operation. Each times a loop that applies the operation to
//! [`support::FIELD_N`] independent operand pairs and stores each result into a
//! preallocated buffer:
//!
//! ```text
//!     while i < n { out[i] = xs[i] OP ys[i]; i += 1; }
//! ```
//!
//! Three consequences worth being explicit about, because they decide what these
//! rows can and cannot be used for:
//!
//! * **This is throughput, not latency.** The operands are independent, so the
//!   CPU overlaps them. That is the right model for this crate — every caller in
//!   `univariate` and `multilinear` is a loop of independent coefficient
//!   arithmetic — but it will read faster than a dependent chain would.
//! * **The loop scaffolding is inside the measurement, and for the base field it
//!   dominates.** Each element costs one `out[i] = …` store, two bounds checks,
//!   and three reloads of the input `Vec` headers — `black_box` makes the output
//!   pointer opaque, so the compiler must assume every store may clobber them.
//!   The compiled `fp_add` loop is 17 instructions per element, of which
//!   `<Fp as Add>::add` is 4. That is identical in both variants, so the
//!   *comparison* stays fair, but it heavily damps the *magnitude*: measured
//!   here, replacing `Fp::add` outright with a `wrapping_add` moves a
//!   two-input row by −6.6% and a one-input row by −33.5% (`fp_neg` and
//!   `fp_new` were loop-versioned and 4x-unrolled, so they escaped the
//!   per-element checks). Two consequences: a change to a base-field primitive
//!   can be real and still land near `harness.py`'s `MIN_EFFECT`, and the rows
//!   are **not comparable to each other** — `fp_neg` reads about half of
//!   `fp_add` for arithmetic of identical cost. `Ext4` rows carry enough work
//!   per element that the scaffolding is a small fraction of them.
//! * **The polynomial rows are the authority.** If a change to `Fp::mul` shows
//!   +3% here and −20% in `univariate/mul`, believe `univariate/mul`. These rows
//!   exist to localize a change, not to score it.
//!
//! Operand streams are seeded per case and never shared between the two sides of
//! a binary operation: `x * x` is a squaring, and squaring is not what `mul` is
//! for.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

// The corpus generator reduces mod its own copy of the modulus. If that copy
// ever disagreed with the field's, every "field element" here would be
// unreduced and every operation would be measured on inputs it does not
// promise to accept.
const _: () = assert!(support::P == cpoly::field::P);
const _: () = assert!(support::P == cpoly_genesis::field::P);
#[cfg(feature = "candidate")]
const _: () = assert!(support::P == cpoly_candidate::field::P);

/// One body per case, instantiated once against the live crate and once against
/// the frozen baseline. Writing the two separately is how a benchmark quietly
/// starts comparing two different computations; a macro makes that impossible.
macro_rules! define_cases {
    ($modname:ident, $cp:path) => {
        mod $modname {
            use std::hint::black_box;

            use $cp as cp;

            use crate::support::{self, Mode};

            // -- corpus -----------------------------------------------------

            fn fps(tag: u64, n: usize) -> Vec<cp::Fp> {
                support::words(tag, n).into_iter().map(cp::Fp::new).collect()
            }

            fn ext4s(tag: u64, n: usize) -> Vec<cp::Ext4> {
                let w = support::words(tag, n * 4);
                (0..n)
                    .map(|i| {
                        cp::Ext4::new(
                            cp::Fp::new(w[4 * i]),
                            cp::Fp::new(w[4 * i + 1]),
                            cp::Fp::new(w[4 * i + 2]),
                            cp::Fp::new(w[4 * i + 3]),
                        )
                    })
                    .collect()
            }

            // -- digests (outside every timed region) -----------------------

            fn d_fp(v: &[cp::Fp]) -> u64 {
                v.iter().fold(0u64, |a, x| support::mix(a, x.to_u64()))
            }

            fn d_ext4(v: &[cp::Ext4]) -> u64 {
                v.iter().fold(0u64, |a, x| {
                    let a = support::mix(a, x.c0.to_u64());
                    let a = support::mix(a, x.c1.to_u64());
                    let a = support::mix(a, x.c2.to_u64());
                    support::mix(a, x.c3.to_u64())
                })
            }

            fn d_u64(v: &[u64]) -> u64 {
                v.iter().fold(0u64, |a, x| support::mix(a, *x))
            }

            // -- base field -------------------------------------------------

            pub fn fp_add(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (fps(0x0101, n), fps(0x0102, n));
                let mut out = vec![cp::Fp::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] + ys[i];
                            i += 1;
                        }
                    },
                    d_fp,
                )
            }

            pub fn fp_sub(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (fps(0x0103, n), fps(0x0104, n));
                let mut out = vec![cp::Fp::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] - ys[i];
                            i += 1;
                        }
                    },
                    d_fp,
                )
            }

            pub fn fp_mul(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (fps(0x0105, n), fps(0x0106, n));
                let mut out = vec![cp::Fp::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] * ys[i];
                            i += 1;
                        }
                    },
                    d_fp,
                )
            }

            pub fn fp_neg(m: Mode<'_, '_>, n: usize) -> u64 {
                let xs = fps(0x0107, n);
                let mut out = vec![cp::Fp::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let xs = black_box(&xs);
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = -xs[i];
                            i += 1;
                        }
                    },
                    d_fp,
                )
            }

            /// `Fp::new` is the reduction, so its inputs are drawn raw rather
            /// than from `support::words`: an already-reduced input is not one
            /// this function is ever called with.
            ///
            /// Not for speed, though — `P` is a `const`, so `v % P` is a
            /// branchless multiply-high and costs the same either way (measured
            /// here: 0.4750 ns/elem unreduced, 0.4765 ns/elem reduced).
            pub fn fp_new(m: Mode<'_, '_>, n: usize) -> u64 {
                let mut rng = support::SplitMix64::new(0x0108);
                let raw: Vec<u64> = (0..n).map(|_| rng.next_u64()).collect();
                let mut out = vec![cp::Fp::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let raw = black_box(&raw);
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = cp::Fp::new(raw[i]);
                            i += 1;
                        }
                    },
                    d_fp,
                )
            }

            // -- extension --------------------------------------------------

            pub fn ext4_add(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (ext4s(0x0201, n), ext4s(0x0202, n));
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] + ys[i];
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            pub fn ext4_sub(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (ext4s(0x0203, n), ext4s(0x0204, n));
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] - ys[i];
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            pub fn ext4_neg(m: Mode<'_, '_>, n: usize) -> u64 {
                let xs = ext4s(0x0205, n);
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let xs = black_box(&xs);
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = -xs[i];
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            /// The hot primitive of the whole crate: 16 base multiplies, 12
            /// additions and 3 doublings per call, and every polynomial
            /// operation is a loop over it.
            pub fn ext4_mul(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (ext4s(0x0206, n), ext4s(0x0207, n));
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] * ys[i];
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            /// The heterogeneous `Fp * Ext4` (4 base multiplies).
            ///
            /// **No caller in this crate reaches it.** Every scalar in
            /// `univariate` and `multilinear` is typed `Ext4` — `smul`, the
            /// Horner layers, the basis builders, `dot` — so all of those
            /// resolve to `impl Mul for Ext4` (16 base multiplies), which is
            /// `field/ext4_mul`. That is the row to follow when a polynomial
            /// row moves; this one shares no code with any of them. It is
            /// benched because it is public and carries a Lean spec
            /// (`ext_smul_spec`), not because it is on a hot path.
            pub fn fp_mul_ext4(m: Mode<'_, '_>, n: usize) -> u64 {
                let (xs, ys) = (fps(0x0208, n), ext4s(0x0209, n));
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let (xs, ys) = (black_box(&xs), black_box(&ys));
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = xs[i] * ys[i];
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            pub fn ext4_from_base(m: Mode<'_, '_>, n: usize) -> u64 {
                let xs = fps(0x020A, n);
                let mut out = vec![cp::Ext4::ZERO; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let xs = black_box(&xs);
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = cp::Ext4::from_base(xs[i]);
                            i += 1;
                        }
                    },
                    d_ext4,
                )
            }

            /// Not a mirrored operation. `UnivariatePoly::trim` is a loop of
            /// nothing else, but this row is a poor localizer for it, and the
            /// direction is easy to get backwards: `&&` exits at the first
            /// **false** test, i.e. at the first **non-zero** coefficient, so a
            /// non-zero corpus is the *early exit* and an all-zero element is
            /// what runs all four comparisons. The corpus is non-zero by
            /// construction, so this row measures the early exit, on every one
            /// of its `n` elements.
            ///
            /// `trim`'s scan takes the complementary branch — it walks zeros,
            /// returning `true`, all the way down — so `univariate/trim` is the
            /// row that exercises the full compare. Two things follow: a change
            /// confined to the `c3` test is invisible here (LLVM merges
            /// `c0|c1|c2` branchlessly and loads `c3` only on the branch this
            /// corpus never takes), and every output of this case is `0`, so
            /// `case!`'s digest folds a constant and could not tell `is_zero`
            /// from `|_| false`. `univariate/trim`, whose digest folds the
            /// trimmed length, is what catches that.
            pub fn ext4_is_zero(m: Mode<'_, '_>, n: usize) -> u64 {
                let xs = ext4s(0x020B, n);
                let mut out = vec![0u64; n];
                support::run_into(
                    m,
                    &mut out,
                    |o| {
                        let xs = black_box(&xs);
                        let mut i = 0usize;
                        while i < o.len() {
                            o[i] = u64::from(xs[i].is_zero());
                            i += 1;
                        }
                    },
                    d_u64,
                )
            }
            /// The harness's A/B fairness control. Both variants of this case
            /// call the *same* function in `benches/support`, so any difference
            /// the report shows for it is measurement bias, not code. See
            /// `support::control_workload`.
            pub fn control(m: Mode<'_, '_>, n: usize) -> u64 {
                let xs = support::words(0x0000, n);
                support::run(m, || support::control_workload(black_box(&xs)),
                    |v: &Vec<u64>| v.iter().fold(0u64, |a, x| support::mix(a, *x)))
            }

        }
    };
}

define_cases!(now, cpoly);
define_cases!(genesis, cpoly_genesis);
#[cfg(feature = "candidate")]
define_cases!(candidate, cpoly_candidate);

fn field_benches(c: &mut Criterion) {
    // The run's sanity check: identical code in both variants, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the
    // machine is in the same state the first real cases will see.
    bench_case!(c, "_control/field", control, [support::CONTROL_N]);

    let n = support::FIELD_N;

    // @covers field::Fp::new
    bench_case!(c, "field/fp_new", fp_new, [n]);
    // @covers field::<Fp as Add>::add
    bench_case!(c, "field/fp_add", fp_add, [n]);
    // @covers field::<Fp as Sub>::sub
    bench_case!(c, "field/fp_sub", fp_sub, [n]);
    // @covers field::<Fp as Mul>::mul
    bench_case!(c, "field/fp_mul", fp_mul, [n]);
    // @covers field::<Fp as Neg>::neg
    bench_case!(c, "field/fp_neg", fp_neg, [n]);

    // @covers field::<Ext4 as Add>::add
    bench_case!(c, "field/ext4_add", ext4_add, [n]);
    // @covers field::<Ext4 as Sub>::sub
    bench_case!(c, "field/ext4_sub", ext4_sub, [n]);
    // @covers field::<Ext4 as Neg>::neg
    bench_case!(c, "field/ext4_neg", ext4_neg, [n]);
    // @covers field::<Ext4 as Mul>::mul
    bench_case!(c, "field/ext4_mul", ext4_mul, [n]);
    // @covers field::<Fp as Mul<Ext4>>::mul
    bench_case!(c, "field/fp_mul_ext4", fp_mul_ext4, [n]);
    // @covers field::Ext4::from_base
    bench_case!(c, "field/ext4_from_base", ext4_from_base, [n]);
    // @covers field::Ext4::is_zero
    bench_case!(c, "field/ext4_is_zero", ext4_is_zero, [n]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = field_benches
}
criterion_main!(benches);
