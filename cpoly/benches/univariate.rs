//! Benchmarks for [`cpoly::univariate`] — dense little-endian coefficient
//! vectors over `Ext4`, mirroring `CompPoly.CPolynomial.Raw`.
//!
//! # Sizes, and why these
//!
//! The `O(n)` operations (`add`, `sub`, `neg`, `smul`, `add_untrimmed`) are
//! measured at one length, [`support::UNI_N`]. A second length would re-measure
//! the same straight line and cost another minute of wall clock.
//!
//! Two operations get two lengths because their *shape*, not just their extent,
//! is what an optimization would change:
//!
//! * `eval` — Horner's method. Its per-coefficient constant is the whole story,
//!   and at n = 64 the call overhead is still visible while at n = 1024 it is
//!   not; a change that only helps long polynomials should be seen to do so.
//! * `mul` — schoolbook convolution, `O(n^2)`. Karatsuba or an NTT would change
//!   the exponent, and an exponent cannot be seen at a single point. 1024 is
//!   deliberately absent: at 16x the work of 256 it would dominate the suite.
//!
//! # Allocation is part of the measurement
//!
//! Every operation here returns a freshly allocated `Vec`, and the timed region
//! includes both that allocation and the drop of that *same* iteration's
//! result — criterion's `Bencher::iter` is `for _ in 0..iters {
//! black_box(routine()); }`, so the returned value is dropped inside the loop,
//! at the end of the statement that produced it. That is not an accident to be
//! corrected: it is what a caller pays,
//! and an "optimization" that halves the arithmetic while doubling the
//! allocations has not made anything faster. Both variants pay it identically.
//!
//! The exception is `trim`, which consumes its input and therefore needs a fresh
//! one per iteration. It uses `iter_batched`, so the clone that produces that
//! input is built outside the timed region — otherwise the row would be a
//! measurement of `Vec::clone`.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

const _: () = assert!(support::P == cpoly::field::P);
const _: () = assert!(support::P == cpoly_genesis::field::P);

macro_rules! define_cases {
    ($modname:ident, $cp:path) => {
        mod $modname {
            use std::hint::black_box;

            use $cp as cp;

            use crate::support::{self, Mode};

            // -- corpus -----------------------------------------------------

            fn coeffs(tag: u64, n: usize) -> Vec<cp::Ext4> {
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

            fn poly(tag: u64, n: usize) -> cp::UnivariatePoly {
                cp::UnivariatePoly::from_coeffs(coeffs(tag, n))
            }

            /// A polynomial whose top quarter is zero.
            ///
            /// `trim` scans down from the end and stops at the first non-zero
            /// coefficient, so a fully random polynomial would exit after one
            /// comparison and measure nothing, while an all-zero one would be a
            /// best case that no caller ever hits. A quarter is a real trim.
            fn poly_with_zero_tail(tag: u64, n: usize) -> cp::UnivariatePoly {
                let mut c = coeffs(tag, n);
                let keep = n - n / 4;
                for slot in c.iter_mut().skip(keep) {
                    *slot = cp::Ext4::ZERO;
                }
                cp::UnivariatePoly::from_coeffs(c)
            }

            fn scalar(tag: u64) -> cp::Ext4 {
                let w = support::words(tag, 4);
                cp::Ext4::new(
                    cp::Fp::new(w[0]),
                    cp::Fp::new(w[1]),
                    cp::Fp::new(w[2]),
                    cp::Fp::new(w[3]),
                )
            }

            // -- digests ----------------------------------------------------

            fn d_ext4(x: &cp::Ext4) -> u64 {
                let a = support::mix(0, x.c0.to_u64());
                let a = support::mix(a, x.c1.to_u64());
                let a = support::mix(a, x.c2.to_u64());
                support::mix(a, x.c3.to_u64())
            }

            fn d_slice(v: &[cp::Ext4]) -> u64 {
                // The length is folded in first: a trim that removes the wrong
                // number of coefficients must not be able to collide with one
                // that removes the right number.
                v.iter()
                    .fold(support::mix(0, v.len() as u64), |a, x| support::mix(a, d_ext4(x)))
            }

            fn d_poly(p: &cp::UnivariatePoly) -> u64 {
                d_slice(p.coeffs())
            }

            // `&Vec` rather than `&[_]` because this is the `digest` argument of
            // `support::run`, whose `R` is the body's return type, and the
            // bodies that use it return an owned `Vec`.
            #[allow(clippy::ptr_arg)]
            fn d_polys(v: &Vec<cp::UnivariatePoly>) -> u64 {
                v.iter().fold(0u64, |a, p| support::mix(a, d_poly(p)))
            }

            // -- construction -----------------------------------------------

            /// `Raw.C`. One `Vec::new` and one `push`, so this is dominated by
            /// the allocator — measured `n` at a time to lift it above the
            /// timer, and worth a row because "constant" acquiring a capacity
            /// argument is exactly the kind of change that looks free.
            pub fn constant(m: Mode<'_, '_>, n: usize) -> u64 {
                let cs = coeffs(0x0301, n);
                support::run(
                    m,
                    || {
                        let cs = black_box(&cs);
                        let mut out = Vec::with_capacity(cs.len());
                        let mut i = 0usize;
                        while i < cs.len() {
                            out.push(cp::UnivariatePoly::constant(cs[i]));
                            i += 1;
                        }
                        out
                    },
                    d_polys,
                )
            }

            /// `Raw.X`. See [`constant`].
            pub fn x(m: Mode<'_, '_>, n: usize) -> u64 {
                support::run(
                    m,
                    || {
                        let n = black_box(n);
                        let mut out = Vec::with_capacity(n);
                        let mut i = 0usize;
                        while i < n {
                            out.push(cp::UnivariatePoly::x());
                            i += 1;
                        }
                        out
                    },
                    d_polys,
                )
            }

            // -- canonicalization -------------------------------------------

            pub fn trim(m: Mode<'_, '_>, n: usize) -> u64 {
                let p = poly_with_zero_tail(0x0302, n);
                support::run_batched(m, || p.clone(), cp::UnivariatePoly::trim, d_poly)
            }

            // -- evaluation --------------------------------------------------

            pub fn eval(m: Mode<'_, '_>, n: usize) -> u64 {
                let p = poly(0x0303, n);
                let pt = scalar(0x0304);
                support::run(
                    m,
                    || black_box(&p).eval(black_box(pt)),
                    d_ext4,
                )
            }

            // -- arithmetic ---------------------------------------------------

            pub fn add(m: Mode<'_, '_>, n: usize) -> u64 {
                let (p, q) = (poly(0x0305, n), poly(0x0306, n));
                support::run(m, || black_box(&p) + black_box(&q), d_poly)
            }

            pub fn add_untrimmed(m: Mode<'_, '_>, n: usize) -> u64 {
                let (p, q) = (poly(0x0307, n), poly(0x0308, n));
                support::run(m, || black_box(&p).add_untrimmed(black_box(&q)), d_poly)
            }

            pub fn sub(m: Mode<'_, '_>, n: usize) -> u64 {
                let (p, q) = (poly(0x0309, n), poly(0x030A, n));
                support::run(m, || black_box(&p) - black_box(&q), d_poly)
            }

            pub fn neg(m: Mode<'_, '_>, n: usize) -> u64 {
                let p = poly(0x030B, n);
                support::run(m, || { let p = black_box(&p); -p }, d_poly)
            }

            pub fn smul(m: Mode<'_, '_>, n: usize) -> u64 {
                let p = poly(0x030C, n);
                let s = scalar(0x030D);
                support::run(m, || black_box(&p) * black_box(s), d_poly)
            }

            pub fn mul(m: Mode<'_, '_>, n: usize) -> u64 {
                let (p, q) = (poly(0x030E, n), poly(0x030F, n));
                support::run(m, || black_box(&p) * black_box(&q), d_poly)
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

fn univariate_benches(c: &mut Criterion) {
    // The run's sanity check: identical code in both variants, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the
    // machine is in the same state the first real cases will see.
    bench_case!(c, "_control/univariate", control, [support::CONTROL_N]);

    let n = support::UNI_N;

    // @covers univariate::UnivariatePoly::constant
    bench_case!(c, "univariate/constant", constant, [n]);
    // @covers univariate::UnivariatePoly::x
    bench_case!(c, "univariate/x", x, [n]);
    // @covers univariate::UnivariatePoly::trim
    bench_case!(c, "univariate/trim", trim, [n]);

    // @covers univariate::UnivariatePoly::eval
    bench_case!(c, "univariate/eval", eval, [support::UNI_EVAL_N[0], support::UNI_EVAL_N[1]]);

    // @covers univariate::<&UnivariatePoly as Add<&UnivariatePoly>>::add
    bench_case!(c, "univariate/add", add, [n]);
    // @covers univariate::UnivariatePoly::add_untrimmed
    bench_case!(c, "univariate/add_untrimmed", add_untrimmed, [n]);
    // @covers univariate::<&UnivariatePoly as Sub<&UnivariatePoly>>::sub
    bench_case!(c, "univariate/sub", sub, [n]);
    // @covers univariate::<&UnivariatePoly as Neg>::neg
    bench_case!(c, "univariate/neg", neg, [n]);
    // @covers univariate::<&UnivariatePoly as Mul<Ext4>>::mul
    bench_case!(c, "univariate/smul", smul, [n]);

    // @covers univariate::<&UnivariatePoly as Mul<&UnivariatePoly>>::mul
    bench_case!(c, "univariate/mul", mul, [support::UNI_MUL_N[0], support::UNI_MUL_N[1]]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = univariate_benches
}
criterion_main!(benches);
