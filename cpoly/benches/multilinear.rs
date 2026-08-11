//! Benchmarks for [`cpoly::multilinear`] — the two readings of a `2^vars`-entry
//! table, and the transforms between them.
//!
//! # The parameter is `vars`, not the table length
//!
//! Every case id ends in the arity, so `multilinear/dot/12` is a dot product
//! over `2^12 = 4096` entries. Reading the exponent keeps the two-reading
//! structure visible and matches how the `CompPoly` definitions are indexed.
//!
//! * The flat `O(2^vars)` passes — the pointwise operations, the single layers,
//!   the allocators — run at [`support::ML_VARS`] only. They are one loop over
//!   one table; a second arity would restate that.
//! * The evaluators and transforms run at both of [`support::ML_VARS_2`],
//!   because each is `O(vars * 2^vars)` or `O(2^vars)` and the pairs of them are
//!   *asymptotically different algorithms for the same answer*: `eval` builds a
//!   basis, `eval_horner` folds; `eval` dots against a Lagrange basis,
//!   `eval_mle` folds. Comparing those two families is much of what the
//!   optimization loop will be doing, and a single arity cannot show a
//!   `vars`-factor.
//!
//! At `vars = 12` a table is 4096 * 32 bytes = 128 KiB, which is *exactly* this
//! machine's P-core L1d (`hw.perflevel0.l1dcachesize` = 131072; the E-core's is
//! half that) and comfortably inside L2 (16 MiB). So one table only just fits,
//! and any case holding two or three of them live — `dot`, `add_pointwise`,
//! `eq_tilde` — spills. That is a deliberate operating point: it is where a
//! layout change has something to say, whereas a table several times smaller
//! than L1 would hide it.
//!
//! # The two readings are not interchangeable
//!
//! `MultilinearPoly` and `MultilinearEvals` are separate types wrapping the same
//! bytes, and each has its own `eval`. The cases keep them apart by name —
//! `poly_*` and `evals_*` — because pairing a coefficient table with the
//! Lagrange evaluator is a mistake that still typechecks in Lean (see
//! `.claude/skills/aeneas-idiomatic-rust`), and a benchmark that made it would
//! report a plausible number for the wrong function.

mod support;

use criterion::{criterion_group, criterion_main, Criterion};

const _: () = assert!(support::P == cpoly::field::P);
const _: () = assert!(support::P == cpoly_genesis::field::P);
#[cfg(feature = "candidate")]
const _: () = assert!(support::P == cpoly_candidate::field::P);

macro_rules! define_cases {
    ($modname:ident, $cp:path) => {
        mod $modname {
            use std::hint::black_box;

            use $cp as cp;

            use crate::support::{self, Mode};

            // -- corpus -----------------------------------------------------

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

            fn table(tag: u64, vars: usize) -> Vec<cp::Ext4> {
                ext4s(tag, cp::multilinear::table_len(vars))
            }

            /// An evaluation point off the Boolean hypercube.
            ///
            /// A point of zeros and ones would make `lagrange_basis` produce a
            /// single non-zero entry and `1 - x` collapse to a constant, turning
            /// several of these into best cases no prover ever evaluates at.
            fn point(tag: u64, vars: usize) -> Vec<cp::Ext4> {
                ext4s(tag, vars)
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
                v.iter()
                    .fold(support::mix(0, v.len() as u64), |a, x| support::mix(a, d_ext4(x)))
            }

            // `&Vec` rather than `&[_]` because these are used as the `digest`
            // argument of `support::run`, whose `R` is the body's return type,
            // and the bodies return owned `Vec`s.
            #[allow(clippy::ptr_arg)]
            fn d_vec(v: &Vec<cp::Ext4>) -> u64 {
                d_slice(v)
            }

            fn d_poly(p: &cp::MultilinearPoly) -> u64 {
                d_slice(p.coeffs())
            }

            fn d_evals(e: &cp::MultilinearEvals) -> u64 {
                d_slice(e.values())
            }

            // -- allocation and conforming ------------------------------------

            pub fn poly_zeros(m: Mode<'_, '_>, vars: usize) -> u64 {
                support::run(m, || cp::MultilinearPoly::zeros(black_box(vars)), d_poly)
            }

            pub fn evals_zeros(m: Mode<'_, '_>, vars: usize) -> u64 {
                support::run(m, || cp::MultilinearEvals::zeros(black_box(vars)), d_evals)
            }

            /// `ofArray` pads a short list and truncates a long one. The corpus
            /// is three quarters of a table, so the padding path is the one
            /// actually taken — an exactly-sized input would make the `resize`
            /// a no-op and measure nothing.
            pub fn poly_from_coeffs(m: Mode<'_, '_>, vars: usize) -> u64 {
                let n = cp::multilinear::table_len(vars);
                let base = ext4s(0x0401, n - n / 4);
                support::run_batched(
                    m,
                    || base.clone(),
                    move |c| cp::MultilinearPoly::from_coeffs(c, vars),
                    d_poly,
                )
            }

            // -- flat passes over one table ------------------------------------

            pub fn dot(m: Mode<'_, '_>, vars: usize) -> u64 {
                let (a, b) = (table(0x0402, vars), table(0x0403, vars));
                support::run(
                    m,
                    || cp::multilinear::dot(black_box(&a), black_box(&b)),
                    d_ext4,
                )
            }

            pub fn add_pointwise(m: Mode<'_, '_>, vars: usize) -> u64 {
                let (a, b) = (table(0x0404, vars), table(0x0405, vars));
                support::run(
                    m,
                    || cp::multilinear::add_pointwise(black_box(&a), black_box(&b)),
                    d_vec,
                )
            }

            pub fn neg_pointwise(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x0406, vars);
                support::run(m, || cp::multilinear::neg_pointwise(black_box(&a)), d_vec)
            }

            pub fn scale_pointwise(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x0407, vars);
                let s = scalar(0x0408);
                support::run(
                    m,
                    || cp::multilinear::scale_pointwise(black_box(&a), black_box(s)),
                    d_vec,
                )
            }

            pub fn eval_horner_layer(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x0409, vars);
                let x0 = scalar(0x040A);
                support::run(
                    m,
                    || cp::multilinear::eval_horner_layer(black_box(&a), black_box(x0)),
                    d_vec,
                )
            }

            pub fn eval_mle_layer(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x040B, vars);
                let x0 = scalar(0x040C);
                support::run(
                    m,
                    || cp::multilinear::eval_mle_layer(black_box(&a), black_box(x0)),
                    d_vec,
                )
            }

            /// The level is `vars / 2`: level 0 has stride 1 and level
            /// `vars - 1` splits the table in half, and neither end is
            /// representative of the strided access the middle levels do.
            pub fn mono_to_lagrange_level(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x040D, vars);
                let j = vars / 2;
                support::run(
                    m,
                    || cp::multilinear::mono_to_lagrange_level(black_box(&a), black_box(j)),
                    d_vec,
                )
            }

            /// See [`mono_to_lagrange_level`].
            pub fn lagrange_to_mono_level(m: Mode<'_, '_>, vars: usize) -> u64 {
                let a = table(0x040E, vars);
                let j = vars / 2;
                support::run(
                    m,
                    || cp::multilinear::lagrange_to_mono_level(black_box(&a), black_box(j)),
                    d_vec,
                )
            }

            // -- bases ----------------------------------------------------------

            pub fn monomial_basis(m: Mode<'_, '_>, vars: usize) -> u64 {
                let pt = point(0x040F, vars);
                support::run(
                    m,
                    || cp::multilinear::monomial_basis(black_box(&pt)),
                    d_vec,
                )
            }

            pub fn lagrange_basis(m: Mode<'_, '_>, vars: usize) -> u64 {
                let pt = point(0x0410, vars);
                support::run(
                    m,
                    || cp::multilinear::lagrange_basis(black_box(&pt)),
                    d_evals,
                )
            }

            pub fn eq_tilde(m: Mode<'_, '_>, vars: usize) -> u64 {
                let (w, x) = (point(0x0411, vars), point(0x0412, vars));
                support::run(
                    m,
                    || cp::multilinear::eq_tilde(black_box(&w), black_box(&x)),
                    d_ext4,
                )
            }

            // -- the monomial reading -------------------------------------------

            pub fn poly_eval(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x0413, vars), vars);
                let pt = point(0x0414, vars);
                support::run(m, || black_box(&p).eval(black_box(&pt)), d_ext4)
            }

            pub fn poly_eval_horner(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x0415, vars), vars);
                let pt = point(0x0416, vars);
                support::run(m, || black_box(&p).eval_horner(black_box(&pt)), d_ext4)
            }

            pub fn poly_to_evals(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x0417, vars), vars);
                support::run_batched(m, || p.clone(), move |q| q.to_evals(vars), d_evals)
            }

            pub fn poly_neg(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x0418, vars), vars);
                support::run(m, || { let p = black_box(&p); -p }, d_poly)
            }

            pub fn poly_smul(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x0419, vars), vars);
                let s = scalar(0x041A);
                support::run(m, || black_box(&p) * black_box(s), d_poly)
            }

            pub fn poly_add(m: Mode<'_, '_>, vars: usize) -> u64 {
                let p = cp::MultilinearPoly::from_coeffs(table(0x041B, vars), vars);
                let q = cp::MultilinearPoly::from_coeffs(table(0x041C, vars), vars);
                support::run(m, || black_box(&p) + black_box(&q), d_poly)
            }

            // -- the Lagrange reading -------------------------------------------

            pub fn evals_eval(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x041D, vars));
                let pt = point(0x041E, vars);
                support::run(m, || black_box(&e).eval(black_box(&pt)), d_ext4)
            }

            pub fn evals_eval_mle(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x041F, vars));
                let pt = point(0x0420, vars);
                support::run(m, || black_box(&e).eval_mle(black_box(&pt)), d_ext4)
            }

            pub fn evals_to_coeffs(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x0421, vars));
                support::run_batched(m, || e.clone(), move |f| f.to_coeffs(vars), d_poly)
            }

            pub fn evals_neg(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x0422, vars));
                support::run(m, || { let e = black_box(&e); -e }, d_evals)
            }

            pub fn evals_smul(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x0423, vars));
                let s = scalar(0x0424);
                support::run(m, || black_box(&e) * black_box(s), d_evals)
            }

            pub fn evals_add(m: Mode<'_, '_>, vars: usize) -> u64 {
                let e = cp::MultilinearEvals::from_values(table(0x0425, vars));
                let f = cp::MultilinearEvals::from_values(table(0x0426, vars));
                support::run(m, || black_box(&e) + black_box(&f), d_evals)
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

fn multilinear_benches(c: &mut Criterion) {
    // The run's sanity check: identical code in both variants, so anything it
    // reads is the harness disagreeing with itself. Runs first, while the
    // machine is in the same state the first real cases will see.
    bench_case!(c, "_control/multilinear", control, [support::CONTROL_N]);

    let v = support::ML_VARS;
    let [v0, v1] = support::ML_VARS_2;

    // -- flat passes, one arity --------------------------------------------

    // @covers multilinear::MultilinearPoly::zeros
    bench_case!(c, "multilinear/poly_zeros", poly_zeros, [v]);
    // @covers multilinear::MultilinearEvals::zeros
    bench_case!(c, "multilinear/evals_zeros", evals_zeros, [v]);
    // @covers multilinear::MultilinearPoly::from_coeffs
    bench_case!(c, "multilinear/poly_from_coeffs", poly_from_coeffs, [v]);

    // @covers multilinear::dot
    bench_case!(c, "multilinear/dot", dot, [v]);
    // @covers multilinear::add_pointwise
    bench_case!(c, "multilinear/add_pointwise", add_pointwise, [v]);
    // @covers multilinear::neg_pointwise
    bench_case!(c, "multilinear/neg_pointwise", neg_pointwise, [v]);
    // @covers multilinear::scale_pointwise
    bench_case!(c, "multilinear/scale_pointwise", scale_pointwise, [v]);

    // @covers multilinear::eval_horner_layer
    bench_case!(c, "multilinear/eval_horner_layer", eval_horner_layer, [v]);
    // @covers multilinear::eval_mle_layer
    bench_case!(c, "multilinear/eval_mle_layer", eval_mle_layer, [v]);
    // @covers multilinear::mono_to_lagrange_level
    bench_case!(c, "multilinear/mono_to_lagrange_level", mono_to_lagrange_level, [v]);
    // @covers multilinear::lagrange_to_mono_level
    bench_case!(c, "multilinear/lagrange_to_mono_level", lagrange_to_mono_level, [v]);

    // @covers multilinear::<&MultilinearPoly as Neg>::neg
    bench_case!(c, "multilinear/poly_neg", poly_neg, [v]);
    // @covers multilinear::<&MultilinearPoly as Mul<Ext4>>::mul
    bench_case!(c, "multilinear/poly_smul", poly_smul, [v]);
    // @covers multilinear::<&MultilinearPoly as Add<&MultilinearPoly>>::add
    bench_case!(c, "multilinear/poly_add", poly_add, [v]);
    // @covers multilinear::<&MultilinearEvals as Neg>::neg
    bench_case!(c, "multilinear/evals_neg", evals_neg, [v]);
    // @covers multilinear::<&MultilinearEvals as Mul<Ext4>>::mul
    bench_case!(c, "multilinear/evals_smul", evals_smul, [v]);
    // @covers multilinear::<&MultilinearEvals as Add<&MultilinearEvals>>::add
    bench_case!(c, "multilinear/evals_add", evals_add, [v]);

    // -- algorithm families, two arities -----------------------------------

    // @covers multilinear::monomial_basis
    bench_case!(c, "multilinear/monomial_basis", monomial_basis, [v0, v1]);
    // @covers multilinear::lagrange_basis
    bench_case!(c, "multilinear/lagrange_basis", lagrange_basis, [v0, v1]);
    // @covers multilinear::eq_tilde
    bench_case!(c, "multilinear/eq_tilde", eq_tilde, [v0, v1]);

    // @covers multilinear::MultilinearPoly::eval
    bench_case!(c, "multilinear/poly_eval", poly_eval, [v0, v1]);
    // @covers multilinear::MultilinearPoly::eval_horner
    bench_case!(c, "multilinear/poly_eval_horner", poly_eval_horner, [v0, v1]);
    // @covers multilinear::MultilinearPoly::to_evals
    bench_case!(c, "multilinear/poly_to_evals", poly_to_evals, [v0, v1]);

    // @covers multilinear::MultilinearEvals::eval
    bench_case!(c, "multilinear/evals_eval", evals_eval, [v0, v1]);
    // @covers multilinear::MultilinearEvals::eval_mle
    bench_case!(c, "multilinear/evals_eval_mle", evals_eval_mle, [v0, v1]);
    // @covers multilinear::MultilinearEvals::to_coeffs
    bench_case!(c, "multilinear/evals_to_coeffs", evals_to_coeffs, [v0, v1]);
}

criterion_group! {
    name = benches;
    config = support::criterion_config();
    targets = multilinear_benches
}
criterion_main!(benches);
