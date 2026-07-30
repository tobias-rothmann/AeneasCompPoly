//! Semantic validation of `cpoly::cmlpoly` against independent brute-force
//! references, run *before* the Lean equivalence proofs are attempted.
//!
//! Each test states the mathematical property that the corresponding
//! `CompPoly.CMlPolynomial` / `CMlPolynomialEval` definition has, and checks it
//! against the Rust implementation over exhaustive small cases plus
//! deterministic pseudo-random data.  The references here are written
//! independently (`u128` base-field arithmetic, a differently-shaped extension
//! product, explicit bit tests, `O(4^n)` sums) so that a shared mistake is
//! unlikely.  See `tests/field_semantics.rs` for the field layer these build on.

use cpoly::cmlpoly::*;
use cpoly::field::{Ext4, EGEN, P, W};

/// The independent representation of an extension element: little-endian
/// coefficients of `Y^0 .. Y^3`.
type E = [u64; 4];

fn of(a: Ext4) -> E {
    [a.c0, a.c1, a.c2, a.c3]
}

fn to(a: E) -> Ext4 {
    Ext4 {
        c0: a[0],
        c1: a[1],
        c2: a[2],
        c3: a[3],
    }
}

fn ofv(v: &[Ext4]) -> Vec<E> {
    v.iter().map(|&a| of(a)).collect()
}

fn tov(v: &[E]) -> Vec<Ext4> {
    v.iter().map(|&a| to(a)).collect()
}

const RZERO: E = [0, 0, 0, 0];

fn rone() -> E {
    [1 % P, 0, 0, 0]
}

// ---------------------------------------------------------------
// Independent field reference (u128, no clever tricks).
// ---------------------------------------------------------------

fn badd(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % P as u128) as u64
}
fn bsub(a: u64, b: u64) -> u64 {
    ((a as u128 + P as u128 - b as u128) % P as u128) as u64
}
fn bmul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % P as u128) as u64
}

fn radd(a: E, b: E) -> E {
    let mut r = RZERO;
    for i in 0..4 {
        r[i] = badd(a[i], b[i]);
    }
    r
}

fn rsub(a: E, b: E) -> E {
    let mut r = RZERO;
    for i in 0..4 {
        r[i] = bsub(a[i], b[i]);
    }
    r
}

fn rneg(a: E) -> E {
    rsub(RZERO, a)
}

/// `a * b` in `F_P[Y] / (Y^4 - W)`: full degree-6 product, then fold the high
/// coefficients down one at a time.  Deliberately not the shape `emul` uses.
fn rmul(a: E, b: E) -> E {
    let mut r = [0u64; 7];
    for i in 0..4 {
        for j in 0..4 {
            r[i + j] = badd(r[i + j], bmul(a[i], b[j]));
        }
    }
    for k in (4..7).rev() {
        r[k - 4] = badd(r[k - 4], bmul(W, r[k]));
        r[k] = 0;
    }
    [r[0], r[1], r[2], r[3]]
}

/// Deterministic pseudo-random reduced extension elements (SplitMix64).
fn sample(seed: u64, count: usize) -> Vec<E> {
    let mut s = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut flat = Vec::new();
    for _ in 0..(4 * count) {
        s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        flat.push(z % P);
    }
    (0..count)
        .map(|i| [flat[4 * i], flat[4 * i + 1], flat[4 * i + 2], flat[4 * i + 3]])
        .collect()
}

fn bit(i: usize, j: usize) -> bool {
    (i >> j) & 1 == 1
}

// ---------------------------------------------------------------
// References mirroring the CompPoly Lean definitions.
// ---------------------------------------------------------------

/// `CMlPolynomial.monomialBasis`: `∏_j (bit j of i ? w[j] : 1)`.
fn ref_monomial_basis(w: &[E]) -> Vec<E> {
    let n = w.len();
    (0..(1usize << n))
        .map(|i| {
            let mut acc = rone();
            for j in 0..n {
                if bit(i, j) {
                    acc = rmul(acc, w[j]);
                }
            }
            acc
        })
        .collect()
}

/// `CMlPolynomialEval.lagrangeBasis`: `∏_j (bit j of i ? w[j] : 1 - w[j])`.
fn ref_lagrange_basis(w: &[E]) -> Vec<E> {
    let n = w.len();
    (0..(1usize << n))
        .map(|i| {
            let mut acc = rone();
            for j in 0..n {
                acc = rmul(acc, if bit(i, j) { w[j] } else { rsub(rone(), w[j]) });
            }
            acc
        })
        .collect()
}

/// `Vector.dotProduct`.
fn ref_dot(a: &[E], b: &[E]) -> E {
    let mut acc = RZERO;
    for i in 0..b.len() {
        acc = radd(acc, rmul(a[i], b[i]));
    }
    acc
}

/// `CMlPolynomial.monoToLagrangeSpec`: `out[i] = Σ_{j ⊆ i} p[j]`.
fn ref_zeta_spec(p: &[E], n: usize) -> Vec<E> {
    (0..(1usize << n))
        .map(|i| {
            let mut acc = RZERO;
            for j in 0..(1usize << n) {
                if i & j == j {
                    acc = radd(acc, p[j]);
                }
            }
            acc
        })
        .collect()
}

/// `CMlPolynomial.lagrangeToMonoSpec`:
/// `out[i] = Σ_{j ⊆ i} (-1)^(popcount i - popcount j) p[j]`.
fn ref_mobius_spec(p: &[E], n: usize) -> Vec<E> {
    (0..(1usize << n))
        .map(|i| {
            let mut acc = RZERO;
            for j in 0..(1usize << n) {
                if i & j == j {
                    let d = (i.count_ones() - j.count_ones()) % 2;
                    acc = if d == 0 { radd(acc, p[j]) } else { rsub(acc, p[j]) };
                }
            }
            acc
        })
        .collect()
}

/// Evaluate a coefficient-form polynomial directly from its definition:
/// `Σ_i p[i] · ∏_{bit j of i set} x[j]`.
fn ref_eval_coeffs(p: &[E], x: &[E]) -> E {
    ref_dot(p, &ref_monomial_basis(x))
}

// ---------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------

#[test]
fn pow2_matches_shift() {
    for n in 0..20 {
        assert_eq!(pow2(n), 1usize << n, "pow2({n})");
    }
}

#[test]
fn zero_is_all_zeros() {
    for n in 0..8 {
        let z = zero(n);
        assert_eq!(z.len(), 1usize << n);
        assert!(ofv(&z).iter().all(|&c| c == RZERO));
    }
}

#[test]
fn of_array_pads_and_truncates() {
    let coeffs = sample(1, 5);
    let cr = tov(&coeffs);
    // Truncate: 2^1 = 2 < 5.
    assert_eq!(ofv(&of_array(&cr, 1)), vec![coeffs[0], coeffs[1]]);
    // Exact: 2^2 = 4 < 5 still truncates.
    assert_eq!(ofv(&of_array(&cr, 2)), coeffs[0..4].to_vec());
    // Pad: 2^3 = 8 > 5.
    let padded = ofv(&of_array(&cr, 3));
    assert_eq!(padded.len(), 8);
    assert_eq!(&padded[0..5], &coeffs[..]);
    assert!(padded[5..].iter().all(|&c| c == RZERO));
}

#[test]
fn add_is_pointwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 10, sz);
        let q = sample(n as u64 + 99, sz);
        let r = ofv(&add(&tov(&p), &tov(&q)));
        assert_eq!(r.len(), sz);
        for i in 0..sz {
            assert_eq!(r[i], radd(p[i], q[i]), "n={n} i={i}");
        }
    }
}

#[test]
fn bases_match_reference() {
    for n in 0..8 {
        let w = sample(n as u64 + 7, n);
        assert_eq!(
            ofv(&monomial_basis(&tov(&w))),
            ref_monomial_basis(&w),
            "monomial n={n}"
        );
        assert_eq!(
            ofv(&lagrange_basis(&tov(&w))),
            ref_lagrange_basis(&w),
            "lagrange n={n}"
        );
    }
}

/// The Lagrange basis is a partition of unity, and at a Boolean point it is the
/// indicator of that point.  Both are basis-defining properties.
#[test]
fn lagrange_basis_properties() {
    for n in 0..7 {
        let w = sample(n as u64 + 21, n);
        let b = ofv(&lagrange_basis(&tov(&w)));
        let total = b.iter().fold(RZERO, |acc, &c| radd(acc, c));
        assert_eq!(total, rone(), "partition of unity, n={n}");

        // At a Boolean point k, lagrangeBasis is the indicator of k.
        for k in 0..(1usize << n) {
            let point: Vec<E> = (0..n)
                .map(|j| if bit(k, j) { rone() } else { RZERO })
                .collect();
            let bk = ofv(&lagrange_basis(&tov(&point)));
            for i in 0..(1usize << n) {
                let expect = if i == k { rone() } else { RZERO };
                assert_eq!(bk[i], expect, "indicator n={n} k={k} i={i}");
            }
        }
    }
}

#[test]
fn eval_matches_reference() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 31, sz);
        let w = sample(n as u64 + 41, n);
        assert_eq!(
            of(eval(&tov(&p), &tov(&w))),
            ref_eval_coeffs(&p, &w),
            "eval n={n}"
        );
        let lb = ref_lagrange_basis(&w);
        assert_eq!(
            of(eval_lagrange(&tov(&p), &tov(&w))),
            ref_dot(&p, &lb),
            "eval_lagrange n={n}"
        );
    }
}

#[test]
fn eval_horner_matches_eval() {
    for n in 0..9 {
        let sz = 1usize << n;
        let p = tov(&sample(n as u64 + 51, sz));
        let w = tov(&sample(n as u64 + 61, n));
        assert_eq!(of(eval_horner(&p, &w)), of(eval(&p, &w)), "horner n={n}");
    }
}

#[test]
fn eval_mle_matches_eval_lagrange() {
    for n in 0..9 {
        let sz = 1usize << n;
        let v = tov(&sample(n as u64 + 71, sz));
        let w = tov(&sample(n as u64 + 81, n));
        assert_eq!(
            of(eval_mle(&v, &w)),
            of(eval_lagrange(&v, &w)),
            "mle n={n}"
        );
    }
}

#[test]
fn zeta_matches_naive_spec() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 91, sz);
        assert_eq!(
            ofv(&mono_to_lagrange(tov(&p), n)),
            ref_zeta_spec(&p, n),
            "zeta n={n}"
        );
    }
}

#[test]
fn mobius_matches_naive_spec() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 101, sz);
        assert_eq!(
            ofv(&lagrange_to_mono(tov(&p), n)),
            ref_mobius_spec(&p, n),
            "mobius n={n}"
        );
    }
}

#[test]
fn zeta_mobius_roundtrip() {
    for n in 0..9 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 111, sz);
        assert_eq!(
            ofv(&lagrange_to_mono(mono_to_lagrange(tov(&p), n), n)),
            p,
            "mobius∘zeta n={n}"
        );
        assert_eq!(
            ofv(&mono_to_lagrange(lagrange_to_mono(tov(&p), n), n)),
            p,
            "zeta∘mobius n={n}"
        );
    }
}

/// The semantic contract of the zeta transform: it turns coefficients into
/// hypercube *evaluations*.  Entry `i` of `mono_to_lagrange(p)` must be `p`
/// evaluated at the Boolean point encoded by `i`.
#[test]
fn zeta_is_hypercube_evaluation() {
    for n in 0..7 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 121, sz);
        let evals = ofv(&mono_to_lagrange(tov(&p), n));
        for i in 0..sz {
            let point: Vec<E> = (0..n)
                .map(|j| if bit(i, j) { rone() } else { RZERO })
                .collect();
            assert_eq!(evals[i], ref_eval_coeffs(&p, &point), "n={n} i={i}");
        }
    }
}

/// The two representations describe the same function: evaluating the
/// coefficient form and the zeta-transformed evaluation form at the same
/// arbitrary (non-Boolean) point must agree.
#[test]
fn representations_agree_off_hypercube() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 131, sz);
        let evals = mono_to_lagrange(tov(&p), n);
        let w = tov(&sample(n as u64 + 141, n));
        assert_eq!(
            of(eval(&tov(&p), &w)),
            of(eval_lagrange(&evals, &w)),
            "n={n}"
        );
    }
}

/// `eq~(w, x) = ∏_j (w[j] x[j] + (1 - w[j])(1 - x[j]))`, and it is symmetric.
#[test]
fn eq_tilde_matches_product_form() {
    for n in 0..8 {
        let w = sample(n as u64 + 151, n);
        let x = sample(n as u64 + 161, n);
        let mut expect = rone();
        for j in 0..n {
            let t = radd(
                rmul(w[j], x[j]),
                rmul(rsub(rone(), w[j]), rsub(rone(), x[j])),
            );
            expect = rmul(expect, t);
        }
        assert_eq!(of(eq_tilde(&tov(&w), &tov(&x))), expect, "eq_tilde n={n}");
        assert_eq!(
            of(eq_tilde(&tov(&w), &tov(&x))),
            of(eq_tilde(&tov(&x), &tov(&w))),
            "symmetry n={n}"
        );
    }
}

/// Negation and scalar multiplication are the univariate ones, reused: the Lean
/// development states their multilinear specs about `cpoly::cpoly::neg` /
/// `cpoly::cpoly::smul`.
#[test]
fn neg_and_smul_are_coefficientwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 181, sz);
        let s = sample(n as u64 + 191, 1)[0];
        assert_eq!(
            ofv(&cpoly::cpoly::neg(&tov(&p))),
            p.iter().map(|&a| rneg(a)).collect::<Vec<E>>(),
            "neg n={n}"
        );
        assert_eq!(
            ofv(&cpoly::cpoly::smul(to(s), &tov(&p))),
            p.iter().map(|&a| rmul(s, a)).collect::<Vec<E>>(),
            "smul n={n}"
        );
    }
}

/// A hand-computed case, to pin the little-endian index convention:
/// `n = 2`, `p = 1 + 2 X0 + 3 X1 + 4 X0 X1`, evaluated at `(5, 7)`
/// is `1 + 10 + 21 + 140 = 172`.
#[test]
fn little_endian_convention_pinned() {
    let cst = |k: u64| -> E { [k, 0, 0, 0] };
    let p = vec![cst(1), cst(2), cst(3), cst(4)];
    let w = vec![cst(5), cst(7)];
    assert_eq!(of(eval(&tov(&p), &tov(&w))), cst(172));
    assert_eq!(of(eval_horner(&tov(&p), &tov(&w))), cst(172));
    // Hypercube evaluations at (0,0), (1,0), (0,1), (1,1): 1, 3, 4, 10.
    assert_eq!(
        ofv(&mono_to_lagrange(tov(&p), 2)),
        vec![cst(1), cst(3), cst(4), cst(10)]
    );
    assert_eq!(
        ofv(&lagrange_to_mono(tov(&[cst(1), cst(3), cst(4), cst(10)]), 2)),
        p
    );
}

/// The same pinned polynomial, but evaluated at a point that genuinely lives in
/// the extension: `p(Y, Y) = 1 + 2Y + 3Y + 4Y^2 = 1 + 5Y + 4Y^2`.  A field-layer
/// mistake that happens to be invisible on the base subfield shows up here.
#[test]
fn extension_point_pinned() {
    let cst = |k: u64| -> E { [k, 0, 0, 0] };
    let p = tov(&[cst(1), cst(2), cst(3), cst(4)]);
    let w = vec![EGEN, EGEN];
    assert_eq!(of(eval(&p, &w)), [1, 5, 4, 0]);
    assert_eq!(of(eval_horner(&p, &w)), [1, 5, 4, 0]);

    // At `(Y^3, Y^3)`: 1 + 2Y^3 + 3Y^3 + 4Y^6 = 1 + 4*W*Y^2 + 5Y^3.
    let y3: E = [0, 0, 0, 1];
    let w2 = vec![to(y3), to(y3)];
    assert_eq!(of(eval(&p, &w2)), [1, 0, 4 * W, 5]);
    assert_eq!(of(eval_horner(&p, &w2)), [1, 0, 4 * W, 5]);
}
