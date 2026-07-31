//! Semantic validation of `cpoly::multilinear` against independent brute-force
//! references, run *before* the Lean equivalence proofs are attempted.
//!
//! Each test states the mathematical property that the corresponding
//! `CompPoly.CMlPolynomial` / `CMlPolynomialEval` definition has, and checks it
//! against the Rust implementation over exhaustive small cases plus
//! deterministic pseudo-random data.  The references here are written
//! independently (`u128` base-field arithmetic, a differently-shaped extension
//! product, explicit bit tests, `O(4^n)` sums) so that a shared mistake is
//! unlikely.  See `tests/field_semantics.rs` for the field layer these build on.
// The reference implementations below are deliberately *unlike* the crate: they
// compute in `u128` so that a `u64` overflow in `src/` shows up as a mismatch
// instead of being reproduced, and they index with explicit `for i in 0..n`
// loops because the shape of the loop is part of what is being cross-checked.
// Clippy's pedantic casting and iterator lints are therefore not wanted here.
#![allow(
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::needless_range_loop,
    clippy::doc_markdown
)]

use cpoly::field::{Ext4, Fp, P, W};
use cpoly::multilinear::{
    add_pointwise, eq_tilde, lagrange_basis, lagrange_to_mono_level, monomial_basis,
    mono_to_lagrange_level, table_len, Coeffs, Evals,
};
use cpoly::univariate::Poly;

/// The independent representation of an extension element: little-endian
/// coefficients of `Y^0 .. Y^3`.
type E = [u64; 4];

fn of(a: Ext4) -> E {
    [
        a.c0.to_u64(),
        a.c1.to_u64(),
        a.c2.to_u64(),
        a.c3.to_u64(),
    ]
}

fn to(a: E) -> Ext4 {
    Ext4::new(Fp::new(a[0]), Fp::new(a[1]), Fp::new(a[2]), Fp::new(a[3]))
}

fn ofv(v: &[Ext4]) -> Vec<E> {
    v.iter().map(|&a| of(a)).collect()
}

fn tov(v: &[E]) -> Vec<Ext4> {
    v.iter().map(|&a| to(a)).collect()
}

/// A `2^n`-entry table read in the monomial basis.
fn coeffs(v: &[E], n: usize) -> Coeffs {
    Coeffs::from_coeffs(tov(v), n)
}

/// The same table read on the Boolean hypercube.  Distinguishing these two is
/// the point of the two types: before the refactor both were `Vec<Ext4>` and
/// nothing stopped a caller evaluating one as if it were the other, which is now
/// a compile error rather than a silently wrong answer.
fn evals(v: &[E]) -> Evals {
    Evals::from_values(tov(v))
}

fn ofc(p: &Coeffs) -> Vec<E> {
    ofv(p.coeffs())
}

fn ofe(p: &Evals) -> Vec<E> {
    ofv(p.values())
}

/// `W` as a raw word, for the reference reduction.
const WV: u64 = W.to_u64();

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
        r[k - 4] = badd(r[k - 4], bmul(WV, r[k]));
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
fn table_len_matches_shift() {
    for n in 0..20 {
        assert_eq!(table_len(n), 1usize << n, "table_len({n})");
    }
}

#[test]
fn zero_is_all_zeros() {
    for n in 0..8 {
        let z = Coeffs::zeros(n);
        assert_eq!(z.len(), 1usize << n);
        assert!(ofc(&z).iter().all(|&c| c == RZERO));
    }
}

#[test]
fn of_array_pads_and_truncates() {
    let table = sample(1, 5);
    // Truncate: 2^1 = 2 < 5.
    assert_eq!(ofc(&coeffs(&table, 1)), vec![table[0], table[1]]);
    // Exact: 2^2 = 4 < 5 still truncates.
    assert_eq!(ofc(&coeffs(&table, 2)), table[0..4].to_vec());
    // Pad: 2^3 = 8 > 5.
    let padded = ofc(&coeffs(&table, 3));
    assert_eq!(padded.len(), 8);
    assert_eq!(&padded[0..5], &table[..]);
    assert!(padded[5..].iter().all(|&c| c == RZERO));
}

#[test]
fn add_is_pointwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 10, sz);
        let q = sample(n as u64 + 99, sz);
        let r = ofc(&(&coeffs(&p, n) + &coeffs(&q, n)));
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
            ofe(&lagrange_basis(&tov(&w))),
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
        let b = ofe(&lagrange_basis(&tov(&w)));
        let total = b.iter().fold(RZERO, |acc, &c| radd(acc, c));
        assert_eq!(total, rone(), "partition of unity, n={n}");

        // At a Boolean point k, lagrangeBasis is the indicator of k.
        for k in 0..(1usize << n) {
            let point: Vec<E> = (0..n)
                .map(|j| if bit(k, j) { rone() } else { RZERO })
                .collect();
            let bk = ofe(&lagrange_basis(&tov(&point)));
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
            of(coeffs(&p, n).eval(&tov(&w))),
            ref_eval_coeffs(&p, &w),
            "eval n={n}"
        );
        let lb = ref_lagrange_basis(&w);
        assert_eq!(
            of(evals(&p).eval(&tov(&w))),
            ref_dot(&p, &lb),
            "eval_lagrange n={n}"
        );
    }
}

#[test]
fn eval_horner_matches_eval() {
    for n in 0..9 {
        let sz = 1usize << n;
        let p = coeffs(&sample(n as u64 + 51, sz), n);
        let w = tov(&sample(n as u64 + 61, n));
        assert_eq!(of(p.eval_horner(&w)), of(p.eval(&w)), "horner n={n}");
    }
}

#[test]
fn eval_mle_matches_eval_lagrange() {
    for n in 0..9 {
        let sz = 1usize << n;
        let v = evals(&sample(n as u64 + 71, sz));
        let w = tov(&sample(n as u64 + 81, n));
        assert_eq!(of(v.eval_mle(&w)), of(v.eval(&w)), "mle n={n}");
    }
}

#[test]
fn zeta_matches_naive_spec() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 91, sz);
        assert_eq!(
            ofe(&coeffs(&p, n).to_evals(n)),
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
            ofc(&evals(&p).to_coeffs(n)),
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
            ofc(&coeffs(&p, n).to_evals(n).to_coeffs(n)),
            p,
            "mobius∘zeta n={n}"
        );
        assert_eq!(
            ofe(&evals(&p).to_coeffs(n).to_evals(n)),
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
        let table = ofe(&coeffs(&p, n).to_evals(n));
        for i in 0..sz {
            let point: Vec<E> = (0..n)
                .map(|j| if bit(i, j) { rone() } else { RZERO })
                .collect();
            assert_eq!(table[i], ref_eval_coeffs(&p, &point), "n={n} i={i}");
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
        let table = coeffs(&p, n).to_evals(n);
        let w = tov(&sample(n as u64 + 141, n));
        assert_eq!(of(coeffs(&p, n).eval(&w)), of(table.eval(&w)), "n={n}");
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
/// development states their multilinear specs about `cpoly::univariate::Poly`'s
/// `Neg` and `Mul<Ext4>` impls.
#[test]
fn neg_and_smul_are_coefficientwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 181, sz);
        let s = sample(n as u64 + 191, 1)[0];
        assert_eq!(
            ofv((-&Poly::from_coeffs(tov(&p))).coeffs()),
            p.iter().map(|&a| rneg(a)).collect::<Vec<E>>(),
            "neg n={n}"
        );
        assert_eq!(
            ofv((&Poly::from_coeffs(tov(&p)) * to(s)).coeffs()),
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
    assert_eq!(of(coeffs(&p, 2).eval(&tov(&w))), cst(172));
    assert_eq!(of(coeffs(&p, 2).eval_horner(&tov(&w))), cst(172));
    // Hypercube evaluations at (0,0), (1,0), (0,1), (1,1): 1, 3, 4, 10.
    assert_eq!(
        ofe(&coeffs(&p, 2).to_evals(2)),
        vec![cst(1), cst(3), cst(4), cst(10)]
    );
    assert_eq!(
        ofc(&evals(&[cst(1), cst(3), cst(4), cst(10)]).to_coeffs(2)),
        p
    );
}

/// The same pinned polynomial, but evaluated at a point that genuinely lives in
/// the extension: `p(Y, Y) = 1 + 2Y + 3Y + 4Y^2 = 1 + 5Y + 4Y^2`.  A field-layer
/// mistake that happens to be invisible on the base subfield shows up here.
#[test]
fn extension_point_pinned() {
    let cst = |k: u64| -> E { [k, 0, 0, 0] };
    let p = coeffs(&[cst(1), cst(2), cst(3), cst(4)], 2);
    let w = vec![Ext4::GEN, Ext4::GEN];
    assert_eq!(of(p.eval(&w)), [1, 5, 4, 0]);
    assert_eq!(of(p.eval_horner(&w)), [1, 5, 4, 0]);

    // At `(Y^3, Y^3)`: 1 + 2Y^3 + 3Y^3 + 4Y^6 = 1 + 4*W*Y^2 + 5Y^3.
    let y3: E = [0, 0, 0, 1];
    let w2 = vec![to(y3), to(y3)];
    assert_eq!(of(p.eval(&w2)), [1, 0, 4 * WV, 5]);
    assert_eq!(of(p.eval_horner(&w2)), [1, 0, 4 * WV, 5]);
}

// ---------------------------------------------------------------
// API introduced by the newtype refactor.
// ---------------------------------------------------------------

/// The two readings round-trip through their constructors and accessors, and
/// `Index` agrees with the slice view.
#[test]
fn tables_round_trip() {
    for n in 0..6 {
        let sz = 1usize << n;
        let t = sample(n as u64 + 201, sz);

        let c = coeffs(&t, n);
        assert_eq!(c.len(), sz);
        assert!(!c.is_empty(), "2^n is never zero");
        assert_eq!(ofc(&c), t);
        assert_eq!(ofv(&c.clone().into_coeffs()), t);

        let e = evals(&t);
        assert_eq!(e.len(), sz);
        assert!(!e.is_empty());
        assert_eq!(ofe(&e), t);
        assert_eq!(ofv(&e.clone().into_values()), t);

        for i in 0..sz {
            assert_eq!(of(c[i]), t[i], "Coeffs[{i}] at n={n}");
            assert_eq!(of(e[i]), t[i], "Evals[{i}] at n={n}");
        }
    }
}

/// The `Evals` `Add` impl is pointwise too, and agrees with the `Coeffs` one on
/// the same underlying words — they share `add_pointwise`.
#[test]
fn evals_add_is_pointwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 211, sz);
        let q = sample(n as u64 + 221, sz);

        let r = ofe(&(&evals(&p) + &evals(&q)));
        assert_eq!(r.len(), sz);
        for i in 0..sz {
            assert_eq!(r[i], radd(p[i], q[i]), "n={n} i={i}");
        }
        // same words either way round
        assert_eq!(r, ofc(&(&coeffs(&p, n) + &coeffs(&q, n))));
        // and directly through the shared helper
        assert_eq!(ofv(&add_pointwise(&tov(&p), &tov(&q))), r);
    }
}

/// One level of the zeta transform adds the lower sibling where the level's bit
/// is set, and the Möbius level subtracts it — so composing them at the same
/// level is the identity.
#[test]
fn transform_levels_are_mutually_inverse() {
    for n in 0..6 {
        let sz = 1usize << n;
        let t = sample(n as u64 + 231, sz);
        for j in 0..n {
            let up = mono_to_lagrange_level(&tov(&t), j);
            let down = lagrange_to_mono_level(&up, j);
            assert_eq!(ofv(&down), t, "level {j} at n={n}");

            // and the level does what its definition says
            let stride = 1usize << j;
            let got = ofv(&up);
            for i in 0..sz {
                let want = if bit(i, j) {
                    radd(t[i], t[i - stride])
                } else {
                    t[i]
                };
                assert_eq!(got[i], want, "zeta level {j}, entry {i}, n={n}");
            }
        }
    }
}
