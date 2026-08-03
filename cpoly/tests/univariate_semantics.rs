//! Semantic validation of `cpoly::univariate` — univariate polynomials as dense
//! little-endian coefficient vectors — run *before* the Lean equivalence proofs
//! are attempted.
//!
//! Each test states the mathematical property that the corresponding
//! `CompPoly.CPolynomial.Raw` definition has, and checks it against the Rust
//! implementation.  The references here are written independently: base-field
//! arithmetic goes through `u128` (so a `u64` overflow in the real code would
//! show up as a mismatch rather than being reproduced), the extension product is
//! an honest degree-6 polynomial multiplication with a top-down reduction loop
//! rather than the unrolled fold in `Ext4`'s `Mul`, polynomial multiplication is
//! checked against the plain
//! convolution and `eval` against `Σ_i p[i] xv^i` rather than Horner.
//!
//! The duplication of the field reference with `tests/field_semantics.rs` is
//! deliberate: a shared helper would let one mistake pass both files.
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
use cpoly::univariate::UnivariatePoly;

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

/// The coefficients of a [`UnivariatePoly`], in the independent representation.
fn ofv(p: &UnivariatePoly) -> Vec<E> {
    p.coeffs().iter().map(|&a| of(a)).collect()
}

/// A [`UnivariatePoly`] from the independent representation, taken verbatim (no trimming).
fn tov(v: &[E]) -> UnivariatePoly {
    UnivariatePoly::from_coeffs(v.iter().map(|&a| to(a)).collect())
}

/// `W` as a raw word, for the reference reduction below.
const WV: u64 = W.to_u64();

// ---------------------------------------------------------------
// Independent base field reference (u128, no clever tricks).
// ---------------------------------------------------------------

fn radd(a: u64, b: u64) -> u64 {
    ((a as u128 + b as u128) % P as u128) as u64
}
fn rsub(a: u64, b: u64) -> u64 {
    ((a as u128 + P as u128 - b as u128) % P as u128) as u64
}
fn rmul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % P as u128) as u64
}
fn rneg(a: u64) -> u64 {
    ((P as u128 - a as u128) % P as u128) as u64
}

// ---------------------------------------------------------------
// Independent extension reference.
// ---------------------------------------------------------------

fn eradd(a: E, b: E) -> E {
    let mut r = [0u64; 4];
    for i in 0..4 {
        r[i] = radd(a[i], b[i]);
    }
    r
}

fn ersub(a: E, b: E) -> E {
    let mut r = [0u64; 4];
    for i in 0..4 {
        r[i] = rsub(a[i], b[i]);
    }
    r
}

fn erneg(a: E) -> E {
    let mut r = [0u64; 4];
    for i in 0..4 {
        r[i] = rneg(a[i]);
    }
    r
}

/// `a * b` in `F_P[Y] / (Y^4 - W)`: full degree-6 product, then fold the high
/// coefficients down one at a time.  Deliberately not the shape `Ext4`'s `Mul` uses.
fn ermul(a: E, b: E) -> E {
    let mut r = [0u64; 7];
    for i in 0..4 {
        for j in 0..4 {
            r[i + j] = radd(r[i + j], rmul(a[i], b[j]));
        }
    }
    for k in (4..7).rev() {
        r[k - 4] = radd(r[k - 4], rmul(WV, r[k]));
        r[k] = 0;
    }
    [r[0], r[1], r[2], r[3]]
}

/// Deterministic pseudo-random reduced base-field elements (SplitMix64).
fn sample_base(seed: u64, count: usize) -> Vec<u64> {
    let mut s = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut out = Vec::new();
    for _ in 0..count {
        s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = s;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        out.push(z % P);
    }
    out
}

/// Deterministic pseudo-random extension elements.
fn sample_ext(seed: u64, count: usize) -> Vec<E> {
    let flat = sample_base(seed, 4 * count);
    (0..count)
        .map(|i| [flat[4 * i], flat[4 * i + 1], flat[4 * i + 2], flat[4 * i + 3]])
        .collect()
}

// ---------------------------------------------------------------
// References mirroring the CompPoly Lean definitions.
// ---------------------------------------------------------------

/// `p * q`, straight from the convolution definition, then trimmed.
fn ref_mul(p: &[E], q: &[E]) -> Vec<E> {
    if p.is_empty() || q.is_empty() {
        return Vec::new();
    }
    let mut r = vec![[0u64; 4]; p.len() + q.len() - 1];
    for i in 0..p.len() {
        for j in 0..q.len() {
            r[i + j] = eradd(r[i + j], ermul(p[i], q[j]));
        }
    }
    while let Some(last) = r.last() {
        if *last == [0, 0, 0, 0] {
            r.pop();
        } else {
            break;
        }
    }
    r
}

/// `p(xv)` by the definition `Σ_i p[i] xv^i`, not by Horner.
fn ref_eval(p: &[E], xv: E) -> E {
    let mut acc = [0u64; 4];
    let mut pw: E = [1 % P, 0, 0, 0];
    for &c in p {
        acc = eradd(acc, ermul(c, pw));
        pw = ermul(pw, xv);
    }
    acc
}

// ---------------------------------------------------------------
// The tests.
// ---------------------------------------------------------------

#[test]
fn univariate_constructors() {
    let r = sample_ext(41, 1)[0];
    assert_eq!(ofv(&UnivariatePoly::constant(to(r))), vec![r]);
    assert_eq!(ofv(&UnivariatePoly::x()), vec![[0, 0, 0, 0], [1 % P, 0, 0, 0]]);
}

#[test]
fn trim_drops_exactly_the_trailing_zeros() {
    let a = sample_ext(43, 3);
    let z: E = [0, 0, 0, 0];
    assert_eq!(ofv(&tov(&[]).trim()), Vec::<E>::new());
    assert_eq!(ofv(&tov(&[z, z, z]).trim()), Vec::<E>::new());
    assert_eq!(ofv(&tov(&[a[0], z, a[1], z, z]).trim()), vec![a[0], z, a[1]]);
    assert_eq!(ofv(&tov(&a).trim()), a.clone());
    // A coefficient that is zero in only three of four coordinates must survive.
    for k in 0..4 {
        let mut e = [0u64; 4];
        e[k] = 5;
        assert_eq!(ofv(&tov(&[z, e]).trim()), vec![z, e], "coord {k}");
    }
}

#[test]
fn univariate_ops_match_reference() {
    for n in 0..6usize {
        for m in 0..6usize {
            let p = sample_ext(50 + n as u64, n);
            let q = sample_ext(70 + m as u64, m);
            let pr = tov(&p);
            let qr = tov(&q);

            // add_raw is zero-padded and untrimmed.
            let want_raw: Vec<E> = (0..n.max(m))
                .map(|i| {
                    eradd(
                        *p.get(i).unwrap_or(&[0; 4]),
                        *q.get(i).unwrap_or(&[0; 4]),
                    )
                })
                .collect();
            assert_eq!(ofv(&pr.add_untrimmed(&qr)), want_raw, "add_untrimmed {n}x{m}");

            let mut want = want_raw.clone();
            while let Some(last) = want.last() {
                if *last == [0, 0, 0, 0] {
                    want.pop();
                } else {
                    break;
                }
            }
            assert_eq!(ofv(&(&pr + &qr)), want, "add {n}x{m}");

            let want_neg: Vec<E> = p.iter().map(|&a| erneg(a)).collect();
            assert_eq!(ofv(&-&pr), want_neg, "neg {n}");

            let want_sub = {
                let mut v: Vec<E> = (0..n.max(m))
                    .map(|i| {
                        ersub(
                            *p.get(i).unwrap_or(&[0; 4]),
                            *q.get(i).unwrap_or(&[0; 4]),
                        )
                    })
                    .collect();
                while let Some(last) = v.last() {
                    if *last == [0, 0, 0, 0] {
                        v.pop();
                    } else {
                        break;
                    }
                }
                v
            };
            assert_eq!(ofv(&(&pr - &qr)), want_sub, "sub {n}x{m}");

            assert_eq!(ofv(&(&pr * &qr)), ref_mul(&p, &q), "mul {n}x{m}");

            let s = sample_ext(90 + n as u64, 1)[0];
            let want_smul: Vec<E> = p.iter().map(|&a| ermul(s, a)).collect();
            assert_eq!(ofv(&(&pr * to(s))), want_smul, "smul {n}");

            let pt = sample_ext(110 + n as u64, 1)[0];
            assert_eq!(of(pr.eval(to(pt))), ref_eval(&p, pt), "eval {n}");
        }
    }
}

/// `eval` is a ring homomorphism in the polynomial argument — the property the
/// Lean side ultimately cares about.
#[test]
fn eval_respects_add_and_mul() {
    for n in 1..5usize {
        let p = tov(&sample_ext(130 + n as u64, n));
        let q = tov(&sample_ext(150 + n as u64, n));
        let pt = to(sample_ext(170 + n as u64, 1)[0]);
        assert_eq!(
            of((&p + &q).eval(pt)),
            eradd(of(p.eval(pt)), of(q.eval(pt))),
            "additive n={n}"
        );
        assert_eq!(
            of((&p * &q).eval(pt)),
            ermul(of(p.eval(pt)), of(q.eval(pt))),
            "multiplicative n={n}"
        );
    }
}

/// A hand-computed case, to pin the little-endian convention in the `X`
/// (polynomial) direction, and its interaction with the `Y` (extension) one.
#[test]
fn conventions_pinned() {
    // (1 + 2X) * (3 + 4X) = 3 + 10X + 8X^2, all coefficients in the base field.
    let p = tov(&[[1, 0, 0, 0], [2, 0, 0, 0]]);
    let q = tov(&[[3, 0, 0, 0], [4, 0, 0, 0]]);
    assert_eq!(
        ofv(&(&p * &q)),
        vec![[3, 0, 0, 0], [10, 0, 0, 0], [8, 0, 0, 0]]
    );
    // Evaluating 1 + 2X at Y gives 1 + 2Y.
    assert_eq!(of(p.eval(Ext4::GEN)), [1, 2, 0, 0]);
    // X^4 evaluated at Y is Y^4 = W, so the two directions do interact.
    let x4 = tov(&[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]);
    assert_eq!(of(x4.eval(Ext4::GEN)), [WV, 0, 0, 0]);
    // And `Ext4`'s `Mul` is the operation `eval` uses for that.
    assert_eq!(of(Ext4::GEN * Ext4::GEN), [0, 0, 1, 0]);
}

// ---------------------------------------------------------------
// API introduced by the newtype refactor.
// ---------------------------------------------------------------

/// The coefficient vector goes in and comes back out unchanged, and `coeffs`
/// agrees with `into_coeffs`.  `UnivariatePoly` is a newtype, not a normalising
/// constructor: `from_coeffs` does not trim.
#[test]
fn coefficients_round_trip() {
    for n in 0..6usize {
        let e = sample_ext(200 + n as u64, n);
        let p = tov(&e);
        assert_eq!(p.len(), n);
        assert_eq!(p.coeffs().len(), n);
        assert_eq!(ofv(&p), e);
        let back: Vec<E> = p.clone().into_coeffs().iter().map(|&a| of(a)).collect();
        assert_eq!(back, e);
        assert_eq!(UnivariatePoly::from(p.clone().into_coeffs()), p, "From<Vec<Ext4>>");
    }
    // trailing zeros are representable, and survive `from_coeffs`
    let z: E = [0, 0, 0, 0];
    assert_eq!(tov(&[z, z]).len(), 2);
}

#[test]
fn len_is_empty_and_degree() {
    assert!(UnivariatePoly::zero().is_empty());
    assert_eq!(UnivariatePoly::zero().len(), 0);
    assert_eq!(UnivariatePoly::zero().degree(), None);
    assert_eq!(UnivariatePoly::default(), UnivariatePoly::zero(), "Default is the zero polynomial");

    // `UnivariatePoly::constant` is untrimmed, so even a zero constant has one coefficient
    assert!(!UnivariatePoly::constant(Ext4::ZERO).is_empty());
    assert_eq!(UnivariatePoly::constant(Ext4::ZERO).degree(), Some(0));
    assert_eq!(UnivariatePoly::x().degree(), Some(1));

    for n in 1..6usize {
        let p = tov(&sample_ext(220 + n as u64, n));
        assert!(!p.is_empty());
        assert_eq!(p.degree(), Some(n - 1));
    }
}

/// `Index` reads the same coefficient `coeffs()` does.
#[test]
fn indexing_agrees_with_coeffs() {
    for n in 1..6usize {
        let e = sample_ext(240 + n as u64, n);
        let p = tov(&e);
        for i in 0..n {
            assert_eq!(of(p[i]), e[i], "p[{i}] at n={n}");
        }
    }
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn indexing_past_the_end_panics() {
    let p = UnivariatePoly::x();
    let _ = p[2];
}
