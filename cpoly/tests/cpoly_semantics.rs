//! Semantic validation of `cpoly::cpoly` — univariate polynomials as dense
//! little-endian coefficient vectors — run *before* the Lean equivalence proofs
//! are attempted.
//!
//! Each test states the mathematical property that the corresponding
//! `CompPoly.CPolynomial.Raw` definition has, and checks it against the Rust
//! implementation.  The references here are written independently: base-field
//! arithmetic goes through `u128` (so a `u64` overflow in the real code would
//! show up as a mismatch rather than being reproduced), the extension product is
//! an honest degree-6 polynomial multiplication with a top-down reduction loop
//! rather than the unrolled fold in `emul`, `mul` is checked against the plain
//! convolution and `eval` against `Σ_i p[i] xv^i` rather than Horner.
//!
//! The duplication of the field reference with `tests/field_semantics.rs` is
//! deliberate: a shared helper would let one mistake pass both files.

use cpoly::cpoly::*;
use cpoly::field::{emul, Ext4, EGEN, P, W};

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
/// coefficients down one at a time.  Deliberately not the shape `emul` uses.
fn ermul(a: E, b: E) -> E {
    let mut r = [0u64; 7];
    for i in 0..4 {
        for j in 0..4 {
            r[i + j] = radd(r[i + j], rmul(a[i], b[j]));
        }
    }
    for k in (4..7).rev() {
        r[k - 4] = radd(r[k - 4], rmul(W, r[k]));
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
    assert_eq!(ofv(&c(to(r))), vec![r]);
    assert_eq!(ofv(&x()), vec![[0, 0, 0, 0], [1 % P, 0, 0, 0]]);
}

#[test]
fn trim_drops_exactly_the_trailing_zeros() {
    let a = sample_ext(43, 3);
    let z: E = [0, 0, 0, 0];
    assert_eq!(ofv(&trim(tov(&[]))), Vec::<E>::new());
    assert_eq!(ofv(&trim(tov(&[z, z, z]))), Vec::<E>::new());
    assert_eq!(ofv(&trim(tov(&[a[0], z, a[1], z, z]))), vec![a[0], z, a[1]]);
    assert_eq!(ofv(&trim(tov(&a))), a.to_vec());
    // A coefficient that is zero in only three of four coordinates must survive.
    for k in 0..4 {
        let mut e = [0u64; 4];
        e[k] = 5;
        assert_eq!(ofv(&trim(tov(&[z, e]))), vec![z, e], "coord {k}");
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
            assert_eq!(ofv(&add_raw(&pr, &qr)), want_raw, "add_raw {n}x{m}");

            let mut want = want_raw.clone();
            while let Some(last) = want.last() {
                if *last == [0, 0, 0, 0] {
                    want.pop();
                } else {
                    break;
                }
            }
            assert_eq!(ofv(&add(&pr, &qr)), want, "add {n}x{m}");

            let want_neg: Vec<E> = p.iter().map(|&a| erneg(a)).collect();
            assert_eq!(ofv(&neg(&pr)), want_neg, "neg {n}");

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
            assert_eq!(ofv(&sub(&pr, &qr)), want_sub, "sub {n}x{m}");

            assert_eq!(ofv(&mul(&pr, &qr)), ref_mul(&p, &q), "mul {n}x{m}");

            let s = sample_ext(90 + n as u64, 1)[0];
            let want_smul: Vec<E> = p.iter().map(|&a| ermul(s, a)).collect();
            assert_eq!(ofv(&smul(to(s), &pr)), want_smul, "smul {n}");

            let pt = sample_ext(110 + n as u64, 1)[0];
            assert_eq!(of(eval(&pr, to(pt))), ref_eval(&p, pt), "eval {n}");
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
            of(eval(&add(&p, &q), pt)),
            eradd(of(eval(&p, pt)), of(eval(&q, pt))),
            "additive n={n}"
        );
        assert_eq!(
            of(eval(&mul(&p, &q), pt)),
            ermul(of(eval(&p, pt)), of(eval(&q, pt))),
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
        ofv(&mul(&p, &q)),
        vec![[3, 0, 0, 0], [10, 0, 0, 0], [8, 0, 0, 0]]
    );
    // Evaluating 1 + 2X at Y gives 1 + 2Y.
    assert_eq!(of(eval(&p, EGEN)), [1, 2, 0, 0]);
    // X^4 evaluated at Y is Y^4 = W, so the two directions do interact.
    let x4 = tov(&[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]);
    assert_eq!(of(eval(&x4, EGEN)), [W, 0, 0, 0]);
    // And `emul` is the operation `eval` uses for that.
    assert_eq!(of(emul(EGEN, EGEN)), [0, 0, 1, 0]);
}
