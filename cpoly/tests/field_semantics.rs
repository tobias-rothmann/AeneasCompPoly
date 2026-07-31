//! Semantic validation of `cpoly::field` — the base field `F_P` and the quartic
//! extension `Ext4` — run *before* the Lean equivalence proofs are attempted.
//!
//! The references here are written independently of `src/field.rs`: base-field
//! arithmetic goes through `u128` (so a `u64` overflow in the real code would
//! show up as a mismatch rather than being reproduced), and the extension
//! product is computed as an honest degree-6 polynomial multiplication followed
//! by a top-down reduction loop, rather than the unrolled fold in `Ext4`'s `Mul`.
//!
//! The references stay on raw `u64` words, so `of` / `to` and the four `f*`
//! adapters below are the only places that touch the crate's [`Fp`] and [`Ext4`]
//! types; everything else is arithmetic the crate has no part in.
//!
//! Also checked here are the two number-theoretic facts CompPoly proves about
//! this field, since a mistake in either would make `Ext4` not a field at all:
//!
//! * `W = 2` is a non-square mod `P` (Euler's criterion);
//! * every nonzero element is invertible, i.e. `x^(P^4 - 1) = 1`, which is what
//!   irreducibility of `Y^4 - 2` buys.
//!
//! The polynomial layers get their own files, `tests/univariate_semantics.rs` and
//! `tests/multilinear_semantics.rs`, each with its own independently written
//! references — the duplication is deliberate, so that a mistake shared with
//! this file is unlikely.
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

use cpoly::field::*;

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

/// `W` as a raw word, for the reference reduction below.
const WV: u64 = W.to_u64();

// ---------------------------------------------------------------
// The crate's base-field operators, on raw words.  Thin adapters, so that the
// assertions read as `fadd(a, b) == radd(a, b)` rather than burying the
// comparison in conversions.
// ---------------------------------------------------------------

fn fadd(a: u64, b: u64) -> u64 {
    (Fp::new(a) + Fp::new(b)).to_u64()
}
fn fsub(a: u64, b: u64) -> u64 {
    (Fp::new(a) - Fp::new(b)).to_u64()
}
fn fmul(a: u64, b: u64) -> u64 {
    (Fp::new(a) * Fp::new(b)).to_u64()
}
fn fneg(a: u64) -> u64 {
    (-Fp::new(a)).to_u64()
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

/// `a^e` in the base field, by repeated squaring.
fn rpow(a: u64, e: u128) -> u64 {
    let mut acc: u64 = 1 % P;
    let mut base = a;
    let mut k = e;
    while k > 0 {
        if k & 1 == 1 {
            acc = rmul(acc, base);
        }
        base = rmul(base, base);
        k >>= 1;
    }
    acc
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

fn erpow(a: E, e: u128) -> E {
    let mut acc: E = [1 % P, 0, 0, 0];
    let mut base = a;
    let mut k = e;
    while k > 0 {
        if k & 1 == 1 {
            acc = ermul(acc, base);
        }
        base = ermul(base, base);
        k >>= 1;
    }
    acc
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
// The modulus and the extension constant.
// ---------------------------------------------------------------

/// `P < 2^32` is what keeps `a * b` inside a `u64`, and `(P-1)^2 < 2^64` is the
/// tightest of the no-overflow bounds the crate documents.  Both are properties
/// of a constant, so they are checked at compile time rather than at test time —
/// a runtime `assert!` on a `const` cannot fail, and clippy is right to say so.
const _: () = assert!(P < 1u64 << 32, "P < 2^32 keeps a*b inside u64");
const _: () = assert!(
    (P as u128 - 1) * (P as u128 - 1) < 1u128 << 64,
    "(P-1)^2 must fit in u64"
);

#[test]
fn modulus_is_the_hachi_prime() {
    assert_eq!(P, (1u64 << 32) - 99, "P = 2^32 - 99");
    // Trial division is enough at this size and is independent of `pratt`.
    let mut d: u64 = 2;
    while d * d <= P {
        assert!(P % d != 0, "P divisible by {d}");
        d += 1;
    }
}

/// `Y^4 - W` can only be irreducible if `W` is a non-square; Euler's criterion
/// says `W^((P-1)/2) = -1`.  This is the fact `Hachi.ext4Params_poly_irreducible`
/// rests on.
#[test]
fn w_is_a_non_square() {
    assert_eq!(WV, 2);
    assert_eq!(rpow(WV, ((P - 1) / 2) as u128), P - 1, "2 is a non-square mod P");
}

/// `P ≡ 1 mod 4` is the hypothesis that makes *every* non-square `W` give an
/// irreducible `Y^4 - W`.
#[test]
fn modulus_is_one_mod_four() {
    assert_eq!(P % 4, 1);
}

// ---------------------------------------------------------------
// Base field operations.
// ---------------------------------------------------------------

#[test]
fn base_ops_match_reference() {
    let mut xs = sample_base(3, 200);
    xs.extend_from_slice(&[0, 1, 2, P - 1, P - 2, (P - 1) / 2]);
    for &a in &xs {
        assert_eq!(fneg(a), rneg(a), "fneg({a})");
        for &b in &xs {
            assert_eq!(fadd(a, b), radd(a, b), "fadd({a},{b})");
            assert_eq!(fsub(a, b), rsub(a, b), "fsub({a},{b})");
            assert_eq!(fmul(a, b), rmul(a, b), "fmul({a},{b})");
        }
    }
}

/// The worst case for the `a * b < 2^64` claim.
#[test]
fn base_mul_at_the_overflow_boundary() {
    assert_eq!(fmul(P - 1, P - 1), rmul(P - 1, P - 1));
    assert_eq!(fmul(P - 1, P - 1), 1 % P, "(-1)^2 = 1");
    assert_eq!(fadd(P - 1, P - 1), rsub(0, 2));
}

// ---------------------------------------------------------------
// Extension operations.
// ---------------------------------------------------------------

#[test]
fn ext_ops_match_reference() {
    let mut xs = sample_ext(11, 60);
    xs.extend_from_slice(&[
        [0, 0, 0, 0],
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [P - 1, P - 1, P - 1, P - 1],
    ]);
    for &a in &xs {
        assert_eq!(of(-to(a)), erneg(a), "-{a:?}");
        for &b in &xs {
            assert_eq!(of(to(a) + to(b)), eradd(a, b), "{a:?} + {b:?}");
            assert_eq!(of(to(a) - to(b)), ersub(a, b), "{a:?} - {b:?}");
            assert_eq!(of(to(a) * to(b)), ermul(a, b), "{a:?} * {b:?}");
        }
    }
}

#[test]
fn constants_and_zero_test() {
    assert_eq!(of(Ext4::ZERO), [0, 0, 0, 0]);
    assert_eq!(of(Ext4::ONE), [1, 0, 0, 0]);
    assert_eq!(of(Ext4::GEN), [0, 1, 0, 0]);
    assert_eq!(of(Ext4::from(7u64)), [7, 0, 0, 0]);

    assert!(Ext4::ZERO.is_zero());
    assert!(!Ext4::ONE.is_zero());
    assert!(!Ext4::GEN.is_zero());
    // Nonzero in any single coordinate must be detected.
    for k in 0..4 {
        let mut e = [0u64; 4];
        e[k] = 1;
        assert!(!to(e).is_zero(), "is_zero must be false for {e:?}");
    }
    for a in sample_ext(5, 50) {
        assert_eq!(to(a).is_zero(), a == [0, 0, 0, 0], "is_zero({a:?})");
    }
}

/// **The defining relation.**  Mirrors `Hachi.ext4Gen_pow_four`.
#[test]
fn gen_to_the_fourth_is_w() {
    let g = of(Ext4::GEN);
    assert_eq!(erpow(g, 4), [WV, 0, 0, 0]);
    let g2 = Ext4::GEN * Ext4::GEN;
    let g4 = g2 * g2;
    assert_eq!(of(g4), [WV, 0, 0, 0], "Ext4::GEN^4 = from_base(W)");
    // Lower powers are the basis vectors, so `Y` really does have degree 4.
    assert_eq!(of(g2), [0, 0, 1, 0]);
    assert_eq!(of(g2 * Ext4::GEN), [0, 0, 0, 1]);
}

/// `Ext4::from_base` is a ring homomorphism, i.e. the base field sits inside `Ext4` the
/// way `Ext.ofBase` says.
#[test]
fn of_base_is_a_ring_hom() {
    assert_eq!(of(Ext4::from(0u64)), of(Ext4::ZERO));
    assert_eq!(of(Ext4::from(1u64 % P)), of(Ext4::ONE));
    let xs = sample_base(17, 40);
    for &a in &xs {
        for &b in &xs {
            assert_eq!(
                of(Ext4::from(a) + Ext4::from(b)),
                of(Ext4::from(fadd(a, b))),
                "additive at ({a},{b})"
            );
            assert_eq!(
                of(Ext4::from(a) * Ext4::from(b)),
                of(Ext4::from(fmul(a, b))),
                "multiplicative at ({a},{b})"
            );
        }
    }
}

#[test]
fn ext_ring_axioms() {
    let xs = sample_ext(23, 14);
    for &a in &xs {
        assert_eq!(of(to(a) + Ext4::ZERO), a, "0 is additive unit");
        assert_eq!(of(to(a) * Ext4::ONE), a, "1 is multiplicative unit");
        assert_eq!(of(to(a) * Ext4::ZERO), [0, 0, 0, 0], "0 absorbs");
        assert_eq!(of(to(a) + -to(a)), [0, 0, 0, 0], "neg cancels");
        assert_eq!(of(to(a) - to(a)), [0, 0, 0, 0], "sub cancels");
        for &b in &xs {
            assert_eq!(of(to(a) + to(b)), of(to(b) + to(a)), "add comm");
            assert_eq!(of(to(a) * to(b)), of(to(b) * to(a)), "mul comm");
            assert_eq!(
                of(to(a) - to(b)),
                of(to(a) + -to(b)),
                "sub = add neg"
            );
            for &c in &xs {
                assert_eq!(
                    of((to(a) + to(b)) + to(c)),
                    of(to(a) + (to(b) + to(c))),
                    "add assoc"
                );
                assert_eq!(
                    of((to(a) * to(b)) * to(c)),
                    of(to(a) * (to(b) * to(c))),
                    "mul assoc"
                );
                assert_eq!(
                    of(to(a) * (to(b) + to(c))),
                    of(to(a) * to(b) + to(a) * to(c)),
                    "distrib"
                );
            }
        }
    }
}

/// `Ext4` really is a field of order `P^4`: every nonzero `x` satisfies
/// `x^(P^4 - 1) = 1`, which fails as soon as `Y^4 - W` factors.  This is the
/// computational counterpart of `Hachi.ext4Params_poly_irreducible` plus
/// `Ext.instField`.
#[test]
fn nonzero_elements_are_invertible() {
    let q = P as u128;
    let order = q * q * q * q - 1;
    for a in sample_ext(29, 12) {
        assert_ne!(a, [0, 0, 0, 0]);
        assert_eq!(erpow(a, order), [1 % P, 0, 0, 0], "x^(P^4-1) = 1 for {a:?}");
        // And the Fermat inverse `x^(P^4-2)` really inverts, using the crate's
        // own `Mul` for the final product.
        let inv = erpow(a, order - 1);
        assert_eq!(of(to(a) * to(inv)), [1 % P, 0, 0, 0], "x * x^-1 = 1");
    }
    // A proper subfield element is invertible too, and its inverse stays in the
    // subfield.
    for a in sample_base(31, 8) {
        if a == 0 {
            continue;
        }
        let inv = rpow(a, q - 2);
        assert_eq!(of(Ext4::from(a) * Ext4::from(inv)), [1 % P, 0, 0, 0]);
    }
}

/// The `Y`-direction (extension) conventions, pinned by hand.  The `X`-direction
/// counterpart lives in `tests/univariate_semantics.rs`.
#[test]
fn extension_conventions_pinned() {
    // (Y^3) * (Y^2) = Y^5 = W * Y = 2Y.
    let y2: E = [0, 0, 1, 0];
    let y3: E = [0, 0, 0, 1];
    assert_eq!(of(to(y3) * to(y2)), [0, WV, 0, 0]);
    // (1 + Y)^2 = 1 + 2Y + Y^2.
    let one_plus_y: E = [1, 1, 0, 0];
    assert_eq!(of(to(one_plus_y) * to(one_plus_y)), [1, 2, 1, 0]);
    // (1 + Y^3)^2 = 1 + 2Y^3 + Y^6 = 1 + 2Y^3 + W*Y^2 = 1 + 2Y^2 + 2Y^3.
    let one_plus_y3: E = [1, 0, 0, 1];
    assert_eq!(of(to(one_plus_y3) * to(one_plus_y3)), [1, 0, WV, 2]);
}

// ---------------------------------------------------------------
// API introduced by the newtype refactor.  These have no counterpart in the
// reference implementations above — they are about the *type*, not the
// arithmetic — so each states its property directly.
// ---------------------------------------------------------------

/// `Fp::new` is the only public way in from a machine word, and it reduces.
/// That is what makes "the representative is below `P`" an invariant of the type
/// rather than a precondition callers have to respect (the Lean proofs call it
/// `Red`).
#[test]
fn fp_new_reduces_every_word() {
    assert_eq!(Fp::MODULUS, P);
    for &v in &[0u64, 1, P - 1, P, P + 1, 2 * P, u64::MAX] {
        let x = Fp::new(v);
        assert!(x.to_u64() < P, "Fp::new({v}) must be reduced");
        assert_eq!(x.to_u64(), v % P);
        assert_eq!(Fp::from(v), x, "From<u64> is Fp::new");
    }
    // and it is the identity on words that are already reduced
    for &v in &sample_base(41, 50) {
        assert_eq!(Fp::new(v).to_u64(), v);
    }
}

#[test]
fn fp_constants_and_zero_test() {
    assert_eq!(Fp::ZERO.to_u64(), 0);
    assert_eq!(Fp::ONE.to_u64(), 1 % P);
    assert!(Fp::ZERO.is_zero());
    assert!(!Fp::ONE.is_zero());
    for &v in &sample_base(43, 50) {
        assert_eq!(Fp::new(v).is_zero(), v == 0);
    }
}

/// `Default` is the additive identity, for every type that has one.
#[test]
fn default_is_zero() {
    assert_eq!(Fp::default(), Fp::ZERO);
    assert_eq!(Ext4::default(), Ext4::ZERO);
}

/// The `*Assign` impls agree with the binary operators they delegate to.
#[test]
fn compound_assignment_agrees() {
    let xs = sample_base(47, 30);
    for &a in &xs {
        for &b in &xs {
            let (x, y) = (Fp::new(a), Fp::new(b));

            let mut t = x;
            t += y;
            assert_eq!(t, x + y, "Fp += at ({a},{b})");
            let mut t = x;
            t -= y;
            assert_eq!(t, x - y, "Fp -= at ({a},{b})");
            let mut t = x;
            t *= y;
            assert_eq!(t, x * y, "Fp *= at ({a},{b})");
        }
    }
    for &a in &sample_ext(53, 12) {
        for &b in &sample_ext(59, 12) {
            let (x, y) = (to(a), to(b));

            let mut t = x;
            t += y;
            assert_eq!(t, x + y, "Ext4 += at ({a:?},{b:?})");
            let mut t = x;
            t -= y;
            assert_eq!(t, x - y, "Ext4 -= at ({a:?},{b:?})");
            let mut t = x;
            t *= y;
            assert_eq!(t, x * y, "Ext4 *= at ({a:?},{b:?})");
        }
    }
}

/// The heterogeneous `impl Mul<Ext4> for Fp` scales coefficient-wise, which must
/// agree with embedding the scalar first and multiplying in `Ext4`.
#[test]
fn base_scalar_scaling_agrees_with_embedding() {
    for &s in &sample_base(61, 20) {
        for &a in &sample_ext(67, 20) {
            let scaled = Fp::new(s) * to(a);
            assert_eq!(scaled, Ext4::from_base(Fp::new(s)) * to(a), "at ({s},{a:?})");
            // ... and coefficient by coefficient, against the u128 reference
            assert_eq!(
                of(scaled),
                [rmul(s, a[0]), rmul(s, a[1]), rmul(s, a[2]), rmul(s, a[3])]
            );
        }
    }
}

/// `From<Fp>` and `From<u64>` for `Ext4` both land on `from_base`, the second
/// reducing on the way.
#[test]
fn ext_conversions_agree() {
    for &v in &[0u64, 1, 7, P - 1, P, P + 5] {
        assert_eq!(Ext4::from(v), Ext4::from_base(Fp::new(v)));
        assert_eq!(Ext4::from(Fp::new(v)), Ext4::from_base(Fp::new(v)));
        assert_eq!(of(Ext4::from(v)), [v % P, 0, 0, 0]);
    }
}

/// The derived `PartialEq` on `Ext4` decides equality in the field, which is what
/// `ext_eq_spec` claims on the Lean side.
#[test]
fn ext_equality_is_field_equality() {
    let xs = sample_ext(71, 25);
    for &a in &xs {
        for &b in &xs {
            assert_eq!(to(a) == to(b), a == b, "at ({a:?},{b:?})");
        }
        assert_eq!(to(a) == Ext4::ZERO, to(a).is_zero());
    }
}
