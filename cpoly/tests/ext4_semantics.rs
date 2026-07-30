//! Semantic validation of the `Ext4` field layer of `cpoly`, run *before* the
//! Lean equivalence proofs are attempted.
//!
//! The references here are written independently of `src/lib.rs`: base-field
//! arithmetic goes through `u128` (so a `u64` overflow in the real code would
//! show up as a mismatch rather than being reproduced), and the extension
//! product is computed as an honest degree-6 polynomial multiplication followed
//! by a top-down reduction loop, rather than the unrolled fold in `emul`.
//!
//! Also checked here are the two number-theoretic facts CompPoly proves about
//! this field, since a mistake in either would make `Ext4` not a field at all:
//!
//! * `W = 2` is a non-square mod `P` (Euler's criterion);
//! * every nonzero element is invertible, i.e. `x^(P^4 - 1) = 1`, which is what
//!   irreducibility of `Y^4 - 2` buys.

use cpoly::*;

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

#[test]
fn modulus_is_the_hachi_prime() {
    assert_eq!(P, (1u64 << 32) - 99, "P = 2^32 - 99");
    assert!(P < 1u64 << 32, "P < 2^32 keeps a*b inside u64");
    // The overflow margin the crate docs claim.
    let hi = (P - 1) as u128 * (P - 1) as u128;
    assert!(hi < 1u128 << 64, "(P-1)^2 must fit in u64");
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
    assert_eq!(W, 2);
    assert_eq!(rpow(W, ((P - 1) / 2) as u128), P - 1, "2 is a non-square mod P");
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
        assert_eq!(of(eneg(to(a))), erneg(a), "eneg({a:?})");
        for &b in &xs {
            assert_eq!(of(eadd(to(a), to(b))), eradd(a, b), "eadd({a:?},{b:?})");
            assert_eq!(of(esub(to(a), to(b))), ersub(a, b), "esub({a:?},{b:?})");
            assert_eq!(of(emul(to(a), to(b))), ermul(a, b), "emul({a:?},{b:?})");
        }
    }
}

#[test]
fn constants_and_zero_test() {
    assert_eq!(of(EZERO), [0, 0, 0, 0]);
    assert_eq!(of(EONE), [1, 0, 0, 0]);
    assert_eq!(of(EGEN), [0, 1, 0, 0]);
    assert_eq!(of(eof_base(7)), [7, 0, 0, 0]);

    assert!(is_ezero(EZERO));
    assert!(!is_ezero(EONE));
    assert!(!is_ezero(EGEN));
    // Nonzero in any single coordinate must be detected.
    for k in 0..4 {
        let mut e = [0u64; 4];
        e[k] = 1;
        assert!(!is_ezero(to(e)), "is_ezero must be false for {e:?}");
    }
    for a in sample_ext(5, 50) {
        assert_eq!(is_ezero(to(a)), a == [0, 0, 0, 0], "is_ezero({a:?})");
    }
}

/// **The defining relation.**  Mirrors `Hachi.ext4Gen_pow_four`.
#[test]
fn gen_to_the_fourth_is_w() {
    let g = of(EGEN);
    assert_eq!(erpow(g, 4), [W, 0, 0, 0]);
    let g2 = emul(EGEN, EGEN);
    let g4 = emul(g2, g2);
    assert_eq!(of(g4), [W, 0, 0, 0], "EGEN^4 = ofBase W");
    // Lower powers are the basis vectors, so `Y` really does have degree 4.
    assert_eq!(of(g2), [0, 0, 1, 0]);
    assert_eq!(of(emul(g2, EGEN)), [0, 0, 0, 1]);
}

/// `eof_base` is a ring homomorphism, i.e. the base field sits inside `Ext4` the
/// way `Ext.ofBase` says.
#[test]
fn of_base_is_a_ring_hom() {
    assert_eq!(of(eof_base(0)), of(EZERO));
    assert_eq!(of(eof_base(1 % P)), of(EONE));
    let xs = sample_base(17, 40);
    for &a in &xs {
        for &b in &xs {
            assert_eq!(
                of(eadd(eof_base(a), eof_base(b))),
                of(eof_base(fadd(a, b))),
                "additive at ({a},{b})"
            );
            assert_eq!(
                of(emul(eof_base(a), eof_base(b))),
                of(eof_base(fmul(a, b))),
                "multiplicative at ({a},{b})"
            );
        }
    }
}

#[test]
fn ext_ring_axioms() {
    let xs = sample_ext(23, 14);
    for &a in &xs {
        assert_eq!(of(eadd(to(a), EZERO)), a, "0 is additive unit");
        assert_eq!(of(emul(to(a), EONE)), a, "1 is multiplicative unit");
        assert_eq!(of(emul(to(a), EZERO)), [0, 0, 0, 0], "0 absorbs");
        assert_eq!(of(eadd(to(a), eneg(to(a)))), [0, 0, 0, 0], "neg cancels");
        assert_eq!(of(esub(to(a), to(a))), [0, 0, 0, 0], "sub cancels");
        for &b in &xs {
            assert_eq!(of(eadd(to(a), to(b))), of(eadd(to(b), to(a))), "add comm");
            assert_eq!(of(emul(to(a), to(b))), of(emul(to(b), to(a))), "mul comm");
            assert_eq!(
                of(esub(to(a), to(b))),
                of(eadd(to(a), eneg(to(b)))),
                "sub = add neg"
            );
            for &c in &xs {
                assert_eq!(
                    of(eadd(eadd(to(a), to(b)), to(c))),
                    of(eadd(to(a), eadd(to(b), to(c)))),
                    "add assoc"
                );
                assert_eq!(
                    of(emul(emul(to(a), to(b)), to(c))),
                    of(emul(to(a), emul(to(b), to(c)))),
                    "mul assoc"
                );
                assert_eq!(
                    of(emul(to(a), eadd(to(b), to(c)))),
                    of(eadd(emul(to(a), to(b)), emul(to(a), to(c)))),
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
        // own `emul` for the final product.
        let inv = erpow(a, order - 1);
        assert_eq!(of(emul(to(a), to(inv))), [1 % P, 0, 0, 0], "x * x^-1 = 1");
    }
    // A proper subfield element is invertible too, and its inverse stays in the
    // subfield.
    for a in sample_base(31, 8) {
        if a == 0 {
            continue;
        }
        let inv = rpow(a, (q - 2) as u128);
        assert_eq!(of(emul(eof_base(a), eof_base(inv))), [1 % P, 0, 0, 0]);
    }
}

// ---------------------------------------------------------------
// The univariate polynomial layer.
// ---------------------------------------------------------------

fn ofv(v: &[Ext4]) -> Vec<E> {
    v.iter().map(|&a| of(a)).collect()
}

fn tov(v: &[E]) -> Vec<Ext4> {
    v.iter().map(|&a| to(a)).collect()
}

/// Coefficient `k` of `p * q`, straight from the convolution definition.
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

/// A hand-computed case, to pin the little-endian conventions in both `X`
/// (polynomial) and `Y` (extension) directions.
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
    // (Y^3) * (Y^2) = Y^5 = W * Y = 2Y.
    let y2: E = [0, 0, 1, 0];
    let y3: E = [0, 0, 0, 1];
    assert_eq!(of(emul(to(y3), to(y2))), [0, W, 0, 0]);
    // (1 + Y)^2 = 1 + 2Y + Y^2.
    let one_plus_y: E = [1, 1, 0, 0];
    assert_eq!(of(emul(to(one_plus_y), to(one_plus_y))), [1, 2, 1, 0]);
    // (1 + Y^3)^2 = 1 + 2Y^3 + Y^6 = 1 + 2Y^3 + W*Y^2 = 1 + 2Y^2 + 2Y^3.
    let one_plus_y3: E = [1, 0, 0, 1];
    assert_eq!(of(emul(to(one_plus_y3), to(one_plus_y3))), [1, 0, W, 2]);
}
