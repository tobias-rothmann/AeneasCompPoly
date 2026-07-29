//! Semantic validation of `cpoly::mlpoly` against independent brute-force
//! references, run *before* the Lean equivalence proofs are attempted.
//!
//! Each test states the mathematical property that the corresponding
//! `CompPoly.CMlPolynomial` / `CMlPolynomialEval` definition has, and checks it
//! against the Rust implementation over exhaustive small cases plus
//! deterministic pseudo-random data.  The references here are written
//! independently (`u128` arithmetic, explicit `Nat` bit tests, `O(4^n)` sums) so
//! that a shared mistake is unlikely.

use cpoly::mlpoly::*;
use cpoly::P;

// ---------------------------------------------------------------
// Independent field reference (u128, no clever tricks).
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

/// Deterministic pseudo-random reduced field elements (SplitMix64).
fn sample(seed: u64, count: usize) -> Vec<u64> {
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

fn bit(i: usize, j: usize) -> bool {
    (i >> j) & 1 == 1
}

// ---------------------------------------------------------------
// References mirroring the CompPoly Lean definitions.
// ---------------------------------------------------------------

/// `CMlPolynomial.monomialBasis`: `∏_j (bit j of i ? w[j] : 1)`.
fn ref_monomial_basis(w: &[u64]) -> Vec<u64> {
    let n = w.len();
    (0..(1usize << n))
        .map(|i| {
            let mut acc = 1u64;
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
fn ref_lagrange_basis(w: &[u64]) -> Vec<u64> {
    let n = w.len();
    (0..(1usize << n))
        .map(|i| {
            let mut acc = 1u64;
            for j in 0..n {
                acc = rmul(acc, if bit(i, j) { w[j] } else { rsub(1, w[j]) });
            }
            acc
        })
        .collect()
}

/// `Vector.dotProduct`.
fn ref_dot(a: &[u64], b: &[u64]) -> u64 {
    let mut acc = 0u64;
    for i in 0..b.len() {
        acc = radd(acc, rmul(a[i], b[i]));
    }
    acc
}

/// `CMlPolynomial.monoToLagrangeSpec`: `out[i] = Σ_{j ⊆ i} p[j]`.
fn ref_zeta_spec(p: &[u64], n: usize) -> Vec<u64> {
    (0..(1usize << n))
        .map(|i| {
            let mut acc = 0u64;
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
fn ref_mobius_spec(p: &[u64], n: usize) -> Vec<u64> {
    (0..(1usize << n))
        .map(|i| {
            let mut acc = 0u64;
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
fn ref_eval_coeffs(p: &[u64], x: &[u64]) -> u64 {
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
        assert!(z.iter().all(|&c| c == 0));
    }
}

#[test]
fn of_array_pads_and_truncates() {
    let coeffs = sample(1, 5);
    // Truncate: 2^1 = 2 < 5.
    assert_eq!(of_array(&coeffs, 1), vec![coeffs[0], coeffs[1]]);
    // Exact: 2^2 = 4 < 5 still truncates.
    assert_eq!(of_array(&coeffs, 2), coeffs[0..4].to_vec());
    // Pad: 2^3 = 8 > 5.
    let padded = of_array(&coeffs, 3);
    assert_eq!(padded.len(), 8);
    assert_eq!(&padded[0..5], &coeffs[..]);
    assert!(padded[5..].iter().all(|&c| c == 0));
}

#[test]
fn add_is_pointwise() {
    for n in 0..6 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 10, sz);
        let q = sample(n as u64 + 99, sz);
        let r = add(&p, &q);
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
        assert_eq!(monomial_basis(&w), ref_monomial_basis(&w), "monomial n={n}");
        assert_eq!(lagrange_basis(&w), ref_lagrange_basis(&w), "lagrange n={n}");
    }
}

/// The Lagrange basis is a partition of unity, and at a Boolean point it is the
/// indicator of that point.  Both are basis-defining properties.
#[test]
fn lagrange_basis_properties() {
    for n in 0..7 {
        let w = sample(n as u64 + 21, n);
        let b = lagrange_basis(&w);
        let total = b.iter().fold(0u64, |acc, &c| radd(acc, c));
        assert_eq!(total, 1 % P, "partition of unity, n={n}");

        // At a Boolean point k, lagrangeBasis is the indicator of k.
        for k in 0..(1usize << n) {
            let point: Vec<u64> = (0..n).map(|j| if bit(k, j) { 1 } else { 0 }).collect();
            let bk = lagrange_basis(&point);
            for i in 0..(1usize << n) {
                let expect = if i == k { 1 % P } else { 0 };
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
        assert_eq!(eval(&p, &w), ref_eval_coeffs(&p, &w), "eval n={n}");
        let lb = ref_lagrange_basis(&w);
        assert_eq!(eval_lagrange(&p, &w), ref_dot(&p, &lb), "eval_lagrange n={n}");
    }
}

#[test]
fn eval_horner_matches_eval() {
    for n in 0..9 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 51, sz);
        let w = sample(n as u64 + 61, n);
        assert_eq!(eval_horner(&p, &w), eval(&p, &w), "horner n={n}");
    }
}

#[test]
fn eval_mle_matches_eval_lagrange() {
    for n in 0..9 {
        let sz = 1usize << n;
        let v = sample(n as u64 + 71, sz);
        let w = sample(n as u64 + 81, n);
        assert_eq!(eval_mle(&v, &w), eval_lagrange(&v, &w), "mle n={n}");
    }
}

#[test]
fn zeta_matches_naive_spec() {
    for n in 0..8 {
        let sz = 1usize << n;
        let p = sample(n as u64 + 91, sz);
        assert_eq!(
            mono_to_lagrange(p.clone(), n),
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
            lagrange_to_mono(p.clone(), n),
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
            lagrange_to_mono(mono_to_lagrange(p.clone(), n), n),
            p,
            "mobius∘zeta n={n}"
        );
        assert_eq!(
            mono_to_lagrange(lagrange_to_mono(p.clone(), n), n),
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
        let evals = mono_to_lagrange(p.clone(), n);
        for i in 0..sz {
            let point: Vec<u64> = (0..n).map(|j| if bit(i, j) { 1 } else { 0 }).collect();
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
        let evals = mono_to_lagrange(p.clone(), n);
        let w = sample(n as u64 + 141, n);
        assert_eq!(eval(&p, &w), eval_lagrange(&evals, &w), "n={n}");
    }
}

/// `eq~(w, x) = ∏_j (w[j] x[j] + (1 - w[j])(1 - x[j]))`, and it is symmetric.
#[test]
fn eq_tilde_matches_product_form() {
    for n in 0..8 {
        let w = sample(n as u64 + 151, n);
        let x = sample(n as u64 + 161, n);
        let mut expect = 1u64;
        for j in 0..n {
            let t = radd(rmul(w[j], x[j]), rmul(rsub(1, w[j]), rsub(1, x[j])));
            expect = rmul(expect, t);
        }
        assert_eq!(eq_tilde(&w, &x), expect, "eq_tilde n={n}");
        assert_eq!(eq_tilde(&w, &x), eq_tilde(&x, &w), "symmetry n={n}");
    }
}

/// A hand-computed case, to pin the little-endian index convention:
/// `n = 2`, `p = 1 + 2 X0 + 3 X1 + 4 X0 X1`, evaluated at `(5, 7)`
/// is `1 + 10 + 21 + 140 = 172`.
#[test]
fn little_endian_convention_pinned() {
    let p = vec![1u64, 2, 3, 4];
    let w = vec![5u64, 7];
    assert_eq!(eval(&p, &w), 172);
    assert_eq!(eval_horner(&p, &w), 172);
    // Hypercube evaluations at (0,0), (1,0), (0,1), (1,1):
    // 1, 3, 4, 10.
    assert_eq!(mono_to_lagrange(p.clone(), 2), vec![1, 3, 4, 10]);
    assert_eq!(lagrange_to_mono(vec![1, 3, 4, 10], 2), p);
}
