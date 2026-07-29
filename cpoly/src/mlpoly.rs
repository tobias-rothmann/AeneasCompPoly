//! Computable **multilinear** polynomials over the same concrete prime field as
//! the univariate layer (see the crate root), written to be translated to Lean
//! by Aeneas/Charon and proved equivalent to `CompPoly.CMlPolynomial` and
//! `CompPoly.CMlPolynomialEval` (see Verified-zkEVM/CompPoly,
//! `CompPoly/Multilinear/Basic.lean`).
//!
//! ## Representation
//!
//! A multilinear polynomial in `n` variables is a `Vec<u64>` of length `2^n`.
//! The index is read **little-endian**: bit `j` of the index is the exponent of
//! variable `j`.  So for `n = 2`, `vec![c0, c1, c2, c3]` denotes
//! `c0 + c1*X0 + c2*X1 + c3*X0*X1`.  This mirrors
//! `CompPoly.CMlPolynomial R n = Vector R (2 ^ n)`.
//!
//! The very same layout, read in the *Lagrange* (Boolean-hypercube) basis,
//! is `CompPoly.CMlPolynomialEval R n`: entry `i` is the value of the
//! polynomial at the Boolean point whose `j`-th coordinate is bit `j` of `i`.
//! The two readings are related by the zeta / Möbius transforms
//! (`mono_to_lagrange` / `lagrange_to_mono`) at the bottom of this file.
//!
//! ## Field arithmetic
//!
//! All coefficient arithmetic goes through the crate-root field helpers
//! `fadd`, `fsub`, `fmul` on reduced representatives in `[0, P)`.  Since
//! `P < 2^31`, no intermediate `u64` overflows, which is what keeps Aeneas's
//! checked-arithmetic `Result` trivially `ok` (see the crate-root docs).
//!
//! Coefficient-wise negation and scalar multiplication are *literally* the
//! univariate `crate::neg` / `crate::smul`: nothing about them depends on how
//! the index is interpreted, so they are not duplicated here — the Lean
//! development states their multilinear specs directly about `cpoly::neg` and
//! `cpoly::smul`.
//!
//! ## Style notes (for clean Aeneas output)
//!
//! Explicit index-based `while` loops, no iterators / closures / slices, fresh
//! `Vec`s built with `push`, and bit tests written with `/` and `%` rather than
//! `>>` / `&` so that the extracted model stays in plain `Usize` arithmetic.

use crate::{fadd, fmul, fsub};

// ------------------------------------------------------------------
// Sizes and bit tests.
// ------------------------------------------------------------------

/// `2^n` as a `usize`.  This is the length index of `CMlPolynomial R n`.
///
/// Uses repeated checked doubling, so it is `Result`-total exactly when
/// `2^n` fits in a `usize`.
pub fn pow2(n: usize) -> usize {
    let mut m: usize = 1;
    let mut k: usize = 0;
    while k < n {
        m = m * 2;
        k += 1;
    }
    m
}

// ------------------------------------------------------------------
// Constructors and coefficient-wise operations.
// ------------------------------------------------------------------

/// The zero polynomial in `n` variables.  Mirrors `CMlPolynomial.zero`.
pub fn zero(n: usize) -> Vec<u64> {
    let sz: usize = pow2(n);
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        r.push(0);
        i += 1;
    }
    r
}

/// Conform a coefficient list to `n` variables, zero-padding or truncating.
/// Mirrors `CMlPolynomial.ofArray`.
pub fn of_array(coeffs: &Vec<u64>, n: usize) -> Vec<u64> {
    let sz: usize = pow2(n);
    let m: usize = coeffs.len();
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        if i < m {
            r.push(coeffs[i]);
        } else {
            r.push(0);
        }
        i += 1;
    }
    r
}

/// Coefficient-wise addition.  Mirrors `CMlPolynomial.add`
/// (`Vector.zipWith (· + ·)`), and likewise `CMlPolynomialEval.add`.
///
/// Both arguments must have the same length `2^n`; there is no zero-padding
/// here, unlike the univariate `crate::add`.
pub fn add(p: &Vec<u64>, q: &Vec<u64>) -> Vec<u64> {
    let n: usize = p.len();
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let s: u64 = fadd(p[i], q[i]);
        r.push(s);
        i += 1;
    }
    r
}

// ------------------------------------------------------------------
// Bases.
// ------------------------------------------------------------------

/// Monomial-basis vector at `w`: entry `i` is `∏_{j : bit j of i is set} w[j]`.
/// Mirrors `CMlPolynomial.monomialBasis`.
///
/// The inner loop walks the bits of `i` from least to most significant, keeping
/// `m = i / 2^j` so that `m % 2` is bit `j`.
pub fn monomial_basis(w: &Vec<u64>) -> Vec<u64> {
    let n: usize = w.len();
    let sz: usize = pow2(n);
    let mut basis: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        let mut acc: u64 = 1;
        let mut m: usize = i;
        let mut j: usize = 0;
        while j < n {
            if m % 2 == 1 {
                acc = fmul(acc, w[j]);
            }
            m = m / 2;
            j += 1;
        }
        basis.push(acc);
        i += 1;
    }
    basis
}

/// Lagrange (Boolean-hypercube) basis vector at `w`: entry `i` is
/// `∏_j (if bit j of i is set then w[j] else 1 - w[j])`.
/// Mirrors `CMlPolynomialEval.lagrangeBasis`.
pub fn lagrange_basis(w: &Vec<u64>) -> Vec<u64> {
    let n: usize = w.len();
    let sz: usize = pow2(n);
    let mut basis: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        let mut acc: u64 = 1;
        let mut m: usize = i;
        let mut j: usize = 0;
        while j < n {
            if m % 2 == 1 {
                acc = fmul(acc, w[j]);
            } else {
                let t: u64 = fsub(1, w[j]);
                acc = fmul(acc, t);
            }
            m = m / 2;
            j += 1;
        }
        basis.push(acc);
        i += 1;
    }
    basis
}

// ------------------------------------------------------------------
// Evaluation by dot product against a basis.
// ------------------------------------------------------------------

/// Inner product `∑_{i < n} a[i] * b[i]`, accumulated left-to-right from `0`.
/// Mirrors `CompPoly.Vector.dotProduct`, which is
/// `a.zipWith (· * ·) b |>.foldl (· + ·) 0`.
pub fn dot(a: &Vec<u64>, b: &Vec<u64>, n: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < n {
        let t: u64 = fmul(a[i], b[i]);
        acc = fadd(acc, t);
        i += 1;
    }
    acc
}

/// Evaluate a coefficient-form multilinear polynomial at `w`.
/// Mirrors `CMlPolynomial.eval` (dot product with the monomial basis).
pub fn eval(p: &Vec<u64>, w: &Vec<u64>) -> u64 {
    let basis: Vec<u64> = monomial_basis(w);
    let sz: usize = basis.len();
    dot(p, &basis, sz)
}

/// Evaluate an evaluation-form (Boolean-hypercube) multilinear polynomial
/// at `w`.  Mirrors `CMlPolynomialEval.eval` (dot product with the Lagrange
/// basis).
pub fn eval_lagrange(p: &Vec<u64>, w: &Vec<u64>) -> u64 {
    let basis: Vec<u64> = lagrange_basis(w);
    let sz: usize = basis.len();
    dot(p, &basis, sz)
}

/// The multilinear equality kernel `eq~(w, x)`, i.e. the Lagrange-basis
/// polynomial of `w` evaluated at `x`.  Mirrors `CMlPolynomialEval.eqTilde`.
pub fn eq_tilde(w: &Vec<u64>, x: &Vec<u64>) -> u64 {
    let b: Vec<u64> = lagrange_basis(w);
    eval_lagrange(&b, x)
}

// ------------------------------------------------------------------
// Evaluation by layered variable elimination (the fast algorithms).
// ------------------------------------------------------------------

/// One Horner layer on a *coefficient*-form table: eliminate the
/// least-significant variable at `x0`, halving the length.
///
/// `out[j] = coeffs[2j] + x0 * coeffs[2j+1]`, mirroring the coefficient-form
/// Horner step behind `CMlPolynomial.evalHorner`.
pub fn eval_horner_layer(coeffs: &Vec<u64>, x0: u64) -> Vec<u64> {
    let half: usize = coeffs.len() / 2;
    let mut out: Vec<u64> = Vec::new();
    let mut j: usize = 0;
    while j < half {
        let lo: u64 = coeffs[2 * j];
        let hi: u64 = coeffs[2 * j + 1];
        let t: u64 = fmul(x0, hi);
        let v: u64 = fadd(lo, t);
        out.push(v);
        j += 1;
    }
    out
}

/// Evaluate a coefficient-form multilinear polynomial by repeated Horner
/// layers: `O(2^n)` field operations, versus `O(n · 2^n)` to build the basis.
/// Mirrors `CMlPolynomial.evalHorner`.
///
/// Variables are eliminated least-significant first, so layer `j` uses `w[j]`.
pub fn eval_horner(p: &Vec<u64>, w: &Vec<u64>) -> u64 {
    let n: usize = w.len();
    let sz: usize = pow2(n);
    let mut cur: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        cur.push(p[i]);
        i += 1;
    }
    let mut j: usize = 0;
    while j < n {
        cur = eval_horner_layer(&cur, w[j]);
        j += 1;
    }
    cur[0]
}

/// One multilinear-extension layer on an *evaluation*-form table: fold the
/// least-significant variable at `x0`, halving the length.
///
/// `out[j] = (1 - x0) * values[2j] + x0 * values[2j+1]`.
/// Mirrors `CMlPolynomialEval.evalMleLayer`.
pub fn eval_mle_layer(values: &Vec<u64>, x0: u64) -> Vec<u64> {
    let half: usize = values.len() / 2;
    let one_minus: u64 = fsub(1, x0);
    let mut out: Vec<u64> = Vec::new();
    let mut j: usize = 0;
    while j < half {
        let lo: u64 = values[2 * j];
        let hi: u64 = values[2 * j + 1];
        let a: u64 = fmul(one_minus, lo);
        let b: u64 = fmul(x0, hi);
        let v: u64 = fadd(a, b);
        out.push(v);
        j += 1;
    }
    out
}

/// Evaluate a Boolean-hypercube table by repeated multilinear-extension
/// layers.  Mirrors `CMlPolynomialEval.evalMle`.
pub fn eval_mle(values: &Vec<u64>, w: &Vec<u64>) -> u64 {
    let n: usize = w.len();
    let sz: usize = pow2(n);
    let mut cur: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        cur.push(values[i]);
        i += 1;
    }
    let mut j: usize = 0;
    while j < n {
        cur = eval_mle_layer(&cur, w[j]);
        j += 1;
    }
    cur[0]
}

// ------------------------------------------------------------------
// Zeta / Möbius transforms between the two representations.
// ------------------------------------------------------------------

/// One level of the zeta transform (coefficients → hypercube evaluations):
///
/// `out[i] = v[i] + v[i - 2^j]` when bit `j` of `i` is set, else `v[i]`.
///
/// Mirrors `CMlPolynomial.monoToLagrangeLevel`.  The bit test is
/// `(i / 2^j) % 2 == 1`, and it guarantees `i >= 2^j`, which is what makes the
/// checked subtraction `i - stride` succeed.
pub fn mono_to_lagrange_level(v: &Vec<u64>, j: usize) -> Vec<u64> {
    let n: usize = v.len();
    let stride: usize = pow2(j);
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if (i / stride) % 2 == 1 {
            let s: u64 = fadd(v[i], v[i - stride]);
            r.push(s);
        } else {
            r.push(v[i]);
        }
        i += 1;
    }
    r
}

/// Full zeta transform: apply levels `0, 1, …, n-1` in that order.
/// Mirrors `CMlPolynomial.monoToLagrange` (a `foldl` over `List.finRange n`).
///
/// Takes ownership of `v` so that no defensive copy is needed.
pub fn mono_to_lagrange(v: Vec<u64>, n: usize) -> Vec<u64> {
    let mut cur: Vec<u64> = v;
    let mut j: usize = 0;
    while j < n {
        cur = mono_to_lagrange_level(&cur, j);
        j += 1;
    }
    cur
}

/// One level of the Möbius / inverse zeta transform
/// (hypercube evaluations → coefficients):
///
/// `out[i] = v[i] - v[i - 2^j]` when bit `j` of `i` is set, else `v[i]`.
///
/// Mirrors `CMlPolynomial.lagrangeToMonoLevel`, and is the exact inverse of
/// `mono_to_lagrange_level` at the same level.
pub fn lagrange_to_mono_level(v: &Vec<u64>, j: usize) -> Vec<u64> {
    let n: usize = v.len();
    let stride: usize = pow2(j);
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if (i / stride) % 2 == 1 {
            let s: u64 = fsub(v[i], v[i - stride]);
            r.push(s);
        } else {
            r.push(v[i]);
        }
        i += 1;
    }
    r
}

/// Full Möbius transform: apply levels `n-1, n-2, …, 0` in that order.
/// Mirrors `CMlPolynomial.lagrangeToMono` (a `foldr` over `List.finRange n`).
pub fn lagrange_to_mono(v: Vec<u64>, n: usize) -> Vec<u64> {
    let mut cur: Vec<u64> = v;
    let mut j: usize = n;
    while j > 0 {
        j -= 1;
        cur = lagrange_to_mono_level(&cur, j);
    }
    cur
}
