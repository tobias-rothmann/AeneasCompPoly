//! Computable **univariate** polynomials over the crate's concrete field
//! ([`crate::field::Ext4`], the degree-4 extension of the Hachi prime field),
//! written to be translated to Lean by Aeneas/Charon and proved equivalent to
//! `CompPoly.CPolynomial.Raw` (see Verified-zkEVM/CompPoly,
//! `CompPoly/Univariate/Raw/Ops.lean`).
//!
//! ## Representation
//!
//! A polynomial is a `Vec<Ext4>` of coefficients, little-endian in `X`:
//! `vec![a, b, c]` represents `a + b*X + c*X^2`.  This mirrors
//! `CompPoly.CPolynomial.Raw R = Array R` at `R = Hachi.Ext4`.
//!
//! The canonical form has no trailing zero coefficient; [`trim`] establishes it
//! and [`add`], [`sub`] and [`mul`] preserve it.
//!
//! ## Field arithmetic
//!
//! All coefficient arithmetic goes through [`crate::field`]'s extension helpers
//! `eadd`, `eneg`, `emul` and the zero test `is_ezero`.  Since the base modulus
//! `P` is below `2^32`, no intermediate `u64` overflows, which is what keeps
//! Aeneas's checked-arithmetic `Result` trivially `ok` (see the `field` docs).
//! The one operation that *can* fail is [`mul`], whose accumulator length is a
//! checked `usize` sum — see its docstring.

use crate::field::{eadd, emul, eneg, is_ezero, Ext4, EONE, EZERO};

// ------------------------------------------------------------------
// Polynomial constructors.  Coefficients are little-endian in X.
// ------------------------------------------------------------------

/// Constant polynomial `C r`.  Mirrors `CPolynomial.Raw.C`.
pub fn c(r: Ext4) -> Vec<Ext4> {
    let mut p: Vec<Ext4> = Vec::new();
    p.push(r);
    p
}

/// The variable `X = #[0, 1]`.  Mirrors `CPolynomial.Raw.X`.
pub fn x() -> Vec<Ext4> {
    let mut p: Vec<Ext4> = Vec::new();
    p.push(EZERO);
    p.push(EONE);
    p
}

// ------------------------------------------------------------------
// Canonicalization.
// ------------------------------------------------------------------

/// Remove trailing zero coefficients.  Mirrors `CPolynomial.Raw.trim`.
/// Takes ownership and returns a freshly built canonical vector.
pub fn trim(p: Vec<Ext4>) -> Vec<Ext4> {
    // Find the length after dropping trailing zeros.
    let mut n: usize = p.len();
    while n > 0 {
        if !is_ezero(p[n - 1]) {
            break;
        }
        n -= 1;
    }
    let mut r: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        r.push(p[i]);
        i += 1;
    }
    r
}

// ------------------------------------------------------------------
// Evaluation (Horner). Mirrors `CPolynomial.Raw.eval` / `eval2Horner`.
// ------------------------------------------------------------------

/// Evaluate `p` at `xv` using Horner's method.
pub fn eval(p: &Vec<Ext4>, xv: Ext4) -> Ext4 {
    let mut acc: Ext4 = EZERO;
    let mut i: usize = p.len();
    while i > 0 {
        i -= 1;
        acc = eadd(emul(acc, xv), p[i]);
    }
    acc
}

// ------------------------------------------------------------------
// Algebraic operations.
// ------------------------------------------------------------------

/// Untrimmed pointwise addition (zero-padded). Mirrors `addRaw`.
pub fn add_raw(p: &Vec<Ext4>, q: &Vec<Ext4>) -> Vec<Ext4> {
    let np: usize = p.len();
    let nq: usize = q.len();
    let n: usize = if np >= nq { np } else { nq };
    let mut r: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let a: Ext4 = if i < np { p[i] } else { EZERO };
        let b: Ext4 = if i < nq { q[i] } else { EZERO };
        r.push(eadd(a, b));
        i += 1;
    }
    r
}

/// Trimmed addition. Mirrors `CPolynomial.Raw.add`.
pub fn add(p: &Vec<Ext4>, q: &Vec<Ext4>) -> Vec<Ext4> {
    trim(add_raw(p, q))
}

/// Coefficient-wise negation (no trim, since `eneg 0 = 0`). Mirrors `neg`.
pub fn neg(p: &Vec<Ext4>) -> Vec<Ext4> {
    let n: usize = p.len();
    let mut r: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        r.push(eneg(p[i]));
        i += 1;
    }
    r
}

/// Subtraction `p - q`. Mirrors `CPolynomial.Raw.sub = p.add q.neg`.
pub fn sub(p: &Vec<Ext4>, q: &Vec<Ext4>) -> Vec<Ext4> {
    let nq: Vec<Ext4> = neg(q);
    add(p, &nq)
}

/// Scalar multiplication `r * p` coefficient-wise. Mirrors `smul`.
pub fn smul(r: Ext4, p: &Vec<Ext4>) -> Vec<Ext4> {
    let n: usize = p.len();
    let mut out: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(emul(r, p[i]));
        i += 1;
    }
    out
}

/// Trimmed schoolbook multiplication. Mirrors `mulRaw |> trim = mul`.
///
/// The accumulator is sized with `np + nq - 1`; in the extracted model that
/// `np + nq` is a *checked* `usize` addition, so the Lean spec carries the
/// hypothesis `np + nq <= usize::MAX` (unreachable for real `Vec`s, which are
/// capacity-bounded by `isize::MAX` bytes).
pub fn mul(p: &Vec<Ext4>, q: &Vec<Ext4>) -> Vec<Ext4> {
    let np: usize = p.len();
    let nq: usize = q.len();
    let mut r: Vec<Ext4> = Vec::new();
    if np == 0 || nq == 0 {
        return r;
    }
    // Allocate np + nq - 1 zero coefficients.
    let n: usize = np + nq - 1;
    let mut k: usize = 0;
    while k < n {
        r.push(EZERO);
        k += 1;
    }
    // Convolution: r[i+j] += p[i] * q[j].
    let mut i: usize = 0;
    while i < np {
        let mut j: usize = 0;
        while j < nq {
            let prod: Ext4 = emul(p[i], q[j]);
            let idx: usize = i + j;
            r[idx] = eadd(r[idx], prod);
            j += 1;
        }
        i += 1;
    }
    trim(r)
}
