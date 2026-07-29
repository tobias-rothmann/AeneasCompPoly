//! Computable univariate polynomials over a concrete prime field, written to
//! be translated to Lean by Aeneas/Charon and proved equivalent to
//! `CompPoly.CPolynomial.Raw` (see Verified-zkEVM/CompPoly).
//!
//! Field: F_P with P = 2013265921 (the "BabyBear" prime, 15 * 2^27 + 1).
//! Since P < 2^31, for reduced elements a, b < P we have a + b < 2^32 and
//! a * b < 2^62, so all intermediate arithmetic fits in u64 with NO overflow.
//! This keeps Aeneas's checked-arithmetic `Result` trivially `ok`.
//!
//! A polynomial is a `Vec<u64>` of coefficients, little-endian:
//! `vec![1, 2, 3]` represents `1 + 2*X + 3*X^2`. This mirrors
//! `CompPoly.CPolynomial.Raw R = Array R`.
//!
//! Style notes (for clean Aeneas output): explicit index-based `while` loops,
//! no iterators / closures / slices, fresh `Vec`s built with `push`.

pub mod mlpoly;

/// The field modulus (BabyBear prime). P < 2^31.
pub const P: u64 = 2013265921;

// ------------------------------------------------------------------
// Field operations on reduced representatives in [0, P).
// Preconditions (maintained as a representation invariant in the proof):
// inputs are < P. Outputs are < P.
// ------------------------------------------------------------------

/// Field addition. Mirrors `+` in `R`.
pub fn fadd(a: u64, b: u64) -> u64 {
    (a + b) % P
}

/// Field subtraction `a - b`.
pub fn fsub(a: u64, b: u64) -> u64 {
    (a + P - b) % P
}

/// Field multiplication. Mirrors `*` in `R`.
pub fn fmul(a: u64, b: u64) -> u64 {
    (a * b) % P
}

/// Field negation. Mirrors `Neg.neg`.
pub fn fneg(a: u64) -> u64 {
    (P - a) % P
}

// ------------------------------------------------------------------
// Polynomial constructors.  Coefficients are little-endian.
// ------------------------------------------------------------------

/// Constant polynomial `C r`.  Mirrors `CPolynomial.Raw.C`.
pub fn c(r: u64) -> Vec<u64> {
    let mut p: Vec<u64> = Vec::new();
    p.push(r);
    p
}

/// The variable `X = #[0, 1]`.  Mirrors `CPolynomial.Raw.X`.
pub fn x() -> Vec<u64> {
    let mut p: Vec<u64> = Vec::new();
    p.push(0);
    p.push(1);
    p
}

// ------------------------------------------------------------------
// Canonicalization.
// ------------------------------------------------------------------

/// Remove trailing zero coefficients.  Mirrors `CPolynomial.Raw.trim`.
/// Takes ownership and returns a freshly built canonical vector.
pub fn trim(p: Vec<u64>) -> Vec<u64> {
    // Find the length after dropping trailing zeros.
    let mut n: usize = p.len();
    while n > 0 {
        if p[n - 1] != 0 {
            break;
        }
        n -= 1;
    }
    let mut r: Vec<u64> = Vec::new();
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

/// Evaluate `p` at `x` using Horner's method.
pub fn eval(p: &Vec<u64>, xv: u64) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = p.len();
    while i > 0 {
        i -= 1;
        acc = fadd(fmul(acc, xv), p[i]);
    }
    acc
}

// ------------------------------------------------------------------
// Algebraic operations.
// ------------------------------------------------------------------

/// Untrimmed pointwise addition (zero-padded). Mirrors `addRaw`.
pub fn add_raw(p: &Vec<u64>, q: &Vec<u64>) -> Vec<u64> {
    let np: usize = p.len();
    let nq: usize = q.len();
    let n: usize = if np >= nq { np } else { nq };
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let a: u64 = if i < np { p[i] } else { 0 };
        let b: u64 = if i < nq { q[i] } else { 0 };
        r.push(fadd(a, b));
        i += 1;
    }
    r
}

/// Trimmed addition. Mirrors `CPolynomial.Raw.add`.
pub fn add(p: &Vec<u64>, q: &Vec<u64>) -> Vec<u64> {
    trim(add_raw(p, q))
}

/// Coefficient-wise negation (no trim, since fneg(0) = 0). Mirrors `neg`.
pub fn neg(p: &Vec<u64>) -> Vec<u64> {
    let n: usize = p.len();
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        r.push(fneg(p[i]));
        i += 1;
    }
    r
}

/// Subtraction `p - q`. Mirrors `CPolynomial.Raw.sub = p.add q.neg`.
pub fn sub(p: &Vec<u64>, q: &Vec<u64>) -> Vec<u64> {
    let nq: Vec<u64> = neg(q);
    add(p, &nq)
}

/// Scalar multiplication `r * p` coefficient-wise. Mirrors `smul`.
pub fn smul(r: u64, p: &Vec<u64>) -> Vec<u64> {
    let n: usize = p.len();
    let mut out: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(fmul(r, p[i]));
        i += 1;
    }
    out
}

/// Trimmed schoolbook multiplication. Mirrors `mulRaw |> trim = mul`.
pub fn mul(p: &Vec<u64>, q: &Vec<u64>) -> Vec<u64> {
    let np: usize = p.len();
    let nq: usize = q.len();
    let mut r: Vec<u64> = Vec::new();
    if np == 0 || nq == 0 {
        return r;
    }
    // Allocate np + nq - 1 zero coefficients.
    let n: usize = np + nq - 1;
    let mut k: usize = 0;
    while k < n {
        r.push(0);
        k += 1;
    }
    // Convolution: r[i+j] += p[i] * q[j].
    let mut i: usize = 0;
    while i < np {
        let mut j: usize = 0;
        while j < nq {
            let prod: u64 = fmul(p[i], q[j]);
            let idx: usize = i + j;
            r[idx] = fadd(r[idx], prod);
            j += 1;
        }
        i += 1;
    }
    trim(r)
}
