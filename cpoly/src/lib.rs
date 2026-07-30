//! Computable univariate polynomials over a concrete degree-4 *extension* field,
//! written to be translated to Lean by Aeneas/Charon and proved equivalent to
//! `CompPoly.CPolynomial.Raw` (see Verified-zkEVM/CompPoly).
//!
//! # The field
//!
//! Base field: `F_P` with `P = 2^32 - 99 = 4294967197`, the "Hachi" prime
//! (`CompPoly/Fields/Hachi.lean`).
//!
//! Extension: `Ext4 = F_P[Y] / (Y^4 - W)` with `W = 2`, the smallest non-square
//! mod `P`.  Because `P ≡ 1 mod 4`, `Y^4 - W` is irreducible for any non-square
//! `W`, so this really is a field of size `P^4` — see
//! `CompPoly/Fields/Hachi/Ext4.lean`.  An element is a dense little-endian
//! coefficient vector `c0 + c1 Y + c2 Y^2 + c3 Y^3`, mirroring
//! `CompPoly.Extension.Ext P = Vector F P.d` at `d = 4`.
//!
//! # No overflow
//!
//! All base-field arithmetic is on reduced representatives in `[0, P)`, in `u64`.
//! This is exactly where the Hachi prime is tighter than BabyBear/KoalaBear, and
//! it still fits:
//!
//! * `a + b <= 2(P-1) = 8589934392 < 2^64`;
//! * `a + P - b <= (P-1) + P = 8589934392 < 2^64`;
//! * `a * b <= (P-1)^2 = 18445885080250352416 < 2^64 = 18446744073709551616`
//!   (`P < 2^32`, so `(P-1)^2 < 2^64`; the slack is about `859 * 2^32`);
//! * `W * t = 2t <= 2(P-1) < 2^33`.
//!
//! So every intermediate fits in `u64` with NO overflow, which keeps Aeneas's
//! checked-arithmetic `Result` trivially `ok`.  Note this is *not* true of the
//! obvious next step: a 64-bit modulus would need `u128` intermediates.
//!
//! # Polynomials
//!
//! A polynomial is a `Vec<Ext4>` of coefficients, little-endian in `X`:
//! `vec![a, b, c]` represents `a + b*X + c*X^2`.  This mirrors
//! `CompPoly.CPolynomial.Raw R = Array R` at `R = Hachi.Ext4`.
//!
//! Style notes (for clean Aeneas output): explicit index-based `while` loops,
//! no iterators / closures / slices, fresh `Vec`s built with `push`, and the
//! extension arithmetic fully unrolled so that no operation on `Ext4` needs a
//! loop of its own.

pub mod mlpoly;

/// The base-field modulus (the Hachi prime `2^32 - 99`).  `P < 2^32`.
pub const P: u64 = 4294967197;

/// The binomial-extension constant: `Ext4 = F_P[Y] / (Y^4 - W)`.
///
/// `W = 2` is the smallest non-square mod `P`, so multiplication by `W` is a
/// doubling.  Mirrors `Hachi.ext4Params.W`.
pub const W: u64 = 2;

// ------------------------------------------------------------------
// Base-field operations on reduced representatives in [0, P).
// Preconditions (maintained as a representation invariant in the proof):
// inputs are < P. Outputs are < P.
// ------------------------------------------------------------------

/// Base-field addition.
pub fn fadd(a: u64, b: u64) -> u64 {
    (a + b) % P
}

/// Base-field subtraction `a - b`.
pub fn fsub(a: u64, b: u64) -> u64 {
    (a + P - b) % P
}

/// Base-field multiplication.
pub fn fmul(a: u64, b: u64) -> u64 {
    (a * b) % P
}

/// Base-field negation.
pub fn fneg(a: u64) -> u64 {
    (P - a) % P
}

// ------------------------------------------------------------------
// The extension field.
// ------------------------------------------------------------------

/// An element of `Ext4 = F_P[Y] / (Y^4 - W)`, as its dense little-endian
/// coefficient vector: `c0 + c1 Y + c2 Y^2 + c3 Y^3`.
///
/// Mirrors `CompPoly.Extension.Ext Hachi.ext4Params`, whose carrier is
/// `Vector Hachi.Field 4` with `coeff x i = x[i]`.  Spelling the four
/// coefficients as named fields rather than a `[u64; 4]` keeps every extension
/// operation straight-line in the extracted model: no bounds checks, no loops.
#[derive(Copy, Clone)]
pub struct Ext4 {
    pub c0: u64,
    pub c1: u64,
    pub c2: u64,
    pub c3: u64,
}

/// The zero of `Ext4`.  Mirrors `(0 : Ext P)`.
pub const EZERO: Ext4 = Ext4 {
    c0: 0,
    c1: 0,
    c2: 0,
    c3: 0,
};

/// The one of `Ext4`.  Mirrors `(1 : Ext P)`, i.e. `ofBase 1`.
pub const EONE: Ext4 = Ext4 {
    c0: 1,
    c1: 0,
    c2: 0,
    c3: 0,
};

/// The adjoined fourth root of `W`, i.e. `Y`.  Mirrors `Ext.gen`.
pub const EGEN: Ext4 = Ext4 {
    c0: 0,
    c1: 1,
    c2: 0,
    c3: 0,
};

/// Embed a base-field element as the constant coefficient.  Mirrors
/// `Ext.ofBase`.
pub fn eof_base(a: u64) -> Ext4 {
    Ext4 {
        c0: a,
        c1: 0,
        c2: 0,
        c3: 0,
    }
}

/// Is this the zero element?  Written out rather than via `PartialEq` so that
/// the extracted model contains no derived-trait machinery; this is the only
/// place the code compares field elements (see `trim`).
pub fn is_ezero(a: Ext4) -> bool {
    a.c0 == 0 && a.c1 == 0 && a.c2 == 0 && a.c3 == 0
}

/// Extension addition, coefficient-wise.  Mirrors `Ext.add`.
pub fn eadd(a: Ext4, b: Ext4) -> Ext4 {
    Ext4 {
        c0: fadd(a.c0, b.c0),
        c1: fadd(a.c1, b.c1),
        c2: fadd(a.c2, b.c2),
        c3: fadd(a.c3, b.c3),
    }
}

/// Extension subtraction, coefficient-wise.  Mirrors `Ext.sub`.
pub fn esub(a: Ext4, b: Ext4) -> Ext4 {
    Ext4 {
        c0: fsub(a.c0, b.c0),
        c1: fsub(a.c1, b.c1),
        c2: fsub(a.c2, b.c2),
        c3: fsub(a.c3, b.c3),
    }
}

/// Extension negation, coefficient-wise.  Mirrors `Ext.neg`.
pub fn eneg(a: Ext4) -> Ext4 {
    Ext4 {
        c0: fneg(a.c0),
        c1: fneg(a.c1),
        c2: fneg(a.c2),
        c3: fneg(a.c3),
    }
}

/// Extension multiplication.  Mirrors `Ext.mul` at `d = 4`.
///
/// `t0 .. t6` are the schoolbook product's coefficients before reduction, then
/// `Y^4 = W` folds the high half back with a factor of `W`:
/// `out[k] = t[k] + W * t[k + 4]` for `k < 3`, and `out[3] = t[3]`
/// (there is no `t7`, since `i + j <= 6` for `i, j < 4`).
pub fn emul(a: Ext4, b: Ext4) -> Ext4 {
    let t0: u64 = fmul(a.c0, b.c0);
    let t1: u64 = fadd(fmul(a.c0, b.c1), fmul(a.c1, b.c0));
    let t2: u64 = fadd(fadd(fmul(a.c0, b.c2), fmul(a.c1, b.c1)), fmul(a.c2, b.c0));
    let t3: u64 = fadd(
        fadd(fadd(fmul(a.c0, b.c3), fmul(a.c1, b.c2)), fmul(a.c2, b.c1)),
        fmul(a.c3, b.c0),
    );
    let t4: u64 = fadd(fadd(fmul(a.c1, b.c3), fmul(a.c2, b.c2)), fmul(a.c3, b.c1));
    let t5: u64 = fadd(fmul(a.c2, b.c3), fmul(a.c3, b.c2));
    let t6: u64 = fmul(a.c3, b.c3);
    Ext4 {
        c0: fadd(t0, fmul(W, t4)),
        c1: fadd(t1, fmul(W, t5)),
        c2: fadd(t2, fmul(W, t6)),
        c3: t3,
    }
}

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
