//! The concrete coefficient field every polynomial layer of this crate computes
//! in: the quartic extension of the "Hachi" prime field.
//!
//! # The base field
//!
//! `F_P` with `P = 2^32 - 99 = 4294967197`, the "Hachi" prime
//! (`CompPoly/Fields/Hachi.lean`).  An element is a *reduced representative* in
//! `[0, P)`, held in a `u64`; that range is a representation invariant the
//! operations below maintain, and it is what the Lean proofs call `Red`.
//!
//! # The extension
//!
//! `Ext4 = F_P[Y] / (Y^4 - W)` with `W = 2`, the smallest non-square mod `P`.
//! Because `P ≡ 1 mod 4`, `Y^4 - W` is irreducible for any non-square `W`, so
//! this really is a field of size `P^4` — see `CompPoly/Fields/Hachi/Ext4.lean`.
//! An element is a dense little-endian coefficient vector
//! `c0 + c1 Y + c2 Y^2 + c3 Y^3`, mirroring
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
//! The extension arithmetic is fully unrolled, so no operation on `Ext4` needs a
//! loop of its own and the extracted model of this module is entirely
//! straight-line.

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
/// place the crate compares field elements (see `crate::cpoly::trim`).
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
