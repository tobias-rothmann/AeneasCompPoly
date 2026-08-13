//! The concrete coefficient field every polynomial layer of this crate computes
//! in: the quartic extension of the "Hachi" prime field.
//!
//! # The base field
//!
//! [`Fp`] is `F_P` with `P = 2^32 - 99 = 4294967197`, the "Hachi" prime
//! (`CompPoly/Fields/Hachi.lean`).  It wraps a `u64` holding the *reduced
//! representative* in `[0, P)`.  That range is a representation invariant, and
//! it is the invariant the Lean proofs call `Red`.
//!
//! The wrapped `u64` is private, and the only public way to build an [`Fp`] from
//! a machine word is [`Fp::new`], which reduces.  So `Red` is not a precondition
//! a caller can violate — it holds of every value of the type.
//!
//! # The extension
//!
//! [`Ext4`] is `F_P[Y] / (Y^4 - W)` with `W = 2`, the smallest non-square mod
//! `P`.  Because `P ≡ 1 mod 4`, `Y^4 - W` is irreducible for any non-square `W`,
//! so this really is a field of size `P^4` — see
//! `CompPoly/Fields/Hachi/Ext4.lean`.  An element is a dense little-endian
//! coefficient vector `c0 + c1 Y + c2 Y^2 + c3 Y^3`, mirroring
//! `CompPoly.Extension.Ext P = Vector F P.d` at `d = 4`.
//!
//! # Operators
//!
//! [`Fp`] and [`Ext4`] implement [`Add`], [`Sub`], [`Mul`], [`Neg`] and the
//! `*Assign` forms, so field arithmetic is written `a + b * c` rather than
//! `fadd(a, fmul(b, c))`.  Charon resolves each operator to its concrete impl,
//! and Aeneas extracts that impl as an ordinary Lean definition.  There is
//! also a heterogeneous `impl Mul<Ext4> for Fp`, which is what makes
//! scalar-by-polynomial multiplication read as `scalar * coefficient`.
//!
//! # No overflow
//!
//! All base-field arithmetic is on reduced representatives in `[0, P)`, in `u64`.
//! This is exactly where the Hachi prime is tighter than BabyBear/KoalaBear, and
//! it still fits:
//!
//! * `a + b <= 2(P-1) = 8589934392 < 2^64`;
//! * `a + P - b <= (P-1) + P = 8589934392 < 2^64`;
//! * `a * b <= (P-1)^2 = 18446743214716102416 < 2^64 = 18446744073709551616`
//!   (`P < 2^32`, so `(P-1)^2 < 2^64`; the slack is about `200 * 2^32`);
//! * `W * t = 2t <= 2(P-1) < 2^33`.
//!
//! So every intermediate fits in `u64` with NO overflow, which keeps Aeneas's
//! checked-arithmetic `Result` trivially `ok`.  Note this is *not* true of the
//! obvious next step: a 64-bit modulus would need `u128` intermediates.
//!
//! The extension arithmetic is fully unrolled, so no operation on [`Ext4`] needs
//! a loop of its own and the extracted model of this module is entirely
//! straight-line.

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The base-field modulus (the Hachi prime `2^32 - 99`).  `P < 2^32`.
pub const P: u64 = 4_294_967_197;

// ------------------------------------------------------------------
// The base field.
// ------------------------------------------------------------------

/// An element of the base field `F_P`, held as its reduced representative in
/// `[0, P)`.
///
/// The invariant is enforced by construction: the inner `u64` is private, and
/// [`Fp::new`] is the only way in from an arbitrary word.  Every operation below
/// takes reduced inputs to a reduced output.
///
/// This is the `Red`-respecting `U64` of the Lean development; `toK` maps it to
/// `ZMod P`.
#[derive(Copy, Clone, PartialEq, Eq, Default, Debug)]
pub struct Fp(u64);

impl Fp {
    /// The additive identity.
    pub const ZERO: Fp = Fp(0);

    /// The multiplicative identity.
    pub const ONE: Fp = Fp(1);

    /// The modulus, as a machine word.
    pub const MODULUS: u64 = P;

    /// Reduce a machine word into the field.
    pub fn new(v: u64) -> Fp {
        Fp(v % P)
    }

    /// The canonical representative, in `[0, P)`.
    pub const fn to_u64(self) -> u64 {
        self.0
    }

    /// Is this the additive identity?
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }
}

impl From<u64> for Fp {
    /// Reduces; see [`Fp::new`].
    fn from(v: u64) -> Fp {
        Fp::new(v)
    }
}

impl Add for Fp {
    type Output = Fp;

    /// `a + b <= 2(P-1) < 2^64`, so the `u64` sum cannot overflow.
    fn add(self, rhs: Fp) -> Fp {
        Fp((self.0 + rhs.0) % P)
    }
}

impl Sub for Fp {
    type Output = Fp;

    /// Adding `P` first keeps the subtraction on `u64` from going negative;
    /// `a + P - b <= (P-1) + P < 2^64`.
    fn sub(self, rhs: Fp) -> Fp {
        Fp((self.0 + P - rhs.0) % P)
    }
}

impl Mul for Fp {
    type Output = Fp;

    /// `a * b <= (P-1)^2 < 2^64` because `P < 2^32`; this is the tightest of the
    /// no-overflow bounds, with about `200 * 2^32` to spare.
    fn mul(self, rhs: Fp) -> Fp {
        Fp((self.0 * rhs.0) % P)
    }
}

impl Neg for Fp {
    type Output = Fp;

    /// The outer `% P` is what sends `0` to `0` rather than to `P`.
    fn neg(self) -> Fp {
        Fp((P - self.0) % P)
    }
}

impl AddAssign for Fp {
    fn add_assign(&mut self, rhs: Fp) {
        *self = *self + rhs;
    }
}

impl SubAssign for Fp {
    fn sub_assign(&mut self, rhs: Fp) {
        *self = *self - rhs;
    }
}

impl MulAssign for Fp {
    fn mul_assign(&mut self, rhs: Fp) {
        *self = *self * rhs;
    }
}

// ------------------------------------------------------------------
// The extension field.
// ------------------------------------------------------------------

/// The binomial-extension constant: `Ext4 = F_P[Y] / (Y^4 - W)`.
///
/// `W = 2` is the smallest non-square mod `P`, so multiplication by `W` is a
/// doubling.  Mirrors `Hachi.ext4Params.W`.
pub const W: Fp = Fp(2);

/// An element of `Ext4 = F_P[Y] / (Y^4 - W)`, as its dense little-endian
/// coefficient vector: `c0 + c1 Y + c2 Y^2 + c3 Y^3`.
///
/// Mirrors `CompPoly.Extension.Ext Hachi.ext4Params`, whose carrier is
/// `Vector Hachi.Field 4` with `coeff x i = x[i]`.  Spelling the four
/// coefficients as named fields rather than a `[Fp; 4]` keeps every extension
/// operation straight-line in the extracted model: no bounds checks, no loops.
///
/// The coefficients are public, as they are in the binomial-extension types of
/// the usual Rust field libraries: they carry no invariant beyond the one each
/// [`Fp`] already carries.
#[derive(Copy, Clone, PartialEq, Eq, Default, Debug)]
pub struct Ext4 {
    /// The constant coefficient.
    pub c0: Fp,
    /// The coefficient of `Y`.
    pub c1: Fp,
    /// The coefficient of `Y^2`.
    pub c2: Fp,
    /// The coefficient of `Y^3`.
    pub c3: Fp,
}

impl Ext4 {
    /// The additive identity.  Mirrors `(0 : Ext P)`.
    pub const ZERO: Ext4 = Ext4 {
        c0: Fp::ZERO,
        c1: Fp::ZERO,
        c2: Fp::ZERO,
        c3: Fp::ZERO,
    };

    /// The multiplicative identity.  Mirrors `(1 : Ext P)`, i.e. `ofBase 1`.
    pub const ONE: Ext4 = Ext4 {
        c0: Fp::ONE,
        c1: Fp::ZERO,
        c2: Fp::ZERO,
        c3: Fp::ZERO,
    };

    /// The adjoined fourth root of [`W`], i.e. `Y`.  Mirrors `Ext.gen`.
    ///
    /// Not used by the arithmetic; it pins the basis convention, so that `c1`
    /// really is the coefficient of `Y` and not of some other basis vector.
    pub const GEN: Ext4 = Ext4 {
        c0: Fp::ZERO,
        c1: Fp::ONE,
        c2: Fp::ZERO,
        c3: Fp::ZERO,
    };

    /// The element with the given little-endian coefficients.
    pub const fn new(c0: Fp, c1: Fp, c2: Fp, c3: Fp) -> Ext4 {
        Ext4 { c0, c1, c2, c3 }
    }

    /// Embed a base-field element as the constant coefficient.  Mirrors
    /// `Ext.ofBase`.
    pub const fn from_base(a: Fp) -> Ext4 {
        Ext4 {
            c0: a,
            c1: Fp::ZERO,
            c2: Fp::ZERO,
            c3: Fp::ZERO,
        }
    }

    /// Is this the additive identity?
    ///
    /// Written out coefficient by coefficient rather than as
    /// `*self == Self::ZERO` so that the extracted model is a plain chain of
    /// word comparisons.  This is the only place the crate compares field
    /// elements (see [`crate::univariate::UnivariatePoly::trim`]).
    pub fn is_zero(self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero() && self.c3.is_zero()
    }
}

impl From<Fp> for Ext4 {
    fn from(a: Fp) -> Ext4 {
        Ext4::from_base(a)
    }
}

impl From<u64> for Ext4 {
    /// Reduces the word, then embeds it; see [`Fp::new`] and [`Ext4::from_base`].
    fn from(a: u64) -> Ext4 {
        Ext4::from_base(Fp::new(a))
    }
}

impl Add for Ext4 {
    type Output = Ext4;

    /// Coefficient-wise.  Mirrors `Ext.add`.
    fn add(self, rhs: Ext4) -> Ext4 {
        Ext4 {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
            c2: self.c2 + rhs.c2,
            c3: self.c3 + rhs.c3,
        }
    }
}

impl Sub for Ext4 {
    type Output = Ext4;

    /// Coefficient-wise.  Mirrors `Ext.sub`.
    fn sub(self, rhs: Ext4) -> Ext4 {
        Ext4 {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
            c2: self.c2 - rhs.c2,
            c3: self.c3 - rhs.c3,
        }
    }
}

impl Neg for Ext4 {
    type Output = Ext4;

    /// Coefficient-wise.  Mirrors `Ext.neg`.
    fn neg(self) -> Ext4 {
        Ext4 {
            c0: -self.c0,
            c1: -self.c1,
            c2: -self.c2,
            c3: -self.c3,
        }
    }
}

impl Mul for Ext4 {
    type Output = Ext4;

    /// Mirrors `Ext.mul` at `d = 4`.
    ///
    /// `t0 .. t6` are the schoolbook product's coefficients before reduction,
    /// then `Y^4 = W` folds the high half back with a factor of [`W`]:
    /// `out[k] = t[k] + W * t[k + 4]` for `k < 3`, and `out[3] = t[3]`
    /// (there is no `t7`, since `i + j <= 6` for `i, j < 4`).
    fn mul(self, rhs: Ext4) -> Ext4 {
        let t0: Fp = self.c0 * rhs.c0;
        let t1: Fp = self.c0 * rhs.c1 + self.c1 * rhs.c0;
        let t2: Fp = self.c0 * rhs.c2 + self.c1 * rhs.c1 + self.c2 * rhs.c0;
        let t3: Fp = self.c0 * rhs.c3 + self.c1 * rhs.c2 + self.c2 * rhs.c1 + self.c3 * rhs.c0;
        let t4: Fp = self.c1 * rhs.c3 + self.c2 * rhs.c2 + self.c3 * rhs.c1;
        let t5: Fp = self.c2 * rhs.c3 + self.c3 * rhs.c2;
        let t6: Fp = self.c3 * rhs.c3;
        Ext4 {
            c0: t0 + W * t4,
            c1: t1 + W * t5,
            c2: t2 + W * t6,
            c3: t3,
        }
    }
}

impl Mul<Ext4> for Fp {
    type Output = Ext4;

    /// Scale an extension element by a base-field one, coefficient-wise.  This
    /// is what lets the polynomial layers write `scalar * coefficient`.
    fn mul(self, rhs: Ext4) -> Ext4 {
        Ext4 {
            c0: self * rhs.c0,
            c1: self * rhs.c1,
            c2: self * rhs.c2,
            c3: self * rhs.c3,
        }
    }
}

impl AddAssign for Ext4 {
    fn add_assign(&mut self, rhs: Ext4) {
        *self = *self + rhs;
    }
}

impl SubAssign for Ext4 {
    fn sub_assign(&mut self, rhs: Ext4) {
        *self = *self - rhs;
    }
}

impl MulAssign for Ext4 {
    fn mul_assign(&mut self, rhs: Ext4) {
        *self = *self * rhs;
    }
}
