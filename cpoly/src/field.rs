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
//! So every base-field intermediate fits in `u64` with NO overflow, which keeps
//! Aeneas's checked-arithmetic `Result` trivially `ok`.  Note this is *not*
//! true of the obvious next step: a 64-bit modulus would need `u128`
//! intermediates.
//!
//! The general extension product deliberately accumulates its unreduced output
//! coefficients in a `(low, high)` pair representing `low + high * 2^64`.
//! The largest one is `7(P - 1)^2 < 7 * 2^64`, so its high word is at most six.
//! This makes it possible to postpone each output's reduction until all of its
//! terms have been folded by `Y^4 = 2`, without either losing a carry or using
//! a wider Rust integer.
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
        let sum = self.0 + rhs.0;
        Fp(if sum >= P { sum - P } else { sum })
    }
}

impl Sub for Fp {
    type Output = Fp;

    /// Adding `P` first keeps the subtraction on `u64` from going negative;
    /// `a + P - b <= (P-1) + P < 2^64`.
    fn sub(self, rhs: Fp) -> Fp {
        Fp(if self.0 >= rhs.0 {
            self.0 - rhs.0
        } else {
            self.0 + P - rhs.0
        })
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

    /// Zero is its own additive inverse; every other canonical representative
    /// has inverse `P - a`, already in `[0, P)`.
    fn neg(self) -> Fp {
        Fp(if self.0 == 0 { 0 } else { P - self.0 })
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

/// Multiply a reduced base-field element by the extension constant `W = 2`.
///
/// This stays private: it expresses the reduction in [`Ext4`]'s arithmetic,
/// rather than an independently useful operation on the base field.  The
/// first translation keeps the direct field expression as its reference.  The
/// general formula below folds unreduced products directly, while this helper
/// remains the specified `W` multiplication used by the field proof.
#[allow(dead_code)]
fn mul_by_w(t: Fp) -> Fp {
    t + t
}

/// Reduce `low + high * 2^64` modulo `P`, for `high <= 6`.
///
/// `2^32 = 99 (mod P)` and `2^64 = 9_801 (mod P)`.  Splitting the low word at
/// 32 bits twice leaves a value below `P + 10_000`, so one subtraction produces
/// the canonical representative.  Division and remainder by this power of two
/// lower to the same shifts and mask as the equivalent spelling.
#[inline(always)]
fn reduce_wide(low: u64, high: u64) -> Fp {
    const LIMB: u64 = 1u64 << 32;
    let folded_once = (low % LIMB) + 99 * (low / LIMB) + 9_801 * high;
    let folded_twice = (folded_once % LIMB) + 99 * (folded_once / LIMB);
    Fp(if folded_twice >= P {
        folded_twice - P
    } else {
        folded_twice
    })
}

/// Add one raw base-field product to a two-word extension accumulator.
#[inline(always)]
fn add_product(acc: (u64, u64), a: Fp, b: Fp) -> (u64, u64) {
    let (low, carry) = acc.0.overflowing_add(a.0 * b.0);
    (low, acc.1 + u64::from(carry))
}

/// Add twice one raw base-field product to a two-word extension accumulator.
#[inline(always)]
fn add_double_product(acc: (u64, u64), a: Fp, b: Fp) -> (u64, u64) {
    let product = a.0 * b.0;
    let (low, carry0) = acc.0.overflowing_add(product);
    let (low, carry1) = low.overflowing_add(product);
    (low, acc.1 + u64::from(carry0) + u64::from(carry1))
}

/// Add four times one raw base-field product to a two-word extension
/// accumulator.
#[inline(always)]
fn add_quadruple_product(acc: (u64, u64), a: Fp, b: Fp) -> (u64, u64) {
    let product = a.0 * b.0;
    let (low, carry0) = acc.0.overflowing_add(product);
    let (low, carry1) = low.overflowing_add(product);
    let (low, carry2) = low.overflowing_add(product);
    let (low, carry3) = low.overflowing_add(product);
    (
        low,
        acc.1
            + u64::from(carry0)
            + u64::from(carry1)
            + u64::from(carry2)
            + u64::from(carry3),
    )
}

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

    /// Square this extension-field element.
    ///
    /// This exploits symmetry in the degree-six product, using ten base-field
    /// products rather than the general multiplier's sixteen.  The unreduced
    /// output bounds are `7`, `6`, `5`, and `4` products respectively, so the
    /// carry words remain within [`reduce_wide`]'s contract.
    #[must_use]
    #[inline(always)]
    pub fn square(self) -> Ext4 {
        let c0 = add_product((0, 0), self.c0, self.c0);
        let c0 = add_quadruple_product(c0, self.c1, self.c3);
        let c0 = add_double_product(c0, self.c2, self.c2);

        let c1 = add_double_product((0, 0), self.c0, self.c1);
        let c1 = add_quadruple_product(c1, self.c2, self.c3);

        let c2 = add_double_product((0, 0), self.c0, self.c2);
        let c2 = add_product(c2, self.c1, self.c1);
        let c2 = add_double_product(c2, self.c3, self.c3);

        let c3 = add_double_product((0, 0), self.c0, self.c3);
        let c3 = add_double_product(c3, self.c1, self.c2);

        Ext4 {
            c0: reduce_wide(c0.0, c0.1),
            c1: reduce_wide(c1.0, c1.1),
            c2: reduce_wide(c2.0, c2.1),
            c3: reduce_wide(c3.0, c3.1),
        }
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

    /// Schoolbook multiplication with one carry-aware reduction per output.
    ///
    /// `Y^4 = 2` lets degrees four through six fold directly into the four
    /// output accumulators.  Their unreduced bounds, in units of
    /// `(P - 1)^2`, are respectively `7`, `6`, `5`, and `4`; consequently the
    /// carry words passed to [`reduce_wide`] are at most `6`, `5`, `4`, and
    /// `3`.  This retains the ordinary degree-six product formula while
    /// avoiding all of its intermediate base-field reductions.
    fn mul(self, rhs: Ext4) -> Ext4 {
        let c0 = add_product((0, 0), self.c0, rhs.c0);
        let c1 = add_product((0, 0), self.c0, rhs.c1);
        let c2 = add_product((0, 0), self.c0, rhs.c2);
        let c3 = add_product((0, 0), self.c0, rhs.c3);

        let c0 = add_double_product(c0, self.c1, rhs.c3);
        let c1 = add_product(c1, self.c1, rhs.c0);
        let c2 = add_product(c2, self.c1, rhs.c1);
        let c3 = add_product(c3, self.c1, rhs.c2);

        let c0 = add_double_product(c0, self.c2, rhs.c2);
        let c1 = add_double_product(c1, self.c2, rhs.c3);
        let c2 = add_product(c2, self.c2, rhs.c0);
        let c3 = add_product(c3, self.c2, rhs.c1);

        let c0 = add_double_product(c0, self.c3, rhs.c1);
        let c1 = add_double_product(c1, self.c3, rhs.c2);
        let c2 = add_double_product(c2, self.c3, rhs.c3);
        let c3 = add_product(c3, self.c3, rhs.c0);

        Ext4 {
            c0: reduce_wide(c0.0, c0.1),
            c1: reduce_wide(c1.0, c1.1),
            c2: reduce_wide(c2.0, c2.1),
            c3: reduce_wide(c3.0, c3.1),
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
