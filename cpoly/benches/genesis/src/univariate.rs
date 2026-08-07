//! Computable **univariate** polynomials over the crate's concrete field
//! ([`Ext4`], the degree-4 extension of the Hachi prime field — see
//! [`crate::field`]), written to be translated to Lean by Aeneas/Charon and
//! proved equivalent to `CompPoly.CPolynomial.Raw` (see Verified-zkEVM/CompPoly,
//! `CompPoly/Univariate/Raw/Ops.lean`).
//!
//! ## Representation
//!
//! [`UnivariatePoly`] wraps a `Vec<Ext4>` of coefficients, little-endian in `X`:
//! `UnivariatePoly::from_coeffs(vec![a, b, c])` is `a + b*X + c*X^2`.  This mirrors
//! `CompPoly.CPolynomial.Raw R = Array R` at `R = Hachi.Ext4`.
//!
//! The canonical form has no trailing zero coefficient; [`UnivariatePoly::trim`]
//! establishes it and the [`Add`], [`Sub`] and [`Mul`] impls preserve it.
//! Trailing zeros are *representable* — nothing here rejects them — which is why
//! [`UnivariatePoly`] is a newtype and not a type alias: it is the thing the trimming
//! discipline is about.
//!
//! ## Operators
//!
//! Arithmetic is the standard traits, on references:
//!
//! ```
//! use cpoly::{Ext4, UnivariatePoly};
//!
//! let p = UnivariatePoly::from_coeffs(vec![Ext4::ONE, Ext4::ONE]); // 1 + X
//! let q = UnivariatePoly::x();                                     // X
//! assert_eq!((&p * &q).coeffs(), &[Ext4::ZERO, Ext4::ONE, Ext4::ONE]); // X + X^2
//! assert_eq!((&p - &q).coeffs(), &[Ext4::ONE]);                    // 1
//! ```
//!
//! Only the by-reference impls exist.  Every one of them allocates a fresh
//! coefficient vector, so a by-value impl could not reuse the input's buffer and
//! would be a pure delegation — and this crate holds itself to a proved Lean
//! spec per public operation, so an unproved delegation would be a real cost for
//! no gain.  `&p + &q` is the same idiom `num-bigint` and `ark-poly` expose.
//!
//! ## Field arithmetic
//!
//! All coefficient arithmetic goes through [`Ext4`]'s operator impls.  Since the
//! base modulus `P` is below `2^32`, no intermediate `u64` overflows, which is
//! what keeps Aeneas's checked-arithmetic `Result` trivially `ok` (see the
//! [`crate::field`] docs).  The one operation that *can* fail is [`Mul`], whose
//! accumulator length is a checked `usize` sum — see its docstring.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, Index, Mul, Neg, Sub};

use crate::field::Ext4;

// @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly
/// A univariate polynomial over [`Ext4`], as a dense little-endian coefficient
/// vector.
///
/// Mirrors `CompPoly.CPolynomial.Raw Hachi.Ext4`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UnivariatePoly(Vec<Ext4>);

// ------------------------------------------------------------------
// Construction and observation.
// ------------------------------------------------------------------

impl UnivariatePoly {
    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::zero
    /// The zero polynomial: no coefficients at all.
    pub fn zero() -> UnivariatePoly {
        UnivariatePoly(Vec::new())
    }

    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::constant
    /// The constant polynomial `c`.  Mirrors `CPolynomial.Raw.C`.
    ///
    /// Not trimmed, so `UnivariatePoly::constant(Ext4::ZERO)` has one (zero) coefficient
    /// rather than none — matching `Raw.C`, whose result is always `#[c]`.
    // `vec![c]` would read better, but the list form of `vec!` goes through a
    // stack array and `Slice::into_vec`, which drags `core::mem::MaybeUninit`
    // into `lean/Generated.lean` as an `axiom`. (The *repeat* form, `vec![x; n]`,
    // is `alloc::vec::from_elem` and is fully modelled — see `UnivariatePoly::mul`.)
    #[allow(clippy::vec_init_then_push)]
    pub fn constant(c: Ext4) -> UnivariatePoly {
        let mut coeffs: Vec<Ext4> = Vec::new();
        coeffs.push(c);
        UnivariatePoly(coeffs)
    }

    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::x
    /// The variable `X`.  Mirrors `CPolynomial.Raw.X`.
    #[allow(clippy::vec_init_then_push)] // see `UnivariatePoly::constant`
    pub fn x() -> UnivariatePoly {
        let mut coeffs: Vec<Ext4> = Vec::new();
        coeffs.push(Ext4::ZERO);
        coeffs.push(Ext4::ONE);
        UnivariatePoly(coeffs)
    }

    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::from_coeffs
    /// Take a coefficient vector as it stands, little-endian in `X`.
    pub fn from_coeffs(coeffs: Vec<Ext4>) -> UnivariatePoly {
        UnivariatePoly(coeffs)
    }

    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::coeffs
    /// The coefficients, little-endian in `X`.
    pub fn coeffs(&self) -> &[Ext4] {
        &self.0
    }

    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::into_coeffs
    /// Give up the coefficient vector without copying it.
    pub fn into_coeffs(self) -> Vec<Ext4> {
        self.0
    }

    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::len
    /// How many coefficients are stored — one more than the degree, when the
    /// polynomial is trimmed and nonzero.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::is_empty
    /// Are there no coefficients?
    ///
    /// Spelled `len() == 0` rather than `Vec::is_empty`, which the Aeneas Lean
    /// backend has no model for: calling it would put an `axiom` into
    /// `lean/Generated.lean`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::degree
    /// The degree, or `None` for a polynomial with no coefficients.
    ///
    /// This reads the *representation*: it is the degree of the polynomial only
    /// when there is no trailing zero coefficient, i.e. after [`UnivariatePoly::trim`].
    pub fn degree(&self) -> Option<usize> {
        let n = self.len();
        if n == 0 {
            None
        } else {
            Some(n - 1)
        }
    }
}

impl Default for UnivariatePoly {
    // @genesis 80b5733 2026-08-03 — univariate::<UnivariatePoly as Default>::default
    fn default() -> UnivariatePoly {
        UnivariatePoly::zero()
    }
}

impl From<Vec<Ext4>> for UnivariatePoly {
    // @genesis 80b5733 2026-08-03 — univariate::<UnivariatePoly as From<Vec<Ext4>>>::from
    fn from(coeffs: Vec<Ext4>) -> UnivariatePoly {
        UnivariatePoly::from_coeffs(coeffs)
    }
}

impl Index<usize> for UnivariatePoly {
    type Output = Ext4;

    // @genesis 7ca92f9 2026-07-31 — univariate::<UnivariatePoly as Index<usize>>::index
    /// # Panics
    ///
    /// If `i` is at or past [`UnivariatePoly::len`].  Out-of-range coefficients of a
    /// polynomial are mathematically zero, but this is the `Index` contract, and
    /// silently reading zero would hide length bugs in callers.
    fn index(&self, i: usize) -> &Ext4 {
        &self.0[i]
    }
}

// ------------------------------------------------------------------
// Canonicalization.
// ------------------------------------------------------------------

impl UnivariatePoly {
    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::trim
    /// Drop trailing zero coefficients.  Mirrors `CPolynomial.Raw.trim`.
    ///
    /// Takes `self` by value and shrinks in place, so this is `O(1)` after the
    /// scan rather than a copy.  The shrink is spelled `resize`, not
    /// `Vec::truncate`, because the Aeneas Lean backend models `resize` and not
    /// `truncate`; for `n <= len` the two agree (std: "If `new_len` is less than
    /// `len`, the `Vec` is simply truncated"), and the fill value is never used.
    #[must_use]
    pub fn trim(mut self) -> UnivariatePoly {
        let mut n: usize = self.0.len();
        while n > 0 {
            if !self.0[n - 1].is_zero() {
                break;
            }
            n -= 1;
        }
        self.0.resize(n, Ext4::ZERO);
        self
    }
}

// ------------------------------------------------------------------
// Evaluation.
// ------------------------------------------------------------------

impl UnivariatePoly {
    // @genesis 7ca92f9 2026-07-31 — univariate::UnivariatePoly::eval
    /// Evaluate at `x` by Horner's method.  Mirrors `CPolynomial.Raw.eval`.
    pub fn eval(&self, x: Ext4) -> Ext4 {
        let mut acc: Ext4 = Ext4::ZERO;
        let mut i: usize = self.0.len();
        while i > 0 {
            i -= 1;
            acc = acc * x + self.0[i];
        }
        acc
    }
}

// ------------------------------------------------------------------
// Algebraic operations.
// ------------------------------------------------------------------

impl UnivariatePoly {
    // @genesis 80b5733 2026-08-03 — univariate::UnivariatePoly::add_untrimmed
    /// Zero-padded pointwise addition, *without* trimming.  Mirrors
    /// `CPolynomial.Raw.addRaw`.
    ///
    /// Exposed because it is the untrimmed half of [`Add`], and because
    /// `CPolynomial.Raw` names it too: the result has
    /// `max(self.len(), rhs.len())` coefficients even if the top ones cancel.
    #[must_use]
    pub fn add_untrimmed(&self, rhs: &UnivariatePoly) -> UnivariatePoly {
        let np: usize = self.0.len();
        let nq: usize = rhs.0.len();
        let n: usize = if np >= nq { np } else { nq };
        let mut out: Vec<Ext4> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let a: Ext4 = if i < np { self.0[i] } else { Ext4::ZERO };
            let b: Ext4 = if i < nq { rhs.0[i] } else { Ext4::ZERO };
            out.push(a + b);
            i += 1;
        }
        UnivariatePoly(out)
    }
}

impl Add<&UnivariatePoly> for &UnivariatePoly {
    type Output = UnivariatePoly;

    // @genesis 80b5733 2026-08-03 — univariate::<&UnivariatePoly as Add<&UnivariatePoly>>::add
    /// Trimmed pointwise addition.  Mirrors `CPolynomial.Raw.add`.
    fn add(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        self.add_untrimmed(rhs).trim()
    }
}

impl Neg for &UnivariatePoly {
    type Output = UnivariatePoly;

    // @genesis 80b5733 2026-08-03 — univariate::<&UnivariatePoly as Neg>::neg
    /// Coefficient-wise negation.  Mirrors `CPolynomial.Raw.neg`.
    ///
    /// No trim is needed: `-0 = 0`, so negation cannot create a trailing zero
    /// that was not already there.
    fn neg(self) -> UnivariatePoly {
        let n: usize = self.0.len();
        let mut out: Vec<Ext4> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(-self.0[i]);
            i += 1;
        }
        UnivariatePoly(out)
    }
}

impl Sub<&UnivariatePoly> for &UnivariatePoly {
    type Output = UnivariatePoly;

    // @genesis 80b5733 2026-08-03 — univariate::<&UnivariatePoly as Sub<&UnivariatePoly>>::sub
    /// Mirrors `CPolynomial.Raw.sub`, which is `p.add q.neg`.
    fn sub(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        let negated: UnivariatePoly = -rhs;
        self + &negated
    }
}

impl Mul<Ext4> for &UnivariatePoly {
    type Output = UnivariatePoly;

    // @genesis 80b5733 2026-08-03 — univariate::<&UnivariatePoly as Mul<Ext4>>::mul
    /// Scale every coefficient.  Mirrors `CPolynomial.Raw.smul`.
    fn mul(self, scalar: Ext4) -> UnivariatePoly {
        let n: usize = self.0.len();
        let mut out: Vec<Ext4> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            out.push(scalar * self.0[i]);
            i += 1;
        }
        UnivariatePoly(out)
    }
}

impl Mul<&UnivariatePoly> for &UnivariatePoly {
    type Output = UnivariatePoly;

    // @genesis 80b5733 2026-08-03 — univariate::<&UnivariatePoly as Mul<&UnivariatePoly>>::mul
    /// Trimmed schoolbook multiplication.  Mirrors `CPolynomial.Raw.mul`, i.e.
    /// `mulRaw |> trim`.
    ///
    /// The accumulator is sized `np + nq - 1`; in the extracted model that
    /// `np + nq` is a *checked* `usize` addition, so the Lean spec carries the
    /// hypothesis `np + nq <= usize::MAX`.  It is unreachable for real `Vec`s,
    /// whose capacity is bounded by `isize::MAX` *bytes*, but the model does not
    /// know that.
    fn mul(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        let np: usize = self.0.len();
        let nq: usize = rhs.0.len();
        if np == 0 || nq == 0 {
            return UnivariatePoly::zero();
        }
        let mut out: Vec<Ext4> = vec![Ext4::ZERO; np + nq - 1];
        // Convolution: out[i + j] += self[i] * rhs[j].
        let mut i: usize = 0;
        while i < np {
            let mut j: usize = 0;
            while j < nq {
                let prod: Ext4 = self.0[i] * rhs.0[j];
                let k: usize = i + j;
                // Not `out[k] += prod`: a compound assignment reads the slot
                // through `IndexMut`, and the extracted model of that is harder
                // to reason about than the read-modify-write below.
                #[allow(clippy::assign_op_pattern)]
                {
                    out[k] = out[k] + prod;
                }
                j += 1;
            }
            i += 1;
        }
        UnivariatePoly(out).trim()
    }
}
