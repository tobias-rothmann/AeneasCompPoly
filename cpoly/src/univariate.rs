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
//! Coefficient arithmetic goes through [`Ext4`]'s operator impls everywhere
//! except the inner loop of the polynomial product, which works on raw base-field
//! words in `u128` accumulators and reduces once per output coefficient rather
//! than once per operation — see the [`Mul`] impl.  Since the base modulus `P` is
//! below `2^32`, no intermediate `u64` overflows, which is what keeps Aeneas's
//! checked-arithmetic `Result` trivially `ok` (see the [`crate::field`] docs);
//! the delayed-reduction accumulator carries its own bound, stated on
//! [`conv_delayed`].  The one operation that *can* fail is [`Mul`], whose
//! accumulator length is a checked `usize` sum — see its docstring.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, Index, Mul, Neg, Sub};

use crate::field::{Ext4, Fp, P};

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
    /// The zero polynomial: no coefficients at all.
    pub fn zero() -> UnivariatePoly {
        UnivariatePoly(Vec::new())
    }

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

    /// The variable `X`.  Mirrors `CPolynomial.Raw.X`.
    #[allow(clippy::vec_init_then_push)] // see `UnivariatePoly::constant`
    pub fn x() -> UnivariatePoly {
        let mut coeffs: Vec<Ext4> = Vec::new();
        coeffs.push(Ext4::ZERO);
        coeffs.push(Ext4::ONE);
        UnivariatePoly(coeffs)
    }

    /// Take a coefficient vector as it stands, little-endian in `X`.
    pub fn from_coeffs(coeffs: Vec<Ext4>) -> UnivariatePoly {
        UnivariatePoly(coeffs)
    }

    /// The coefficients, little-endian in `X`.
    pub fn coeffs(&self) -> &[Ext4] {
        &self.0
    }

    /// Give up the coefficient vector without copying it.
    pub fn into_coeffs(self) -> Vec<Ext4> {
        self.0
    }

    /// How many coefficients are stored — one more than the degree, when the
    /// polynomial is trimmed and nonzero.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Are there no coefficients?
    ///
    /// Spelled `len() == 0` rather than `Vec::is_empty`, which the Aeneas Lean
    /// backend has no model for: calling it would put an `axiom` into
    /// `lean/Generated.lean`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

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
    fn default() -> UnivariatePoly {
        UnivariatePoly::zero()
    }
}

impl From<Vec<Ext4>> for UnivariatePoly {
    fn from(coeffs: Vec<Ext4>) -> UnivariatePoly {
        UnivariatePoly::from_coeffs(coeffs)
    }
}

impl Index<usize> for UnivariatePoly {
    type Output = Ext4;

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
        let mut out: Vec<Ext4> = Vec::with_capacity(n);
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

    /// Trimmed pointwise addition.  Mirrors `CPolynomial.Raw.add`.
    fn add(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        self.add_untrimmed(rhs).trim()
    }
}

impl Neg for &UnivariatePoly {
    type Output = UnivariatePoly;

    /// Coefficient-wise negation.  Mirrors `CPolynomial.Raw.neg`.
    ///
    /// No trim is needed: `-0 = 0`, so negation cannot create a trailing zero
    /// that was not already there.
    fn neg(self) -> UnivariatePoly {
        let n: usize = self.0.len();
        let mut out: Vec<Ext4> = Vec::with_capacity(n);
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

    /// Mirrors `CPolynomial.Raw.sub`, which is `p.add q.neg`.
    fn sub(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        let negated: UnivariatePoly = -rhs;
        self + &negated
    }
}

impl Mul<Ext4> for &UnivariatePoly {
    type Output = UnivariatePoly;

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

// ------------------------------------------------------------------
// Multiplication: Karatsuba over a delayed-reduction base case.
//
// Both layers compute the same convolution the reference does — coefficient
// `k` of the product is `Σ_{i+j=k} p[i] * q[j]` — so neither is a change of
// result, only of the order the sum is accumulated in and of how often the
// intermediate is put back into `[0, P)`.
// ------------------------------------------------------------------

/// `2^64 mod P`, the only fact about the modulus [`reduce_u128`] needs.
///
/// `P = 2^32 - 99`, so `2^32 ≡ 99 (mod P)`, hence `2^64 ≡ 99^2 = 9801 (mod P)`.
const R64: u64 = 9801;

/// The slice length at or below which [`mul_karatsuba`] stops splitting and
/// runs [`conv_delayed`] directly.
///
/// One Karatsuba level over operands of length `n` trades a quarter of the
/// base-case pair work — `(n/2)^2` pairs, each 16 word multiplies and 16 `u128`
/// accumulations — for two half-length [`Ext4`] additions, two full-length
/// subtractions and two full-length shifted additions (about `5n` [`Ext4`]
/// add/sub, each carrying four `% P`), plus a handful of allocations.  Equating
/// the two puts the crossover near `n = 20` on this machine's cost model, with
/// the allocation term the least certain. A sweep puts the measured optimum at
/// `16`: it reduces raw base-case work by a further quarter relative to `32`,
/// while still keeping the seven `u128` lanes as the loop's whole state. At the
/// benchmark sizes, `n = 64` takes two splits and `n = 256` takes four.
const KARATSUBA_CUTOFF: usize = 16;

/// The class of `x` in the base field.
///
/// Not spelled `x % P`: `u128` division by a constant is *not* strength-reduced
/// by LLVM on this target — it lowers to a call to the `__umodti3` software
/// division routine, which would cost more than the whole inner loop it is
/// reducing.  Splitting `x` at the word boundary and folding the high half with
/// [`R64`] keeps the entire reduction in `u64` multiply-high sequences.
///
/// No `u64` here can overflow: `hi % P < P < 2^32`, so `(hi % P) * R64 < 2^32 *
/// 2^14 = 2^46`; and the final sum of two reduced words is below `2P < 2^33`.
// The two `as` casts are the halves of a `u128`, which are `u64` by construction.
#[allow(clippy::cast_possible_truncation)]
fn reduce_u128(x: u128) -> Fp {
    let lo: u64 = x as u64;
    let hi: u64 = (x >> 64) as u64;
    let folded: u64 = ((hi % P) * R64) % P;
    Fp::new((lo % P) + folded)
}

/// Schoolbook convolution of two coefficient slices, with **one** modular
/// reduction per output coefficient instead of roughly 35 per coefficient
/// *pair*.
///
/// The loop is output-indexed: for each `k` it accumulates the seven unreduced
/// extension products
/// `t_l = Σ_{i+j=k} Σ_{u+v=l} p[i].c_u * q[j].c_v` (`l = 0..6`)
/// in `u128` lanes, then folds `Y^4 = W = 2` exactly as `Ext4`'s `Mul` does
/// (`c_l = t_l + 2 t_{l+4}` for `l < 3`, `c_3 = t_3`) and reduces four times.
/// The result is `mulRaw p q`, untrimmed, of length `np + nq - 1`.
///
/// **Overflow.**  Each `p[i].c_u * q[j].c_v` is a product of two words below
/// `P < 2^32`, hence at most `(P-1)^2 < 2^64` — the same bound `field::Fp`'s
/// `Mul` already relies on, which is why the *products* still fit `u64` and only
/// the *sums* need `u128`.  A lane takes at most `4 * min(np, nq)` such products
/// (`t_3` is the widest), and the fold at most `7 * min(np, nq)` (`c_0 = t_0 + 2
/// t_4`), so every accumulator is below `7 * min(np, nq) * (P-1)^2`: under
/// `2^128` for any slice length up to `2^61`, the bound the Lean spec states,
/// and under `2^76` at the bench sizes.  `u64` could not hold even *two* of
/// these products — the slack under
/// `2^64` is only about `200 * 2^32` — which is why the lanes have to be `u128`
/// and cannot be wider `u64` accumulators.
// The `as u128` widenings are exact; `clippy::cast_lossless` wants
// `u128::from`, but `as` is what the extraction models (a plain scalar cast)
// and a `From` impl on a primitive is not in the supported set.
#[allow(clippy::cast_lossless)]
fn conv_delayed(lhs: &[Ext4], rhs: &[Ext4]) -> Vec<Ext4> {
    let np: usize = lhs.len();
    let nq: usize = rhs.len();
    if np == 0 || nq == 0 {
        return Vec::new();
    }
    // Guarded by the early return above; `np_last + nq` is `np + nq - 1`
    // without a second checked subtraction.
    let np_last: usize = np - 1;
    let nout: usize = np_last + nq;
    let mut out: Vec<Ext4> = Vec::with_capacity(nout);
    let mut k: usize = 0;
    while k < nout {
        // The pairs contributing to output `k` are `(i, k - i)` for
        // `max(0, k + 1 - nq) <= i <= min(k, np - 1)`.  Both bounds are
        // `usize` subtractions and both sit under an explicit guard.
        let lo: usize = if k >= nq { (k - nq) + 1 } else { 0 };
        let hi: usize = if k < np { k } else { np_last };
        let mut t0: u128 = 0;
        let mut t1: u128 = 0;
        let mut t2: u128 = 0;
        let mut t3: u128 = 0;
        let mut t4: u128 = 0;
        let mut t5: u128 = 0;
        let mut t6: u128 = 0;
        let mut i: usize = lo;
        while i <= hi {
            if i <= k {
                let j: usize = k - i;
                let pi: Ext4 = lhs[i];
                let qj: Ext4 = rhs[j];
                let x0: u64 = pi.c0.to_u64();
                let x1: u64 = pi.c1.to_u64();
                let x2: u64 = pi.c2.to_u64();
                let x3: u64 = pi.c3.to_u64();
                let y0: u64 = qj.c0.to_u64();
                let y1: u64 = qj.c1.to_u64();
                let y2: u64 = qj.c2.to_u64();
                let y3: u64 = qj.c3.to_u64();
                t0 += (x0 * y0) as u128;
                t1 += (x0 * y1) as u128;
                t1 += (x1 * y0) as u128;
                t2 += (x0 * y2) as u128;
                t2 += (x1 * y1) as u128;
                t2 += (x2 * y0) as u128;
                t3 += (x0 * y3) as u128;
                t3 += (x1 * y2) as u128;
                t3 += (x2 * y1) as u128;
                t3 += (x3 * y0) as u128;
                t4 += (x1 * y3) as u128;
                t4 += (x2 * y2) as u128;
                t4 += (x3 * y1) as u128;
                t5 += (x2 * y3) as u128;
                t5 += (x3 * y2) as u128;
                t6 += (x3 * y3) as u128;
            }
            i += 1;
        }
        // `Y^4 = W = 2`: doubling is `t + t`, so no `u128` shift is needed.
        let c0: u128 = t0 + (t4 + t4);
        let c1: u128 = t1 + (t5 + t5);
        let c2: u128 = t2 + (t6 + t6);
        out.push(Ext4::new(
            reduce_u128(c0),
            reduce_u128(c1),
            reduce_u128(c2),
            reduce_u128(t3),
        ));
        k += 1;
    }
    out
}

/// Zero-padded pointwise sum of two coefficient slices, of length
/// `max(lhs.len(), rhs.len())`.
///
/// The same shape as [`UnivariatePoly::add_untrimmed`], on slices, for
/// [`mul_karatsuba`]'s `p0 + p1` halves.
fn add_slices(lhs: &[Ext4], rhs: &[Ext4]) -> Vec<Ext4> {
    let na: usize = lhs.len();
    let nb: usize = rhs.len();
    let nout: usize = if na >= nb { na } else { nb };
    let mut out: Vec<Ext4> = Vec::with_capacity(nout);
    let mut i: usize = 0;
    while i < nout {
        let a: Ext4 = if i < na { lhs[i] } else { Ext4::ZERO };
        let b: Ext4 = if i < nb { rhs[i] } else { Ext4::ZERO };
        out.push(a + b);
        i += 1;
    }
    out
}

/// `mulRaw lhs rhs` by Karatsuba, bottoming out in [`conv_delayed`].
///
/// Splitting at `m` gives `p = p0 + p1 X^m` and `q = q0 + q1 X^m`, and
/// `p q = z0 + (zm - z0 - z2) X^m + z2 X^{2m}` with `z0 = p0 q0`,
/// `z2 = p1 q1`, `zm = (p0 + p1)(q0 + q1)` — three half-size products where
/// the convolution would take four.  The split point is `min(np, nq) / 2`, so
/// both halves of both operands are nonempty and `min` strictly decreases down
/// the recursion; unbalanced inputs degrade to the base case rather than
/// looping.
///
/// The recombination is written as explicit counter loops over pre-sized
/// buffers: `z1` is formed in place in `zm`, and the three pieces are added
/// into one `np + nq - 1` output at offsets `0`, `m` and `2m`.
// `out[t] = out[t] + …` rather than `out[t] += …`: a compound assignment reads
// the slot through `IndexMut`, whose extracted model is harder to reason about
// than the read-modify-write (same call as `UnivariatePoly::trim`'s neighbours).
#[allow(clippy::assign_op_pattern)]
fn mul_karatsuba(lhs: &[Ext4], rhs: &[Ext4]) -> Vec<Ext4> {
    let np: usize = lhs.len();
    let nq: usize = rhs.len();
    let nmin: usize = if np <= nq { np } else { nq };
    if nmin <= KARATSUBA_CUTOFF {
        return conv_delayed(lhs, rhs);
    }
    // Clamp the split point into both operands explicitly.  The model's
    // range-slice instances *fail* out of range (where Lean's `Array.extract`
    // would clamp), so `m <= min(np, nq)` has to be established here rather
    // than inferred from `nmin / 2`.
    let half: usize = nmin / 2;
    let m: usize = if half <= nmin { half } else { nmin };

    let p0: &[Ext4] = &lhs[..m];
    let p1: &[Ext4] = &lhs[m..];
    let q0: &[Ext4] = &rhs[..m];
    let q1: &[Ext4] = &rhs[m..];

    let z0: Vec<Ext4> = mul_karatsuba(p0, q0);
    let z2: Vec<Ext4> = mul_karatsuba(p1, q1);
    let ps: Vec<Ext4> = add_slices(p0, p1);
    let qs: Vec<Ext4> = add_slices(q0, q1);
    let mut z1: Vec<Ext4> = mul_karatsuba(&ps, &qs);

    let n0: usize = z0.len();
    let n1: usize = z1.len();
    let n2: usize = z2.len();

    // z1 := zm - z0 - z2, in place.
    let mut k: usize = 0;
    while k < n1 {
        let mut v: Ext4 = z1[k];
        if k < n0 {
            v = v - z0[k];
        }
        if k < n2 {
            v = v - z2[k];
        }
        z1[k] = v;
        k += 1;
    }

    // `n2 + 2m` is `np + nq - 1`, spelled without a subtraction.
    let mut out: Vec<Ext4> = vec![Ext4::ZERO; n2 + m + m];
    let mut k0: usize = 0;
    while k0 < n0 {
        out[k0] = z0[k0];
        k0 += 1;
    }
    let mut k1: usize = 0;
    while k1 < n1 {
        let t: usize = k1 + m;
        out[t] = out[t] + z1[k1];
        k1 += 1;
    }
    let mut k2: usize = 0;
    while k2 < n2 {
        let t: usize = k2 + m + m;
        out[t] = out[t] + z2[k2];
        k2 += 1;
    }
    out
}

impl Mul<&UnivariatePoly> for &UnivariatePoly {
    type Output = UnivariatePoly;

    /// Trimmed multiplication.  Mirrors `CPolynomial.Raw.mul`, i.e.
    /// `mulRaw |> trim`.
    ///
    /// The untrimmed convolution is [`mul_karatsuba`]: Karatsuba splitting down
    /// to [`KARATSUBA_CUTOFF`], then a schoolbook base case that accumulates the
    /// extension product in `u128` lanes and reduces once per output
    /// coefficient.  Both are reorderings and re-groupings of the very sum the
    /// reference definition takes — coefficient `k` of the product is
    /// `Σ_{i+j=k} p[i] * q[j]` either way.
    ///
    /// The accumulator is sized `np + nq - 1`, spelled `np_last + nq` in the
    /// base case and `n2 + m + m` in the recombination; each is a *checked*
    /// `usize` add in the extracted model, so the Lean spec carries the
    /// hypothesis `np + nq <= usize::MAX`.  It is unreachable for real `Vec`s,
    /// whose capacity is bounded by `isize::MAX` *bytes*, but the model does not
    /// know that.
    fn mul(self, rhs: &UnivariatePoly) -> UnivariatePoly {
        let np: usize = self.0.len();
        let nq: usize = rhs.0.len();
        if np == 0 || nq == 0 {
            return UnivariatePoly::zero();
        }
        UnivariatePoly(mul_karatsuba(&self.0, &rhs.0)).trim()
    }
}
