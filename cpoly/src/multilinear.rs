//! Computable **multilinear** polynomials over the same concrete field as the
//! univariate layer — the degree-4 extension [`Ext4`] of the Hachi prime field
//! (see [`crate::field`]) — written to be translated to Lean by Aeneas/Charon and
//! proved equivalent to `CompPoly.CMlPolynomial` and
//! `CompPoly.CMlPolynomialEval` (see Verified-zkEVM/CompPoly,
//! `CompPoly/Multilinear/Basic.lean`).
//!
//! ## Two readings of one table, and two types
//!
//! A multilinear polynomial in `vars` variables is `2^vars` field elements. The
//! index is read **little-endian**: bit `j` of the index belongs to variable `j`.
//! There are two *different* things that table can mean, and this module gives
//! each of them its own type:
//!
//! * [`Coeffs`] — the **monomial** reading. Entry `i` is the coefficient of
//!   `∏_{j : bit j of i is set} X_j`. So for `vars = 2`, `[c0, c1, c2, c3]` is
//!   `c0 + c1*X0 + c2*X1 + c3*X0*X1`. Mirrors `CompPoly.CMlPolynomial R vars`.
//! * [`Evals`] — the **Lagrange** (Boolean-hypercube) reading. Entry `i` is the
//!   value of the polynomial at the point whose `j`-th coordinate is bit `j` of
//!   `i`. Mirrors `CompPoly.CMlPolynomialEval R vars`.
//!
//! These are the same `2^vars` words in memory, and the previous version of this
//! crate used `Vec<Ext4>` for both — which meant nothing stopped a caller
//! evaluating a hypercube table as if it were a coefficient table. That is now a
//! type error. The two are related by the zeta and Möbius transforms,
//! [`Coeffs::to_evals`] and [`Evals::to_coeffs`], which are the only way across.
//!
//! Both wrappers cost the Lean side nothing: Aeneas extracts a single-field
//! tuple struct as a `@[reducible]` abbreviation of its content, so
//! `cpoly.multilinear.Coeffs` *is* `alloc.vec.Vec cpoly.field.Ext4` to the proofs.
//!
//! ```
//! use cpoly::{Ext4, Fp, MultilinearCoeffs};
//!
//! // 1 + X0*X1, in two variables
//! let p = MultilinearCoeffs::from_coeffs(
//!     vec![Ext4::ONE, Ext4::ZERO, Ext4::ZERO, Ext4::ONE], 2);
//! let point = [Ext4::from(3u64), Ext4::from(5u64)];
//! assert_eq!(p.eval(&point), Ext4::from(16u64));   // 1 + 3*5
//! assert_eq!(p.eval_horner(&point), p.eval(&point)); // the fast path agrees
//! let _ = Fp::ONE;
//! ```
//!
//! ## Arity
//!
//! `vars` is passed explicitly wherever it is needed, mirroring the `n` of the
//! `CompPoly` definitions; it is not stored in the types, so
//! `p.len() == table_len(vars)` is a caller obligation rather than an invariant
//! of [`Coeffs`].  Making it a field instead is the first item under "what is
//! still missing" in the README.
//!
//! ## Field arithmetic
//!
//! All coefficient arithmetic goes through [`Ext4`]'s operator impls, which in
//! turn use [`crate::field::Fp`]'s on reduced representatives in `[0, P)`. Since
//! `P < 2^32`, no intermediate `u64` overflows, which is what keeps Aeneas's
//! checked-arithmetic `Result` trivially `ok` (see the [`crate::field`] docs).
//!
//! ## Style notes (for clean Aeneas output)
//!
//! Explicit index-based `while` loops, no iterator adaptors, fresh `Vec`s built
//! with `push`, and bit tests written with `/` and `%` rather than `>>` / `&` so
//! that the extracted model stays in plain `Usize` arithmetic.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, Index};

use crate::field::Ext4;

// ------------------------------------------------------------------
// Sizes.
// ------------------------------------------------------------------

/// The number of table entries for `vars` variables, i.e. `2^vars`.
///
/// # Panics
///
/// If `vars >= usize::BITS`, i.e. if `2^vars` does not fit in a `usize`. That is
/// the shift's own contract, and it is exactly the condition the Lean spec
/// carries (`2^vars ≤ usize::MAX`) — the previous version of this function built
/// `2^vars` by checked doubling, which fails on the same inputs.
pub fn table_len(vars: usize) -> usize {
    1usize << vars
}

// ------------------------------------------------------------------
// Inner product, and the two bases.
// ------------------------------------------------------------------

/// `∑_i a[i] * b[i]`, accumulated left to right from zero.
///
/// Mirrors `CompPoly.Vector.dotProduct`, which is
/// `a.zipWith (· * ·) b |>.foldl (· + ·) 0`.
///
/// # Panics
///
/// If `b` is shorter than `a`: the loop runs over `a.len()`.
pub fn dot(a: &[Ext4], b: &[Ext4]) -> Ext4 {
    let n: usize = a.len();
    let mut acc: Ext4 = Ext4::ZERO;
    let mut i: usize = 0;
    while i < n {
        acc += a[i] * b[i];
        i += 1;
    }
    acc
}

/// The monomial basis at `point`: entry `i` is `∏_{j : bit j of i is set}
/// point[j]`.  Mirrors `CMlPolynomial.monomialBasis`.
///
/// This is the vector [`Coeffs::eval`] dots a coefficient table against. The inner
/// loop walks the bits of `i` from least to most significant, keeping
/// `m = i / 2^j` so that `m % 2` is bit `j`.
pub fn monomial_basis(point: &[Ext4]) -> Vec<Ext4> {
    let vars: usize = point.len();
    let sz: usize = table_len(vars);
    let mut basis: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        let mut acc: Ext4 = Ext4::ONE;
        let mut m: usize = i;
        let mut j: usize = 0;
        while j < vars {
            if m % 2 == 1 {
                acc *= point[j];
            }
            m /= 2;
            j += 1;
        }
        basis.push(acc);
        i += 1;
    }
    basis
}

/// The Lagrange basis at `point`: entry `i` is
/// `∏_j (if bit j of i is set then point[j] else 1 - point[j])`.
/// Mirrors `CMlPolynomialEval.lagrangeBasis`.
///
/// The result is returned as [`Evals`] because that is what it is: the
/// hypercube table of the equality kernel `eq~(point, ·)`, which is why
/// [`eq_tilde`] is just this followed by [`Evals::eval`].
pub fn lagrange_basis(point: &[Ext4]) -> Evals {
    let vars: usize = point.len();
    let sz: usize = table_len(vars);
    let mut basis: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < sz {
        let mut acc: Ext4 = Ext4::ONE;
        let mut m: usize = i;
        let mut j: usize = 0;
        while j < vars {
            if m % 2 == 1 {
                acc *= point[j];
            } else {
                acc *= Ext4::ONE - point[j];
            }
            m /= 2;
            j += 1;
        }
        basis.push(acc);
        i += 1;
    }
    Evals(basis)
}

/// Pointwise sum of two equal-length tables.
///
/// Shared by the [`Coeffs`] and [`Evals`] [`Add`] impls: adding entry by entry
/// does not care which basis the index is read in, so there is one loop here
/// rather than one in each.  Mirrors `CMlPolynomial.add` and
/// `CMlPolynomialEval.add`, which are both `Vector.zipWith (· + ·)`.
///
/// # Panics
///
/// If `b` is shorter than `a`: the loop runs over `a.len()`.
pub fn add_pointwise(a: &[Ext4], b: &[Ext4]) -> Vec<Ext4> {
    let n: usize = a.len();
    let mut out: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        out.push(a[i] + b[i]);
        i += 1;
    }
    out
}

/// The multilinear equality kernel `eq~(w, x)`.  Mirrors
/// `CMlPolynomialEval.eqTilde`.
pub fn eq_tilde(w: &[Ext4], x: &[Ext4]) -> Ext4 {
    lagrange_basis(w).eval(x)
}

// ------------------------------------------------------------------
// One transform / evaluation layer each.  Free functions, because each is a
// step on a raw table rather than an operation on a whole polynomial.
// ------------------------------------------------------------------

/// One Horner layer on a *coefficient* table: eliminate the least-significant
/// variable at `x0`, halving the length.
///
/// `out[j] = coeffs[2j] + x0 * coeffs[2j+1]`, mirroring the coefficient-form
/// Horner step behind `CMlPolynomial.evalHorner`.
pub fn eval_horner_layer(coeffs: &[Ext4], x0: Ext4) -> Vec<Ext4> {
    let half: usize = coeffs.len() / 2;
    let mut out: Vec<Ext4> = Vec::new();
    let mut j: usize = 0;
    while j < half {
        let lo: Ext4 = coeffs[2 * j];
        let hi: Ext4 = coeffs[2 * j + 1];
        out.push(lo + x0 * hi);
        j += 1;
    }
    out
}

/// One multilinear-extension layer on an *evaluation* table: fold the
/// least-significant variable at `x0`, halving the length.
///
/// `out[j] = (1 - x0) * values[2j] + x0 * values[2j+1]`.
/// Mirrors `CMlPolynomialEval.evalMleLayer`.
pub fn eval_mle_layer(values: &[Ext4], x0: Ext4) -> Vec<Ext4> {
    let half: usize = values.len() / 2;
    let one_minus: Ext4 = Ext4::ONE - x0;
    let mut out: Vec<Ext4> = Vec::new();
    let mut j: usize = 0;
    while j < half {
        let lo: Ext4 = values[2 * j];
        let hi: Ext4 = values[2 * j + 1];
        out.push(one_minus * lo + x0 * hi);
        j += 1;
    }
    out
}

/// One level of the zeta transform (coefficients → hypercube evaluations):
/// `out[i] = v[i] + v[i - 2^j]` when bit `j` of `i` is set, else `v[i]`.
///
/// Mirrors `CMlPolynomial.monoToLagrangeLevel`.  The bit test is
/// `(i / 2^j) % 2 == 1`, and it guarantees `i >= 2^j`, which is what makes the
/// subtraction `i - stride` succeed.
pub fn mono_to_lagrange_level(v: &[Ext4], j: usize) -> Vec<Ext4> {
    let n: usize = v.len();
    let stride: usize = table_len(j);
    let mut out: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if (i / stride) % 2 == 1 {
            out.push(v[i] + v[i - stride]);
        } else {
            out.push(v[i]);
        }
        i += 1;
    }
    out
}

/// One level of the Möbius / inverse zeta transform (hypercube evaluations →
/// coefficients): `out[i] = v[i] - v[i - 2^j]` when bit `j` of `i` is set, else
/// `v[i]`.
///
/// Mirrors `CMlPolynomial.lagrangeToMonoLevel`, and is the exact inverse of
/// [`mono_to_lagrange_level`] at the same level.
pub fn lagrange_to_mono_level(v: &[Ext4], j: usize) -> Vec<Ext4> {
    let n: usize = v.len();
    let stride: usize = table_len(j);
    let mut out: Vec<Ext4> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if (i / stride) % 2 == 1 {
            out.push(v[i] - v[i - stride]);
        } else {
            out.push(v[i]);
        }
        i += 1;
    }
    out
}

// ------------------------------------------------------------------
// The monomial reading.
// ------------------------------------------------------------------

/// A multilinear polynomial in coefficient (monomial) form: `2^vars` entries,
/// entry `i` the coefficient of the monomial whose variable set is the bits of
/// `i`.
///
/// Mirrors `CompPoly.CMlPolynomial Hachi.Ext4 vars`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Coeffs(Vec<Ext4>);

impl Coeffs {
    /// The zero polynomial in `vars` variables.  Mirrors `CMlPolynomial.zero`.
    pub fn zeros(vars: usize) -> Coeffs {
        Coeffs(vec![Ext4::ZERO; table_len(vars)])
    }

    /// Conform a coefficient list to `vars` variables, zero-padding it or
    /// dropping the tail.  Mirrors `CMlPolynomial.ofArray`.
    ///
    /// One `Vec::resize` does both halves of that: it pads with `ZERO` when the
    /// list is short and truncates when it is long.
    pub fn from_coeffs(mut coeffs: Vec<Ext4>, vars: usize) -> Coeffs {
        coeffs.resize(table_len(vars), Ext4::ZERO);
        Coeffs(coeffs)
    }

    /// The coefficient table.
    pub fn coeffs(&self) -> &[Ext4] {
        &self.0
    }

    /// Give up the coefficient table without copying it.
    pub fn into_coeffs(self) -> Vec<Ext4> {
        self.0
    }

    /// The number of entries, `2^vars`.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the table empty?  (It is not, for any `vars`: `2^0 = 1`.)
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Evaluate at `point` by dotting against the monomial basis: `O(vars·2^vars)`
    /// field operations.  Mirrors `CMlPolynomial.eval`.
    ///
    /// [`Coeffs::eval_horner`] computes the same thing in `O(2^vars)`.
    pub fn eval(&self, point: &[Ext4]) -> Ext4 {
        let basis: Vec<Ext4> = monomial_basis(point);
        dot(&self.0, &basis)
    }

    /// Evaluate at `point` by repeated Horner layers: `O(2^vars)` field
    /// operations, against `O(vars·2^vars)` to build the basis.  Mirrors
    /// `CMlPolynomial.evalHorner`.
    ///
    /// Variables are eliminated least-significant first, so layer `j` uses
    /// `point[j]`.
    pub fn eval_horner(&self, point: &[Ext4]) -> Ext4 {
        let vars: usize = point.len();
        let mut cur: Vec<Ext4> = self.0.clone();
        let mut j: usize = 0;
        while j < vars {
            cur = eval_horner_layer(&cur, point[j]);
            j += 1;
        }
        cur[0]
    }

    /// The zeta transform: reinterpret this coefficient table as the hypercube
    /// table of the same polynomial, by applying levels `0, 1, …, vars-1` in
    /// that order.  Mirrors `CMlPolynomial.monoToLagrange`.
    ///
    /// Consumes `self`, so no defensive copy of the table is needed.
    pub fn to_evals(self, vars: usize) -> Evals {
        let mut cur: Vec<Ext4> = self.0;
        let mut j: usize = 0;
        while j < vars {
            cur = mono_to_lagrange_level(&cur, j);
            j += 1;
        }
        Evals(cur)
    }
}

impl Index<usize> for Coeffs {
    type Output = Ext4;

    /// # Panics
    ///
    /// If `i >= self.len()`.
    fn index(&self, i: usize) -> &Ext4 {
        &self.0[i]
    }
}

impl Add<&Coeffs> for &Coeffs {
    type Output = Coeffs;

    /// Coefficient-wise.  Mirrors `CMlPolynomial.add`
    /// (`Vector.zipWith (· + ·)`).
    ///
    /// # Panics
    ///
    /// If `rhs` is shorter than `self`. Unlike the univariate
    /// [`crate::univariate::Poly`], there is no zero-padding here: two
    /// multilinear polynomials are only added when they have the same arity.
    fn add(self, rhs: &Coeffs) -> Coeffs {
        Coeffs(add_pointwise(&self.0, &rhs.0))
    }
}

// ------------------------------------------------------------------
// The Lagrange reading.
// ------------------------------------------------------------------

/// A multilinear polynomial in evaluation form: `2^vars` values on the Boolean
/// hypercube, entry `i` the value at the point whose `j`-th coordinate is bit `j`
/// of `i`.
///
/// Mirrors `CompPoly.CMlPolynomialEval Hachi.Ext4 vars`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Evals(Vec<Ext4>);

impl Evals {
    /// Take a table of hypercube values as it stands.
    pub fn from_values(values: Vec<Ext4>) -> Evals {
        Evals(values)
    }

    /// The hypercube values.
    pub fn values(&self) -> &[Ext4] {
        &self.0
    }

    /// Give up the value table without copying it.
    pub fn into_values(self) -> Vec<Ext4> {
        self.0
    }

    /// The number of entries, `2^vars`.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the table empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Evaluate the multilinear extension at `point` by dotting against the
    /// Lagrange basis: `O(vars·2^vars)` field operations.  Mirrors
    /// `CMlPolynomialEval.eval`.
    ///
    /// [`Evals::eval_mle`] computes the same thing in `O(2^vars)`.
    pub fn eval(&self, point: &[Ext4]) -> Ext4 {
        let basis: Evals = lagrange_basis(point);
        dot(&self.0, &basis.0)
    }

    /// Evaluate the multilinear extension at `point` by repeated folding layers:
    /// `O(2^vars)` field operations.  Mirrors `CMlPolynomialEval.evalMle`.
    pub fn eval_mle(&self, point: &[Ext4]) -> Ext4 {
        let vars: usize = point.len();
        let mut cur: Vec<Ext4> = self.0.clone();
        let mut j: usize = 0;
        while j < vars {
            cur = eval_mle_layer(&cur, point[j]);
            j += 1;
        }
        cur[0]
    }

    /// The Möbius transform: recover the coefficient table from the hypercube
    /// table, by applying levels `vars-1, vars-2, …, 0` in that order.  Mirrors
    /// `CMlPolynomial.lagrangeToMono`.
    ///
    /// Consumes `self`; the exact inverse of [`Coeffs::to_evals`].
    pub fn to_coeffs(self, vars: usize) -> Coeffs {
        let mut cur: Vec<Ext4> = self.0;
        let mut j: usize = vars;
        while j > 0 {
            j -= 1;
            cur = lagrange_to_mono_level(&cur, j);
        }
        Coeffs(cur)
    }
}

impl Index<usize> for Evals {
    type Output = Ext4;

    /// # Panics
    ///
    /// If `i >= self.len()`.
    fn index(&self, i: usize) -> &Ext4 {
        &self.0[i]
    }
}

impl Add<&Evals> for &Evals {
    type Output = Evals;

    /// Pointwise on the hypercube.  Mirrors `CMlPolynomialEval.add`.
    ///
    /// # Panics
    ///
    /// If `rhs` is shorter than `self`.
    fn add(self, rhs: &Evals) -> Evals {
        Evals(add_pointwise(&self.0, &rhs.0))
    }
}
