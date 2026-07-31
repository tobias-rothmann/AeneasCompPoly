//! Computable polynomials over a concrete degree-4 *extension* field, written to
//! be translated to Lean by Aeneas/Charon and proved equivalent to the reference
//! development in Verified-zkEVM/CompPoly.
//!
//! # Layout
//!
//! One module per layer, and the Lean side mirrors it: a Rust path
//! `cpoly::<module>::<item>` becomes the extracted Lean name
//! `cpoly.<module>.<item>` (see `lean/Generated.lean`).
//!
//! * [`field`] — the coefficient field.  [`Fp`] is the base field `F_P` with
//!   `P = 2^32 - 99` (the "Hachi" prime, `CompPoly/Fields/Hachi.lean`) and
//!   [`Ext4`] its quartic extension `F_P[Y] / (Y^4 - 2)`
//!   (`CompPoly/Fields/Hachi/Ext4.lean`), mirroring
//!   `CompPoly.Extension.Ext Hachi.ext4Params`.  Read its header for the
//!   no-overflow argument the whole crate rests on.
//! * [`univariate`] — [`UnivariatePoly`], dense little-endian coefficient
//!   vectors, mirroring `CompPoly.CPolynomial.Raw` at `R = Hachi.Ext4`.
//! * [`multilinear`] — [`MultilinearCoeffs`] and [`MultilinearEvals`], the
//!   monomial and the Lagrange reading of a `2^vars`-entry table, mirroring
//!   `CompPoly.CMlPolynomial` and `CompPoly.CMlPolynomialEval`.
//!
//! The dependency order is `field` ← `univariate`, `field` ← `multilinear`; the
//! two polynomial modules are independent of each other.
//!
//! # Types, not aliases
//!
//! Every layer wraps its representation in a newtype rather than passing
//! `Vec<Ext4>` around.  That is not decoration: [`MultilinearCoeffs`] and
//! [`MultilinearEvals`] are *the same bytes* under two different readings, and
//! before they were separate types nothing stopped a caller evaluating one as if
//! it were the other.  Likewise [`Fp`] hides its `u64`, so the reducedness
//! invariant the Lean proofs call `Red` cannot be violated through the public
//! API — it holds of every value of the type.
//!
//! All of this is free on the Lean side.  Aeneas extracts a single-field tuple
//! struct as a `@[reducible]` abbreviation of its content, so
//! `cpoly.field.Fp` *is* `Std.U64` and `cpoly.univariate.Poly` *is*
//! `alloc.vec.Vec cpoly.field.Ext4` as far as the proofs are concerned, while
//! `lean/Generated.lean` gains the more informative names.
//!
//! # Operators
//!
//! Field and polynomial arithmetic is the standard [`core::ops`] traits, so the
//! code reads `a + b * c` rather than `fadd(a, fmul(b, c))`.  Charon resolves
//! each operator to its concrete impl and Aeneas extracts that impl as an
//! ordinary definition, whose body is exactly what the corresponding free
//! function's was — the operators cost the proofs a rename and nothing else.
//!
//! # Style notes (for clean Aeneas output)
//!
//! Two habits here are for the extraction's benefit rather than the reader's,
//! and both are load-bearing:
//!
//! * **Explicit index-based `while` loops, and no iterator adaptors.**  `.map`,
//!   `.zip`, `.fold` and `.collect` have no model in the Aeneas Lean backend —
//!   using them puts unknown definitions in the extracted file.  `for i in 0..n`
//!   *is* modelled, but it turns every loop's state from a `usize` counter into a
//!   `Range<usize>` iterator, and `lean/Generated.lean` is an artefact people
//!   read here.  The counter loops stay.
//! * **Bit tests written with `/` and `%`** rather than `>>` and `&`, so the
//!   extracted model stays in plain `Usize` arithmetic that `scalar_tac` and
//!   `omega` can see through.
//!
//! Two more, which are about keeping `lean/Generated.lean` free of `axiom`s: the
//! extension arithmetic is fully unrolled, so no operation on [`Ext4`] needs a
//! loop; and `Vec::is_empty`, `Vec::truncate` and `#[derive(Default)]` on a
//! `Vec`-holding struct are avoided, because none of the three has a model.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![warn(missing_debug_implementations)]

extern crate alloc;

pub mod field;

pub mod multilinear;

pub mod univariate;

pub use field::{Ext4, Fp};
pub use multilinear::{Coeffs as MultilinearCoeffs, Evals as MultilinearEvals};
pub use univariate::Poly as UnivariatePoly;
