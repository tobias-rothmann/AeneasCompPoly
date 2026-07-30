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
//! * [`field`] — the coefficient field.  Base field `F_P` with
//!   `P = 2^32 - 99` (the "Hachi" prime, `CompPoly/Fields/Hachi.lean`) and its
//!   quartic extension `Ext4 = F_P[Y] / (Y^4 - 2)`
//!   (`CompPoly/Fields/Hachi/Ext4.lean`), mirroring
//!   `CompPoly.Extension.Ext Hachi.ext4Params`.  Read its header for the
//!   no-overflow argument the whole crate rests on.
//! * [`cpoly`] — univariate polynomials as dense little-endian coefficient
//!   vectors, mirroring `CompPoly.CPolynomial.Raw` at `R = Hachi.Ext4`.
//! * [`cmlpoly`] — multilinear polynomials as `2^n`-entry tables, in both the
//!   monomial and the Lagrange reading, mirroring `CompPoly.CMlPolynomial` and
//!   `CompPoly.CMlPolynomialEval`.
//!
//! The dependency order is `field` ← `cpoly`, `field` ← `cmlpoly`; the two
//! polynomial modules are independent of each other (`cmlpoly` reuses `cpoly`'s
//! `neg`/`smul` at the spec level only, since coefficient-wise operations do not
//! care how the index is read).
//!
//! # Style notes (for clean Aeneas output)
//!
//! Explicit index-based `while` loops, no iterators / closures / slices, fresh
//! `Vec`s built with `push`, bit tests written with `/` and `%` rather than
//! `>>` / `&` so the extracted model stays in plain `Usize` arithmetic, and the
//! extension arithmetic fully unrolled so that no operation on `Ext4` needs a
//! loop of its own.

pub mod field;

pub mod cpoly;

pub mod cmlpoly;
