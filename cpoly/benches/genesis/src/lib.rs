//! **Frozen.** The first translation of every `cpoly` operation, kept so that
//! the optimization loop always has a starting point it can *re-measure* rather
//! than merely remember.
//!
//! # Why a whole crate exists for this
//!
//! The fitness function of this project is criterion wall-clock time. A number
//! recorded three weeks ago on a laptop that may since have been rebooted,
//! updated, or thermally throttled is not comparable to a number recorded today,
//! and comparing them anyway is how an autonomous loop convinces itself of a
//! speedup it never achieved. So `make run-bench` does not compare against a
//! remembered number: it measures this crate and `cpoly` **back to back in the
//! same criterion session**, on the same machine, at the same temperature, with
//! the same compiler. The genesis time is re-derived every run.
//!
//! Everything is compared inside a single run for the same reason. Comparing a
//! run against the previous one's numbers was tried and removed: it inherits the
//! difference in machine conditions between two moments possibly days apart, and
//! on an ordinary desktop that dwarfs anything the code does. The harness's error
//! bar is measured within each run instead, by the `_control/*` cases.
//!
//! # Why a separate crate rather than a module inside `benches/`
//!
//! Symmetry of compilation. If the baseline lived in the bench binary's own
//! crate it would be inlinable at will, while `cpoly` — a real external crate —
//! would be inlinable only through LTO. The baseline would look artificially
//! fast and every genuine improvement would be understated or inverted. As a
//! sibling crate, `cpoly_genesis` and `cpoly` reach the bench binary through the
//! identical path: same profile, same LTO decision, same codegen units.
//!
//! # The contract
//!
//! 1. **Nothing here is ever edited.** Not to fix a lint, not to fix a typo, not
//!    to follow a rename in `cpoly`. Editing genesis silently rewrites history
//!    for every past measurement.
//! 2. **Append only.** When a CompPoly definition is translated to Rust *for the
//!    first time*, that first translation is copied here verbatim, in the same
//!    commit that adds it to `cpoly/src/`.
//! 3. **Every item carries `// @genesis <sha> <date> — <path>`**, naming the
//!    earliest commit whose `cpoly/src/<file>` contains that item's body
//!    verbatim. `make bench-check` re-derives this from git and fails if an
//!    annotation is wrong, missing, or has been edited away.
//! 4. **Genesis composes with genesis.** A function frozen today calls the
//!    *frozen* field arithmetic, not today's. So "vs genesis" is the cumulative
//!    improvement over the first translation of the whole call chain, which is
//!    what "compared against the starting Rust functions" means.
//!
//! Point 4 is the one worth stating out loud: if `Fp::mul` is later optimized,
//! every downstream genesis figure keeps using the *original* `Fp::mul`, so the
//! field-level win shows up in the univariate and multilinear rows too. That is
//! deliberate — it is the total distance travelled, not the last step.
//!
//! # Layout
//!
//! Mirrors `cpoly/src/` exactly, so a frozen item sits at the same module path
//! as its live counterpart and `cpoly/benches/genesis.py` can pair them by name.

#![no_std]
#![forbid(unsafe_code)]
// Frozen code answers to the standards of the day it was frozen, not today's.
// A lint that fires here can never be fixed (see contract point 1), so it must
// never be able to fail a build either.
#![allow(warnings, clippy::all, clippy::pedantic)]

extern crate alloc;

pub mod field;

pub mod multilinear;

pub mod univariate;

pub use field::{Ext4, Fp};
pub use multilinear::{MultilinearEvals, MultilinearPoly};
pub use univariate::UnivariatePoly;
