//! The **candidate slot** of the bench harness: the third variant `make
//! run-bench CANDIDATE=1` measures, next to `cpoly` (the current champion) and
//! `cpoly-genesis` (the frozen first translation).
//!
//! # Why a third crate
//!
//! The optimization loop (`perf-loop`) has to answer "is this candidate faster
//! than the champion?", and the harness's design rules out every cross-run
//! answer: machine conditions between two runs dwarf what code changes do
//! (measured; see `benches/genesis/src/lib.rs`). So the candidate must be
//! measured **in the same criterion session** as the champion. A sibling crate
//! is the only shape that keeps the comparison fair — the same reasoning as
//! genesis: all three variants reach the bench binary through the identical
//! path (same profile, same fat-LTO merge, same codegen units), so none is
//! artificially inlinable relative to the others.
//!
//! # The contract
//!
//! 1. **At rest, `src/{field,univariate,multilinear}.rs` are byte-copies of
//!    `cpoly/src/`** — a *null candidate*. `make bench-check` enforces this
//!    (`harness.py check-candidate`). Two things follow: the crate always
//!    compiles, and a `CANDIDATE=1` run against the null candidate is a free
//!    harness self-test — every `candidate` row must read as noise against
//!    `now`, exactly like a `_control` case.
//! 2. **The loop overwrites, measures, and restores.** `perf-loop` applies a
//!    candidate's diff to this crate *inside its own git worktree*, runs the
//!    filtered bench, and the worktree is discarded; the checked-in copy never
//!    diverges. After the champion swap lands in `cpoly/src`, the copies here
//!    are refreshed in the same change.
//! 3. **`lib.rs` is this file, not a copy.** Like genesis's `lib.rs`, it
//!    carries the slot's own documentation; `check-candidate` compares the
//!    three module files only, which are the code that gets measured.
//! 4. **Without `--features candidate` this crate is compiled but never
//!    timed.** The default suite measures exactly what it measured before the
//!    slot existed.

#![no_std]
#![forbid(unsafe_code)]
// At rest this is a copy of cpoly/src, whose lints travel with it; a candidate
// diff under test answers to `cargo clippy` in the loop's worktree, not here.
#![allow(warnings, clippy::all, clippy::pedantic)]

extern crate alloc;

pub mod field;

pub mod multilinear;

pub mod univariate;

pub use field::{Ext4, Fp};
pub use multilinear::{MultilinearEvals, MultilinearPoly};
pub use univariate::UnivariatePoly;
