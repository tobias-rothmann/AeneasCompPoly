import Lake
open Lake DSL

-- This Lake package sits in the *same* directory as the Rust crate it is about:
-- `src/` is the crate, `lean/` is the proof development, and `../toolchain`
-- turns the former into `lean/Generated.lean` (see `make extract`).
-- Keeping them together is what lets Aeneas write its output straight into the
-- library, with no copy of the generated model to keep in sync.

-- CompPoly's `Fields/Hachi.lean` and `Fields/Extension/` -- the field this
-- development is about -- only exist after CompPoly's Lean v4.32.0 bump, so this
-- package is on v4.32.0 / Mathlib v4.32.0; see `lean-toolchain`.
--
-- Which is why this is a *fork* and not upstream. Upstream Aeneas has no v4.32.0
-- release: its Lean backend hard-`require`s Mathlib v4.31.0, and every nightly
-- up to and including `nightly-2026.07.30-3a8586f` is still on v4.31.0. The
-- branch below is `nightly-2026.07.26-3a8586f` plus one commit repairing the
-- v4.32.0 API drift -- API only, no semantic change and no `sorry`.
--
-- Replace this with
--
--   require aeneas from git
--     "https://github.com/AeneasVerif/aeneas.git" @ "<a v4.32.0 nightly>"
--       / "backends" / "lean"
--
-- as soon as upstream publishes one, and the fork can then be deleted. Until
-- then the fork has to stay reachable, because this build depends on it.
--
-- Read the branch name as a moving target and `lake-manifest.json` as the truth:
-- the manifest records the resolved commit, which is what makes a clone
-- reproducible. Move it deliberately with `lake update aeneas`.
--
-- Either way the extraction binaries (`../toolchain/{charon,aeneas}`, pinned by
-- `AENEAS_TAG` in the Makefile) must stay on the same Aeneas commit as this
-- library: `Generated.lean` is only valid against the Aeneas version that
-- produced it. `make setup` and `make extract` check that they do.
require aeneas from git
  "https://github.com/tobias-rothmann/aeneas.git" @ "lean-4.32.0"
    / "backends" / "lean"

-- Fetched from GitHub rather than a sibling checkout. The concrete revision is
-- pinned in `lake-manifest.json`; bump it deliberately with
-- `lake update CompPoly`. Since this tracks `main`, re-check the Mathlib
-- invariant above after any bump -- `aeneas` and `lean-toolchain` have to move
-- with CompPoly's Mathlib pin.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "main"

package «CPolyEquiv» where

-- `lean/`, not the package root: the package root is the Rust crate, so `src/`
-- is Rust and `lean/` holds the modules of this library -- flat, with no
-- directory level of its own: `lean/Field.lean` is the module `Field`.
--
-- Which is why `roots` has to name every module. There is no module called
-- after the library to reach the rest through, and Lake counts a module as part
-- of a library only when one of the roots is a *prefix* of its name -- under the
-- default `roots := #[`CPolyEquiv]` not one of these files would resolve. The
-- default `globs` is one glob per root, so listing them is also what makes
-- `lake build` check all of them, `Check.lean` included: nothing imports that
-- one, it is only ever built as a root of its own.
--
-- Adding a module under `lean/` therefore means adding it here too. Listed in
-- dependency order, which is also the order to read them in.
@[default_target]
lean_lib «CPolyEquiv» where
  srcDir := "lean"
  roots := #[`Generated, `Field, `Univariate, `Multilinear, `Check]
