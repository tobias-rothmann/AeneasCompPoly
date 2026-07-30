import Lake
open Lake DSL

-- CompPoly's `Fields/Hachi.lean` and `Fields/Extension/` -- the field this
-- development is about -- only exist after CompPoly's Lean v4.32.0 bump, so this
-- package is on v4.32.0 / Mathlib v4.32.0; see `lean-toolchain`.
--
-- Upstream Aeneas has no v4.32.0 release yet: its Lean backend hard-`require`s
-- Mathlib v4.31.0. So `aeneas` comes from a local checkout of
-- `nightly-2026.07.26-3a8586f` with the v4.32.0 API drift patched -- branch
-- `lean-4.32.0` of the sibling `aeneas` clone, checked out as a git worktree at
-- `../aeneas-432`. Replace this with
--
--   require aeneas from git
--     "https://github.com/AeneasVerif/aeneas.git" @ "<a v4.32.0 nightly>"
--       / "backends" / "lean"
--
-- as soon as upstream publishes one. Either way the extraction binaries
-- (`../toolchain/{charon,aeneas}`, see `../cpoly/extract.sh`) must stay on the
-- same Aeneas commit as this library: `Generated.lean` is only valid against the
-- Aeneas version that produced it.
require aeneas from "../aeneas-432/backends/lean"

-- Fetched from GitHub rather than a sibling checkout. The concrete revision is
-- pinned in `lake-manifest.json`; bump it deliberately with
-- `lake update CompPoly`. Since this tracks `main`, re-check the Mathlib
-- invariant above after any bump -- `aeneas` and `lean-toolchain` have to move
-- with CompPoly's Mathlib pin.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "main"

package «CPolyEquiv» where

@[default_target]
lean_lib «CPolyEquiv» where
