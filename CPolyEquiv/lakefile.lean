import Lake
open Lake DSL

-- Aeneas's Lean backend library already `require`s mathlib @ v4.31.0,
-- the same revision CompPoly pins, so there is no Mathlib version conflict.
-- Pinned to a nightly tag rather than a branch: the extracted `Generated.lean`
-- is only valid against the Aeneas version that produced it.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "nightly-2026.07.26-3a8586f" / "backends" / "lean"

-- Fetched from GitHub rather than a sibling checkout. The concrete revision is
-- pinned in `lake-manifest.json`; bump it deliberately with
-- `lake update CompPoly`. Since this tracks `main`, re-check the Mathlib
-- invariant above after any bump -- if CompPoly moves off v4.31.0, `aeneas` and
-- `lean-toolchain` have to move with it.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "main"

package «CPolyEquiv» where

@[default_target]
lean_lib «CPolyEquiv» where
