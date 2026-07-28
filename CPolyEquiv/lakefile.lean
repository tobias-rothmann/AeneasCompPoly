import Lake
open Lake DSL

-- Aeneas's Lean backend library already `require`s mathlib @ v4.31.0,
-- the same revision CompPoly pins, so there is no Mathlib version conflict.
require aeneas from "../aeneas/backends/lean"

require CompPoly from "../CompPoly"

package «CPolyEquiv» where

@[default_target]
lean_lib «CPolyEquiv» where
