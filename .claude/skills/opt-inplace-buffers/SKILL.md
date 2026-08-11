---
name: opt-inplace-buffers
description: Optimization strategy — pre-sized buffers, loop/pass fusion, and in-place mutation shapes for a targeted CompPoly definition, expressed in Lean so the translation stays trivial, as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows reallocation growth, repeated passes over the same array, or an output the size of the input
---

# Strategy: In-Place / Pre-Sized Buffers

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `compoly-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `cpoly/lean/Opt.lean`
plus the proved `Foo.opt_eq_spec`.

## The one rule: the buffer discipline is expressed in Lean, or it does not exist

`Vec::new()` + `push` is the *deliberate* trivial shape (`lean-to-rust`'s
fold row) — a translator that quietly adds `with_capacity` or fuses two loops
has made an optimization, and optimizations live in Lean. The Rust building
blocks are already probed extraction-safe (`aeneas-extract` ceiling table,
`nightly-2026.07.26-3a8586f`: `with_capacity`, `&mut` in-place writes, both
axiom-free) — what this strategy adds is the *Lean-side* def whose trivial
translation produces them: `Array.emptyWithCapacity n` + push-loop,
`Array.set!`/`Array.modify` index loops, one fused pass where the spec makes
two. A correspondence not yet in `lean-to-rust`'s conventions table is a
one-row extension of that table — name it in the candidate note; the row
lands in `lean-to-rust` (its owner) when the candidate is accepted.

## What it attempts

* **Pre-sizing**: output length is known up front (`n`, `np + nq − 1`, `2^k`)
  → `Array.emptyWithCapacity` + push-loop, or `mkArray` + `set!` loop.
* **Pass fusion**: consecutive map/fold traversals of the same array → one
  loop with named per-iteration intermediates. (Algorithm substitution —
  computing *fewer* field ops — is `opt-algo-swap`'s side of the boundary;
  this skill only changes how memory moves.)
* **In-place accumulation**: `acc = f acc x` chains that rebuild an array →
  `Array.set!` on a single buffer, shaped so the Rust is `&mut`-friendly.

Orient on kim-em/lean-zip's `lean-content-preservation` for the lemma side:
prefix-preservation and characterize-the-new-cells patterns for `set!` loops.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* Reallocation/pass-count claims in the candidate note are counted from the
  def, cited to the brief — never "should allocate less".
* Any new Lean↔Rust correspondence is named explicitly for `lean-to-rust` to
  adopt; it is never applied silently in the translation.
