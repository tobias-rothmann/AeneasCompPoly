---
name: opt-tailrec-loops
description: Optimization strategy — rewriting structural or non-tail recursion in a targeted CompPoly definition into a tail-recursive accumulator loop or fold that lands 1:1 on a Rust while loop, as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows non-tail recursion or per-call allocation on the hot path
---

# Strategy: Tail-Recursion / Loop Shape

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `compoly-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `cpoly/lean/Opt.lean`
plus the proved `Foo.opt_eq_spec`.

## The one rule: the target shape is the one `lean-to-rust` already translates

The point is not that tail calls are fast in Lean — Lean's cost model is
explicitly not the fitness function. A tail-recursive accumulator def is the
*Lean image* of the counter-`while` row of `lean-to-rust`'s conventions table:
rewriting into it keeps the translation inside the six trivial-grade moves and
keeps the extracted loop state a small tuple (the `aeneas-idiomatic-rust`
lesson: a fattened loop state broke the invariant shape the proofs expect). A
rewrite that lands outside that table has left this strategy's mandate — file
it as a different strategy or drop it.

## What it attempts

* structural (non-tail) recursion → tail recursion with an accumulator
  argument, or an explicit `foldl` / index loop over `Array`;
* recursion whose call tree re-traverses data → a single forward pass with
  named intermediate state.

Orient on kim-em/lean-zip's `lean-wf-recursion` and `lean-fuel-induction` for
the proof side: `Foo.induct` for the original's induction principle, the
generalize-the-accumulator pattern, `termination_by` for the variant when its
recursion is no longer structural.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* The variant's recursion/loop shape maps onto conventions-table rows with no
  new translation move required — if it would need one, say so in the
  candidate note instead of smuggling it.
