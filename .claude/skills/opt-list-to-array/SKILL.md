---
name: opt-list-to-array
description: Optimization strategy — replacing List/Vector shapes in a targeted CompPoly definition with Array and index loops to kill per-element allocation and O(n) appends, as Foo.opt + its proved opt_eq_spec lemma; run only when the brief shows an actual List, append chain, or per-element allocation on the hot path
---

# Strategy: List → Array

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `compoly-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `cpoly/lean/Opt.lean`
plus the proved `Foo.opt_eq_spec`.

## The one rule: fire on brief evidence, not on reflex

This corpus is already Array-based — `CPolynomial.Raw F = Array F` is
literally `rfl` (`Check.lean` §6), and `CMlPolynomial F n = Vector F (2^n)`
is `Array`-backed with a size proof. The strategy exists for the exceptions:
a `List` on a hot path, a `++`-chain, a `.toList`/`.ofFn` round-trip, a
per-element boxing shape the brief names with its `file:line`. If the brief
shows none, report `no-strategy-applies` and stop — that outcome is expected
and costs the loop nothing; a forced rewrite of an already-Array def costs a
candidate slot and a bench run.

## What it attempts

* `List F` recursion → `Array F` with an index loop or `foldl`;
* append-accumulation (`acc ++ [x]`, `List.concat`) → `Array.push`
  accumulation;
* `Vector`/`List` interconversions inside a computation → staying in `Array`
  end-to-end, converting once at the boundary.

Orient on kim-em/lean-zip's `lean-array-list` for the lemma side
(`Array`/`List` indexing and size lemmas, `toList`-bridging).

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full.
* The candidate note cites the brief's `file:line` for the List-shape it
  removed — no citation, no candidate.
