---
name: opt-algo-swap
description: Optimization strategy — substituting the algorithm behind a targeted CompPoly definition (Horner evaluation, Karatsuba multiplication, precomputed tables) as a Lean Foo.opt variant with its proved opt_eq_spec lemma; run when the brief shows an operation-count or complexity-class win
---

# Strategy: Algorithm Substitution

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `compoly-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `cpoly/lean/Opt.lean`,
written inside `lean-to-rust`'s translatable subset, plus the proved
`Foo.opt_eq_spec`. This is the strategy the driver tries **first**: a
complexity-class or operation-count win dwarfs constant-factor tuning, and it
changes which constants are worth tuning afterwards.

## The one rule: the algorithm changes in Lean, never in the translation

This repo already carries the counterexample. `cpoly/src/univariate.rs`'s
`eval` is Horner's method while its `Mirrors` line names
`CPolynomial.Raw.eval` — the naive `foldl` with `x ^ i` — because the swap was
made during translation, before the trivial-grade checklist existed. The cost:
the Aeneas equivalence proof absorbed an algorithm gap that a pure-Lean lemma
upstream *already ships* (`eval₂Horner_eq_eval₂`) would have carried, and that
Rust cannot be regenerated from the def it claims to mirror. A swap lands as
`Foo.opt` + lemma first; the translation of it stays trivial.

## Upstream first

CompPoly already ships some optimized variants with their lemmas — check the
pinned copy (`cpoly/.lake/packages/CompPoly/`, rev per `lake-manifest.json`)
before writing one. Exemplar pair: `eval₂Horner`
(`CompPoly/Univariate/Raw/Ops.lean`) with `eval₂Horner_eq_eval₂`
(`CompPoly/Univariate/Raw/Proofs.lean`). When upstream has the variant, the
candidate is "mirror upstream's def directly" and nothing lands in `Opt.lean`.

## The moves this strategy owns

* **Horner** for evaluation shapes: `∑ aᵢ xⁱ` → fold with one mul + add per
  step, no `x ^ i`.
* **Karatsuba** for convolution: 3 half-size products instead of 4; needs
  subtraction, so expect `Ring R` where the spec asked `Semiring R` —
  typeclass strengthening is allowed by the opt-contract when `F` satisfies
  it and the candidate note says why it was needed.
* **Precomputed tables** for values recomputed inside a loop (powers, basis
  elements) — the table construction must itself be a translatable def.

Loop/pass *fusion* is not this skill: memory-traffic restructuring belongs to
`opt-inplace-buffers`. The boundary: this skill changes *what* is computed
(fewer field operations); that one changes *how memory moves*.

Measured constraint on NTT ambitions: the Hachi prime has
q − 1 = 2²·3·13·67·163·2521 — two-adicity **2** (verified 2026-08-11), so
radix-2 NTT caps at size 4 in the base field. Do not propose NTT without
first solving the root-of-unity problem in `Ext4` and citing the evidence.

## Ledger-born lessons

* **Karatsuba on `CPolynomial.Raw.mul`, 2026-08-11 (accepted)**: cutoff 32,
  predicted −58%/−25% by mul count at n = 256/64, measured **−48.8%/−18.2%**
  (recentered, ledger row 1). The gap is the recombination's O(n) passes and
  allocations, as the candidate note estimated — mul-count predictions
  overshoot by ~10 points at depth 3 and ~7 at depth 1; keep quantifying
  both. Proof route that worked: `toPoly` bridge + `noncomm_ring` for the
  splitting identity (stated with a *central* `x`, so no commutativity),
  coefficient-level only for the base case; array equality only after `trim`.

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met in full — def, proved lemma,
  candidate note with the op-count claim cited from the brief.
* The `Mirrors` line of the translated Rust names `Foo.opt` (or the upstream
  variant), never the original def the algorithm no longer matches.
