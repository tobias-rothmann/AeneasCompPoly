---
name: route-r1
description: The Lean-first route — optimize a targeted CompPoly definition entirely on the Lean side (all applicable opt-* strategies stacked to a fixpoint, ranked by op counts, no benching between candidates), translate the final variant once, confirm with a single accept run, then verify; run when asked to execute route R1 or a Lean-first optimization pass on one target
---

# Route R1 — Lean-first, translate once

Pure composition; every procedure lives in the stage skill named. The target
definition is handed in. What makes this route R1: **the bench appears
exactly once, at the end** — selection among Lean variants uses only the
opt-contract and the brief's operation counts, never a measurement.

1. `compoly-analyze` — target definition in → optimization brief out.
2. `lean-opt`, run to a fixpoint — all applicable `opt-*` strategies,
   stacking each accepted rewrite on the last; out: one final `Foo.opt`
   chain with its proved `opt_eq_spec` composition, selected by op-count
   ranking alone. Contract failures are ledger rows as always.
3. `lean-to-rust` — the final variant in → one trivial-grade translation
   out.
4. `perf-loop`, entered at its per-candidate steps for this single
   candidate — semantics tests, one recentered `CANDIDATE=1` accept run
   against the champion. The one verdict decides whether the whole chain
   lands; a reject ends the route with its ledger row (there is no
   per-strategy retreat — that would be R3).
5. `verify-campaign` (K=1, trigger `champion-accept`) — on accept: champion
   branch in → verified module, campaign ledger row, merge plan out.
