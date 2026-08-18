---
name: route-r3
description: The hybrid route (the default) — optimize a targeted CompPoly definition on the Lean side with bench-steered iteration, then pay the proof debt per accepted champion; run when asked to execute route R3, the default optimization route, or an end-to-end optimize-and-verify pass on one target
---

# Route R3 — Lean-side optimization, bench-steered (the default)

Pure composition; every procedure lives in the stage skill named. Invocation
resolves the target definition — choosing targets is the caller's job
(`autonomy-harness` or the user).

## Invocation

**Human invocation:** start with `/route-r3` alone. Ask: **“Which CompPoly
operation should route R3 optimize and verify?”** Resolve and confirm that
single target, then run the fixed default route; its Lean-side candidate stage
is not a tuning parameter.

**Agent invocation:** bypass the dialogue with:

```yaml
agent_request:
  target: CompPoly.<fully-qualified-definition>
```

Return an invalid or missing target to the invoking agent, never to the human.

1. `compoly-analyze` — target definition in → optimization brief out.
2. `perf-loop`, candidate stage `lean-opt` (+ the `opt-*` strategies) —
   brief in → iterated bench-steered accepts; out: staged champion,
   candidate ledger rows, and the `champion/<op>` branch material in the
   commit plan. Benching happens inside the loop, per candidate — that
   interleaving is what makes this route R3 and not R1.
3. `verify-campaign` (K=1, trigger `champion-accept`) — champion branch in →
   verified module, campaign ledger row, ordered merge plan out.

The route ends when step 2 finds no further accept and step 3 has paid the
last accept's debt.
