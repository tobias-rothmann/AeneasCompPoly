---
name: verify-campaign
description: Driving the outer verification pass for a champion or a regenerated extraction — scope the proof debt on the champion branch, champion idiomatic review, re-extraction and determinism check, spec repair/authoring stubs, prove-sorry runs per sorry, Check.lean audit, metered effort into a campaign ledger row, merge plan; use when an accepted optimization awaits its equivalence proofs (K=1: every accepted champion), when Generated.lean regenerated for any reason (Rust edits, aeneas/charon bump) and specs broke, or when asked to verify a module end-to-end
---

# The Outer Verification Pass

Drives one **campaign**: from a champion branch (or any regenerated
`Generated.lean`) to a module whose specs are proved, audited, and ready to
merge. Stages, each owned by its own skill: the `aeneas-idiomatic-rust`
champion review → `aeneas-extract` → `aeneas-spec-author` (with
`aeneas-equivalence-bridges` on demand) → `prove-sorry` per sorry → the
`Check.lean` audit → this skill's ledger row and merge plan. The upstream
`verification-campaigns` skill is the playbook for planning and for mass
breakage (>~5 files red, from-scratch primitives); this skill is the
project-local orchestration around it. The inner optimization loop
(`perf-loop`) never proves; this pass never benches.

## The one rule: main only ever receives a green module

A champion's Rust swap, its regenerated `Generated.lean`, and the specs it
breaks travel together on a `champion/<op>` branch (prepared by
`perf-loop`), and that branch merges only when `lake build` is green, every
`_spec` is sorry-free, and the `Check.lean` audit passes. No intermediate
state — sorried stubs, re-pinned-but-unproved aliases, a "temporarily red"
build — is ever staged for main itself. The debt is paid where it was
incurred. Trigger cadence is **K=1**: one campaign per accepted champion,
before the next optimization target is taken up; the ledger's effort
numbers are what may later relax K, not convenience in the moment.

## The procedure

1. **Scope the debt** (in the champion worktree/branch). Re-run extraction
   per `aeneas-extract` — the determinism check is mandatory before any
   spec work, or the whole prove stage can be spent against a flaky
   snapshot. Diff `Generated.lean`; list every alias, `_spec`, and
   `Check.lean` entry affected, and classify each: *intact* / *re-pin only*
   (names re-mangled, semantics unchanged) / *stale loops* (opt structure
   changed the `*_loop` functions) / *new function*. Mass breakage or a
   from-scratch primitive → plan the file/folder structure with the
   upstream `verification-campaigns` skill before touching anything.
2. **Champion review.** One reviewer agent applies the
   `aeneas-idiomatic-rust` verdict tables to the champion's Rust, evidence
   required (candidates got only the mechanical clippy gate in the inner
   loop; the champion gets the real review). Findings that change the Rust
   send the campaign back to step 1 — the extraction must match what merges.
3. **Re-spec** per `aeneas-spec-author`: headline statements carried over
   verbatim, aliases re-derived and re-pinned, new loop specs shaped after
   the opt definition with `Foo.opt_eq_spec` splicing onto the unchanged
   right-hand side, everything delivered as typechecked `sorry` stubs. A
   representation mismatch that resists the house pattern goes through
   `aeneas-equivalence-bridges` before any relation is invented.
4. **Prove.** One `prove-sorry` run per sorried theorem — or one run over a
   scaffolded batch when several sorries share a decomposition (the loop
   spec + headline of one operation is the natural batch). Its approval
   gate, agent rules, and axiom hygiene apply unchanged. Machine
   discipline: Lean building and criterion benching never overlap, so a
   campaign never runs concurrently with an inner-loop bench session.
5. **Audit and close.** Full `lake build`; `Check.lean` §14 prints show
   axioms exactly `[propext, Classical.choice, Quot.sound]` for every
   headline spec; grep the touched files for
   `sorry|native_decide|axiom|implemented_by|unsafe|maxHeartbeats`; new
   Check entries for anything the campaign introduced.
6. **Ledger row, then stage — never commit.** Append the campaign row
   (below), stage the branch state, and end by handing the user an ordered
   plan: the champion-branch commits, the merge to main, and any post-merge
   step the landing owes (e.g. `make bench-stamp` when the merge freezes
   new genesis items).

## Effort metering — the campaign's second product

The P3 questions (does `opt_eq_spec` keep proofs at trivial-translation
cost? should K stay 1? where does the trivial-grade dial sit?) are decided
by these numbers, so a campaign that forgets to meter has produced half its
value. Meter **as you go** — post-hoc estimates are fiction:

* `tokens` — output tokens of the prover/verifier fleets (the Workflow
  tool's `budget.spent()` read per phase) plus a stated estimate for
  main-loop work;
* `wall_min` — wall-clock minutes per phase: scope, review, spec, prove,
  audit;
* `retries` — prover attempts beyond the first per lemma, plus repair-agent
  escalations;
* `interventions` — approval-gate hits and any other point a human had to
  unblock the run.

The row goes in `ledger.jsonl` at the repo root (file conventions —
append-only, one line per event, `pins.repo` honesty — and the full `kind`
table are owned by the `skill-lab` skill; campaign rows are distinguished
by `"kind": "campaign"`, rows without a `kind` are the inner loop's):

```json
{"kind": "campaign", "ts": "2026-08-12T10:00:00+02:00",
 "op": "univariate/mul", "champion": "mul.opt — karatsuba, cutoff 32",
 "trigger": "champion-accept",
 "specs": {"carried": 2, "repinned": 5, "new_loops": 3, "new": 0},
 "effort": {"tokens": 0, "wall_min": {"scope": 0, "review": 0, "spec": 0,
            "prove": 0, "audit": 0}, "retries": 0, "interventions": 0},
 "result": "verified",
 "axioms": "clean",
 "pins": {"repo": "abc1234", "dirty": true, "compoly": "c0fcf450",
          "aeneas": "nightly-2026.07.26-3a8586f"},
 "notes": "…"}
```

`trigger` ∈ champion-accept · regeneration · from-scratch. `result` ∈
verified · partial · blocked — partial and blocked rows are appended too,
with the blocking lemma named in `notes`; an abandoned campaign without a
row is invisible to the K decision.

## Failure modes with teeth

* **Treating re-mangled names as broken proofs.** A regenerated extraction
  re-mangles operator-impl names whenever the impl shape moves; the failure
  is at the alias layer, not the semantics. Re-pin first (step 1's
  classification), or hours of proving are spent on what one `abbrev` edit
  fixes.
* **Merging early.** A champion branch merged with sorried specs makes
  `lake build` red for every consumer of main and turns `Check.lean`'s
  build-visible-`sorry` design into noise. Green first, merge second.
* **Benching during a campaign.** Worktrees isolate files, not the machine:
  a `lake build` landing inside someone's criterion session corrupts the
  measurements silently (the inner loop's serial rule is loop-wide, and
  campaigns count).
* **Spec work on an unchecked extraction.** Skipping the determinism check
  and authoring against a snapshot that differs run-to-run wastes the
  entire prove stage — the check is two extractions, the prove stage is the
  expensive fleet.
* **Reconstructed effort numbers.** Numbers written at close-out from
  memory undercount retries and interventions — exactly the fields the K
  decision needs. Keep the tally in the campaign's scratchpad from step 1.

## Invariants to keep green

* Main always builds green: no `sorry`, no broken alias pin, axiom closure
  exactly `[propext, Classical.choice, Quot.sound]` on every headline spec.
* Every campaign — verified, partial, or blocked — has exactly one ledger
  row with its effort block filled from a running tally.
* Stage, never commit: a campaign ends with staged changes and an ordered
  commit-and-merge plan for the user.
* A champion branch merges only after step 5 passes in full, and the merge
  plan names any post-merge obligation.
* K=1 stands until a ledger-backed decision changes it — and that decision
  updates this skill in the same session.
