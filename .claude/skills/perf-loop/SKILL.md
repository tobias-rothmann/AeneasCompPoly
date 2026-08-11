---
name: perf-loop
description: Orchestrating the inner optimization loop for a targeted CompPoly definition — compoly-analyze brief, lean-opt candidate fan-out, trivial translation, semantics tests, within-run candidate bench (CANDIDATE=1), accept/reject on cand-vs-now, ledger row, champion staging; use when asked to optimize a CompPoly operation end-to-end or to run the perf loop
---

# The Inner Performance Loop

Drives the inner loop of `skills-plan.html` §2/§5 for **one target definition**
(handed in; choosing targets is a route/user decision). Stages, each owned by
its own skill: `compoly-analyze` → `lean-opt` (+ the `opt-*` strategies) →
`lean-to-rust` → the `rust-bench` candidate mode → this skill's accept rule
and ledger. Aeneas is never touched per candidate; the accepted champion owes
one extraction check before landing, and the proofs belong to the outer pass.

## The one rule: only a within-run measurement accepts a candidate

The accept column is the **recentered** `cand vs now` from a single
`CANDIDATE=1` run — the candidate and the champion measured in the same
criterion session, the slot's signed identical-code lean (measured by that
binary's `_control` in the same run) divided out, the 5% floor applied to
what remains. Nothing else accepts: not op counts (they only rank candidates
for benching), not Lean intuition, not a delta assembled from two runs
(frozen code drifted 75% and 373% between runs when that was tried), not the
raw un-recentered ratio (the lean was −3.6% on byte-identical code the day
the slot landed — adversarial review showed a symmetric threshold on the raw
value accepts null candidates at ~20% per row), and not a run whose report
says `unusable`. Every shortcut here converts machine noise into a
"champion", and the loop would then optimize the weather.

## The procedure, per iteration

1. **Brief** — `compoly-analyze` on the target.
2. **Candidates** — `lean-opt`: tiered strategy fan-out (one Opus agent per
   strategy, worktree-isolated), opt-contract enforced. Contract failures are
   already ledger rows; only contract-ok candidates continue.
3. **Per candidate, in its worktree**, in this order:
   * apply the translation (`lean-to-rust`) of the opt def to `cpoly/src`;
   * `cargo test` — the cheap semantics filter; failure → row
     `tests-failed`, drop the candidate;
   * copy the three module files over the slot
     (`cp cpoly/src/*.rs cpoly/benches/candidate/src/`), then restore
     `cpoly/src` to the champion (`git restore cpoly/src`);
   * `make run-bench CANDIDATE=1 BENCH='<op>|_control' JSON=<file>` — keep
     `_control` in the filter; the report exits 2 with `unvalidated` verdicts
     if a candidate case ran in a binary whose control did not (enforced, not
     advisory). `CANDIDATE` must be exactly `1`.
4. **Bench discipline.** Bench runs are strictly serial — one criterion
   session on the machine at a time, loop-wide; two at once corrupt both.
   Exit code 2 (`unusable`, identical code measured >10% apart) → close what
   else is running and repeat once; never lower a threshold to make a run
   count.
5. **Verdict**, from the run's JSON, on the target's rows only, always via
   `cand_vs_now_verdict` (which is computed from the recentered
   `cand_vs_now_adj`, never from the raw ratio):
   * accept iff **every** measured row of the target reads `faster` — the
     rows share one lean but their noises are independent, so demanding all
     of them cuts the residual false-accept rate multiplicatively, and a
     real algorithmic win shows at every size it claims to help;
   * mixed rows (`faster` at one size, `slower` at another) are a real
     algorithmic trade-off: reject, but surface it to the user with the
     numbers — it may deserve a size-split champion, which is a target
     decision, not a bench verdict;
   * anything else → `rejected-noise` / `rejected-slower` per the worst row.
6. **Tournament.** Multiple accepted candidates for one target: rank by
   `cand_vs_now` at the largest measured size, then confirm the winner with
   one fresh `CANDIDATE=1` run against the champion. Never chain deltas
   across candidates' separate runs.
7. **Champion landing** (accepted winner):
   * `Opt.lean` def + lemma + `Check.lean` §15 line — pure additions;
   * `cpoly/src` swap with `Mirrors` lines renamed to the variant
     (`Mirrors \`CPolynomial.Raw.mul.opt\``), semantics tests extended per
     `lean-to-rust`'s obligations;
   * any **new** helper fn is a first translation: freeze into genesis +
     case/exclusion, per `rust-bench` — `make bench-check` must be green;
   * re-sync the slot (byte-copy of the new `cpoly/src`);
   * one extraction check in the worktree per `aeneas-extract`
     (deterministic, zero axioms, loop shapes); its result goes in the row;
   * ledger row, then **stage — never commit** (user settings enforce it):
     the loop ends by handing the user an ordered commit plan.
   * *Until `verify-campaign` exists (P3):* the Rust swap + regenerated
     `Generated.lean` + broken `_spec`s are proof debt that must not reach
     main — prepare them as a `champion/<op>` branch in the commit plan and
     mark the row `TODO(P3)`. Once the outer pass exists, debt is paid per
     accept (K=1 until the ledger says otherwise).
8. **Iterate** — next `lean-opt` tier on the (possibly new) champion — until
   a full round yields no accept, or the user stops the loop.

## The ledger (owned here until `skill-lab` exists)

`ledger.jsonl` at the repo root. Append-only; one JSON object per line per
candidate verdict, accepted or not — rejects are the cheap lessons the
strategy skills grow from. The numbers in a row are copies of one run's
within-run deltas and are valid **only as that run's claim**: no tooling may
subtract two rows' numbers, and nothing here justifies a cross-run
comparison (the attempt that failed is documented in `benches/genesis`).

```json
{"ts": "2026-08-11T14:03:00+02:00",
 "target": "CompPoly.CPolynomial.Raw.mul",
 "op": "univariate/mul",
 "strategy": "opt-algo-swap",
 "candidate": "mul.opt — karatsuba, 1 level",
 "verdict": "accepted",
 "rows": [{"case": "univariate/mul/256", "cand_vs_now": -0.33,
           "cand_vs_now_adj": -0.31, "cand_vs_genesis": -0.31,
           "verdict": "faster"}],
 "cand_lean": -0.021, "slot_sha": {"univariate": "1a2b3c4d5e6f"},
 "threshold": 0.05, "ab_bias": 0.021, "machine": "<id from the report>",
 "extraction": "clean",
 "pins": {"repo": "abc1234", "dirty": false, "compoly": "c0fcf450",
          "aeneas": "nightly-2026.07.26-3a8586f",
          "bench_toolchain": "nightly-2026-06-01"},
 "notes": "TODO(P3): champion/univariate-mul branch carries the swap"}
```

`verdict` ∈ accepted · rejected-slower · rejected-noise · rejected-mixed ·
tests-failed · lemma-failed · not-translatable · no-strategy-applies ·
contract-violation · bench-unusable. `pins.repo` is `HEAD` (short) with
`dirty` true when the skills/infra under test are staged but uncommitted —
honest provenance beats pretty provenance. `skill@commit` pinning needs no
per-skill field: every skill lives in this repo, so `pins.repo` pins them all.
`slot_sha` and `cand_lean` come from the run's report (`candidate_slot` /
`cand_leans` in the JSON): the sha ties the numbers to the diff the slot
actually held, the lean records what was divided out of the accept column.

## Failure modes with teeth

* **A `BENCH=` filter that drops `_control`.** For the accept column this is
  now a hard failure — candidate verdicts read `unvalidated` and the report
  exits 2 (adversarial review demonstrated the fail-open version: a stale
  30%-bias run's controls filtered away, a 20% "win" printed, exit 0). For
  plain `vs genesis` runs it still degrades to an unvalidated print, so
  write the filter correctly either way: `BENCH='<op>|_control'`.
* **Accepting on `vs genesis`, or on the raw `cand_vs_now`.** The first
  contains every *previous* champion's gain; the second contains the slot's
  signed layout lean (−3.6% measured on identical code). The accept column
  is the recentered `cand_vs_now_adj` via its verdict, nothing else.
* **A landed run that forgot the restore step.** `cpoly/src` still carrying a
  candidate diff, or the slot left divergent — `make bench-check`
  (`check-candidate`) is the tripwire; run it before writing the commit plan.
* **Two loops at once.** Worktrees isolate files, not the machine: a lake
  build or second bench during a criterion session lands asymmetrically on
  the variants. Lean building and benching never overlap.
* **A worktree freezes the harness at creation time.** The first supervised
  run benched through a worktree whose `harness.py` predated the same-day
  review fixes — the measurements were fine, the report semantics were not.
  If harness code changed since the worktree was cut, re-copy it before the
  accept run; a report-only rerun on the same criterion state (`harness.py
  report --since <original stamp>`) is the honest repair when it happens.
* **The report rides the run.** `make run-bench` benches and reports in one
  invocation; the slot fingerprint is read at *report* time, so a post-hoc
  re-report describes the slot as it is then, not as it was benched. Record
  `slot_sha` from the run's own report, and note any report-only rerun in
  the ledger row.

## Invariants to keep green

* Stage, never commit — every loop run ends with staged changes and a
  written, ordered commit plan for the user.
* Every candidate that reached step 3 has a ledger row, whatever its fate.
* No champion lands without: tests green, an `accepted` row, the extraction
  check recorded, `make bench-check` green, `Mirrors` lines truthful.
* At rest, slot ≡ `cpoly/src` byte-for-byte, and `ledger.jsonl` is
  append-only — a rewritten row is a falsified history.
