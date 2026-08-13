---
name: skill-lab
description: Running measured experiments over the loop's skills — the route bake-off (route-r1/r2/r3 arms on the same target, metered not capped), skill-version A/Bs (session-scoped variants, exactly one skill bumped per experiment), ownership of ledger.jsonl and its kind-discriminated row schemas, and folding each verdict back into the responsible skill; use when comparing routes or skill versions, when appending bakeoff or ab rows, or when deciding whether ledger variance justifies an A/B
---

# The Skill Lab

The experiment layer over the loop: routes and skill versions are compared
the way candidates are — measured, within-run, with the verdict folded back
into exactly one place. Read this **before** running a bake-off arm,
starting an A/B, or writing any ledger row that is not a candidate or
campaign row. Variant mechanics (session-scoped `-v2` directories, git-only
versioning) are `skill-authoring`'s; this file owns *when* an experiment
runs and *how its result is recorded*.

## The one rule: an experiment varies exactly one thing

One route per arm on the same target; one skill per A/B, everything else at
HEAD. The ledger must attribute every win or loss to exactly one skill —
that is why strategies are born as their own skills — and an experiment
that varies two things produces a row that blames neither. Corollary for
routes: route skills contain no procedure, so an arm's outcome is
attributable to the composition itself; a procedure smuggled into a route
skill invalidates the arm.

## The ledger — `ledger.jsonl`, owned here

File conventions, unchanged from the day the file was born: append-only at
the repo root, one JSON object per line per event, `pins.repo` = short HEAD
with `dirty: true` when the machinery under test is staged but uncommitted.
The numbers in a row are one run's within-run claims — no tooling may
subtract two rows' numbers (cross-run comparison drifted 75–373% on frozen
code when it was tried; the full argument lives in `cpoly/benches/genesis`).

Rows are discriminated by `kind`; any tooling over the ledger filters on it
first:

| `kind`      | meaning                        | schema lives in  |
|-------------|--------------------------------|------------------|
| *(absent)*  | inner-loop candidate verdict   | `perf-loop`      |
| `campaign`  | one verification campaign      | `verify-campaign`|
| `bakeoff`   | one completed bake-off arm     | here             |
| `ab`        | one settled skill A/B          | here             |

## The route bake-off

Arms are the `route-r1` / `route-r2` / `route-r3` skills run on the **same
target definition**, each from the same genesis baseline, each in its own
worktree, each blind to the sibling arms' artifacts (an arm that reads
another arm's candidate notes is contaminated — its row says so or is not
written). Discipline:

* **Metered, not capped.** Every arm runs to its natural finish — no
  significant win left, proofs done. Effort is measured per the
  `verify-campaign` effort block (tokens, wall-clock per phase, retries,
  interventions), extended over the arm's perf stages too. Cost differences
  between arms *are* the result; a cap would amputate them.
* **Machine serialization is bake-off-wide.** One criterion session or
  `lake build` on the machine at a time across *all* arms — arms interleave
  by stage, never on the machine ( `perf-loop`'s serial rule, promoted a
  level).
* **The answer is a pair, never a scalar.** Per arm: the verified champion's
  recentered bench delta at the largest measured size, alongside the total
  effort block. No formula collapses speed and proof cost into one number —
  that trade-off is the user's to read.

One row per completed arm:

```json
{"kind": "bakeoff", "ts": "…",
 "op": "univariate/mul", "arm": "route-r3",
 "target": "CompPoly.CPolynomial.Raw.mul",
 "champion": "mul.opt — karatsuba, cutoff 32",
 "bench": {"case": "univariate/mul/256", "vs_genesis": -0.49},
 "effort": {"tokens": 0,
            "wall_min": {"perf": 0, "scope": 0, "review": 0, "spec": 0,
                         "prove": 0, "audit": 0},
            "retries": 0, "interventions": 0},
 "result": "verified",
 "reference": {"impl": "bench-only unrestricted Rust", "vs_genesis": null},
 "pins": {"repo": "…", "dirty": false, "compoly": "…", "aeneas": "…"},
 "notes": "…"}
```

`result` ∈ verified · partial · abandoned — an arm that dies (extraction
wall, unprovable champion) still gets its row; a missing arm is invisible
to the exit question. `effort` honesty: when an arm reuses work whose
effort predates metering (a champion accepted before the conventions
existed), the row says so in `notes` and marks the unmeterable phases
`null` — a guessed number is worse than a hole.

`reference` is the "gap vs unrestricted Rust" anchor (?2 in
`skills-plan.html`): an unrestricted-but-safe Rust implementation of the
same operation, measured **through the candidate slot** in a worktree —
`make run-bench CANDIDATE=1` like any candidate, so it gets the recentered
within-run delta and the digest assert for free — then discarded with the
worktree. It is never a bench case of its own (an absolute time or a
cross-row comparison would say nothing), never enters `cpoly/src`, never
extracts, and is never verified. Its candidate ledger row uses
`"strategy": "reference-unrestricted"`, `"verdict": "reference"` — nothing
may cite it as a champion; it exists so a bake-off row can state what
staying inside the ceiling cost.

## Skill A/Bs

* **Trigger criterion — variance in the ledger, not curiosity.** An A/B
  runs only when rows attribute divergent outcomes to one skill: the same
  strategy skill producing accepts on one target and contract failures on
  a like target; a campaign whose retries concentrate in one stage across
  campaigns; a translation gate that keeps needing the same manual repair.
  The suspect sentence in the skill is named before the variant is written.
* Mechanics per `skill-authoring`: variant directory beside the canonical
  one, this session only; the experiment runs both versions on the same
  fixed input (a target already in the ledger is ideal); the row records
  both outcomes; the winner is folded into the canonical directory and the
  variant deleted before the session ends.

```json
{"kind": "ab", "ts": "…", "skill": "lean-to-rust",
 "hypothesis": "…the sentence under test…",
 "input": "CompPoly.CPolynomial.Raw.mul",
 "a": {"version": "HEAD@abc1234", "outcome": "…"},
 "b": {"version": "session variant", "outcome": "…"},
 "verdict": "b-folded" ,
 "pins": {"repo": "…", "dirty": true},
 "notes": "…"}
```

`verdict` ∈ a-kept · b-folded · inconclusive — inconclusive rows are kept
and the variant still dies with the session.

## Fold-back — the experiment's second product

Every settled experiment amends the responsible skill in the same session:
a bake-off arm that surfaced a missing gate amends the stage skill that
lacked it; an A/B's winning text lands in the canonical directory; a
surprising ledger row grows a "failure modes" tooth where it belongs. An
experiment whose lesson stays in the ledger has produced half its value —
the same rule `prove-sorry` applies to itself.

## Invariants to keep green

* `ledger.jsonl` is append-only; every row carries a valid `kind` (or none,
  for candidate verdicts) and honest pins.
* No experiment varies more than one thing; no arm reads a sibling arm's
  artifacts.
* No variant directory survives its session; every settled experiment has
  both its row and its fold-back edit.
* Bake-off conclusions quote the pair (speed, effort) — never a collapsed
  score.
