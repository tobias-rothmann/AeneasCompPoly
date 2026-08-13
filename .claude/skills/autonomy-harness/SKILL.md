---
name: autonomy-harness
description: Running the optimization loop unattended under /loop — one iteration picks the next target by brief headroom over the genesis corpus, runs the chosen route (default route-r3) through perf-loop and its K=1 verify-campaign, appends ledger rows, and extends the ordered commit plan; halts on proof failure, approval gates, dependence on unmerged staged work, or an exhausted corpus; use when asked to run the loop autonomously, start an unattended optimization session, or put the pipeline under /loop
---

# The Autonomy Harness (/loop v1)

How the pipeline runs without a user driving each stage: a `/loop` session
in which each firing performs (or continues) **one iteration** of the loop
below. This is deliberately the supervised form — the session is watchable
and interruptible, and its gates block rather than self-approve. Scheduled
routines and CI triggers have no procedure here on purpose: they get one
only after the loop has proved itself under supervision, and the ledger
rows from these runs are that proof.

## The one rule: the loop never outruns its debt

K=1 holds inside the loop: an iteration is target → accepted champion →
**verified** champion, and the next iteration starts only if its target
does not depend on unmerged staged state. Agent sessions cannot commit
(user settings enforce stage-only), so every iteration *extends one ordered
commit plan* rather than landing anything; a second iteration on the same
module would build on an uncommitted foundation and is therefore a halt,
not a queue. The loop's output is verified champions plus a commit plan the
user executes — never a pile of unverified speed.

## One iteration

1. **Target selection.** Corpus = every operation with a genesis item in
   `cpoly/benches/genesis` (new operations enter the corpus only through a
   user-triggered `op-genesis`, never from inside the loop). Exclude
   operations with an open champion branch or staged unmerged work. Rank
   the rest by algorithmic headroom from fresh `compoly-analyze` briefs —
   targets are never hardcoded. Nothing rankable → halt "corpus exhausted".
2. **Route.** Run `route-r3` on the selected target unless the user pinned
   a different route for the session. The route's own stages produce the
   candidate rows, the champion, and the campaign row.
3. **Bookkeeping.** Verify the iteration left: candidate rows for every
   benched candidate, one campaign row, `make bench-check` green, and the
   commit plan extended with this iteration's ordered steps (champion
   branch material, merge, any post-merge `make bench-stamp`).
4. **Report.** One user-visible summary per iteration: target, verdicts
   with numbers, campaign result, what the commit plan now contains.

## Pacing under /loop

* An iteration spans hours; /loop firings are checkpoints, not iterations.
  On each firing: if a stage is still running, `noop` with a long delay
  (the machine-serialization rule makes polling useless — benches and
  `lake build`s cannot be parallelized anyway); if a stage just finished,
  advance to the next; if the iteration closed, start the next one at
  step 1.
* **Machine serialization survives autonomy.** One criterion session or
  Lean build at a time, loop-wide — an unattended run is the easiest place
  to violate this silently, and it corrupts both measurements.

## Halt conditions — halt loudly, never degrade

* `verify-campaign` result ≠ `verified` → halt; the partial/blocked row and
  the blocking lemma go in the iteration report. The loop does not take a
  new target on top of unpaid debt.
* An approval gate (e.g. `prove-sorry`'s statement-weakening gate) → block
  on the user; the gate exists precisely for the unattended case and is
  never self-approved.
* Next viable target depends on unmerged staged work → halt "waiting on
  commit plan"; resumption is the user executing the plan.
* Bench verdict `unusable` twice in a row, or any sign of machine
  contention → halt; the weather is not optimized around.

## Invariants to keep green

* Stage, never commit — the loop ends (or halts) with staged changes and
  one ordered commit plan covering every iteration it ran.
* No iteration starts on unpaid proof debt or unmerged same-module state.
* Every iteration is fully accounted: its candidate rows, its campaign row,
  its commit-plan extension, its one-summary report.
* Gates block; nothing is auto-approved because nobody was watching.
