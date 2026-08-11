---
name: op-genesis
description: Onboarding a new CompPoly operation into the loop — creating the naive (trivial-grade) first translation in cpoly/src and freezing it into the genesis baseline; chain closure, semantics tests, extraction pass, verbatim freeze + birth bench case, and the interleaved stage-only commit plan the stamp mechanics force; use when asked to translate a new CompPoly definition, create a naive translation, onboard an operation, or put a first translation into genesis
---

# Onboarding an Operation: Naive Translation → Genesis

For a targeted CompPoly definition that has no counterpart in `cpoly/src`.
This is the stage *before* `perf-loop` — §5 of `skills-plan.html` opens with

    champion ← trivial translation of the CompPoly def
    baseline ← criterion(champion)

and this skill owns those two lines. The target is handed in (user or route
skill); choosing it is not this skill's job. An orchestrator in the
`perf-loop` mold: every stage procedure lives in its own skill —
`compoly-analyze` (the brief), `lean-to-rust` (the translation), `rust-bench`
(freeze, case, audit, runs), `aeneas-extract` (the extraction pass) — this
file holds only the ordering, the artifact contract each stage hands the
next, and the two things that exist only at the composition level: the
validate-before-freeze discipline and the stage-only commit choreography.

## The one rule: everything is validated before the freeze, because after it nothing can be repaired

`benches/genesis/` is write-once (its `lib.rs` contract: never edited,
append only). Two distinct mistakes become permanent at the moment of the
copy:

* **Freezing a semantics bug.** The `case!` digest oracle compares `now`
  against `genesis`, and at birth they share any bug — no signal. The bug
  surfaces only when the *fix* lands in `cpoly/src`: from then on the digest
  assert panics the whole bench file, and the only way out is editing
  genesis. So the independently-written semantics tests (the house pattern
  in `cpoly/tests/*_semantics.rs`: references computed in `u128` so a `u64`
  overflow mismatches instead of being reproduced, plain convolution instead
  of the unrolled fold, `Σ_i p[i]·x^i` instead of Horner) are the *only*
  oracle the freeze gets. They go green before the copy, always.
* **Freezing anything other than the spec's trivial translation.** Genesis
  is the zero point of the fitness function; freeze an improved version and
  its gains read zero forever, undetectably (`rust-bench` §1). The thing
  frozen is the trivial-grade translation of the CompPoly definition
  itself — never an `Opt.lean` variant, never a body improved while
  translating. Ideas that arrive during translation are filed for
  `perf-loop`, not acted on (`lean-to-rust`'s rule, applied at the
  composition level).

If a defect slips past both and is caught at birth — before any run has been
reported against the item — the honest repair is an immediate re-freeze:
replace the frozen text with the fixed first translation, re-stamp against
the fixing commit, and say so in the commit. That rewrites no measurement
history because there is none yet. Once numbers have been published against
the item there is no honest repair; that is why the rule sits at the top of
this file.

## The composition

1. **Brief** — `compoly-analyze` on the target. Its definition chain is the
   work list: every def in the chain missing from `cpoly/src` is onboarded
   too, dependencies before dependents (one def = one fn, so a dependent's
   body calls helpers that must already exist). Defs already in `cpoly/src`
   are reused as they are — calling an already-optimized champion helper is
   fine; that gain being contained in the new op's `vs genesis` is the
   defined meaning of that column (`perf-loop`). The brief's opt-* section
   is filed for later, per the one rule. Batch the whole chain into one
   pass: one commit plan, one birth run (~18 min each).
2. **Translate** — `lean-to-rust` per def, bottom-up: the six enumerated
   moves, `Mirrors` line naming the spec identifier at the pinned rev, house
   shell. Collect the spec debt as you go: every new *public* op owes an
   Aeneas `_spec` it will not get until P3's `aeneas-spec-author` exists —
   the debt is named in the commit plan (`TODO(P3)`), never silent.
3. **Oracle** — extend `cpoly/tests/<module>_semantics.rs` in the house
   pattern (each test states the CompPoly definition's mathematical
   property; the reference is written deliberately *unlike* the crate).
   `cargo test` green, `cargo clippy --all-targets` clean under pedantic —
   before anything is frozen.
4. **Extraction pass** — `aeneas-extract`: deterministic, zero axioms, loop
   shapes, name skim; finish with the proof re-check (`make build`), since
   the additive regeneration of `Generated.lean` must not move any existing
   `_spec`. This runs *before* the freeze because a ceiling failure reshapes
   the translation within the six moves — i.e. changes the text that would
   have been frozen. An unsupported construct that no reshape avoids is a
   stop-and-surface: the op cannot enter the loop yet.
5. **Freeze, case, slot** — `rust-bench` §1–§2 minus its git commands: copy
   the new items verbatim (copy, never retype) into
   `benches/genesis/src/<module>.rs`; a case with `@covers` per public op, a
   by-name exclusion with a checkable reason otherwise (private helpers get
   the structural exclusion — "private; measured through `<op>`'s rows", the
   2026-08-11 Karatsuba helpers are the exemplar). Then sync the candidate
   slot: byte-copy the changed `cpoly/src` files over
   `benches/candidate/src/` — `check-candidate` pins slot ≡ src, so a new
   item breaks `make bench-check` until the copy lands.
6. **The interleaved commit plan** — next section; ends with
   `make bench-check` green.
7. **Birth run + audit** — `rust-bench` §3–§5 unchanged: the filtered
   shake-out run, the adversarial case audit, then one full
   `make run-bench`. **At birth the new op's rows must read noise**: `now`
   and `genesis` are byte-identical for it, so any significant delta is a
   defect in the freeze or the case (an adapter doing work, a degenerate
   input, a wrong copy), never a result. The P1 exit test measured exactly
   this shape: a from-scratch re-derivation benched digest-identical at
   +0.7%, inside the threshold. Audit findings that change the *case* are
   normal post-commit edits; findings that change the *item* take the
   re-freeze carve-out above.
8. **Handoff** — the naive translation is the champion, genesis is its
   baseline, the brief already exists: the op is loop-eligible and
   `perf-loop` takes it from here. No ledger row is written — the ledger
   records candidate verdicts; an onboarding's provenance is the
   `@genesis <sha> <date>` stamp itself.

## The commit choreography (stage-only)

Three enforced mechanics fix the shape; none can be worked around:

* `stamp-genesis` refuses text that is in no commit ("no commit contains
  this text verbatim") and refuses a match that exists only in the dirty
  working tree at HEAD (`harness.py`);
* `check-genesis` fails while any live item lacks a frozen *and stamped*
  counterpart;
* `make run-bench` hard-gates on `check-genesis` (Makefile: "statistics
  cannot rescue a corrupted baseline") — so there is no pre-commit bench
  number, and stages 6–7 cannot be reordered around it.

Under the no-agent-commit settings (`git commit` is blocked; a chained
`add && commit` stages nothing), the session stages and the user commits, so
the plan interleaves:

1. *(agent)* stage everything from stages 2–5: `cpoly/src`, tests, the bench
   case, the **unstamped** genesis copy, the slot sync.
2. *(user)* commit 1 — all of it, one commit: the genesis `lib.rs` contract
   wants the item added to `cpoly/src` and to genesis in the same commit,
   and the stamp will name this sha.
3. *(either)* `make bench-stamp` — derives `// @genesis <sha> <date>` from
   commit 1; stage the annotations.
4. *(user)* commit 2 — the stamp lines alone. Never `--amend` commit 1
   instead: the stamp stores commit 1's sha, and an amend orphans it.
5. `make bench-check` green → stage 7 can run. If the session ends at
   step 1, steps 2–5 and stage 7 are the written plan's tail, in this order.

## Failure modes with teeth

* **Freezing an already-optimized body.** The one failure invisible from the
  numbers forever after — `rust-bench` §1 owns the late-recovery procedure
  (`git show` the *original* text); at the composition level the trap is
  starting stage 2 from `Opt.lean` or "improving while translating".
* **A shared semantics bug at birth.** The digest oracle is parity, not
  truth: it catches a stale or divergent *copy* (frozen ≠ src → panic on the
  first run), but a bug present in both variants sails through and detonates
  under the future fix. The stage-3 tests are the only birth oracle — which
  is why they are written against independent references, never against the
  code under test.
* **Forgetting the slot sync.** `make bench-check` fails on
  `check-candidate` the moment `cpoly/src` gains an item the slot lacks.
  Byte-copy, same change, every time.
* **A new module, not just a new item.** `MODULES` is a fixed tuple in
  `harness.py` (`field`, `univariate`, `multilinear`); a fourth module means
  extending it, the slot's exactly-four-files check, genesis's `lib.rs`, a
  declared `[[bench]]` (`autobenches = false`: an undeclared bench file is
  *silent* — `rust-bench`), and the corpus in `support/`. Untraveled as of
  2026-08-11 — the three modules were born with the harness. Expect to amend
  this skill the first time it happens.
* **Working around the run-bench gate.** A "quick number" from `cargo bench`
  before the commits exist has no genesis variant, no control, no
  threshold — it is exactly the un-validated absolute time `rust-bench`
  forbids reasoning from. The gate order is the design; wait for the
  commits.

## Invariants to keep green

* What genesis receives is the trivial translation of the *spec* definition,
  tests-green and extraction-clean before the copy, byte-identical to
  `cpoly/src` at commit 1.
* Chain closure: every def the target depends on exists in `cpoly/src`
  (reused or onboarded) before the target itself.
* Every new item is benched or excluded by name with a checkable reason;
  `make bench-check` green at the end of the choreography.
* The birth run's rows for the new op read noise, and the case survived the
  `rust-bench` §4 audit before any number from it is believed.
* Spec debt of every new public op is named in the commit plan (`TODO(P3)`).
* The session ends with staged changes and the interleaved plan — never a
  commit (user settings enforce it).
* No ledger row for an onboarding; the `@genesis` stamp is the provenance.
