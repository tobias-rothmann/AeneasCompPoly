---
name: prove-sorry
description: End-to-end workflow for filling a `sorry` in a Lean 4 spec of Aeneas-extracted Rust code (Aeneas triples `m ⦃ r => post r ⦄` relating generated Result-monad code to a reference implementation). First audits whether the statement is even TRUE (hunts for counterexamples such as checked-arithmetic overflow in the Aeneas model), gates any weakening statement change (stronger hypotheses, weaker conclusion) on explicit user approval, decomposes the proof into a typechecked scaffold of sub-lemmas, proves them with parallel Opus agents via the Workflow tool, then adversarially verifies statements, hypotheses, and proofs, and folds lessons back into itself. Use when asked to prove, fill, or fix a `sorry` in an Aeneas verification project (imports of `Aeneas.Std`, `Generated.lean`-style extracted models, `⦃ ⦄` triples).
---

<!-- Vendored from the user-level skill at ~/.claude/skills/prove-sorry so the
     repo's proving engine is git-versioned like every other skill here (the
     project-level copy is the one loaded in this repo). Phase 6 self-improvement
     applies to THIS copy; a lesson general enough for other Aeneas repos is
     worth mirroring to the user-level copy by hand. -->

# prove-sorry — Aeneas spec proofs: audit, decompose, prove, verify, self-improve

Scope: theorems of the shape `f args ⦃ r => post r ⦄` where `f` is
Aeneas-extracted from Rust into the `Result` monad and `post` relates its
output (through a representation function) to a reference implementation. The
triple is `Aeneas.Std.spec`, definitionally `∃ r, f args = ok r ∧ post r` —
TOTAL correctness: every reachable `fail`/`div` falsifies the theorem.

## Invocation

**Human invocation:** start with `/prove-sorry` alone. Ask: **“Which theorem
should I prove, or should I list the open `sorry`s?”** If listing is chosen,
show the candidates and ask the next single selection question. Resolve the
file and declaration before Phase 0; do not silently choose among several
open theorems.

**Agent invocation:** bypass the dialogue with exactly one of these named
requests:

```yaml
agent_request:
  target: <file path and theorem declaration>
```

```yaml
agent_request:
  list_open: true
```

Validate the selected form. Return a missing, ambiguous, or nonexistent target
to the invoking agent rather than asking the human. The statement-change
approval gate below remains a human interaction even in agent mode.

## Division of labor (fixed)

- **You (the main model)** do all the thinking: scoping, statement audit,
  counterexample construction, hypothesis design, decomposition, scaffolding,
  integration, triage, self-improvement, and the final report. Do NOT delegate
  these to subagents. This skill assumes the main session runs on a top-tier
  model; the judgment-heavy phases are not safe to hand to a smaller one.
- **Workflow subagents** do the grinding: sub-lemma proofs and adversarial
  verification run with `model: 'opus'` — provers and audit lenses at
  `effort: 'xhigh'`, repair agents and the completeness critic at `effort: 'max'`.
- **The approval gate — the ONE mandatory authorization interaction after the
  target is resolved.** Any change to the target theorem's statement that makes
  it assume MORE or assert LESS (a new or strengthened hypothesis, a weakened
  or dropped conclusion, a binder change that alters meaning) requires explicit
  approval via `AskUserQuestion` BEFORE it is introduced — in any phase,
  including verification triage. A purely additive strengthening of the
  conclusion (extra conjunct, hypotheses unchanged) may be applied
  autonomously but must be flagged prominently in the report. Everything else
  runs without asking.

## Phase 0 — Scope (main loop)

1. Locate the target `sorry` (from the skill args, or grep the file/repo). If
   no target was named and several sorries exist, list them and ask which to
   take (allowed despite the no-questions default); never silently pick one.
2. Read: the target theorem and everything it mentions; the extracted model
   (the Aeneas-generated Lean) AND the Rust source it came from; the reference
   implementation and its lemma library; neighboring proofs in the same file
   (they define the required style and idioms — loop specs, `step` usage,
   representation functions and invariants).
3. Run `lake build` ONCE so the library `.olean`s are fresh. If it fails or
   would compile a huge dependency from source, fetch caches if supported
   (`lake exe cache get`), otherwise stop and report — build repair is a
   different task.
4. Probe the API: write a scratch file of `#check`/`example` lines for
   everything the plan will lean on — `Aeneas.Std.loop.spec_decr_nat`,
   `spec_bind`/`spec_mono`/`spec_ok`/`spec_imp_exists`, `Vec.push_spec`,
   `Vec.index_usize_spec`, `Vec.index_mut_usize_spec`, the project's
   field/scalar op specs, representation-function lemmas, instance synthesis.
   Compile it with `lake env lean <probe-file>` and time the run — the
   iteration cost you will quote to agents. `lake env lean` does not write to
   the build dir, so agents can run it concurrently; `lake build` takes the
   Lake lock and is later forbidden for agents. Facts fed to agents must be
   compiler-verified here, not guessed.
5. Grep the whole workspace for downstream users of the target theorem so a
   signature change cannot silently break callers.

## Phase 1 — Audit the statement BEFORE proving anything

Adversarially examine whether the theorem is true as stated. The Aeneas model
is where specs die; walk EVERY operation on EVERY path and ask what makes it
`fail`:

- **Checked scalar arithmetic:** every `let i ← a + b` (or `-`, `*`) on
  `UScalar`/`IScalar` fails on overflow — and intermediates count: `a + b`
  can overflow even when the final `a + b - 1` fits. Size intermediates by
  what the code actually allocates, not by the inputs: divide-and-conquer
  code pads by a working width (a `max` of sizes), so a sum-of-input-sizes
  hypothesis can hold while an intermediate twice the max overflows.
- **The `Vec` over-approximation:** `alloc.vec.Vec α =
  { l // l.length ≤ Usize.max }` — maximal-length vectors are legal terms no
  machine holds, sums of lengths overflow `Usize`, and counterexamples built
  from them still falsify the theorem.
- `Vec.push` fails at length `Usize.max`; `index`/`index_mut` fail out of
  bounds — check the invariants actually cover every read/write index.
- Representation invariants (e.g. "every word `< P`") — are they strong enough
  to discharge the no-overflow side conditions of the field ops?
- Quantifier direction; vacuity (are the hypotheses jointly satisfiable?);
  canonicalization/trimming conventions differing between model and reference.

**If you find a counterexample:**

1. Machine-check it in a **scratchpad** file: prove `¬ (original statement)`
   outright. Recipe: build the witness values (the `Vec` subtype accepts
   `⟨List.replicate Usize.max x, by simp⟩`), characterize the failing
   operation via its `_equiv` lemma (e.g. `UScalar.add_equiv`: `ok` implies
   the sum is in bounds), and refute the triple via `spec_imp_exists`. Never
   claim falseness from intuition alone; check the closure with `#print axioms`.
2. Design the repair: the **weakest natural hypothesis** that makes the
   statement true. Test minimality — try to break each strictly weaker form
   (an intermediate checked add usually forces the stronger bound).
3. **Enter the approval gate.** Ask via `AskUserQuestion`, presenting: one
   concrete counterexample, the proposed hypothesis, why it is minimal, and
   alternatives. Offer at least: "Add `<hypothesis>` (Recommended)", "Different
   repair", "Keep statement unchanged" (then report the disproof and stop). If
   `AskUserQuestion` is not among your tools or the call errors, treat the run
   as non-interactive: make NO statement change, keep the disproof in the
   scratchpad, and end the run with the counterexample and proposed repair as
   the deliverable.
4. After approval, the new statement lives ONLY in the Phase-2 scaffold until
   Phase 4 — no repo file is edited before integration. Keep the disproof in
   the scratchpad; the theorem's docstring (written in Phase 4) records why
   the hypothesis is necessary, why it cannot be weakened, and — for `Vec`
   over-approximation cases — that it is a model artifact, not a Rust bug
   (real vectors are capacity-bounded by `isize::MAX` bytes). Do not add a
   disproof file to the repo unless asked; offer it in the report.

If the statement is fine as-is, say so in the report and continue.

## Phase 2 — Decompose and scaffold (main loop)

1. Split the proof into sub-lemmas. The seams for Aeneas code:
   - one lemma per generated `*_loop` function, proved via
     `loop.spec_decr_nat` with a decreasing `Nat` measure (typically
     `n.val - i.val`) and an invariant tying the accumulator's image under the
     representation function to the processed prefix — or, for in-place
     writes, a pointwise characterization;
   - pure math bridges (Finset/algebra reasoning) separated from the monadic
     plumbing, e.g. an invariant-carrying `def` (partial-sum function) with
     `_zero`/`_succ` step lemmas;
   - shared representation helpers (in-range/out-of-range coefficient lemmas)
     proved up front.
   Flag as hardest the lemma that breaks the file's usual pattern (e.g. a
   pointwise `Vec.set` update where everything else is prefix-append).
2. Write a **scaffold file** in the scratchpad: imports the built library,
   proves the shared helpers outright, states every sub-lemma with a `sorry`
   body — including the (approved) new statement of the target. Iterate until
   it typechecks; this locks the interfaces so parallel proofs must compose.
   If a sub-lemma cannot be stated standalone (private defs, section
   variables), restate it with all binders explicit; if the environment
   genuinely cannot be reproduced in a scratch file, give each agent its own
   COPY of the real file as the work file (its out file then holds the full
   modified declaration text).
3. Assign attempt counts: 1 for routine pieces, 2 independent attempts (one
   skeleton-following, one diversity-seeking) for the hard ones.

## Phase 3 — Prove in parallel (Workflow tool)

Adapt `references/prove-workflow.js` (read it first — its header documents the
Workflow DSL contract it relies on). If the Workflow tool is unavailable in
this session, run the same prompts as parallel Agent-tool calls, pasting each
JSON schema into the prompt and requiring the reply to be exactly one matching
JSON object (validate it yourself); with no subagent mechanism at all, prove
the lemmas sequentially yourself and say so in the report. Key contract:

- Each prover: `model: 'opus'`, `effort: 'xhigh'`. It copies the scaffold to a
  **private** work file, replaces ONLY its own lemma's `sorry` (other sorried
  lemmas usable as black boxes), self-verifies with `lake env lean`, and
  writes a pasteable final text (helpers + theorem, no imports) to a private
  out file.
- Hard rules in every prompt (full list in the template's PREAMBLE): never modify
  repo files, the scaffold, or `.lake`; never run `lake build`; never change
  any theorem STATEMENT (report a counterexample instead if convinced one is
  false); no `sorry`, `native_decide`, new `axiom`s, or other escapes.
- Success criterion, stated exactly: zero `error:` lines from `lake env lean`,
  and the `declaration uses sorry` warning for the agent's OWN lemma gone
  (warnings for the other scaffold lemmas are expected).
- Structured output: `{lemma, compiles, outFile, workFile, helperNames, notes}`
  — `notes` carries surprises and, on failure, the exact remaining goal.
- Feed each prompt the Phase-0 verified API facts, the reading list (neighbor
  proofs to imitate), and the appendix gotchas.
- Escalation: a lemma with no compiling attempt goes to a repair agent
  (`model: 'opus'`, `effort: 'max'`) that reads the failed work files first.

**If a lemma still has no compiling proof after repair:** prove it yourself in
the main loop. If a prover credibly reports a counterexample to a SUB-lemma,
the decomposition is wrong — return to Phase 2 (and if the flaw traces to the
target statement itself, re-enter the approval gate). Never integrate a
partial proof: if genuinely stuck, leave the repo untouched and report the
compiling sub-lemmas as partial progress.

## Phase 4 — Integrate (main loop)

This is the first phase that edits the repo (the approved statement change
included). If any repo file was edited earlier for any reason, re-run
`lake build` before trusting agent results — they verified against the
Phase-0 `.olean`s.

1. Merge the winning variants into the real file (fewest helpers, closest
   style match); sparse comments only for non-obvious constraints. An out
   file may end in a term-mode proof (`:=` term, no `by`) — splice the body
   as written rather than forcing a `by` wrapper. If a merged
   proof fails there, the usual cause is opens/namespace/variable-block
   mismatch, not the proof — fix qualification yourself; else fall back to the
   lemma's other compiling attempt; else re-run a single-lemma workflow
   against a scaffold mirroring the real context.
2. Update everything the change makes stale: module docstring, roadmap
   comments, the target theorem's docstring (hypothesis justification lives
   here).
3. Make integrated helpers load-bearing or delete them — no dead declarations.
   Be deliberate about attributes (`@[simp]` on a new lemma is a global API
   change) and about what is `private`.
4. Full `lake build` — must succeed.
5. Axiom hygiene: `#print axioms` on the new theorem AND every other theorem
   in the file must show only `[propext, Classical.choice, Quot.sound]`. This
   is not vacuous — the Aeneas stdlib itself contains `sorry`s that would
   surface here as `sorryAx`. Also grep the file for
   `sorry|native_decide|axiom|implemented_by|unsafe|maxHeartbeats`.

## Phase 5 — Adversarial verification (Workflow tool)

Adapt `references/verify-workflow.js`: four independent audit lenses
(`model: 'opus'`, `effort: 'xhigh'`) plus a completeness critic
(`effort: 'max'`) that adjudicates, spot-verifies load-bearing claims, and
does whatever nobody checked. Auditors verify with `lake env lean` only; the
integrity lens alone may run `lake build`. Lenses:

1. **Faithfulness & vacuity** — does the statement assert what a reader wants
   (the Aeneas triple carries SUCCESS — confirm no vacuous reading)? Is each
   sub-lemma's hypothesis set satisfiable? Instantiate concretely.
2. **Hypothesis audit** — necessity (re-check the disproof), minimality
   (attempt weaker forms in scratch), sufficiency (enumerate EVERY `fail`/
   `div` point on the code path — checked arithmetic, pushes, indexing — and
   confirm the hypotheses exclude each), downstream breakage. If no statement
   change was made, repurpose this lens: audit the ORIGINAL hypotheses for
   sufficiency and downstream impact, and whether the theorem could be stated
   more strongly.
3. **Empirical cross-check** — `#eval` both sides on concrete inputs: the
   extracted function (expect `ok …`) against the reference implementation.
   Cover empty/degenerate, small generic, and the domain's edge behavior
   (modular wraparound near the prime, inputs where canonicalization/trimming
   fires). Any disagreement is critical. `native_decide` stays banned.
4. **Proof integrity** — build, axiom closure of every theorem, hidden
   escapes, composition seams (invariant seeds match what producers
   guarantee), loop measures genuinely decrease.

Triage yourself: **fix critical and major findings before reporting.** A known
major pattern: a new precondition without a matching postcondition breaks
self-composition — if chaining the theorem needs facts about the OUTPUT,
extend the postcondition and prove a chaining `example` in scratch. Any triage
fix that changes the target statement goes back through the approval gate
(additive conclusion-strengthening is the one autonomous exception — flag it
in the report). Minors and nits: mention in the report, fix only the cheap
ones.

## Phase 6 — Self-improve this skill (main loop, every run)

This skill maintains itself. Before writing the report — after every run,
successful or not — fold what the run taught into these files.

1. Harvest candidates: gotchas that cost an agent a failed compile or a
   round-trip; Aeneas/Mathlib facts that had to be discovered mid-run;
   template bugs or prompt ambiguities; claims in this skill that proved wrong
   or stale; attempt-count calibration.
2. Filter: admit a lesson ONLY if it helps on a *different* Aeneas repo;
   project-specific facts go to that project's CLAUDE.md or memory, never here.
3. Edit `SKILL.md` and `references/*.js` in place, integrating each lesson
   exactly where a future reader needs it — a phase step, a hard rule, an
   appendix bullet, a template comment.
4. Litter contract — non-negotiable:
   - The files must always read as written fresh, in one sitting, by one
     author: imperative voice, present tense, no seams.
   - No meta-commentary of any kind: no dates, no "learned/discovered/
     updated", no changelog, no version markers, no references to earlier
     revisions of this skill or to particular sessions, users, or projects.
   - Replace, never append: a lesson refining an existing line rewrites that
     line; a lesson contradicting existing text deletes the loser. One idea,
     one place.
   - Prune every pass: merge overlapping bullets, delete anything stale.
     Deleting a wrong claim is itself an improvement — never keep known
     misinformation because no replacement is ready.
   - Hard budgets: `SKILL.md` ≤ 300 lines; appendix ≤ 15 bullets and ≤ 40
     lines, one lesson per bullet; each template ≤ 200 lines. Over budget →
     drop the least valuable content, do not compress into unreadability.
   - Protected invariants — may be tightened, never weakened or removed: the
     approval gate, the division of labor, the agents-never-`lake build` rule,
     the forbidden-escapes list, and this litter contract including this
     bullet.
5. Verify: re-read each edited file for exactly two things — it stands alone,
   and nothing betrays its edit history; if a reader could reconstruct "what
   changed this run" from the prose, rewrite until they cannot.

## Phase 7 — Report

Lead with the outcome. Then: statement verdict (true as-is / repaired, with
the counterexample and why the hypothesis is minimal); the decomposition; what
the audit found and what you fixed; axiom-closure result; remaining warnings;
the disproof-file offer if applicable; skill updates made in Phase 6 (one
line). Complete sentences — the reader did not watch the run.

## Appendix — prover-prompt gotchas (feed these to every prover)

- After `rintro ⟨a, b⟩` on a loop-state invariant, hypotheses keep unreduced
  projections `(a, b).1`/`(a, b).2` that `omega` treats as opaque atoms (while
  `scalar_tac` may cope). Fix: `rintro ⟨a, b⟩ hinv` then re-ascribe by defeq:
  `obtain ⟨h1, h2, …⟩ : <explicitly beta-reduced conjunction> := hinv`.
- Goals after `step` in loop bodies come out as FLAT right-associated
  conjunctions (invariant conjuncts + measure): use flat `refine ⟨_, _, _, _⟩`
  shapes; nested anonymous constructors mismatch.
- Put bound facts in context BEFORE the step that needs them:
  `have : idx.val < len := by scalar_tac`, then `step as ⟨…⟩`.
- `Vec.index_mut_usize_spec` has a BINARY postcondition (value + write-back
  function): destructure `step as ⟨x, back, hx, hback⟩`, then `subst hback` to
  expose `v.set idx`; `Vec.set_val_eq` (simp) turns it into `List.set`.
- Pointwise-update invariants: characterize the whole updated abstraction once
  (`have : ∀ k, coeff (set …) k = if k = idx then new else old k`) via
  `List.getElem_set` + in/out-of-range coefficient lemmas, then case-split.
- `rw` fails on `l[i]` under a list equality (dependent motive) — use a
  `getElem_of_list_eq`-style helper if the file has one.
- Nat subtraction truncates: guard convolution-style sums with `if i ≤ k` and
  reach for `omega` on every side condition.
- Scalar types carry their range in the type: `n.val ≤ Usize.max` is free,
  `scalar_tac` knows it, and `Vec.push_spec` wants `length < Usize.max` given.
- A self-recursive Rust `fn` extracts as `def … partial_fixpoint`, not a
  `@[rust_loop]`: Lean generates an `.eq_def` unfolding equation for it —
  prove its spec by strong induction on the width/size argument, unfolding
  one step per level, mirroring the reference function's own induction.
- In-place write loops whose reference function is defined by the same
  recursion the loop runs: skip the pointwise-coefficient invariant and use
  the conserved-value form — "reference-fn applied to the current buffer
  from the current index equals reference-fn applied to the initial buffer
  from the start index". It composes by `rfl`-like rewriting where the
  pointwise form needs a case-split per write.
