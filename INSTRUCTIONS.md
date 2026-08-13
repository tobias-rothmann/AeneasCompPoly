# Working with the skills in this repo

This repository turns CompPoly definitions into fast Rust that is *proved* to
compute what the definition says. Two loops do the work: an inner loop that
optimizes an operation and accepts a change only when a benchmark says it is
faster, and an outer pass that proves the optimized Rust equivalent to the
original definition. The skills in `.claude/skills/` are how that work is
carried out — each one is a written procedure an agent follows.

This file is the catalogue. The first half is for **you**, the human: the
handful of skills you would invoke to start a piece of work, and what you can
tell them. The second half is a **complete reference table** of every skill,
for agents to look up mid-task. The skills themselves are the source of truth;
if this file ever disagrees with one, the skill is right and this file is a
bug.

---

## Part 1 · The skills you invoke

Invoke a skill by naming it (`/perf-loop`, or "run the perf loop on
`CPolynomial.Raw.mul`"). Everything else in `.claude/skills/` is machinery the
skills invoke, or reference an agent consults mid-task.

### Choosing one

| You want to… | Invoke | Hand it |
|---|---|---|
| Bring a CompPoly definition into the pipeline for the first time | `op-genesis` | the definition |
| Make an existing operation faster (and prove it after) | `perf-loop` | the operation |
| Run one optimization route end to end | `route-r1` · `route-r2` · `route-r3` | the operation |
| Prove an accepted optimization correct, or verify a module from scratch | `verify-campaign` | the champion branch, or the module |
| Fill in one unproved `sorry` | `prove-sorry` | the theorem (or let it list them) |
| Compare routes, or two versions of a skill | `skill-lab` | the target and the arms |
| Run the whole pipeline unattended | `autonomy-harness` | nothing; optionally pin a route |

### What each one does, and what you can tell it

**`op-genesis` — onboard a new operation.** Writes a deliberately *naive* first
translation of a definition into `cpoly/src`, tests it, extracts it, and
freezes that first version as the permanent baseline every future speed-up is
measured against. Hand it a definition; it onboards the whole dependency chain
in one pass, dependencies first. Optimizing is explicitly *not* its job — the
first translation is meant to be slow and obvious.

*What it asks of you*: the plan is interleaved, because the stamps record a
commit that must already exist. You commit the translation and the frozen
baseline together, `make bench-stamp` derives the stamps from that commit, you
commit those separately — never `--amend` the first, since a stamp stores its
sha — and only then can the birth benchmark run.

> The freeze is permanent once any number has been published against the item.
> `cpoly/benches/genesis/` is append-only, so freezing an already-optimized
> body would silently report all its gains as zero, forever. This is why
> onboarding and optimizing are separate steps.

**`perf-loop` — optimize one operation.** Generates candidate optimizations,
translates them, and measures each against the current champion inside a single
benchmark session, accepting only what is measurably faster at every measured
size. Repeats until a full round of strategies yields nothing.

- *Hand it*: the operation. It never picks a target itself.
- *Accept rule you can rely on*: a candidate is accepted only if every measured
  size reads faster by at least 5% after the harness divides out its own
  measured bias (measured noise reaches 6%, so a verdict just over the line is
  thin). A candidate that is faster at one size and slower at another is
  rejected and reported to you with the numbers, because that is a real
  trade-off and the choice of what to do about it is yours.
- *It may ask*: a candidate that is only equivalent under an input condition
  the original definition does not have needs your sign-off; it is never
  accepted as an ordinary candidate.
- *Proof debt*: every accepted champion is handed to `verify-campaign` before
  the next target is taken up.

**`route-r1` / `route-r2` / `route-r3` — pick the route.** Three ways to reach
the same goal. Each route runs `perf-loop` as its optimization stage and hands
the result to `verify-campaign`; `route-r3` is the default.

| Route | How it optimizes | Speed and effort, per its bake-off arm on univariate `mul` |
|---|---|---|
| `route-r3` (default) | Optimizes in Lean, benchmarks every candidate, proves each accepted one | −48.7% vs genesis at n=256, verified; 3.14M tokens and 115 minutes of metered proving and auditing |
| `route-r2` | Optimizes the Rust directly, within what Aeneas can extract | −83.4% vs genesis at n=256, verified; 5.33M tokens and 300 minutes for the whole arm, and it needed no approval gate |
| `route-r1` | Stacks every Lean optimization first, benchmarks once at the end | No champion: its one benchmark read faster at 256 and 17.5% slower at 64, so a proved lemma chain bought code that will not ship; 1.04M tokens |

Hand any of them the operation. Their behaviour is otherwise fixed — the point
of having three is that they are comparable, so they take no tuning knobs.

**`verify-campaign` — prove an optimization correct.** Takes a champion branch
and drives it to a module where every equivalence spec is proved and audited,
so it can merge. Hand it the champion branch (or any regenerated
`Generated.lean` whose specs broke). It re-extracts, checks the extraction is
deterministic, repairs the specs, proves them, audits that nothing depends on
an unexpected axiom, and records what the campaign cost.

> **It may stop and ask for your approval.** Any change to a theorem's
> statement that makes it assume more or assert less — a new or strengthened
> hypothesis, a weakened conclusion — waits for you; it is never
> self-approved, including under `/loop`. Planning a from-scratch or
> mass-breakage campaign also puts its file and folder structure to you before
> anything is created.

**`prove-sorry` — fill in one unproved theorem.** Audits whether the statement
is even true before trying, decomposes the proof, proves the pieces with
parallel agents, then adversarially attacks its own result. Hand it a specific
`sorry`, or invoke it and let it list what is open. Same approval gate as
above: it never weakens a statement without asking.

**`skill-lab` — run an experiment.** Two kinds: a *bake-off* comparing whole
routes on one operation, and an *A/B* comparing two versions of a single
skill. For a bake-off, hand it the target and the arms. An A/B takes the skill
and the sentence in it you suspect, and runs only when ledger rows already
attribute divergent outcomes to that skill — not curiosity. Arms are metered, never
capped — each runs to its natural finish and the effort is measured, because
the cost difference between approaches is itself the result. It answers with a
pair, speed *and* effort, never a single score.

**`autonomy-harness` — run unattended.** Under `/loop`, each iteration picks the
next operation by how much headroom it has, runs a route end to end, proves the
result, and extends one commit plan. You can pin a route for the session;
otherwise it uses `route-r3`. It halts loudly rather than degrading: on a
failed proof, on an approval gate, on anything needing a commit you have not
made, when a benchmark reads unusable twice running or the machine looks
contended, or when the corpus is exhausted. New operations never enter the
corpus this way — that stays a deliberate `op-genesis` decision.

### Two things every skill here obeys

**Agents stage; they never commit** — settings enforce it, and every loop run
ends by handing you an ordered commit plan.

**Only a benchmark accepts an optimization.** Not operation counts, not
reasoning about what should be faster. Measurements are only ever compared
within one benchmark run, because the same frozen code has measured 75% and
373% apart across runs on this machine.

### The commands underneath

You rarely need these directly — the skills run them — but they are what the
loop runs:

```
make setup            install toolchains and dependencies (once, after cloning)
make build            check the Lean proofs; fails on any error or `sorry`
make test             run the Rust semantics tests
make extract          regenerate cpoly/lean/Generated.lean from cpoly/src/
make run-bench        time every operation against its frozen first translation
make clean            drop build output, keeping fetched dependencies
make check-toolchain  verify the charon/aeneas pin in both directions
make bench-check      verify the frozen baseline against git, and bench coverage
make bench-stamp      re-derive the @genesis stamps after adding a function
```

Useful variables: `BENCH=<regex>` to bench a subset, `JSON=<path>` to write a
machine-readable report, `CANDIDATE=1` to also time the candidate slot (the
optimization loop's A/B), and `CHARON=`/`AENEAS=` to point `extract` at
binaries elsewhere.

> Benchmarking needs the machine to itself. A build running alongside it — from
> this repo *or any other project* — corrupts the measurement, and another
> project's work is invisible to every check this repo can make. So check the
> machine before a run (`ps -eo command | grep -c "[b]in/lean"` plus the load
> average) and wait for someone else's build rather than racing it. The
> harness's own instrument is narrower: when identical code measures more than
> 10% apart it voids the run instead of publishing a number.

---

## Part 2 · Complete reference

Every skill in `.claude/skills/`, by role. **Entry point** = a human may invoke
it directly. **Stage** = invoked by another skill with an artifact handed in;
calling it cold makes little sense. **Reference** = consulted for facts and
verdict tables while doing something else; some carry a procedure of their own,
but nothing invokes them as a pipeline stage. **Meta** = about the skills
themselves.

### Entry points

| Skill | Use it when | Takes | Produces |
|---|---|---|---|
| `op-genesis` | A definition has no Rust counterpart yet | The definition; onboards its whole chain | Naive translation, semantics tests, frozen genesis baseline + `@genesis` stamps, birth bench case, interleaved commit plan. No ledger row — the stamp is the provenance |
| `perf-loop` | An operation should get faster | Target operation; the route in force picks the candidate stage | Candidate ledger row per verdict, accepted champion staged on a `champion/<op>` branch, extraction check recorded |
| `route-r3` | Default optimization of one target | Target | Champion + campaign, benchmark deciding each accept |
| `route-r2` | Rust-first optimization of one target | Target | Champion via `rust-direct` candidates; specs prove the extraction directly against the definition, with no Lean lemma chain |
| `route-r1` | Lean-first optimization of one target | Target | One stacked variant, one benchmark at the end; a rejection ends the route |
| `verify-campaign` | A champion awaits proof, an extraction regenerated and broke specs, or a module needs verifying end to end | Champion branch, a regenerated `Generated.lean`, or a module with no specs yet; trigger kind (`champion-accept` · `regeneration` · `from-scratch`) | Proved + audited module, campaign ledger row with its metered effort, ordered merge plan |
| `prove-sorry` | A `sorry` needs filling | The target theorem, or none (it lists them) | Proved theorem, integrated and axiom-audited; folds its own lessons back into itself |
| `skill-lab` | Comparing routes or skill versions | Bake-off: target + arms. A/B: the skill and the sentence under test | `bakeoff` / `ab` ledger rows; owns `ledger.jsonl` and its `kind` schemas; requires a fold-back edit into the responsible skill |
| `autonomy-harness` | Running unattended under `/loop` | Nothing per iteration; optional route pin | One iteration per target: rows, verified champion, extended commit plan; halts loudly |

### Stages

| Skill | Invoked when | Takes | Produces |
|---|---|---|---|
| `compoly-analyze` | A target needs its optimization brief | The target definition (never chosen here) | Brief: definition chain, semantics risks, cost model, applicable `opt-*` strategies with one line of why each, and representation notes |
| `lean-opt` | Lean-side candidates are wanted | Brief + strategies already tried | Contract-checked candidates (`Foo.opt` + proved `Foo.opt_eq_spec`, axiom-clean, `Check.lean` line). Selects and sequences strategies; contains none itself |
| `rust-direct` | Candidates are Rust diffs (the `route-r2` candidate stage) | Brief + current champion | Rust candidate diffs inside the extraction ceiling, gated by a ceiling audit instead of the opt-contract; deliberately no `opt_eq_spec` |
| `opt-algo-swap` | The brief shows an operation-count or complexity win | Target + brief | A `Foo.opt` variant with its proved equivalence lemma |
| `opt-word-arith` | The brief shows reduction or widening work on the hot path | Target + brief | Word-level variant + lemma; representation changes are gated, not free |
| `opt-inplace-buffers` | The brief shows reallocation or repeated passes | Target + brief | Buffer-shaped variant + lemma |
| `opt-list-to-array` | The brief shows a real `List`, append chain, or per-element allocation | Target + brief | Array-shaped variant + lemma |
| `opt-tailrec-loops` | The brief shows non-tail recursion on the hot path | Target + brief | Tail-recursive variant + lemma |
| `lean-to-rust` | A Lean definition must become Rust | The targeted definition | A trivial-grade translation: an idiomatic shell around a body that mirrors the Lean, plus its bench and test obligations |
| `aeneas-extract` | Rust changed, or extraction must be triaged | The current `cpoly/src` | A regenerated `Generated.lean`, a determinism check, post-extract audits, and a measured row added to the supported-constructs table on every new contact |
| `rust-bench` | A newly translated operation needs a benchmark | The new operation | Frozen genesis entry, a case that measures that operation and nothing else, proved so by adversarial review before any number is trusted |
| `aeneas-spec-author` | A new or regenerated operation needs specs | The extracted model + reference definition | Typechecked `sorry` stubs: aliases, representation functions, loop specs, headline theorem stated against the original definition |

### Reference

| Skill | Consult it for |
|---|---|
| `aeneas-idiomatic-rust` | Which Rust idioms are free, which inject axioms, and how to repair specs after idiomatizing |
| `aeneas-equivalence-bridges` | Whether a spec genuinely needs a relation instead of a function — read it to confirm you do not |
| `aeneas-lean-core` | The translation model, spec patterns, tactics and pitfalls of Aeneas proofs |
| `aeneas-tactics-quickref` | Tactic decision tree, banned tactics, common combinations |
| `proof-patterns` | Canonical proof shapes: the loop template, function wrappers, sub-patterns |
| `verification-campaigns` | Planning large campaigns: from-scratch primitives, mass breakage, recovery |
| `launching-proof-agents` | Multi-agent proof orchestration, review gates, task decomposition |
| `lean-lsp-mcp` | Interactive Lean tooling when the MCP server is available |
| `aeneas-crypto-verification` | Crypto-specific strategies: Montgomery, NTT, modular arithmetic, bit-vectors |

### Meta

| Skill | Consult it for |
|---|---|
| `skill-authoring` | Writing or changing any skill here: the house file shape, git-only versioning, compositions-as-skills, the vendoring policy, and the rule that keeps this catalogue in step with the skills |

### Provenance

Seven skills are vendored verbatim from the upstream Aeneas project, each
carrying a header naming the upstream commit: `aeneas-lean-core`,
`aeneas-tactics-quickref`, `proof-patterns`, `verification-campaigns`,
`launching-proof-agents`, `lean-lsp-mcp`, `aeneas-crypto-verification`. They
are refreshed against upstream *before* any local edit, so history separates
"upstream moved" from "we diverged". `prove-sorry` is vendored from the
user-level skill of the same name; the copy here is the one that loads in this
repo. Everything else is written for this project.
