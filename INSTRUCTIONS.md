# Working with the skills in this repo

This repository turns CompPoly definitions into fast Rust that is *proved* to
compute what the definition says. Two loops do the work: an inner loop that
optimizes an operation and accepts a change only when a benchmark says it is
faster, and an outer pass that proves the optimized Rust equivalent to the
original definition. The skills in `.claude/skills/` are how that work is
carried out — each one is a written procedure an agent follows.

This file is the catalogue. The first half is for **you**, the human: the
handful of skills you would invoke to start a piece of work, and what they
will ask you. The second half is a **complete reference table** of every skill,
for agents to look up mid-task. The skills themselves are the source of truth;
if this file ever disagrees with one, the skill is right and this file is a
bug.

---

## Part 1 · The skills you invoke

### How human invocation works

Start every skill with its **bare slash command**: `/perf-loop`, not
`/perf-loop CPolynomial.Raw.mul`. The command starts a short intake: the skill
asks one direct question at a time, uses information already established in the
conversation, and confirms the resolved request before it begins work. This
keeps a target, route, trigger, or experiment detail from silently disappearing
from the request.

The fields below are questions for humans, not command-line arguments. An agent
calling another skill instead supplies the named `agent_request` packet in that
skill's reference entry; a complete packet skips human intake. An approval gate
that needs your authorization still asks you, whichever way the skill started.

Everything else in `.claude/skills/` is machinery the skills invoke, or
reference an agent consults mid-task.

### Choosing one

| You want to… | Invoke | It first asks |
|---|---|---|
| Bring a CompPoly definition into the pipeline for the first time | `/op-genesis` | Which definition should I onboard? |
| Define unproved Aeneas theorem stubs after extraction | `/aeneas-spec-author` | Which extracted CompPoly operation should I specify? |
| Send substantial Lean proof debt to Aristotle | `/aristotle-prove` | Which files contain the large or genuinely hard proof backlog? |
| Check Aristotle proof sessions | `/aristotle-check` | It checks only recorded sessions; it asks for a fresh key only when a session is active. |
| Fill in one unproved `sorry` | `/prove-sorry` | Which theorem should I prove, or should I list open `sorry`s? |
| Make an existing operation faster (and prove it after) | `/perf-loop` | Which operation should I optimize? Then choose the direct candidate stage. |
| Run a supplied optimization route, or define a new one | `/route-r1` · `/route-r2` · `/route-r3` (or request a new `route-<name>`) | Which operation should it optimize? For a new route: which skills, constraints, or strategy should shape it? |
| Compare routes, or two versions of a skill | `/skill-lab` | Do you want a route bake-off or a skill A/B? |
| Run the whole pipeline unattended | `/autonomy-harness` | Use default `route-r3`, or pin another route? |

### What each one does, and what it asks

**`op-genesis` — onboard a new operation.** Writes a deliberately *naive* first
translation of a definition into `cpoly/src`, tests it, extracts it, and
freezes that first version as the permanent baseline every future speed-up is
measured against. It asks which definition to onboard, then onboards the whole
dependency chain in one pass, dependencies first. Optimizing is explicitly
*not* its job — the first translation is meant to be slow and obvious.

*What it asks of you*: the plan is interleaved, because the stamps record a
commit that must already exist. You commit the translation and the frozen
baseline together, `make bench-stamp` derives the stamps from that commit, you
commit those separately — never `--amend` the first, since a stamp stores its
sha — and only then can the birth benchmark run.

> The freeze is permanent once any number has been published against the item.
> `cpoly/benches/genesis/` is append-only, so freezing an already-optimized
> body would silently report all its gains as zero, forever. This is why
> onboarding and optimizing are separate steps.

**`aeneas-spec-author` — state the extracted operation's proof interface.**
Use this after `/op-genesis` has extracted a new operation, or after a
regeneration makes an existing operation's specs stale. It resolves the
original CompPoly definition and its freshly extracted counterpart, then writes
the aliases, representation functions and invariants, loop specs, and headline
theorem against the original definition. It leaves the theorem bodies as
typechecked `sorry` stubs for `/prove-sorry`; it does not attempt the proofs.

*It asks*: which extracted CompPoly operation needs specs. If the operation
does not identify the destination Lean module or reference definition, it asks
one follow-up, then confirms the resolved request before writing stubs.

**`aristotle-prove` / `aristotle-check` — long-running remote proof work.** The
prove skill starts an asynchronous Aristotle run only for a substantial backlog
or genuinely hard scope, logs it, and returns immediately. The check skill
polls only logged sessions; a verified complete or no-progress result is
integrated, while verified partial progress is resubmitted on its remaining
holes. Each human-requested API operation asks for a fresh, one-time key and
never stores it.

**`prove-sorry` — fill in one unproved theorem.** Audits whether the statement
is even true before trying, decomposes the proof, proves the pieces with
parallel agents, then adversarially attacks its own result. It asks for a
specific theorem or whether to list what is open. Same approval gate as above:
it never weakens a statement without asking.

**`perf-loop` — optimize one operation.** Generates candidate optimizations,
translates them, and measures each against the current champion inside a single
benchmark session, accepting only what is measurably faster at every measured
size. Repeats until a full round of strategies yields nothing.

- *It asks*: which operation to optimize, then, when invoked directly, whether
  candidates come from Lean-side or direct Rust optimization. A route supplies
  that second choice and it is not re-asked.
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

**`route-r1` / `route-r2` / `route-r3` — compose an optimization strategy.**
A route is a named composition through the agent-facing optimization-skill
pool, not an optimizer in its own right. It decides which stages and
strategies participate, their order, where candidates originate, and when
benchmarking and verification occur. The supplied routes below are tested
compositions; `route-r3` is the default, not the only available strategy.

| Route | How it optimizes |
|---|---|
| `route-r3` (default) | Lean-side `opt-*` pool, benchmark after every candidate, then verify each accepted champion |
| `route-r2` | Rust-first `rust-direct` pool within the Aeneas ceiling, bench-steered, then prove the extraction directly |
| `route-r1` | Lean-side `opt-*` pool to a fixpoint, one translation and benchmark at the end |

Invoke a supplied route when it already embodies the strategy you want. To
create another strategy, specify a different subset or ordering of the pool —
or ask an agent to design one from a performance goal and constraints. The
result is a distinct `route-<name>` skill, whose composition stays fixed while
it runs so its outcome is measurable and comparable. Each supplied route asks
only for the operation; a new route also resolves its intended composition
before it is created.

**`skill-lab` — run an experiment.** Two kinds: a *bake-off* comparing whole
routes on one operation, and an *A/B* comparing two versions of a single
skill. It asks which experiment to run; a bake-off then collects the target
and arms, while an A/B collects the skill and its exact suspect sentence. It
runs only when ledger rows already attribute divergent outcomes to that skill
— not curiosity. Arms are metered, never capped — each runs to its natural
finish and the effort is measured, because the cost difference between
approaches is itself the result. It answers with a pair, speed *and* effort,
never a single score.

**`autonomy-harness` — run unattended.** Under `/loop`, each iteration picks the
next operation by how much headroom it has, runs a route end to end, proves the
result, and extends one commit plan. It asks whether to pin a route; an explicit
default selects `route-r3`. It halts loudly rather than degrading: on a
failed proof, on an approval gate, on anything needing a commit you have not
made, when a benchmark reads unusable twice running or the machine looks
contended, or when the corpus is exhausted. New operations never enter the
corpus this way — that stays a deliberate `op-genesis` decision.

### Logs

`logs/ledger.jsonl` is the append-only optimization and verification ledger.
`logs/aristotle-sessions.jsonl` is the append-only record of asynchronous
Aristotle proof sessions. Both are tracked; bulky Aristotle downloads and
snapshots remain ignored under `.aristotle-artifacts/`.

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
make ledger-check     validate logs/ledger.jsonl rows and append-only history
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

In the tables below, an **agent packet** is the named content placed under
`agent_request` when one agent invokes another. A complete packet uses the
non-interactive path; missing fields are returned to the caller, not asked of
the human.

### Entry points

| Skill | Use it when | Agent packet | Produces |
|---|---|---|---|
| `op-genesis` | A definition has no Rust counterpart yet | `target` | Naive translation, semantics tests, frozen genesis baseline + `@genesis` stamps, birth bench case, interleaved commit plan. No ledger row — the stamp is the provenance |
| `aeneas-spec-author` | A new operation was extracted, or a regeneration made its specs stale | `target`, `trigger` (`onboarding` or `regeneration`) | Typechecked `sorry` stubs: aliases, representation functions and invariants, loop specs, headline theorem stated against the original definition, and `Check.lean` audit entries |
| `perf-loop` | An operation should get faster | `target`, `candidate_stage` (`lean-opt` or `rust-direct`; inherited inside a route) | Candidate ledger row per verdict, accepted champion staged on a `champion/<op>` branch, extraction check recorded |
| `route-r3` | Default supplied composition through the Lean-side optimization pool | `target` | Champion + campaign, benchmark deciding each accept |
| `route-r2` | Supplied Rust-first composition through the direct-Rust optimization pool | `target` | Champion via `rust-direct` candidates; specs prove the extraction directly against the definition, with no Lean lemma chain |
| `route-r1` | Supplied Lean-first composition through the Lean-side optimization pool | `target` | One stacked variant, one benchmark at the end; a rejection ends the route |
| `prove-sorry` | A `sorry` needs filling | Exactly one: `target`, or `list_open: true` | Proved theorem, integrated and axiom-audited; folds its own lessons back into itself |
| `aristotle-prove` | A Lean proof backlog is large or genuinely hard | `targets`, with `complex: true` for <=3 hard holes | Asynchronous Aristotle session ID and a `logs/aristotle-sessions.jsonl` record |
| `aristotle-check` | A user asks for a recorded Aristotle session's status | Optional `session_ids` | Status records; verified integration or an asynchronous restart after partial progress |
| `skill-lab` | Comparing routes or skill versions | Bake-off: `kind`, `target`, `arms`. A/B: `kind`, `skill`, `hypothesis`, `input` | `bakeoff` / `ab` ledger rows; owns `logs/ledger.jsonl` and its `kind` schemas; requires a fold-back edit into the responsible skill |
| `autonomy-harness` | Running unattended under `/loop` | Optional `route`; omission explicitly selects `route-r3` | One iteration per target: rows, verified champion, extended commit plan; halts loudly |

### Stages

| Skill | Invoked when | Agent inputs | Produces |
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
| `verify-campaign` | An accepted champion has proof debt, or regenerated extraction leaves a module's specs stale | `trigger` (`champion-accept` · `regeneration` · `from-scratch`), `subject` | Proved and audited module, campaign ledger row with metered effort, and an ordered merge plan |

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
