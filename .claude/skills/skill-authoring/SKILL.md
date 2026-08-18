---
name: skill-authoring
description: Writing, versioning, or composing a skill in this repo — the house SKILL.md shape, git-only versioning with session-scoped A/B variants, compositions-as-skills, one-strategy-one-skill granularity, and the refresh-before-edit policy for the vendored upstream Aeneas suite
---

# Authoring Skills for This Repo

For work on `.claude/skills/` — every skill of the optimization loop lives
there, tracked in git as part of the project. Read this **before** adding,
editing, versioning, or composing a skill. The exemplars for shape and tone are
`aeneas-idiomatic-rust` and `rust-bench`. The vendored upstream files follow
their own meta-rules (`skill-file-authoring` in `aeneas/documentation/skills/`)
where those do not conflict with this file; where they conflict, this file wins.

## The one rule: a skill records lessons, not plans

Every load-bearing section of the two exemplars earns its place with something
that was measured or something that failed — a probe result, a 28% LTO artifact,
a rename that corrupted a proof. A skill written ahead of its experience is
speculation with frontmatter: it reads as authority and misleads with it. Born
thin is fine (see granularity below); padded to look mature is not. And when a
result surprises — a bench verdict, a proof that should have worked, an agent
that misread an instruction — the skill responsible is amended in the same
session, the pattern `prove-sorry` already uses on itself.

## File shape

* One directory per skill: `.claude/skills/<name>/SKILL.md`, kebab-case,
  frontmatter `name:` equal to the directory name, both required fields:

  ```yaml
  ---
  name: kebab-case-name
  description: the load heuristic — see below
  ---
  ```
* **`description:` is the trigger, not a summary.** It is what decides whether
  an agent loads the skill, so it names the *task* ("Adding a criterion
  benchmark for a newly translated operation…"), not the topic ("benchmarking
  notes"). Front-load the words an agent would match on.
* Body sections, in house order:
  1. Title, then a scope preamble: what work this is for, "read this
     **before** X", and pointers to the design docs the skill defers to.
     Designs live in module docs and `README.md`; **the skill holds the
     procedure** — point, do not duplicate.
  2. `## The one rule: …` — the single discipline that dominates everything
     else in the file, stated with the reason it exists.
  3. The procedure and its verdict tables — measured, not guessed; quote
     numbers, name commits.
  4. Failure modes with teeth — what actually went wrong and what it cost.
  5. `## Invariants to keep green` — the closing checklist.
* Cross-reference other skills **by name** (``the `rust-bench` skill``), never
  by path — the upstream convention, and it survives delivery mechanics.
* A rule that must appear in two files has one source of truth; mark the
  derived copy (upstream's `⚠️ SYNC RULE` marker) and re-check it when the
  source changes.

## Invocation contracts

Human-facing entry points are **conversations, not parameterized commands**.
Their human interface is the bare slash name — `/perf-loop`, not
`/perf-loop CompPoly.…` — followed by a short intake that asks one direct
question at a time for every decision the procedure cannot safely infer.
Use the supplied context when it resolves a value, never re-ask it, and
confirm the resolved request before irreversible work. Defaults are stated as
choices; a default is never silently assumed. Do not expose an internal
artifact, flag, or positional-argument syntax to the human interface.

Every human-invocable `SKILL.md` carries an `## Invocation` section before
its one rule or procedure. It states the bare command, the first question and any
conditional follow-ups, then its exact agent packet. A complete agent packet
is the non-interactive interface: the invoking agent supplies named fields
under `agent_request`, the callee validates them, and it proceeds without
asking the human. A missing or invalid packet field goes back to the invoking
agent as a missing-input result; it never leaks into an unrelated human
dialogue. Approval gates that deliberately require human authorization remain
in force in either mode.

Stages and reference skills are agent-only unless the catalogue designates
them as entry points. An agent calling any such skill also supplies its
declared input artifacts explicitly, rather than expecting the callee to
interview a human. Keep the packet names aligned with the skill's input/output
contract, so compositions can pass artifacts directly and a value is never
lost in prose.

## Versioning: git-only, one exception

* **No version fields, no variant directories at rest.** The live version of
  every skill is whatever HEAD holds; history, diff, and blame are git's job.
  Where provenance matters — a ledger row, reproducing a run — pin the *repo
  commit*: `lean-to-rust@abc1234` means "the skill as of that commit".
* **The exception is a live A/B** — directly comparing whether a change to a
  skill is an improvement. Then a variant directory (`lean-to-rust-v2/`) may
  exist beside the original, *within one session only*. Before the session
  ends: settle on a winner, fold it into the canonical directory, delete the
  variant. Two versions of a skill never survive a session, and a variant
  directory is never committed — the losing text lives on in git history,
  which is where it belongs.
* Why so strict: every directory under `.claude/skills/` is offered to every
  agent in every session. A stale parallel version is not an archive, it is an
  alternative trigger target.

## Cleanliness: present tense, no archaeology

* **A skill never mentions its own previous versions.** No version labels in
  prose, headings, or `description:` ("checklist v1"); no "was removed", "used
  to, then we switched", no changelog framing. The live text describes only
  what is true now — what changed and when is git's job, same as the
  versioning rule above, and provenance is pinned as `skill@commit`, never as
  a label in the text.
* This does not touch lessons — failure modes with teeth are the point of a
  skill. The test is whether the sentence binds the reader *today*:
  "cross-run comparison drifts 75–373% on frozen code, so everything compares
  within one run" binds and stays; "the store of past timings was removed"
  is history and goes. When a removed mechanism must be warned against,
  restate it as the present-tense reason it is absent.
* **Concise and intelligible, in that order of repair.** Every sentence
  states a rule, its reason, or its evidence; anything else dilutes the file
  for the agent that loads it. And the reader is an agent with none of this
  repo's session history: plan-phase codenames (`P2`, `?1`) and other
  shorthand never stand alone — name the thing itself ("until
  `verify-campaign` exists", "the maps in `cpoly/lean/Field.lean`") and let a
  codename at most trail it as a pointer into `skills-plan.html`. The fixed
  ledger tag `TODO(P3)` is a tag, not prose, and stays as-is.

## `INSTRUCTIONS.md` is part of every skill change

`INSTRUCTIONS.md` at the repo root is the catalogue: a user-facing overview of
the skills a human invokes and the questions they ask, then a complete
agent-facing table of every skill in `.claude/skills/`. It is the only
skill-related file written for readers outside this directory, and it is
**derived** — the SKILL.md files are the source of truth, so a claim there
that contradicts a skill is a bug in the catalogue, not in the skill.

* **A skill change is not done until the catalogue matches it.** Adding,
  renaming, deleting, or re-scoping a skill — anything that changes what a
  reader would need to know to invoke it — updates `INSTRUCTIONS.md` in the
  same change. The table has one row per directory under `.claude/skills/`,
  so a new directory without a new row is an incomplete change, the same way
  a missing status pill in `skills-plan.html` is.
* **Edits confined to a skill's interior need no catalogue edit.** Growing a
  failure mode, adding a measured table row, tightening a procedure — none of
  that reaches the catalogue unless it changes the skill's audience, its
  inputs, its options, or what it produces.
* **The cleanliness rules above apply to it verbatim**: present tense, no
  narration of removed or superseded versions, no version labels, no bare
  plan codenames, every sentence stating a rule, its reason, or its evidence.
  The binds-today test decides every borderline sentence there too.
* Keep the two halves distinct in kind, not just in position: the user
  overview explains *what work each bare entry point starts and what it will
  ask of you*; the agent table records the corresponding named packets. Neither
  duplicates a skill's procedure — both point at it.

## Compositions are skills

* A named pipeline (the plan's `R1`, `R2`, `R3-a`) is itself a skill —
  `route-r3a/SKILL.md` — whose body is *only* the composition: the ordered
  stages, each naming a stage skill and the artifact contract handed to the
  next (brief in → candidates out → verdict out …). Its `description:` says
  when to run the route.
* **Route skills contain no procedure.** Anything procedural belongs in a
  stage skill — otherwise an A/B between routes cannot tell whether the route
  or the smuggled procedure made the difference.
* A route variant ("`R3-b` = `R3-a` but `lean-to-rust` changed") uses the same
  session-scoped variant mechanics as any other skill, applied to the route
  directory or the stage directory — whichever is the thing under test.

## Granularity: own skill from birth

* Every named strategy — each `opt-*` rewrite strategy, each proving strategy
  — is born as its own skill, however thin. The ledger must attribute a win or
  loss to exactly one skill, and an A/B must bump exactly one. A newborn
  strategy skill carries its *contract* (what it attempts, input → output, the
  opt-contract `Foo.opt` + `Foo.opt_eq_spec`) and grows its lessons from
  ledger rows as they arrive.
* Drivers (`lean-opt`) select and sequence strategies; they contain none.
* The split test for anything else: would the ledger want to blame it
  independently, or a composition want to pin it independently? Then it is its
  own skill.

## The vendored upstream suite

* Seven files from `AeneasVerif/aeneas documentation/skills/` are vendored
  verbatim into `.claude/skills/`, each with a provenance header naming the
  upstream commit (currently `864eddb4`, 2026-04-10): `aeneas-lean-core`,
  `aeneas-tactics-quickref`, `proof-patterns`, `verification-campaigns`,
  `launching-proof-agents`, `lean-lsp-mcp`, `aeneas-crypto-verification`.
* They are copies, not symlinks, because `.claude/skills/` is tracked and the
  `aeneas/` checkout is not — a committed symlink would dangle on any fresh
  clone.
* Not vendored, deliberately: `aeneas-compiler-dev` (compiler-internal; this
  repo consumes aeneas), `agent-fleet-management` (upstream's fleet mechanics;
  orchestration here is the Workflow tool and `prove-sorry`),
  `formalizing-crypto-specs` (upstream CompPoly *is* the spec), and
  `skill-file-authoring` (this file is its local replacement). Cross-references
  to these inside vendored text resolve to `aeneas/documentation/skills/` on
  machines that have the checkout.
* **Refresh before editing** — the same shape as the aeneas fork drift policy:
  before any local edit to a vendored file, `git -C aeneas fetch origin`, diff
  the file against upstream's current version, refresh the copy and its header
  commit first, then apply the local edit on top. Git history then cleanly
  separates "upstream moved" from "we diverged".

## Invariants to keep green

* Every directory under `.claude/skills/` holds a `SKILL.md` whose frontmatter
  `name` equals the directory name, with a `description` that names a task.
* No `-v2` / `-candidate` variant directory exists at rest; none is ever
  committed. End of session means settled.
* Skill prose is present-tense and self-history-free: no version labels, no
  narration of removed or superseded versions, no bare plan codenames — the
  binds-today test from the cleanliness section decides every borderline.
* Every vendored file keeps its provenance header current, and a local edit to
  one lands only after a refresh against upstream.
* `README.md`'s one-line description of `.claude/skills/` stays truthful.
* `INSTRUCTIONS.md` has exactly one table row per directory under
  `.claude/skills/`, and every user-invocable entry point it lists still asks
  the questions and accepts the agent packet it claims.
* A new skill flips its status pill in `skills-plan.html`'s catalog (§4) the
  same day it lands, and a surprising result amends the responsible skill in
  the same session it surprised.
