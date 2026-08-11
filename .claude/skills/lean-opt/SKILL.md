---
name: lean-opt
description: Driver for the Lean-side optimization stage — given a targeted CompPoly definition and its compoly-analyze brief, select opt-* strategies (highest tier first), fan out one prover agent per strategy, and enforce the opt-contract (Foo.opt in Opt.lean + proved Foo.opt_eq_spec, axiom-clean) on every candidate; produces candidates for perf-loop to translate and bench
---

# Driving the Lean-Side Optimization

For stage B of the loop: a target definition and its brief (`compoly-analyze`)
come in; contract-satisfying candidates come out, ready for `lean-to-rust`.
The target arrives from upstream (`perf-loop`, a route skill, the user);
choosing it is not this skill's job. This driver selects and sequences the
`opt-*` strategy skills and **contains no strategy of its own** — anything
procedural about a rewrite belongs in the strategy skill, or the ledger
cannot attribute wins.

## The one rule: no lemma, no candidate

A fast def without its proved `opt_eq_spec` is not a candidate, it is a
liability — the lemma is the down payment that keeps the eventual Aeneas
proof at trivial-translation distance (the project's R3 bet). Reject outright
(`lemma-failed`), record the ledger row, move on. Never forward an unlemma'd
def to translation "to see how fast it would be": the bench slot it burns is
cheap, but the precedent — champions the proof layer cannot pay for — is the
exact debt spiral the inner loop exists to prevent.

## The opt-contract (source of truth)

Every candidate consists of a change to `cpoly/lean/Opt.lean` (or an
upstream-variant reference, see below), its `Check.lean` §15 audit line, and
a candidate note. In full:

1. **Placement + naming.** `Foo.opt` is declared in `cpoly/lean/Opt.lean`,
   its name extending the original (`CPolynomial.Raw.mul.opt`), at the
   weakest typeclass that supports it. Strengthening the class (`Semiring` →
   `Ring` for Karatsuba's subtraction) is allowed when `F` satisfies it; the
   note says why it was needed.
2. **The lemma.** Same carrier: `Foo.opt_eq_spec : ∀ …, Foo.opt … = Foo …`.
   Word carrier (`opt-word-arith`): the commutes-through-representation form
   `toK (Foo.opt w) = Foo (toK w)` under `Red`/`Reduced`, using only the
   representation maps the spec files already own (`toK`, `toExt`, `toRaw`
   in `cpoly/lean/`).
3. **Proof discipline.** Sorry-free; `#print axioms Foo.opt_eq_spec` shows at
   most `[propext, Classical.choice, Quot.sound]`. `native_decide`
   (`Lean.ofReduceBool`/`Lean.trustCompiler`) is banned — it would add the
   Lean compiler to the TCB the README table does not include, and upstream
   CompPoly bans it too. The `#print axioms` line lands in `Check.lean` §15
   in the same change.
4. **Translatable body.** The def stays inside `lean-to-rust`'s conventions
   table — it will be translated *unchanged*. A shape needing a new
   correspondence names it in the note (the row lands in `lean-to-rust` on
   acceptance); a shape that cannot be trivially translated is
   `not-translatable`, rejected.
5. **No new value-level preconditions without a gate.** A variant equal to
   the spec only under an input hypothesis the original does not have makes
   the eventual composed theorem weaker and can fail the bench's
   digest-equality on arbitrary corpus inputs. Like `prove-sorry`'s
   weakening gate: such a candidate is a flagged proposal requiring explicit
   user sign-off, never a normal candidate.
6. **The candidate note.** Strategy skill used, what changed, expected effect
   quantified from the brief (op counts, allocation counts — with the
   brief's `file:line` citations), typeclass strengthening rationale, any
   new-correspondence request.

## Upstream first

Before any rewrite: check whether the pinned CompPoly
(`cpoly/.lake/packages/CompPoly/`) already ships a variant of the target with
its lemma (`eval₂Horner` + `eval₂Horner_eq_eval₂` is the exemplar). If yes,
emit an **upstream-variant candidate** — a reference to the upstream def,
no `Opt.lean` change, contract items 4–6 still apply.

## Procedure

1. **Inputs**: target def, brief, and the set of strategies already tried on
   this target (from `perf-loop` / the ledger).
2. **Upstream check** (above). An upstream variant found on the first round
   short-circuits tier selection: it *is* round one.
3. **Tier selection** — high-level first, as a general rule: a
   complexity-class win dwarfs constant-factor tuning and changes which
   constants are worth tuning afterwards.
   * Tier 1 `opt-algo-swap` — different algorithm.
   * Tier 2 `opt-inplace-buffers`, `opt-tailrec-loops`, `opt-list-to-array`
     — same algorithm, better shape (parallel, they rarely collide).
   * Tier 3 `opt-word-arith` — word-level arithmetic under the fixed
     representation (last: it tunes whatever algorithm survived tiers 1–2).
   Each round emits the applicable-and-untried strategies of the highest
   tier that still has any; "applicable" is read from the brief's strategy
   section, never guessed.
4. **Fan-out**: one Opus agent per selected strategy, each in its own git
   worktree (parallel candidates edit the same `Opt.lean`). A fresh worktree
   has no `.lake`, and a cold `lake build` there rebuilds Mathlib — hours.
   Transplant the cache: `cp -Rc cpoly/.lake <worktree>/cpoly/.lake` (APFS
   clonefile, seconds; this volume is APFS). Measured 2026-08-11: the
   transplanted worktree's full `lake build` was 2336 jobs, all cached.
   Overlay uncommitted work with `git diff HEAD | git -C <worktree> apply`
   **plus** explicit copies of untracked files (`Opt.lean` before its first
   commit!) — `git diff` does not carry untracked files, and a worktree
   missing `Opt.lean` fails its build immediately. Each agent gets: its
   strategy skill, the brief, the target's definition chain, this contract,
   and builds with `lake build` in `cpoly/` until green (use `lean-lsp-mcp`
   when the MCP server is available; build-loop otherwise). Capture the
   `#print axioms` output as evidence.
5. **Contract enforcement** — mechanical, on evidence, before anything is
   forwarded: lemma present and sorry-free, axiom set exact, note complete,
   body inside the conventions table. Verdicts for the ledger:
   `contract-ok`, `lemma-failed`, `not-translatable`, `no-strategy-applies`,
   `contract-violation`, `build-failed`.
6. **Hand off** contract-ok candidates to `perf-loop` (translation, tests,
   bench are its pipeline, via `lean-to-rust` and the `rust-bench`
   candidate mode).

## Invariants to keep green

* `Opt.lean` never gains a def without its proved lemma and its `Check.lean`
  §15 line in the same change.
* Every candidate's ledger row names exactly one strategy skill.
* Tier order is only ever advanced, never skipped downward mid-target, and
  "applicable" always cites the brief.
* Gated proposals (weakening, representation change) reach the user
  explicitly or die; they never ride along as normal candidates.
