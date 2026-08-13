---
name: rust-direct
description: Optimization strategy — rewriting the Rust translation of a targeted CompPoly definition directly in cpoly/src (algorithm swaps, buffer shapes, loop restructuring) while staying inside the Aeneas-supported ceiling; the candidate stage of route-r2, where no Lean opt lemma exists and the equivalence proof relates the extracted model straight to the original CompPoly definition; use when running the Rust-first route or when a Rust-level rewrite of a targeted operation is proposed
---

# Rust-Direct Optimization (the R2 candidate stage)

The candidate stage of the `route-r2` composition: candidates are written as
Rust diffs against the current champion in `cpoly/src`, not as Lean `Foo.opt`
definitions. Read this **before** writing any such candidate. The bench,
accept rule, and ledger mechanics are `perf-loop`'s and apply unchanged — a
rust-direct candidate enters that procedure at the semantics-test step, since
it is already Rust. Idiom/axiom boundaries are `aeneas-idiomatic-rust`'s; the
supported-constructs ceiling is `aeneas-extract`'s.

## The one rule: never write a construct without a green ceiling row

Extraction is checked once, at champion landing — not per candidate. A
candidate that uses a construct absent from `aeneas-extract`'s measured
ceiling table gambles the whole bench-and-accept effort on an extraction
failure discovered last. So: every construct in a candidate either has a
green row in the table, or gets probed first by that skill's recipe (which
grows the table one measured row per contact). `unsafe` and SIMD are the
hard cap — no probe changes that. This rule is the whole difference between
"optimize within the ceiling" and "write Rust and hope".

## The candidate contract

* **Input** — the target's `compoly-analyze` brief (its cost model reads on
  the Rust hot path too) and the current champion's `cpoly/src`.
* **Output** — a candidate diff in an isolated worktree, plus a candidate
  note stating: the predicted win and why, and the list of constructs used
  that are near the ceiling's edge, each pointed at its table row (or the
  probe that just added one).
* **Gates before benching** (replacing the opt-contract of the Lean-side
  strategies — there is no `Foo.opt` and no `opt_eq_spec` here):
  * ceiling audit per the one rule;
  * `cargo clippy --all-targets` clean at the mechanical level the inner
    loop uses;
  * `cargo test` semantics pass;
  * `Mirrors` lines keep naming the **original** CompPoly definition — a
    rust-direct champion still mirrors that definition semantically; there
    is no opt variant to rename to.
* **Verdict** — `perf-loop`'s recentered `CANDIDATE=1` accept rule, verbatim.
  The ledger row is a standard candidate row with `"strategy": "rust-direct"`.

## Proof-debt pricing — what this strategy deliberately forgoes

An accepted rust-direct champion carries **no Lean lemma chain**: the
`verify-campaign` for it proves the extracted model against the original
CompPoly definition directly, with no `opt_eq_spec` to splice onto the
right-hand side. That cost difference is not a defect — it is the R2 datum
the bake-off exists to measure (the with/without-lemma question the plan
keeps open). A representation change (different coefficient layout, packed
words) goes through `aeneas-equivalence-bridges` before any relation is
invented; its decision tree ("a function beats a relation") applies with
extra force here, because there is no Lean-side variant to anchor one.

## Invariants to keep green

* Every construct in an accepted champion has a green ceiling row dated no
  later than the accept.
* No `unsafe`, no SIMD, no iterator adaptors beyond the table's green rows.
* `Mirrors` lines truthful to the original CompPoly definition; semantics
  tests extended per `lean-to-rust`'s obligations when behavior surface
  grows.
* Every candidate that reached the bench has a ledger row with
  `"strategy": "rust-direct"`, whatever its fate.
