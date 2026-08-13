---
name: aeneas-equivalence-bridges
description: Choosing and building the relation layer when a spec cannot be stated with a plain representation function — representation relations, ResultRel over both monadic sides, state relations for mutable records, backward-continuation relations for escaping mutable borrows; use when a type mismatch between the extracted model and the CompPoly reference resists the `rep r = CompPoly.op (rep args)` pattern, which today means: almost never — read this to confirm you actually need a relation before inventing one
---

# Equivalence Bridges

For the moment a spec **cannot** be stated in the house pattern — a total
representation function plus an invariant (the `aeneas-spec-author` skill).
Read this **before** defining any relation, `ResultRel`, state relation, or
backward-continuation apparatus. The unexercised design sketches this skill
selects from live in `skills.md` §"Representation relations and proof
architecture" (relation table, `ResultRel`/`StateRel`/`BackRel` skeletons,
the multi-level-bridge architecture) and in the `aeneas-lean-core` skill's
backward-continuation material — point there, do not re-derive.

## The one rule: a function beats a relation, every time

Every spec proved in this repo so far — the whole of `Field.lean`,
`Univariate.lean`, `Multilinear.lean` — needed only representation
*functions* (`toExt`, `toRaw`) under invariants (`Reduced`, `VecReduced`).
A function gives rewriting, congruence, and `simp` for free; a relation
demands transport lemmas for every operation that touches it, and that cost
is paid in every proof forever after. So the decision procedure is: first
try to make a function exist (a partial map becomes total under the
invariant you were going to assume anyway; a quotient collapses under a
canonicalization the code already performs). Only when that genuinely fails
does a relation earn its place — and trivial-grade translation
(`lean-to-rust`) is designed to keep it failing rarely: rising bridge cost
is a signal the translation drifted from trivial, worth reporting alongside
any new relation.

## Choosing the bridge, by mismatch

| Mismatch | Bridge | Source of the skeleton |
|---|---|---|
| Extracted type ↔ reference type, total conversion exists under the invariant | representation **function** + invariant — not this skill | `aeneas-spec-author` |
| Many extracted values per reference value, no canonical pick | representation relation `R : α → β → Prop` + per-operation transport lemmas | `skills.md` relation table |
| Both sides monadic (`Result` vs `Result`, e.g. extracted-vs-extracted comparisons) | `ResultRel R` lifting `R` through `ok`/`fail` | `skills.md` `ResultRel` skeleton |
| Mutable Rust record ↔ pure reference state | `StateRel` (record-wise) + field-projection lemmas | `skills.md` `StateRel` skeleton |
| Function returns a mutable borrow (value **plus** backward function) | backward-continuation relation (`BackRel` shape) over the write-back | `skills.md` `BackRel`; `aeneas-lean-core` on backward functions |

Two placement rules, whichever bridge is chosen: relation definitions and
their transport lemmas live beside the representation layer of the module
they serve (the `toRaw` section of `Univariate.lean` is the pattern), and
every new relation gets `Check.lean` non-degeneracy entries just as a
representation function would (the relation is inhabited, is not `True`,
distinguishes something).

## Growth rule

This skill is thin by design and grows one worked example per real contact,
the way the `aeneas-extract` ceiling table grows one measured row per probe.
On first use of any bridge kind: land the definitions and transport lemmas
in the module, then replace that row's pointer above with the concrete
in-repo pattern (names, the transport lemmas that were actually needed,
what they cost). Until a kind has been exercised, its `skills.md` skeleton
is a starting sketch, not a proven pattern — say so when handing it to a
prover agent.

## Invariants to keep green

* No relation exists where a representation function could — each relation
  in the tree is justified by a recorded reason a function cannot exist.
* Every relation has its transport lemmas and its `Check.lean`
  non-degeneracy entries in the same change that introduces it.
* Headline specs still end on the CompPoly reference side: a bridge changes
  how the two sides are related, never which definition is trusted
  (`aeneas-spec-author`'s one rule).
