---
name: opt-word-arith
description: Optimization strategy — word-level arithmetic rewrites of a targeted CompPoly definition (delayed reduction with stated headroom, conditional-subtract reduction, u128 accumulators) as Foo.opt + its proved opt_eq_spec lemma; run when the brief shows reduction or widening work on the hot path. Representation changes (Montgomery/Barrett) are gated, not free
---

# Strategy: Word Arithmetic

One strategy of the optimization loop. Invoked by the `lean-opt` driver with a
target definition and its `compoly-analyze` brief; delivers a candidate under
the opt-contract that `lean-opt` owns: `Foo.opt` in `cpoly/lean/Opt.lean`
plus the proved `Foo.opt_eq_spec`. A word-level variant usually lives on a
word carrier, so its lemma takes the commutes-through-representation form the
opt-contract allows (`toK (Foo.opt w) = Foo (toK w)` under `Red`), using the
representation maps the spec files already own (`toK`, `toExt`, `toRaw` in
`cpoly/lean/`).

## The one rule: the representation invariant is global; arithmetic under it is local

The type table (`lean-to-rust`) fixes what the Rust newtypes *store*: reduced
representatives, `Red`/`Reduced` as invariants of the type. A variant may
restructure arithmetic **under** that invariant — that is this strategy's
mandate. A variant that changes what the words *mean* (Montgomery form,
Barrett with a different stored range) changes `Red` and `toK` for every
operation of the module at once: that is a corpus-wide migration needing its
own bridge layer and campaign, not a per-op candidate. Propose it only as a
flagged, driver-gated proposal (ledger tag `TODO(P3)`) — never as a normal
candidate.

## Measured headroom facts for the Hachi prime (verified 2026-08-11)

* q = 2³² − 99 = 4294967197; q·(q−1) = 18446743219011069612 < 2⁶⁴ — one
  product of a reduced representative by anything < q fits u64.
* (q−1)² ≈ 2^63.997 — **two** unreduced products already overflow u64: any
  delayed-reduction accumulation needs u128, which is extraction-supported
  (`aeneas-extract`'s ceiling table, probed `nightly-2026.07.26-3a8586f`).
* q − 1 = 2²·3·13·67·163·2521; R = 2⁶⁴ mod q = 9801 (Montgomery constant, if
  the gated migration is ever proposed).
* Upstream's Hachi facts live in `CompPoly/Fields/Hachi*.lean` in the pinned
  copy — cite them, do not re-derive.

## What it attempts

* **Delayed reduction**: accumulate k products in u128 (or split limbs) and
  reduce once, with the headroom inequality stated in the candidate note and
  carried as a lemma hypothesis if it depends on input sizes.
* **Conditional-subtract reduction**: replace a `% q` on a value known < 2q
  by `if x ≥ q then x - q else x`, with the bound cited from the brief.
* **Widening discipline**: choose u64-only vs u128 paths from the headroom
  facts above, not defensively (hachi's own `ring.rs` u128 widening was
  measured unnecessary, 2026-07-27).

## Invariants to keep green

* The opt-contract (owned by `lean-opt`) is met; word-carrier lemmas go
  through the *existing* representation maps only.
* `Red`/`Reduced` stay the module invariants — no candidate changes what a
  newtype stores without the gated-proposal route.
* Every headroom claim in the note is an inequality with numbers, not "fits".
