---
name: aeneas-extract
description: Running and triaging the Rust→Lean extraction (make extract) — the charon+aeneas pin discipline, the determinism check, the post-extract audits (axioms, loop-state shapes, name collisions), and the supported-constructs ceiling table with the probe procedure that grows it
---

# Extracting Rust to Lean

For regenerating `cpoly/lean/Generated.lean` from `cpoly/src/`, and for
diagnosing what went wrong when that fails. Read this **before** running
`make extract` as part of the loop, and read the Makefile's comments — they
are the design, this file is the procedure. `Generated.lean` is derived
output: **never hand-edit it**; every change to it goes through the Rust and
a re-extraction.

## The one rule: the extraction is deterministic, or it is broken

`make extract` on unchanged Rust must report `unchanged` — the target
copies the previous `Generated.lean` aside and `cmp`s after regenerating.
That check is the contract everything downstream leans on: the proofs are
about *this* extraction, and an extraction that drifts without a Rust change
means the toolchain moved. If `unchanged` unexpectedly becomes
`regenerated`, stop and find out which binary changed (`make
check-toolchain` verifies the pin in both directions — the binaries
self-report their commit) before trusting anything else. Determinism is also
the last step of every idiomatization pass: re-run `make extract` and demand
`unchanged`.

## Mechanics

```
make extract                # charon → generated.llbc → aeneas → cpoly/lean/Generated.lean
make extract CHARON=<path> AENEAS=<path>   # e.g. from a worktree, pointing at the
                                           # main checkout's ./toolchain binaries
```

* The pin is `AENEAS_TAG` in the Makefile (`nightly-2026.07.26-3a8586f` at
  the time of writing); `make setup` downloads the release binaries into
  `./toolchain/`, and `check-toolchain` fails on any mismatch between pin
  and binary.
* Aeneas names the Lean module after the `.llbc` basename —
  `generated.llbc` is what makes `import Generated` resolve. Renaming the
  file renames the module the proofs import.
* charon resolves its rustc from the `rust-toolchain` file *beside the
  charon binary*, not from the repo — overriding `CHARON=` moves that too.
* After a successful extraction: `make build` re-checks every proof.

## Post-extract audits — before `make build`, every time

<!-- ⚠️ SYNC RULE: source of truth is aeneas-idiomatic-rust "Staged workflow" step 3 -->

1. `grep -c '^axiom' cpoly/lean/Generated.lean` — must be **0**. Any axiom
   means some construct dragged an unmodelled `std` item into the trusted
   base.
2. Diff the loop-state shapes against the previous generation:
   ```bash
   grep -A6 "^    (fun (" cpoly/lean/Generated.lean | grep -oE "\(fun \([a-z0-9, ]+\)" | sort | uniq -c
   ```
   A tuple that grew (2-tuple → 3-tuple) breaks every invariant written
   about that loop — see the `aeneas-idiomatic-rust` failure modes.
3. Skim the new names for `Shared<n><T>` prefixes that collide across
   modules — a collision is a hard aeneas error, but near-misses deserve a
   rename before they become one.

## Triage, by failure shape

* **Hard error: "The chosen name is already in the names set" —**
  `Shared<n><T>` collision from by-reference trait impls on same-named types
  in different modules. Fix by making the *type names* distinct
  (`MultilinearPoly`, not `Poly`), never by contorting the API.
* **Warning: `could not find the information for item 'X'` / output
  "contains extracted external, unknown definitions" —** the construct has
  no Aeneas model. Consult the ceiling table below; reshape the Rust per the
  `lean-to-rust` conventions so the construct disappears. **Never patch the
  aeneas fork to add a model for convenience** — the fork exists for Lean
  version fixes only, and every divergence from upstream is drift the fork
  policy has to pay back.
* **`unchanged` became `regenerated` with no Rust change —** read the diff
  before alarming. If every changed line is a `Source: '…', lines N` doc
  comment, the *committed artifact* was stale — a comment-only source edit
  once landed without a re-extraction — and the fix is to commit the
  regeneration (measured 2026-08-10: 174 changed line-pairs, all `Source:`
  spans, zero code lines). If extracted **code** changed: toolchain drift —
  `make check-toolchain`, compare `AENEAS_TAG`, find which binary moved.

## The ceiling table (open unknown ?2)

What the pinned toolchain supports, **measured, not guessed**. Two seeds:
the idiom-level verdicts live in `aeneas-idiomatic-rust` (free idioms,
strict simplifications, and the forbidden list: iterator adaptors,
`Vec::is_empty`, `derive(Default)` on `Vec`-holding structs, `vec![a, b]`
list form, `truncate`/`pop`/`last`/`first`/`clear`/`extend`,
`checked_shl`); the construct-level rows below were probed 2026-08-10
against `nightly-2026.07.26-3a8586f`, one construct per item, all four
checks (error / warning / `^axiom` grep / typecheck under `cpoly`'s lake
env) green:

| Construct | Extracts to | Note |
|---|---|---|
| `Vec::with_capacity(n)` | `alloc.vec.Vec.with_capacity` | pre-sizing accumulators is free |
| local `[u64; 4]`: repeat-init, index read/write | `Array Std.U64 4#usize`, `Array.index_usize` / update | fixed-size accumulators work |
| `pub const TABLE: [u64; 4]` + indexing | `Array Std.U64 4#usize` def + `index_usize` | precomputed tables work |
| `(a as u64) * (b as u64)` widening, `a as u32` narrowing | `UScalar.cast` | the word-arith primitive |
| `>>`, `&` on `u64` | pure/`ok` scalar ops | shifts and masks fine |
| write through `&mut [u64]`: `v[i] = …` in a counter loop | `@[rust_loop]` defs, state `(Slice U64) × Usize` | in-place mutation keeps the 2-tuple |
| `&mut Vec<u64>` parameter + `push` | ordinary `Vec.push` calls | out-parameters work |
| `break` from a counter loop | `ControlFlow` loop encoding | |
| early `return` inside a loop | `ControlFlow` loop encoding | |
| `a.wrapping_mul(b)` | `ok (core.num.U64.wrapping_mul a b)` — **pure** | wrap-around arithmetic without `Result` friction |
| `u128` intermediates: cast, `*`, `>> 64`, cast back | `UScalar.cast .U128` + U128 scalar ops | Barrett/Montgomery high-half pattern available |
| `a.checked_add(b)` + `match` on the `Option` | `U64.checked_add` | `checked_shl` is the axiom, not the whole `checked_*` family |
| self-recursive `fn` (probed 2026-08-12) | `def … partial_fixpoint` | extracts clean, zero axioms — but it is a **different proof shape**: fixpoint unfold/induction, not the `@[rust_loop]` template |
| `a + b` on `u128` (probed 2026-08-12) | monadic `Std.U128` add in `Result` | standard overflow-checked shape |
| `<` / `>=` on `u128` (probed 2026-08-12) | **pure** boolean comparisons | no `Result` friction in guards |
| `a & mask`, `a >> 32` on `u128` (probed 2026-08-12) | pure lifted `&&&` + monadic `>>>` (shift RHS is an `#i32` literal) | mid-shifts work, not just `>> 64` |
| `a % b` on `u128`, constant divisor (probed 2026-08-12) | monadic `%` with `#u128` literal | divisor-nonzero side condition trivially dischargeable |
| guarded `usize` sub in a counter loop: `if j <= k { k - j }` (probed 2026-08-12) | monadic sub under a pure guard; loop state stays a **2-tuple** | the k-outer convolution shape is safe |
| range subslices `&p[..end]`, `&p[start..]` (probed 2026-08-12) | `core.slice.index.SliceIndexRange{To,From}UsizeSlice.index` | modelled instances with `step_spec` lemmas in the Aeneas Std (`Slice.lean:490`, `:990`); out-of-range indices `fail` in the model where Lean's `Array.extract` clamps — clamp explicitly first |

Unprobed (add a measured row on first contact — closures, const generics,
generic functions, `match` on custom enums, `u128` division, trait objects,
…). And the permanent ceiling: no `unsafe`, no SIMD intrinsics, no inline
asm — nothing without a model, ever; quantifying that gap against
unrestricted Rust is a P4 ledger question.

## Growing the table: the probe recipe

<!-- ⚠️ SYNC RULE: source of truth is aeneas-idiomatic-rust "The one rule: probe, do not reason" -->

The recipe is `aeneas-idiomatic-rust`'s: a scratch crate in the session
scratchpad, **one construct per item** plus a `use_all()` caller so charon
cannot drop anything as dead code, then charon + aeneas + the four checks.
Two minutes, decisive. Every probe's verdict lands here as a table row with
its date and toolchain tag; every extraction failure on a new construct is a
probe that hasn't been written yet.

## Invariants to keep green

* `Generated.lean` is never hand-edited; `lean/Generated.lean` **is**
  tracked, so a regeneration shows up in `git diff` — read that diff.
* A no-op re-extraction reports `unchanged`.
* Zero `^axiom` lines in `Generated.lean`, always.
* `make build` green after every regeneration — a regeneration without a
  proof re-check is half-done. (A worktree without the `.lake` package cache
  cannot run it; the re-check is then *deferred to the main checkout*, and it
  still blocks "done".)
* Every new-construct contact adds a measured row to the ceiling table, with
  date and toolchain tag.
* The fork stays extraction-conservative: no local models added to dodge a
  reshape.
