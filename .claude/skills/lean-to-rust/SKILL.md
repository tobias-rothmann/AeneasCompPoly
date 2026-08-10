---
name: lean-to-rust
description: Translating a targeted Lean definition (CompPoly spec or optimized variant) into Rust in cpoly/src — the conventions table and the trivial-grade checklist v1, idiomatic shell (newtypes, core::ops, methods) around a trivial body (counter loops, named intermediates, bind-order-preserving straight-line code)
---

# Translating a Lean Definition to Rust

For turning a *targeted* Lean definition — the CompPoly spec itself, or an
optimized `Foo.opt` variant that already carries its `Foo.opt_eq_spec` lemma —
into Rust under `cpoly/src/`. The target arrives from upstream (user,
`perf-loop`, a route skill); choosing it is not this skill's job. Read this
**before** writing the Rust, together with the brief from `compoly-analyze`;
the idiom/axiom boundary is owned by the `aeneas-idiomatic-rust` skill and the
post-landing obligations by `rust-bench` and `aeneas-extract`.

## The one rule: the translation must be provably boring

Translation distance is proof distance — that is the project's core bet. So
every place the Rust deviates from the Lean definition's syntactic structure
must be one of the enumerated moves in the checklist below, and anything
else — an algorithm change, a data-structure change, loop fusion, hoisting,
precomputation — is an *optimization*, and optimizations belong in Lean (an
`opt-*` rewrite with its equivalence lemma), never in the translator. When
you catch yourself improving the code while translating: stop, file the idea
for the Lean side, translate the definition you were given.

The checklist is v1 of the trivial-grade dial (open unknown ?1). It moves on
ledger evidence from P3 proof effort, not on taste.

## Conventions: types

| Lean | Rust | Why this shape |
|---|---|---|
| `ZMod P`, reduced representative | `Fp(u64)`, field private, `Fp::new` reduces | the `Red` invariant holds by construction — not a precondition callers can break (`field.rs`) |
| `Vector F d`, small known `d` | named-fields struct (`Ext4 { c0..c3 }`) | keeps every operation straight-line in the extracted model: no loops, no bounds checks |
| `List F` / `Array F`, dynamic | `Vec<Ext4>` newtype; `&[Ext4]` for borrowed views | slices keep helper loop states 2-tuples; distinct newtype *names* dodge `Shared<n><T>` collisions |
| `Fin n` | `usize` + the structural bound (`i < v.len()`) | never a stored index type; the bound is re-established where used |
| `UInt32` / `UInt64` | `u32` / `u64`; `as`-casts for widening/narrowing | casts extract to `UScalar.cast`, modelled, axiom-free (probed 2026-08-10, `nightly-2026.07.26-3a8586f`) |
| subtype with a Prop | newtype whose constructors enforce the invariant | the proofs then get the invariant from the type, as with `Red` |

## Conventions: terms and structure

| Lean shape | Rust shape |
|---|---|
| `let x := e; body` | `let x = e;` — **statement order is bind order**; never collapse intermediates into one expression |
| `ofFn` / `∑` over `Fin d`, `d` known small | unroll to named lets (`t0..t6` in `Ext4::mul`), with the index regrouping justified in the doc comment |
| fold / map / structural recursion over a list | counter loop: `let n: usize = …; let mut out: Vec<Ext4> = Vec::new(); let mut i: usize = 0; while i < n { out.push(…); i += 1; }` |
| shared sub-definition | helper `fn` over slices (`add_pointwise(a: &[Ext4], b: &[Ext4]) -> Vec<Ext4>`) |
| `if` / `match` | `if` / `match` with the same nesting |
| one `def` | one `fn`, with a `Mirrors \`<exact Lean name>\`` doc line |

**Every `let` in a translated body carries an explicit type**
(`let mut i: usize = 0;`, `let t0: Fp = …;`) — extraction is insensitive to
it, but the binds stay legible and reviewable. (The pre-existing corpus has
untyped exceptions; new translations follow the rule.) The counter `while`
is deliberate: `for i in 0..n` works but puts a `Range` in every loop
invariant — see "Deliberately declined" in `aeneas-idiomatic-rust`.

The unroll-and-regroup move (row 2 of the table), stated generically rather
than by example: collect terms into columns by output index, columns in
ascending order, products within a column in ascending first-operand index;
when a wrap/fold constant scales a whole column, factor it **once** —
distributivity, exact in the field — with the constant on the left (matching
the Lean's `P.W * (…)`), and the direct column first in the fold add
(`t_k + W * t_{k+4}`). Per-term scaling (the literal Lean shape) and
per-column factoring extract to *different bind sequences*; the checklist
picks per-column, justified in the doc comment.

## Conventions: the shell

The public surface is the house API from day one — every idiom in it is
measured free in `aeneas-idiomatic-rust`'s verdict tables:

* Operators via `core::ops` impls (`Add`/`Sub`/`Mul`/`Neg`), `*Assign` forms
  delegating to them; heterogeneous impls where the math reads that way
  (`impl Mul<Ext4> for Fp`).
* Constants as `pub const` (extracts `@[global_simps, irreducible]`, same as
  a module-level `const`).
* Type names distinct across modules (`UnivariatePoly`, `MultilinearPoly`) —
  by-reference operator impls mangle to `Shared<n><TypeName>` *without* module
  qualification, and a collision is a hard extraction failure.
* Doc comments carry the semantics the reviewer needs: the `Mirrors` line,
  and — whenever new word arithmetic appears — the overflow-headroom bounds
  written out numerically, in the style of `field.rs`'s module doc.

## Trivial-grade checklist v1 — the enumerated moves

A translation may do exactly these, and nothing else:

1. Unroll a fixed-size `ofFn`/`∑` (known small `d`), regrouping indices, with
   the regrouping stated in the doc comment.
2. Turn fold/map/recursion into the counter-`while` + `Vec::new()`/`push`
   accumulator shape.
3. Introduce *more* named intermediates than the Lean has (never fewer).
4. Extract a shared helper `fn` over slices.
5. Pick representations per the type table above.
6. Keep arithmetic on reduced representatives with the headroom argument
   stated (`a * b ≤ (P-1)² < 2^64` and its friends).

If the improvement you want is not on this list, it is an optimization:
return it to the Lean side (P2's `opt-*` + `opt_eq_spec`), then translate
*that* definition with these same six moves.

## What a translation owes before it is done

* `cargo test` green, with the module's semantics tests extended to cover the
  new item against non-degenerate inputs.
* `cargo clippy --all-targets` clean under pedantic; `#[allow]` only with a
  one-line reason at the narrowest scope.
* The bench obligations of the `rust-bench` skill: freeze the item into
  `benches/genesis/`, then a case or a by-name exclusion with a checkable
  reason — `make bench-check` enforces this.
* An extraction pass per the `aeneas-extract` skill: zero axioms, loop-state
  shapes diffed, names skimmed.
* **A new public operation owes an Aeneas spec.** "Every public operation has
  a spec" currently holds literally (111 `_spec` theorems). Landing the Rust
  without the spec breaks that invariant — flag the debt to the outer
  verification pass explicitly; never let it accrue silently.

## Failure modes with teeth

These are `aeneas-idiomatic-rust` lessons restated as translation rules —
that skill is the source of truth for all four:

* **Collapsing binds.** Merging `let lo = c[2*j]; let hi = c[2*j+1];
  out.push(lo + x0*hi)` into one expression reorders the extracted binds and
  invalidates every `step as ⟨…⟩` walk. Same for `+=` vs `x = x + y` — they
  extract differently; pick one deliberately.
* **Fattening a loop's state.** Writing a binary operation's loop inline over
  `self`/`rhs` carried a 3-tuple `(rhs, out, i)` where the invariant expected
  `(out, i)`. Helpers over slices restore the 2-tuple.
* **Two newtypes over the same inner type are the same Lean type.** A spec
  pairing the wrong reading still typechecks. After translating into a module
  with two readings (coefficients vs evaluations), check the pairings by
  hand.
* **Reflexive tidying.** `vec![a, b]` (list form), `v.is_empty()`,
  `derive(Default)` on a `Vec`-holding struct — each drags an axiom in. The
  verdict tables decide, not Rust habit.

## Invariants to keep green

* Statement order = bind order; every deviation from the Lean is one of the
  six moves, and moves 1 and 6 are justified in doc comments.
* The `Mirrors` line names the exact, current Lean identifier at the pinned
  CompPoly rev.
* Zero axioms and zero `sorry` after the extraction pass.
* The spec debt of a new public op is flagged, never silent.
* This checklist changes only with ledger evidence (P3 proof-effort rows),
  and the change lands here, in this file.
