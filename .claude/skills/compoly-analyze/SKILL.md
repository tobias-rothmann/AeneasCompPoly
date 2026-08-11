---
name: compoly-analyze
description: Producing the optimization brief for a targeted CompPoly definition — the definition chain behind the notation, the semantics risks (overflow headroom, partiality, checked-arithmetic traps), the cost model, and which opt-* strategies apply; the target is handed in, never chosen here
---

# Analyzing a CompPoly Definition

For the first stage of the loop: a *targeted* Lean definition goes in, an
optimization brief comes out. The target arrives from upstream — the user, the
`perf-loop` driver, a route skill. **Choosing what to translate or optimize is
not this skill's job**; if no target is named, stop and ask, do not scan for
one.

Read the definition from the pinned copy the proofs actually build against:
`cpoly/.lake/packages/CompPoly/` at the rev in `cpoly/lake-manifest.json`. The
`./CompPoly` directory at the repo root is a browsing clone on its own clock —
it is allowed to drift from the pin, and it does.

## The one rule: every claim in the brief cites the line it was read from

The brief is what the optimization agents act on. An asymptotic bound, a "this
cannot overflow", or a "the inner sum is the hot path" that was guessed rather
than read sends the optimization agents optimizing fiction — and unlike a wrong benchmark, a
wrong brief fails silently twice (the candidates it inspires still measure
honestly, but the strategies never aim at the real cost). Cite
`file:line` of the pinned copy for every claim; if a claim needs a lemma (a
value range, an invariant), name the lemma.

## Producing the brief

1. **Unfold the notation.** Write down the chain from the surface syntax to
   the computation: which instance `*` resolves to, what the definition's body
   really is after the `ofFn`/`Finset.sum`/typeclass layers. Example shape:
   `x * y : Ext P` → `Mul (Ext P)` instance → `Ext.mul` → `ofFn fun k => ∑ i, ∑ j, if …`
   (`CompPoly/Fields/Extension/Defs.lean`). The translation layer works from
   this chain, not from the pretty notation.
2. **Semantics risks — the section that must never be thin.**
   * *Value ranges and overflow headroom.* When the Rust side will hold word
     representatives, state the bound arithmetic explicitly, the way
     `cpoly/src/field.rs`'s module doc does for the Hachi prime
     (`a * b ≤ (P-1)² < 2^64`, slack quantified). Aeneas models Rust
     arithmetic as checked: every `+`/`*`/index returns `Result`, and the
     eventual proofs must show `ok` — an overflow that "cannot happen in
     practice" is a proof obligation, so the brief must say *why* it cannot
     happen.
   * *Partiality.* Division, `Fin` arithmetic, subtraction on `ℕ`, functions
     defined by well-founded recursion — anything whose Lean totality is
     non-obvious becomes a precondition or a representation choice downstream.
   * *Exactness traps.* Note where the definition branches on equality of
     field elements, degenerate sizes (`n = 0`, empty vectors), or hypercube
     structure — these decide what a non-degenerate test corpus looks like.
3. **Cost model.** Count field operations as a function of the size
   parameters; name what dominates and what allocates. Say it in the terms the
   bench thinks in (`field/ext4_mul` ≈ 14 ns per `Ext4` multiply on the
   reference M2 — from the `rust-bench` skill's floor method), so a later
   "this rewrite should win" is checkable against a first-principles floor.
4. **Strategy candidates.** Name which `opt-*` strategy skills plausibly
   apply (tail-recursion shaping, list→array, word arithmetic, algorithm
   substitution, in-place buffers) and *why*, one line each. Pointers only:
   the strategies themselves live in their skills, and the brief must not
   duplicate them. A promising direction that matches no existing `opt-*`
   skill is still named, in the same one-line form, marked `(no skill yet)` —
   never invent a pointer to a skill that does not exist.
5. **Representation notes.** Which existing Rust types the translation slots
   into (`Fp`, `Ext4`, the poly newtypes) — or, for a genuinely new carrier,
   a proposal with the reasoning pattern of `field.rs`: small fixed dimension
   → named-fields struct so the extracted model is straight-line; dynamic
   length → `Vec` newtype with slice helpers.

## Brief format

One markdown block, fixed headings, handed verbatim to `lean-opt` and
`lean-to-rust`:

```markdown
# Brief: <full Lean name>            (CompPoly @ <lake-manifest rev>)
## Definition chain                  (notation → instances → body, file:line)
## Semantics risks                   (ranges + headroom arithmetic, partiality, traps)
## Cost model                        (op counts, allocations, dominant term)
## Strategy candidates               (opt-* names + one-line why)
## Representation                    (existing types to slot into, or proposal)
```

## Invariants to keep green

* The brief names the lake-manifest rev it was read at; a brief against a
  drifted checkout is invalid.
* Every claim carries its `file:line` or lemma name.
* When word representations are in play, the overflow-headroom arithmetic is
  written out — numbers, not adjectives.
* Strategy detail stays in the `opt-*` skills; the brief only points.
* No target selection. A brief exists because something upstream targeted the
  definition.
