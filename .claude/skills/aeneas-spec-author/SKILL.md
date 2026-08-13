---
name: aeneas-spec-author
description: Stating the ⦃·⦄ spec layer for Aeneas-extracted functions in cpoly/lean — readable aliases for mangled impl names, representation functions and invariants, headline triples stated against the original CompPoly definition, loop-spec decomposition, sorry stubs for prove-sorry, Check.lean audit lines; use when a new operation needs specs (after op-genesis/extraction), when an accepted champion regenerates Generated.lean and the old specs go stale, or whenever a `_spec` theorem must be written or restated
---

# Authoring Aeneas Specs

For the **statement layer** only: what the `_spec` theorems in `cpoly/lean/`
claim, not how they are proved (`prove-sorry` proves; this skill hands it
typechecked `sorry` stubs). Read this **before** writing or repairing any
`_spec`. The triple form `m ⦃ r => post r ⦄` and how it composes are
documented in `cpoly/lean/Field.lean`'s header; the translation model and
`@[step]` machinery in the `aeneas-lean-core` skill; the loop-spec template
in the `proof-patterns` skill. The proved files `Field.lean`,
`Univariate.lean`, `Multilinear.lean` are the style exemplars — a new spec
should read as if it always lived beside them. When the representation-
function pattern below stops fitting, read the `aeneas-equivalence-bridges`
skill before inventing anything.

## The one rule: the headline spec states the original CompPoly definition

Every headline triple has the shape

```
theorem op_spec (inputs …) (hinv : invariants …) :
    extracted_op inputs ⦃ r => Inv r ∧ rep r = CompPoly.<op> (rep inputs) ⦄
```

with a `CompPoly.*` reference name on the right-hand side — never an
optimized variant (`Foo.opt`), never a description of what the extracted
code structurally does. When `perf-loop` lands a faster champion, **the
statement does not move**: the proof reroutes through the variant's
`Foo.opt_eq_spec` lemma (the opt-contract, see the `lean-opt` skill) to land
on the unchanged right-hand side. The trusted statement is what readers and
downstream proofs consume; if it tracked champions it would churn on every
accept, and the `Check.lean` audit prints would stop pinning anything.

## The procedure

1. **Extract first, then author.** Specs are stated only against a freshly
   extracted, determinism-checked `Generated.lean` (the `aeneas-extract`
   skill; even comment-only Rust edits shift `Source` spans and regenerate
   the file, so a stale copy is easy to hold without knowing). The cheap
   probe is `make extract` followed by `git diff -- cpoly/lean/Generated.lean`;
   a session that cannot run the extraction treats the file as unverified
   and says so in its deliverable.
2. **Alias the mangled names.** Aeneas builds operator-impl names from the
   impl header — `impl Add<&UnivariatePoly> for &UnivariatePoly` becomes
   `cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add`.
   Do not try to predict the `Shared<n>` numbering (it tracks the impl's
   borrows): grep `Generated.lean` for the trait fragment
   (`CoreOpsArithNeg`, …) and read the name off. Conventions, per the proved
   files: aliases live in a per-module `namespace Poly`-style block, ordered
   as in the Rust source; loop aliases are camelCase (`negLoop`); the
   docstring is the backticked impl header for an operation
   (`` `impl Neg for &UnivariatePoly` ``) and a lowercase phrase for its
   loop (`` the loop of `Neg` ``). An `abbrev` is `@[reducible]`, so a
   theorem about the alias *is* a theorem about the generated definition —
   nothing extra to trust — but every operation alias must be pinned in
   `Check.lean` (§12) as
   `example : Poly.neg = cpoly.<generated name> := rfl`, because the mangled
   name encodes the impl's shape and moves when the impl moves.
3. **Representation layer before any statement.** Reuse the house functions:
   `toExt` on field words under `Reduced`, `toRaw` (= `map toExt`, giving a
   `CPolynomial.Raw F`) on `Vec Ext4` under `VecReduced`. A genuinely new
   extracted type gets, in this order and before its first spec: a
   representation **function**, its invariant predicate, the coefficient kit
   (`_coeff` characterization, `@[simp] _size`, in-range and out-of-range
   lemmas — the `toRaw_coeff*` family is the template), and `Check.lean`
   entries proving the invariant is not `True` and the function does not
   collapse (§2/§4 pattern). If no total representation function can exist,
   stop and read `aeneas-equivalence-bridges`.
4. **Hypotheses: invariants plus earned value bounds, nothing else.** Each
   input contributes its representation invariant. A *value* hypothesis is
   admitted only when a concrete fail point in the generated code forces it —
   walk every checked scalar op, `Vec.push`, and index on every path. The
   canonical example: `mul_spec` carries
   `v.val.length + w.val.length ≤ Usize.max` because the generated code sizes
   its accumulator with a **checked** `np + nq`; without it the triple is
   *false*, not merely unprovable. Most fail points discharge under the
   invariants alone — recognize these and do NOT hypothesize for them:
   a `Vec.push` whose output length is bounded by an input vector's length
   (the `Vec` type itself carries `≤ Usize.max`); a counter's checked
   `i + 1` under the loop guard `i < n`; guarded indexing with the bound
   pinned to `Vec.len`; `Vec.len`/`Vec.new`, which are pure. The theorem's
   docstring records the walk either way: for a value bound, the fail point
   and why the bound is minimal; when no bound is needed, one or two lines
   saying why the walk closes (this is what a reviewer disputing a *missing*
   hypothesis reads). Constructing the disproof and gating any weakening is
   `prove-sorry` Phase 1's job — the author's job is to draft the minimal
   set and leave the justification trail.
5. **Postcondition: success, invariant, commutation.** The triple is
   `Aeneas.Std.spec`, definitionally `∃ r, m = ok r ∧ post r` — total
   correctness, so success is asserted by the form itself; the postcondition
   states invariant preservation and the `rep`-commutation equality, with
   the **named** CompPoly def on the right (`CPolynomial.Raw.neg (toRaw v)`,
   never the instance notation `-(toRaw v)`). A caller must be able to chain
   the theorem, so whatever the proof needs about inputs must be
   reestablished about outputs (a precondition without the matching
   postcondition breaks self-composition) — but add an explicit clause
   (size, bounds) only when it is *not derivable* from the commutation
   equality: a length that follows via `toRaw_size` is noise, while
   `mul_spec`'s `z.val.length ≤ v.val.length + w.val.length` earns its place
   because trimming makes the length non-derivable and the clause is the
   caller's only route to discharging `hlen` on the outer product of
   `(v * w) * u`.
6. **One loop spec per generated `*_loop`.** Stated general in the loop
   state, with an invariant tying the accumulator's rep-image to the
   processed prefix (`s.1.val.map toExt = (p.val.take s.2.val).map …`) — or a
   pointwise characterization for in-place writes — shaped so the headline
   spec composes via `spec_bind`/`spec_mono`. The proved files carry the
   loop-state arguments both as plain binders with named hypotheses and
   under an inner `∀ … →` after the colon; both compose — match the nearest
   structural sibling and keep the loop-state components last so the
   headline instantiates them. Pure mathematics (convolution sums and their
   kin) is factored into plain defs with `_zero`/`_succ` step lemmas, kept
   free of the monadic plumbing (`convol` in `Univariate.lean` is the
   template).
7. **`@[step]` policy, per the proved files:** constructors and observers
   (`zero`, `from_coeffs`, `len`, `index`, `degree`, …) carry `@[step]` so
   larger proofs step through them; anything proved via a loop spec — and
   every headline operation spec — is a plain theorem, composed explicitly.
8. **Deliver stubs, not proofs.** Statements are born with `sorry` bodies
   but the file must typecheck before `prove-sorry` is launched — the stub
   set is the interface contract the parallel provers must compose against.
   The gate is mechanical: from `cpoly/`, `lake env lean lean/<file>.lean`
   (no Lake lock taken); success is zero `error:` lines, with
   `declaration uses 'sorry'` warnings expected on every stub. Each new
   headline spec also adds its `#print axioms <full name>` line to
   `Check.lean` §14 (cheap, and it is what makes a hidden `sorryAx`
   build-visible), plus a totality witness in the §5/§10 shape —
   `example : ∃ z, <generated name> args = ok z ∧ … := by
   have h := spec_imp_exists … (op_spec …); …` — only when no sibling of the
   same shape already witnesses that section.
9. **Champion re-spec** (accepted optimization, regenerated
   `Generated.lean`): headline statement text is carried over verbatim (the
   one rule); aliases are re-derived and re-pinned, since a changed impl
   shape re-mangles them; the *loop* specs are new and follow the opt
   definition's structure (a Karatsuba champion gets recursion-shaped
   sub-specs, not the schoolbook loops'), with `Foo.opt_eq_spec` splicing
   the proof onto the unchanged right-hand side. Any new hypothesis on a
   carried-over headline is a weakening and goes through `prove-sorry`'s
   approval gate.

## Failure modes with teeth

* **An unpinned alias.** Without the `rfl` pin, an upstream re-mangle (the
  impl header changed, Aeneas changed) silently repoints the theorem at a
  different definition — the build stays green and the spec claims nothing
  about the shipped code. `Check.lean` §12 exists because the names are
  derived, not chosen.
* **A hypothesis added for provability.** Every hypothesis weakens the
  theorem for every caller, and "add the bound, move on" is how a spec
  quietly stops covering real inputs. The gate is a concrete fail point in
  the generated code, machine-checked when disputed.
* **A true-but-vacuous spec.** A triple can typecheck and prove while
  claiming nothing — degenerate field, invariant secretly `True`, collapsed
  representation. This repo's entire `Check.lean` is the countermeasure;
  a new representation layer without its non-degeneracy entries is not done.
* **Stating what the code does.** A postcondition that mirrors the extracted
  structure ("returns the vec built by this loop") proves easily and pins
  nothing. The right-hand side is the CompPoly reference operation, always.
* **Authoring against a stale `Generated.lean`.** A committed extraction can
  lag the Rust after comment-only edits (Source-span drift); specs written
  against it bind names and shapes that no longer exist. Triage lives in the
  `aeneas-extract` skill — re-extract, then author.

## Invariants to keep green

* Every headline `_spec`: right-hand side is a `CompPoly.*` name; hypotheses
  are representation invariants plus counterexample-earned value bounds
  only; every value bound carries its docstring justification.
* Every alias is `rfl`-pinned in `Check.lean`, and every headline spec has
  its `#print axioms` line there.
* Stub files typecheck under `lake env lean` before `prove-sorry` launches.
* Loop specs compose: the headline proof is `spec_bind`/`spec_mono` over the
  stated sub-specs, never a monolith.
* A `sorry` in `cpoly/lean/` never reaches main — sorried states live on the
  champion branch until `verify-campaign` clears them.
