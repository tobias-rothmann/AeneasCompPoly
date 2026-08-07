---
name: aeneas-idiomatic-rust
description: Making an Aeneas-extracted Rust crate idiomatic (newtypes, core::ops operators, methods, slices) without breaking extraction or the Lean equivalence proofs — which idioms are free, which inject axioms, and how to repair the specs
---

# Idiomatic Rust Under Aeneas

For work on `cpoly/src/` — turning transliterated-Lean Rust into Rust, while
`make build` stays green and no `sorry` appears. Read this **before** touching
`src/`, and read `README.md` § "The Rust side" plus `src/lib.rs`'s style notes,
which record the decisions this skill explains how to make.

## The one rule: probe, do not reason

Every prediction about what Aeneas does with a Rust idiom was wrong at least once
— including confident ones about newtypes, trait names, and loop shapes. A probe
takes two minutes and is decisive. Do it for **every** idiom you are unsure about.

```bash
S=/private/tmp/probe                     # or the session scratchpad
T=/Volumes/Festplatte/AeneasCompPoly/toolchain
mkdir -p $S/src && cd $S
printf '[package]\nname = "probe"\nversion = "0.1.0"\nedition = "2021"\n[lib]\nname = "probe"\npath = "src/lib.rs"\n' > Cargo.toml
# ... write src/lib.rs exercising ONE idiom per item, with a `pub fn use_it()`
#     caller so charon cannot drop it as dead code ...
$T/charon cargo --preset=aeneas --dest-file p.llbc -- --lib
mkdir -p out && $T/aeneas -backend lean -dest out p.llbc
```

Check **all four** things, in this order — each catches a different failure:

1. **Did aeneas error?** A name collision is a hard failure, not a warning.
2. **Did aeneas warn** `could not find the information for item 'X'`, or
   `contains extracted external, unknown definitions`? Then `X` has no model and
   the idiom is off-limits.
3. `grep -n '^axiom' out/P.lean` — **any** axiom means the idiom drags an
   unmodelled `std` item into the trusted base. `cpoly/lean/Generated.lean` has
   **zero** axioms; keep it that way.
4. **Does the output typecheck?** `cd cpoly && lake env lean $S/out/P.lean`.
   Warnings are fine; errors mean the model is unusable.

## Idiom verdicts (measured, not guessed)

### Free — the Lean model is unchanged or only renamed

| Rust | Extracted Lean | Proof cost |
|---|---|---|
| `pub struct Fp(u64);` — even with a **private** field | `@[reducible] def Fp := Std.U64` | none, it is reducibly the inner type |
| `pub struct Poly(Vec<Ext4>);` | `@[reducible] def Poly := alloc.vec.Vec Ext4` | none |
| two distinct newtypes over the same inner type | two reducible aliases — **note they are then the same Lean type** | none |
| `type Alias = Vec<Ext4>;` | vanishes entirely | none, and no Lean-side gain either |
| `impl Add for Ext4` | `def Ext4.Insts.CoreOpsArithAddExt4Ext4.add (self rhs : Ext4) : Result Ext4`, **body identical to the free function's** | rename |
| `impl Mul<Ext4> for Fp` (heterogeneous) | `Fp.Insts.CoreOpsArithMulExt4Ext4.mul` | rename |
| `impl Add<&T> for &T` | `Shared1T.Insts.CoreOpsArithAddShared0TT.add (self rhs : T)` — refs erased | rename (but see collisions below) |
| `impl T { const ZERO: T }` | `@[global_simps, irreducible] def T.ZERO` — same shape as a module-level `const` | rename |
| inherent `fn is_zero(self)` | `def T.is_zero (self : T) : Result Bool` | rename |
| `impl Index<usize> for T` | one extra def unfolding to `alloc.vec.Vec.index …` | one `@[step]` lemma |
| `&[T]` parameter | `Slice T`, indexed by `Slice.index_usize` (has `@[step]`) | domain change, mechanical |
| `&Vec<T>` → `&[T]` at a call site | `alloc.vec.Vec.deref` — a **pure** function, not monadic | free |
| `#[derive(Debug)]` | transparent `fmt` def; **no axioms** | none |

### Strict simplifications — a loop disappears, so a proof gets *shorter*

| Rust | Extracted Lean |
|---|---|
| `vec![x; n]` (repeat form) | `alloc.vec.from_elem`, `@[step]` spec |
| `v.resize(n, x)` | `alloc.vec.Vec.resize`, `@[step]` spec. Pads **and** truncates, so it does pad-or-drop in one call |
| `v.clone()` | `alloc.vec.CloneVec.clone`; with `Ext4::clone = id` it collapses via `Slice.clone_spec` |
| `1usize << n` | `1#usize <<< n`. Fails iff `n ≥ numBits`, i.e. **exactly** where a checked-doubling `pow2` loop fails — same precondition, no loop |

### Forbidden — breaks extraction or adds an axiom

* **Iterator adaptors** — `.map`, `.zip`, `.fold`, `.collect` have no model.
  Aeneas warns and emits unknown definitions. Plain `for x in slice` and
  `for i in 0..n` *are* modelled.
* **`Vec::is_empty`** → `axiom alloc.vec.Vec.is_empty`. Write `self.len() == 0`.
  (`<[T]>::is_empty` on a **slice** *is* modelled — the asymmetry is real.)
* **`#[derive(Default)]` on a `Vec`-holding struct** → needs `Vec::default`,
  → axiom. Write the impl by hand.
* **The list form of `vec!`** — `vec![a, b]` goes through a stack array and
  `Slice::into_vec`, dragging in `axiom core.mem.maybe_uninit.MaybeUninit`. The
  *repeat* form `vec![x; n]` is fine. Use `Vec::new()` + `push` for short literals
  and `#[allow(clippy::vec_init_then_push)]` with a comment saying why.
* **`Vec::truncate`, `pop`, `last`, `first`, `clear`, `extend`** — no model.
  `resize` is the substitute for `truncate` and is documented as equivalent when
  shrinking.
* **`checked_shl`** and friends returning `Option` → axiom.

### Deliberately declined: `for i in 0..n`

It *works*. But it replaces a `usize` counter with a `Range<usize>` iterator in
the loop's **state**, and that state is what every loop invariant in
`lean/Univariate.lean` and `lean/Multilinear.lean` is written about. ~20 invariants
get worse in the files people actually read. Keep the counter loops and keep the
justification pointed at the theorem files.

## Who reads what — how to justify a Rust choice

The reviewer reads `lean/{Field,Univariate,Multilinear,Check}.lean`. They do **not**
read `Generated.lean`. Never argue "the generated model would be uglier"; ask what
the *theorem statement and its invariant* look like. Two consequences:

* Idioms that only make `Generated.lean` noisier (derives, extra trait impls that
  are pure delegation) are fine.
* Idioms that complicate a loop's state or a spec's domain are expensive even when
  the generated file looks tidy.

## Three failure modes that cost real time

### 1. `Shared<n><T>` name collisions — a hard extraction failure

Aeneas mangles `impl Trait for &T` into a prefix `Shared<n><T>` that is **not
module-qualified**. So `univariate::Poly` and `multilinear::Poly` both produce
`Shared1Poly.Insts.CoreOpsArithAddShared0PolyPoly` and extraction *fails*:

```
Error when registering the name for id: trait_impl_id: 56:
The chosen name is already in the names set: Shared1Poly.Insts.CoreOpsArithAddShared0PolyPoly
```

**Fix by making the type names distinct, not by contorting the API.**
`multilinear::MultilinearPoly` gives `Shared1MultilinearPoly` and coexists fine.
Two things that make this cheap: `clippy::module_name_repetitions` does **not**
fire in this toolchain, so `multilinear::MultilinearPoly` costs nothing; and a
*by-value* `impl Add for T` is module-qualified (`m.T.Insts.CoreOpsArithAddTT.add`)
and never collides. Current naming — `univariate::UnivariatePoly`,
`multilinear::{MultilinearPoly, MultilinearEvals}` — exists for this reason.

### 2. A loop's state shape can change silently

`impl Add for &Coeffs` written as `out.push(self.0[i] + rhs.0[i])` made Aeneas
carry `rhs` in the loop state as a **3-tuple** `(rhs, out, i)`, which breaks every
`rintro ⟨r1, i1⟩` and `s.2.val` in the invariant. Factoring the body into a helper
over slices — `fn add_pointwise(a: &[Ext4], b: &[Ext4]) -> Vec<Ext4>` — restored the
2-tuple **and** deduplicated the Rust between the two readings.

After every re-extraction, diff the loop states:

```bash
grep -A6 "^    (fun (" cpoly/lean/Generated.lean | grep -oE "\(fun \([a-z0-9, ]+\)" | sort | uniq -c
```

### 3. Statement order in Rust is bind order in Lean

Collapsing

```rust
let lo = coeffs[2 * j];
let hi = coeffs[2 * j + 1];
out.push(lo + x0 * hi);
```

into one expression reorders the extracted binds and invalidates the whole
`step as ⟨…⟩` sequence that walks it. Naming intermediates costs nothing and reads
better anyway. Same for `mul`: bind `prod` and `k` before the indexed assignment.

Corollary: `out[k] = out[k] + prod` and `out[k] += prod` extract **differently**
(the second goes through `IndexMut` and a write-back closure). Pick one, and
`#[allow(clippy::assign_op_pattern)]` with a reason if you keep the first.

## Staged workflow

Never do the Rust rewrite and the proof repair as one step.

1. **Probe** every uncertain idiom (above).
2. **Write the new Rust.** Get `cargo clippy --all-targets` clean and doc-tests
   passing *before* extracting. Doc examples are free — they are not extracted.
3. **`make extract`.** Then: `grep -c '^axiom'` must be 0; diff the loop-state
   shapes; skim the new names.
4. **Mechanical rename pass** on the Lean files. Build the map **longest-first** —
   `cpoly.cpoly.mul` is a prefix of `cpoly.cpoly.mul_loop0`, and replacing the
   short one first silently corrupts the long one. Assert every replacement landed;
   a silent no-op `str.replace` is the main way this goes wrong.
5. **Fix the structural changes one at a time**, checking with
   `lake env lean lean/<File>.lean` — not a full `lake build`.
6. **`make build` && `make test`**, then re-run `make extract`: it must report
   `unchanged`, which is the determinism check.

## Lean-side repair kit

Things the repaired proofs need that are not obvious:

* **`bind_ok_id`.** Methods whose Rust tail is a local they just bound extract as
  `let x ← m; ok x`, which blocks `spec_mono` from seeing the last call as the
  whole body. `Field.lean` defines `@[simp] theorem bind_ok_id (m : Result α) :
  (do let x ← m; ok x) = m`; open such a proof with `simp only [bind_ok_id]`.
* **`Slice α` and `Vec α` are the same subtype** (`{ l : List α // l.length ≤
  Usize.max }`), so a predicate written about `alloc.vec.Vec` applies to a `Slice`
  and `.val` works on both. `Vec.deref` is the identity, so `deref_val`,
  `deref_len`, `coeffFn_deref` are all `rfl`.
* **`abbrev` aliases for mangled operator names.** The statements are what gets
  read, and
  `cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add`
  is not readable. Declare `abbrev Poly.add := <mangled>` and state the spec about
  `Poly.add`. `abbrev` is `@[reducible]`, so this is an abbreviation and not a
  wrapper — nothing is added to the trusted base. **Pin every alias in
  `Check.lean` with `rfl`** so an upstream rename cannot silently repoint one.
  Gotcha: **`rw [Poly.add]` does not work** on an `abbrev` ("Failed to rewrite
  using equation theorems"). Open the proof with `unfold Poly.add` and then
  `rw [<mangled name>]`.
* **`toMlEval` is an `abbrev` for `toMl`**, so `rw [X]` whose LHS is `toMl n z`
  will not fire on a goal displaying `toMlEval n z`. Insert
  `show toMl n z = _` first.
* **Stale `.olean` trap.** `lake env lean lean/Univariate.lean` uses whatever
  `Field.olean` exists. After editing `Field.lean`, run `lake build Field` first —
  otherwise you get a screen of bogus `unknown identifier` errors and waste time
  hunting a rename that was already correct.
* **`Usize.numBits` is opaque**, not definitionally `System.Platform.numBits`; the
  bridge is `Std.Usize.numBits_eq`, and `Usize.max_def` / `Usize.size_def` open the
  `irreducible_def`s. State shift side conditions in terms of
  `System.Platform.numBits`, not `64`, so they do not assume the platform.

## Invariants to keep green

* **Zero axioms** in `Generated.lean`.
* **Zero `sorry`** — `make build` greps for it and fails, so a `sorry` is not a
  usable placeholder here.
* **Every public operation has a spec.** This currently holds *literally* —
  accessors, `Index`, `Default`, `From` included, 111 `_spec` theorems. It is easy
  to break by adding API; adding a by-value operator impl means adding its
  one-line corollary spec too.
* **`cargo clippy --all-targets` clean** under `pedantic`. Note `--all-targets`
  now includes `benches/`. Where a lint is wrong for this crate, `#[allow]` it
  **with a one-line reason**, at the narrowest scope.
* **`make bench-check` passes.** Touching `src/` has benchmark obligations; see
  the section below.
* **Never weaken a spec to make it pass.** If a statement cannot be proved,
  the interesting possibilities are that the Rust is wrong, the reference is a
  different operation, or a hypothesis is genuinely needed — say which, do not
  quietly add a hypothesis or drop a conjunct.

## The trap a mechanical rename sets

Two newtypes over the same inner type are **the same Lean type**. So a spec that
pairs `MultilinearEvals::add` with `CMlPolynomial.add` (the *coefficient*-form
reference) typechecks and is **wrong**, and no amount of `lake build` will catch
it. After any rename touching the two readings, check every pairing by hand:

```bash
for t in add_spec add_evals_spec eval_spec eval_lagrange_spec \
         eval_horner_spec eval_mle_spec mono_to_lagrange_spec lagrange_to_mono_spec; do
  printf '%-26s ' "$t"
  sed -n "/^theorem $t /,/:= by/p" cpoly/lean/Multilinear.lean \
    | grep -oE "toMl(Eval)? |CMlPolynomial(Eval)?\.[a-zA-Z]+" | sort -u | tr '\n' ' '
  echo
done
```

`CMlPolynomial` must go with `toMl`, `CMlPolynomialEval` with `toMlEval`, and the
two transforms cross exactly once each. `Check.lean` §8 records that this
separation is enforced by rustc and *not* by the proofs — that belongs in the
trusted-computing-base table, because it is a real limitation.

## Watch for capability regressions

Splitting one type into two removes every operation the callers used to get from
the shared type. Making `MultilinearPoly` and `MultilinearEvals` distinct silently
removed *negation and scalar multiplication* from the multilinear layer — they had
been the univariate operations applied to a shared `Vec<Ext4>` — and left two specs
proving things about operations no caller could invoke any more. After a type split,
enumerate what the old shared type could do and check each capability survived.

## What a change to `src/` owes the benchmarks

`cpoly/benches/` measures every operation here against `benches/genesis/`, a
frozen copy of its *first* translation. Three obligations follow, and
`make bench-check` enforces all three — run it before you call a refactor done.

**Never apply a rename inside `benches/genesis/`.** This is the trap, because the
mechanical rename pass above trains exactly the wrong reflex. Genesis is
append-only and byte-exact: every item is verified against the git blob of the
commit its `// @genesis` annotation names, so "fixing" it to match a rename
breaks the check *and*, if the check were somehow satisfied, would silently
rewrite what every past measurement was compared against. Genesis records what
the code used to be. That is the whole point of it.

**A renamed or split item needs a new frozen entry.** `bench-check` lists items
in `src/` with no counterpart in genesis, and a rename produces exactly that: the
new path is unfrozen while the old one sits in genesis forever. Copy the item's
current text in, `make bench-stamp`, and leave the old entry alone. The 2026-07-31
split of `Poly` into `MultilinearPoly`/`MultilinearEvals` is the shape of change
that does this.

**A renamed item also orphans its coverage markers.** `// @covers <path>` lines in
`benches/*.rs` and keys in `benches/exclusions.toml` are full item paths —
`multilinear::<&MultilinearPoly as Neg>::neg` — so a rename dangles them.
`bench-check` fails on a `@covers` path that names no item, which is how you find
them; grep the old name in `benches/` and fix both places.

The reverse direction matters too: **adding a public operation** means freezing it
and, if its docstring says `Mirrors CompPoly.X`, benching it or excluding it by
name with a reason. `.claude/skills/rust-bench` is the procedure.
