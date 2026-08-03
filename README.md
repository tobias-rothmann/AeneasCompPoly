# AeneasCompPoly

Executable Rust for Lean specifications, with a machine-checked proof that the
Rust computes what the specification says — here for the computable polynomials
of [Verified-zkEVM/CompPoly](https://github.com/Verified-zkEVM/CompPoly).

```
        Lean world             ┊             Rust world
                               ┊
   ┌──────────────────┐   AI writes it  ┌──────────────────┐
   │  CompPoly specs  │────────────────►│    cpoly/src     │
   └──────────────────┘        ┊        └──────────────────┘
             ▲                 ┊                  │
             │  equivalence    ┊                  │  extract via
             │  proofs         ┊                  │  Aeneas
             ▼                 ┊                  │
   ┌──────────────────┐        ┊                  │
   │  Generated.lean  │◄──────────────────────────┘
   └──────────────────┘        ┊
```

Every operation is proved to succeed and to commute with its CompPoly
counterpart, with no `sorry`. The AI step is never trusted, but proved. What *is*
trusted is enumerated under [Trusted computing base](#trusted-computing-base).

The Rust is meant to be Rust, not transliterated Lean: the arithmetic is the
`core::ops` traits, each layer's representation is a newtype, and the crate is
`no_std`, `forbid(unsafe_code)` and clean under `clippy::pedantic`. See
[The Rust side](#the-rust-side) for what that costs the proofs (almost nothing)
and where the extraction still constrains the code (loops, and three `std` calls
to avoid).

The goal of this project is not only to do the trivial translation, but to employ AI to heavily optimize the Lean definitions, Rust code, and the Lean-Rust loop. 

The field is concrete throughout: base field `F_P` with `P = 2^32 - 99` (the
"Hachi" prime), and its quartic extension `Ext4 = F_P[Y] / (Y^4 - 2)`.

## Usage

```sh
make setup     # install everything: elan, the Lean dependencies, rust, the extraction binaries
make build     # check the proofs
make extract   # regenerate lean/Generated.lean from src/
```

`make` on its own lists the targets.

A fresh clone needs `make setup` once. It takes a few minutes, and installs nothing system-wide: the extraction binaries go in
`./toolchain`, the rest into the per-user directories elan and rustup manage.

`make build` fails if any declaration under `lean/` uses `sorry`, or if `sorryAx`
turns up in the axiom dependencies `Check.lean` prints.

`make clean` drops the build output and keeps the downloads. Overriding
`CHARON=` or `AENEAS=` on the command line points `make extract` at binaries
kept elsewhere.

## Layout

```
Makefile              setup, build, test, extraction
toolchain/            charon and aeneas, put there by `make setup`; not in git

cpoly/
  Cargo.toml          the `cpoly` crate: a library, no dependencies
  src/
    field.rs          Fp (base field) and Ext4 (its quartic extension)
    univariate.rs     UnivariatePoly: dense coefficient vectors
    multilinear.rs    MultilinearPoly / MultilinearEvals: two readings of a 2^vars table
  tests/              Rust-side semantics tests, one per module

  lakefile.lean       Lean library, srcDir `lean/`
  lean-toolchain      leanprover/lean4:v4.32.0
  lean/
    Generated.lean    the extracted model -- DERIVED by `make extract`, never hand-edit
    Field.lean        proves src/field.rs against CompPoly's Hachi.Ext4
    Univariate.lean   proves src/univariate.rs against CPolynomial.Raw
    Multilinear.lean  proves src/multilinear.rs against CMlPolynomial(Eval)
    Check.lean        audit: the specs are not vacuous, and no `sorryAx` hides under one
```

Each Rust module maps onto one Lean module, and the extracted names keep the
Rust path: `cpoly::field::Fp::new` becomes `cpoly.field.Fp.new`. Trait impls get
the name Aeneas mangles from the impl header, so `impl Add for Ext4` becomes
`cpoly.field.Ext4.Insts.CoreOpsArithAddExt4Ext4.add`; `impl Add<&Poly> for &Poly`
becomes `cpoly.Shared1Poly.Insts.CoreOpsArithAddShared0PolyPoly.add`, whose
`Shared`-prefix is *not* module-qualified — so two types in different modules may
not share a *base* name if both have by-reference operator impls. That is the only
reason the multilinear types are `MultilinearPoly`/`MultilinearEvals` rather than
`Poly`/`Evals`, and why the univariate one is `UnivariatePoly` rather than
`Poly`: the two would collide.

Two things to keep in mind when adding to either side. Adding a module under
`lean/` means adding it to `roots` in `lakefile.lean`, which lists every module
explicitly. Renaming or adding one under `src/` renames extracted Lean
definitions, so the modules under `lean/` have to be updated to match.

## The Rust side

The crate is written as a Rust library first. `Fp` wraps a *private* `u64`, so the
"representative is below `P`" invariant the proofs call `Red` holds of every value a
caller can build. `UnivariatePoly`, `MultilinearPoly` and `MultilinearEvals` are
newtypes, and the last two matter most: they are the same `2^vars` words under two
different readings, and before they were separate types nothing stopped a caller
evaluating a hypercube table as if it were a coefficient table. As on the CompPoly
side, the unmarked name is the coefficient form — `MultilinearPoly` mirrors
`CMlPolynomial`, `MultilinearEvals` mirrors `CMlPolynomialEval` — and
`MultilinearPoly::to_evals` / `MultilinearEvals::to_coeffs` are the only way across.

Arithmetic is `Add`, `Sub`, `Mul`, `Neg` and the `*Assign` forms, plus
`impl Mul<Ext4> for Fp` for scaling and `Index<usize>` on the polynomial types. The
binary operators on polynomials are the by-reference impls (`&p + &q`), as in
`num-bigint` and `ark-poly`.

None of that costs the proofs anything structural. Aeneas extracts a single-field
tuple struct as a `@[reducible]` abbreviation, so `cpoly.field.Fp` *is* `Std.U64`
and `cpoly.univariate.Poly` *is* `alloc.vec.Vec cpoly.field.Ext4` on the Lean side;
and it extracts a trait impl as an ordinary definition whose body is exactly what
the corresponding free function's was. Moving from free functions to operators was a
rename in the proofs. [Check.lean](cpoly/lean/Check.lean) §7–§11 verify that, and §8
records the limitation that comes with it: because the wrappers are erased,
`MultilinearPoly` and `MultilinearEvals` are the *same* Lean type, so their
separation is enforced by rustc and not by the proofs.

Three habits in `src/` *are* for the extraction rather than the reader, and
`src/lib.rs` says so at the point of use:

* **Index-based `while` loops, and no iterator adaptors.** `.map`, `.zip`, `.fold`
  and `.collect` have no model in the Aeneas Lean backend. `for i in 0..n` *does*,
  but it replaces a `usize` counter with a `Range<usize>` iterator, and that state
  is what every loop invariant in `Univariate.lean` and `Multilinear.lean` is
  written about — so the cost lands in the files people actually read.
* **Readable aliases for the operator impls.** Aeneas mangles
  `impl Add<&UnivariatePoly> for &UnivariatePoly` into
  `cpoly.Shared1UnivariatePoly.Insts.CoreOpsArithAddShared0UnivariatePolyUnivariatePoly.add`,
  which is unreadable in a theorem statement, so `Univariate.lean` and
  `Multilinear.lean` open with a block of `abbrev`s (`Poly.add`, `Ml.polyNeg`, …).
  An `abbrev` is `@[reducible]`, so a theorem about the alias *is* a theorem about
  the extracted definition — nothing extra to trust — and `Check.lean` §12 pins
  each alias to its generated name with `rfl`.
* **Bit tests as `/` and `%`, not `>>` and `&`**, so the model stays in `Usize`
  arithmetic that `scalar_tac` and `omega` see through.
* **Three `std` calls avoided**: `Vec::is_empty`, `Vec::truncate` and
  `#[derive(Default)]` on a `Vec`-holding struct, each of which would put an `axiom`
  into `Generated.lean`. It currently has none, which is worth keeping: grep for
  `axiom` after every `make extract`.

To find out what Aeneas does with an idiom, do not reason about it — probe it. Build
a throwaway crate, run `toolchain/charon cargo --preset=aeneas --dest-file p.llbc --
--lib` then `toolchain/aeneas -backend lean -dest out p.llbc`, and read the Lean.
Two things that are easy to get wrong: the *shape of a loop's state* can change when
a helper is inlined (check the `(fun (…) =>` line of each generated loop after
re-extracting), and the *order of statements* in Rust is the order of binds in Lean,
so collapsing `let lo = …; let hi = …; lo + x*hi` into one expression invalidates
every `step as ⟨…⟩` sequence that walks it.

What is still missing, in rough order of value:

* `MultilinearPoly`/`MultilinearEvals` do not store their arity, so
  `p.len() == table_len(vars)` is a caller obligation and `vars` is passed to
  `zeros`, `from_coeffs`, `to_evals` and `to_coeffs` separately. Making it a field
  would turn that into an invariant, at the cost of the Lean representation
  functions moving from the vector to a `.table` projection.
* No inversion, hence no `Div` and no `Field`-style trait. `Ext4` *is* a field
  ([field_semantics.rs](cpoly/tests/field_semantics.rs) checks `x^(P^4-1) = 1`), so
  this is a gap in the API rather than in the mathematics.
* By-value operator impls (`p + q` as well as `&p + &q`) would each need their own
  one-line spec to keep the "every public operation is proved" property. That
  property currently does hold literally, accessors and `Index` included — 105
  `_spec` theorems across the three proof files — which is worth preserving when
  adding API.
* `Display`, and a `Debug` that prints the value rather than the derived `Fp(1234)`,
  both of which need `core::fmt` plumbing in the extracted model.

## Dependencies and pins

Lake fetches both Lean dependencies itself and records the exact revision of
each in `lake-manifest.json`, which is what makes a clone reproducible:

* **CompPoly** — `Verified-zkEVM/CompPoly` @ `main`. Bump with `lake update
  CompPoly`, and re-check the Mathlib pin afterwards: `aeneas` and
  `lean-toolchain` have to move with it.

* **aeneas** — `tobias-rothmann/aeneas` @ `lean-4.32.0`, a **fork** of
  `nightly-2026.07.26-3a8586f` carrying Lean v4.32.0 API-drift fixes. The
  comments in `cpoly/lakefile.lean` say why it exists and when it can be dropped
  for upstream.

The charon and aeneas *binaries* `make extract` runs are a separate artifact,
pinned by `AENEAS_TAG` and `AENEAS_COMMIT` in the `Makefile` and downloaded from
the **upstream** release: the fork touches only `backends/lean`, so its binaries
would be identical. They have to stay on the same Aeneas commit as the backend,
since `lean/Generated.lean` is only valid against the version that produced it —
`make setup` checks both directions and `make extract` re-checks the binaries.

A Lean bump therefore moves the fork first, then `lake-manifest.json`,
`lean-toolchain` and the Makefile pins together.

## Trusted computing base

We list the trusted computing base (TBC) here. These are trusted components that lie outside of our verification boundary.

| Trusted | Why it cannot be checked away | If it is wrong |
|---|---|---|
| **[Lean kernel](https://github.com/leanprover/lean4/tree/v4.32.0/src/kernel)** — ~8k lines of C++, plus `propext`, `Classical.choice`, `Quot.sound` | No machine-checked proof of it exists; its C fast path for `Nat` carries every `decide` in [Field.lean](cpoly/lean/Field.lean) | A false theorem, with no diagnostic |
| **Aeneas extraction** — [charon](https://github.com/AeneasVerif/charon) + [aeneas](https://github.com/AeneasVerif/aeneas), and their hand-written [model of Rust `std`](https://github.com/AeneasVerif/aeneas/blob/main/backends/lean/Aeneas/Std/Vec.lean) | [`Generated.lean`](cpoly/lean/Generated.lean) is asserted to model [`src/`](cpoly/src/), never proved: the paper proof covers a fragment, the OCaml that ran does not | The proofs are about a different program |
| **Rust to machine code** — rustc, LLVM, linker, libc, OS, CPU | No verified Rust compiler exists; memory safety is inherited from the borrow checker, not proved | The binary betrays a correct proof |
| **The specs** — [CompPoly](https://github.com/Verified-zkEVM/CompPoly)'s definitions and the `toExt`/`Reduced` relations | They *are* the definition of correct; degenerate ones would make every spec true and empty | True theorems about the wrong thing |

## License

Apache-2.0 — see [LICENSE](LICENSE). The same terms as both dependencies,
[CompPoly](https://github.com/Verified-zkEVM/CompPoly) and
[aeneas](https://github.com/AeneasVerif/aeneas), so combining them adds no
further obligations.
