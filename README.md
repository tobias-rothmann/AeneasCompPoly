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
    univariate.rs     Poly: dense coefficient vectors
    multilinear.rs    Coeffs / Evals: the two readings of a 2^vars table
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
`Shared`-prefix is *not* module-qualified — which is why two types in different
modules may not share a name (see the note on `Coeffs` below).

Two things to keep in mind when adding to either side. Adding a module under
`lean/` means adding it to `roots` in `lakefile.lean`, which lists every module
explicitly. Renaming or adding one under `src/` renames extracted Lean
definitions, so the modules under `lean/` have to be updated to match.

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
