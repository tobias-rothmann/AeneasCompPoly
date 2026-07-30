# AeneasCompPoly

A machine-checked proof that a Rust implementation of computable polynomials
computes the same thing as the reference development in
[Verified-zkEVM/CompPoly](https://github.com/Verified-zkEVM/CompPoly).

The Rust crate is translated to a Lean model by
[Aeneas](https://github.com/AeneasVerif/aeneas)/Charon, and every operation of
that model is then proved — in Lean, against CompPoly — to succeed and to
commute with its CompPoly counterpart. The development contains no `sorry`.

The field is concrete throughout: base field `F_P` with `P = 2^32 - 99` (the
"Hachi" prime), and its quartic extension `Ext4 = F_P[Y] / (Y^4 - 2)`.

## Layout

The crate and the proofs about it live in one directory, `cpoly/`, which is
what lets Aeneas write its output straight into the Lean library with no copy
to keep in sync.

```
cpoly/
  Cargo.toml            the `cpoly` crate: a library, no dependencies
  src/
    lib.rs
    field.rs            Ext4 = F_P[Y]/(Y^4-2) over the Hachi prime P = 2^32-99
    cpoly.rs            univariate polynomials, Vec<Ext4> little-endian in X
    cmlpoly.rs          multilinear polynomials, Vec<Ext4> of length 2^n
  tests/                Rust-side semantics tests, one per module
  extract.sh            charon -> generated.llbc -> aeneas -> lean/Generated.lean

  lakefile.lean         Lean library `CPolyEquiv`, srcDir `lean/`
  lean-toolchain        leanprover/lean4:v4.32.0
  lake-manifest.json    pins the CompPoly revision
  lean/
    Generated.lean      DERIVED by extract.sh -- never hand-edit
    Field.lean          field layer:       cpoly.field.*   vs CompPoly.Extension.Ext
    CPoly.lean          univariate layer:  cpoly.cpoly.*   vs CompPoly.CPolynomial.Raw
    CMlPoly.lean        multilinear layer: cpoly.cmlpoly.* vs CompPoly.CMlPolynomial
    Check.lean          audit: checks the specs above are not vacuous
```

Each Rust module maps onto one Lean module, and the extracted names keep the
Rust path: `cpoly::field::fadd` becomes `cpoly.field.fadd`. Hence the doubled
`cpoly.cpoly` — the crate `cpoly` has a module named `cpoly`.

`Check.lean` is worth knowing about: nothing imports it, and it is a library
root of its own purely so that `lake build` checks it. It exists to catch specs
that are true but vacuous, and it prints the axiom dependencies of the headline
theorems so a reader can confirm no `sorryAx` is hiding under one.

## Building

Lake fetches everything the proofs need, so a fresh clone just builds:

```sh
cd cpoly
lake exe cache get     # Mathlib's prebuilt oleans; skip this and you compile Mathlib yourself
lake build
```

Run the Rust-side tests:

```sh
cd cpoly && cargo test
```

`lakefile.lean` names two dependencies, and `lake-manifest.json` pins the exact
commit of each. The manifest, not the branch name in the lakefile, is what makes
a clone reproducible:

* **CompPoly** — `Verified-zkEVM/CompPoly` @ `main`. Bump it deliberately with
  `lake update CompPoly`, and re-read the note below afterwards: `aeneas` and
  `lean-toolchain` have to move with CompPoly's Mathlib pin.

* **aeneas** — `tobias-rothmann/aeneas` @ `lean-4.32.0`, a **fork**. That needs
  explaining.

### Why the Aeneas backend is a fork

This development is on Lean/Mathlib v4.32.0, and has to be: the field it is
*about* lives in CompPoly's `Fields/Hachi.lean` and `Fields/Extension/`, which
only exist after CompPoly's own v4.32.0 bump. Upstream Aeneas has no v4.32.0
release — its Lean backend hard-`require`s Mathlib v4.31.0, and every nightly up
to and including `nightly-2026.07.30-3a8586f` is still on v4.31.0.

So the backend is `nightly-2026.07.26-3a8586f` (commit `3a8586fa`) plus a single
commit repairing the v4.32.0 API drift: `lean-toolchain` and `lakefile.lean`
moved to v4.32.0, plus API-only fixes under `Aeneas/Data`, `Aeneas/Tactic` and
`AeneasMeta`. No semantic change, no `sorry`, no weakened proof, and the
`#guard_msgs` expectations are untouched.

**When upstream publishes a v4.32.0 nightly**, point the `require` in
`cpoly/lakefile.lean` at it, run `lake update aeneas`, and the fork can be
deleted. Until then this build depends on the fork staying reachable — that is
the one external thing holding reproducibility up.

## Prerequisites, for re-extraction only

Nothing above needs anything from outside the repository. Regenerating
`lean/Generated.lean` from the Rust source does: it needs the charon and aeneas
binaries, which blow past GitHub's 100 MB file limit and so live in an ignored
`../toolchain`.

```sh
cd ..
mkdir -p toolchain
curl -sSL https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.07.26-3a8586f/aeneas-macos-aarch64.tar.gz \
  | tar xz -C toolchain
```

Those binaries must stay on the **same Aeneas commit as the Lean backend above**
(`3a8586fa`): `lean/Generated.lean` is only valid against the Aeneas version that
produced it, so bumping one without the other silently invalidates the proofs.
charon additionally needs the Rust toolchain named in `toolchain/rust-toolchain`
(`nightly-2026-06-01`, with the `rustc-dev`, `llvm-tools-preview` and `rust-src`
components). `extract.sh` takes `CHARON` and `AENEAS` overrides if the binaries
live elsewhere.

## Regenerating the extracted model

After any change to `src/`:

```sh
cd cpoly && ./extract.sh && lake build
```

This runs charon into `generated.llbc` and then aeneas into
`lean/Generated.lean`, and reports whether the model actually moved. Read the
header of `extract.sh` before changing anything about it — in particular, the
intermediate is called `generated.llbc` precisely because Aeneas names its
output module after the file's basename, so renaming it renames the Lean module
that `Field.lean`, `CPoly.lean` and `CMlPoly.lean` import.

Renaming or adding a module under `src/` likewise renames extracted Lean
definitions, and adding a module under `lean/` means adding it to `roots` in
`lakefile.lean` — the library has no root module to reach the rest through, so
every module is listed there explicitly.
