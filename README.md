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
counterpart, with no `sorry`. The AI step is never trusted, but proved. 

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
  src/                the Rust: the field, then polynomials over it
  tests/              Rust-side semantics tests, one per module

  lakefile.lean       Lean library, srcDir `lean/`
  lean-toolchain      leanprover/lean4:v4.32.0
  lean/
    Generated.lean    the extracted model -- DERIVED by `make extract`, never hand-edit
    *.lean            one module per Rust module, proving it against CompPoly
    Check.lean        audit: the specs are not vacuous, and no `sorryAx` hides under one
```

Each Rust module maps onto one Lean module, and the extracted names keep the
Rust path: `cpoly::field::fadd` becomes `cpoly.field.fadd`.

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
