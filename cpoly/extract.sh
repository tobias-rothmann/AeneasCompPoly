#!/usr/bin/env bash
# Regenerate the Aeneas-extracted Lean model of this crate.
#
#   ./extract.sh
#
# Pipeline:  cargo/charon -> generated.llbc -> aeneas -> lean/Generated.lean
#
# That last path is *inside* the Lean library (see `lakefile.lean`), so there is
# no copy of the model to keep in sync: aeneas writes the very file that
# lean/{Field,CPoly,CMlPoly}.lean import.
#
# Aeneas names its output after the basename of the .llbc, capitalised, which is
# the only reason the intermediate is called `generated.llbc`: it is what makes
# the Lean module come out as `Generated`, i.e. what `import Generated` finds.
# The module is top-level because `lean/` is the library's srcDir and has no
# subdirectory -- rename the .llbc and you rename the module.
#
# `Generated.lean` is DERIVED OUTPUT: never hand-edit it, run this instead.
#
# Naming: the whole crate lands in the Lean namespace `cpoly` (the crate name),
# and each item keeps its Rust module path. So `src/field.rs` gives
# `cpoly.field.*`, `src/cmlpoly.rs` gives `cpoly.cmlpoly.*`, and `src/cpoly.rs`
# -- a module whose name repeats the crate's -- gives `cpoly.cpoly.*`. Renaming
# or adding a module in `src/` therefore renames Lean definitions and requires
# updating lean/{Field,CPoly,CMlPoly,Check}.lean to match.
#
# Toolchain: charon and aeneas must match each other and the Aeneas Lean backend
# that this library builds against. That backend is fetched by Lake from the fork
# named in `lakefile.lean`, at the commit pinned in `lake-manifest.json`; it is
# nightly-2026.07.26-3a8586f plus Lean v4.32.0 API-drift fixes, which leave the
# extraction contract untouched. So the binaries to use are the ones from that
# upstream release -- the fixes are Lean-side only and do not affect extraction:
#
#   curl -sSL -o t.tar.gz \
#     https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.07.26-3a8586f/aeneas-macos-aarch64.tar.gz
#   mkdir -p ../toolchain && tar xzf t.tar.gz -C ../toolchain
#
# If the pinned backend commit ever moves to a different *upstream* base, these
# binaries have to move with it: `lean/Generated.lean` is only valid against the
# Aeneas version that produced it. Check with
#
#   python3 -c "import json;print([p for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='aeneas'][0]['rev'])"
#
# charon also needs the rust toolchain named in toolchain/rust-toolchain
# (with the rustc-dev, llvm-tools-preview and rust-src components).
#
# Override the binaries with CHARON / AENEAS if they live elsewhere.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(dirname "$here")"

CHARON="${CHARON:-$root/toolchain/charon}"
AENEAS="${AENEAS:-$root/toolchain/aeneas}"

for bin in "$CHARON" "$AENEAS"; do
  if [ ! -x "$bin" ]; then
    echo "error: $bin not found or not executable. See the header of $0." >&2
    exit 1
  fi
done

cd "$here"

# `--preset=aeneas` is mandatory: aeneas rejects an llbc emitted without it.
# `-- --lib` keeps cargo off the test targets, which are not part of the model.
echo "==> charon"
"$CHARON" cargo --preset=aeneas --dest-file generated.llbc -- --lib

# The library's srcDir. Aeneas drops `Generated.lean` straight in beside the
# hand-written modules; it writes nothing else here.
dest="lean"

# Keep a copy of the previous model outside the source tree, only so that the
# script can report whether anything actually moved.
before="$(mktemp -t cpoly-generated)"
trap 'rm -f "$before"' EXIT
[ -f "$dest/Generated.lean" ] && cp "$dest/Generated.lean" "$before"

echo "==> aeneas"
"$AENEAS" -backend lean -dest "$dest" generated.llbc

if [ -s "$before" ] && cmp -s "$before" "$dest/Generated.lean"; then
  echo "==> $dest/Generated.lean unchanged"
else
  echo "==> regenerated $dest/Generated.lean"
fi

echo
echo "Now re-check the proofs:  (cd $here && lake build)"
