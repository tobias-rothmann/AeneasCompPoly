#!/usr/bin/env bash
# Regenerate the Aeneas-extracted Lean model of this crate.
#
#   ./extract.sh
#
# Pipeline:  cargo/charon -> cpoly.llbc -> aeneas -> lean-gen/Cpoly.lean
# and then installs the result as CPolyEquiv/CPolyEquiv/Generated.lean, which is
# what CPolyEquiv/CPolyEquiv/{Equiv,EquivMl}.lean prove things about.
#
# `Generated.lean` is DERIVED OUTPUT: never hand-edit it, run this instead.
#
# Toolchain: charon and aeneas must match each other and the Aeneas Lean backend
# checked out at ../aeneas. The simplest way to get a matching pair is the
# release built from that exact commit:
#
#   cd .. && git -C aeneas describe --tags        # e.g. nightly-2026.07.28-3a8586f
#   curl -sSL -o t.tar.gz \
#     https://github.com/AeneasVerif/aeneas/releases/download/<TAG>/aeneas-macos-aarch64.tar.gz
#   mkdir -p toolchain && tar xzf t.tar.gz -C toolchain
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
"$CHARON" cargo --preset=aeneas --dest-file cpoly.llbc -- --lib

echo "==> aeneas"
"$AENEAS" -backend lean -dest lean-gen cpoly.llbc

dest="$root/CPolyEquiv/CPolyEquiv/Generated.lean"
if [ -f "$dest" ] && cmp -s lean-gen/Cpoly.lean "$dest"; then
  echo "==> $dest already up to date"
else
  cp lean-gen/Cpoly.lean "$dest"
  echo "==> installed $dest"
fi

echo
echo "Now re-check the proofs:  (cd $root/CPolyEquiv && lake build)"
