# Setup, proof checking and re-extraction for AeneasCompPoly.
#
#   make setup     install everything the other targets need
#   make build     check the Lean proofs
#   make extract   regenerate cpoly/lean/Generated.lean from cpoly/src/
#
# `make setup` is idempotent and safe to re-run: it records what it did in
# ./.make/ and skips work already done. What it installs goes either inside this
# directory (./toolchain) or into the standard per-user toolchain roots that
# elan and rustup manage themselves (~/.elan, ~/.rustup, ~/.cargo). Nothing is
# installed system-wide.
#
# README.md says what the repository is; this file is how you drive it.

SHELL := /bin/bash

# --- Pins --------------------------------------------------------------------

# The Aeneas release the extraction binaries come from, and the upstream commit
# it was built at. That commit is the invariant worth protecting: the Lean
# backend required by cpoly/lakefile.lean is a fork of this same commit, and
# cpoly/lean/Generated.lean is only valid against the Aeneas version that
# produced it. The binaries self-report the commit, so `setup` and `extract`
# check it rather than assume it -- bumping one side without the other would
# otherwise silently invalidate the proofs.
AENEAS_TAG    := nightly-2026.07.26-3a8586f
AENEAS_COMMIT := 3a8586f

# Rust components charon needs on top of a bare toolchain. The *channel* is not
# pinned here: it is read from the `rust-toolchain` that ships beside charon,
# which is also where charon itself looks -- so overriding CHARON below moves
# the lookup with it.
RUST_COMPONENTS := rustc-dev llvm-tools-preview rust-src

# --- Layout ------------------------------------------------------------------

PKG       := $(CURDIR)/cpoly
TOOLCHAIN := $(CURDIR)/toolchain
STAMPS    := $(CURDIR)/.make

# Overridable, for binaries kept somewhere else: `make extract CHARON=/path/to/charon`.
CHARON := $(TOOLCHAIN)/charon
AENEAS := $(TOOLCHAIN)/aeneas

# The extraction pipeline: charon writes the .llbc, aeneas turns it into a Lean
# module inside the library's srcDir. Aeneas names that module after the
# basename of the .llbc, so `generated.llbc` is what makes `import Generated`
# resolve -- renaming it renames the module the proofs import.
LLBC      := generated.llbc
GENERATED := $(PKG)/lean/Generated.lean

# charon resolves its rustc toolchain from a `rust-toolchain` beside its own
# executable, so this follows CHARON rather than assuming ./toolchain.
RUST_TOOLCHAIN_FILE := $(dir $(CHARON))rust-toolchain

# So that a freshly installed elan or rustup is usable within this same `make`
# run, without the user having to open a new shell first.
export PATH := $(HOME)/.elan/bin:$(HOME)/.cargo/bin:$(PATH)

OS    := $(shell uname -s | tr '[:upper:]' '[:lower:]' | sed 's/^darwin$$/macos/')
ARCH  := $(shell uname -m | sed -e 's/^arm64$$/aarch64/' -e 's/^amd64$$/x86_64/')
ASSET := aeneas-$(OS)-$(ARCH).tar.gz
URL   := https://github.com/AeneasVerif/aeneas/releases/download/$(AENEAS_TAG)/$(ASSET)

# Two halves of the setup, tracked separately so `build` does not drag in the
# extraction toolchain and vice versa. The tag is part of the toolchain stamp's
# name, so moving the pin above invalidates it on its own.
LEAN_STAMP := $(STAMPS)/lean-deps
TC_STAMP   := $(STAMPS)/toolchain-$(AENEAS_TAG)
BUILD_LOG  := $(STAMPS)/build.log

.DEFAULT_GOAL := help
.PHONY: help setup build test extract check-toolchain clean

help:
	@echo ''
	@echo '  make setup     install all prerequisites (elan, Lean deps, charon/aeneas, rust)'
	@echo '  make build     check the Lean proofs -- fails on any error or `sorry`'
	@echo '  make extract   regenerate cpoly/lean/Generated.lean from cpoly/src/'
	@echo '  make test      run the Rust-side semantics tests'
	@echo '  make clean     drop build output, keeping fetched dependencies'
	@echo ''
	@echo '  A fresh clone needs `make setup` once, then `make build`: roughly three'
	@echo '  minutes and 8.5 GB for the first, four for the second. Mathlib comes'
	@echo '  prebuilt from its cache, but the Aeneas backend and CompPoly are'
	@echo '  compiled locally. Later builds are incremental.'
	@echo ''

# --- setup -------------------------------------------------------------------

setup: $(LEAN_STAMP) check-toolchain
	@echo '==> setup complete. `make build` checks the proofs, `make extract` regenerates the model.'

$(STAMPS):
	@mkdir -p $@

# Lean side: elan, then the dependency graph pinned in lake-manifest.json, then
# Mathlib's prebuilt oleans. Re-runs if either pin file moves -- notably after a
# `lake update`.
$(LEAN_STAMP): $(PKG)/lean-toolchain $(PKG)/lake-manifest.json | $(STAMPS)
	@echo '==> Lean toolchain and dependencies'
	@set -euo pipefail; \
	if ! command -v elan >/dev/null; then \
	  echo '    installing elan (Lean toolchain manager)'; \
	  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none; \
	fi; \
	echo "    elan $$(elan --version | awk '{print $$2}'), toolchain $$(cat $(PKG)/lean-toolchain)"
	@set -euo pipefail; cd $(PKG); \
	if ! lake exe cache get; then \
	  echo 'warning: `lake exe cache get` failed. The build will still work, but it' >&2; \
	  echo '         will compile Mathlib from source, which takes hours. Re-run' >&2; \
	  echo '         `make setup` to retry the cache download.' >&2; \
	fi
	@set -euo pipefail; \
	fork='$(PKG)/.lake/packages/aeneas'; \
	if [ ! -d "$$fork/.git" ]; then \
	  echo '    backend commit unchecked: no git history in .lake/packages/aeneas'; \
	elif git -C "$$fork" merge-base --is-ancestor '$(AENEAS_COMMIT)' HEAD 2>/dev/null; then \
	  echo "    backend is $(AENEAS_COMMIT) + $$(git -C "$$fork" rev-list --count '$(AENEAS_COMMIT)'..HEAD) commit(s)"; \
	else \
	  echo 'error: the pinned Aeneas backend is not a descendant of $(AENEAS_COMMIT), the' >&2; \
	  echo '       commit the extraction binaries are built from. lean/Generated.lean is' >&2; \
	  echo '       only valid against the Aeneas version that produced it, so move the' >&2; \
	  echo '       Makefile pins and the aeneas rev in lake-manifest.json together.' >&2; \
	  exit 1; \
	fi
	@touch $@

# Extraction side: the charon/aeneas release binaries, plus the rustc nightly
# charon needs. Skips the download when binaries at the right commit are already
# in place, so an existing ./toolchain is adopted rather than re-fetched.
$(TC_STAMP): | $(STAMPS)
	@echo '==> extraction binaries ($(AENEAS_TAG), $(OS)-$(ARCH))'
	@set -euo pipefail; \
	if [ -x '$(CHARON)' ] && [ -x '$(AENEAS)' ] && '$(AENEAS)' -version | grep -q -- '$(AENEAS_COMMIT)'; then \
	  echo "    already present: $$('$(AENEAS)' -version)"; \
	else \
	  mkdir -p '$(TOOLCHAIN)'; \
	  echo '    downloading $(ASSET) (~124 MB)'; \
	  curl -fL --retry 3 --progress-bar -o '$(TOOLCHAIN)/$(ASSET).part' '$(URL)'; \
	  tar xzf '$(TOOLCHAIN)/$(ASSET).part' -C '$(TOOLCHAIN)'; \
	  rm -f '$(TOOLCHAIN)/$(ASSET).part'; \
	fi
	@set -euo pipefail; \
	if ! command -v rustup >/dev/null; then \
	  echo '    installing rustup'; \
	  curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal; \
	fi; \
	channel=$$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' '$(RUST_TOOLCHAIN_FILE)' | head -1); \
	if [ -z "$$channel" ]; then \
	  echo 'error: no channel found in $(RUST_TOOLCHAIN_FILE)' >&2; exit 1; \
	fi; \
	echo "    rust $$channel + $(RUST_COMPONENTS) (for charon)"; \
	rustup toolchain install --profile minimal --no-self-update "$$channel" >/dev/null; \
	rustup component add --toolchain "$$channel" $(RUST_COMPONENTS) >/dev/null; \
	'$(CHARON)' toolchain-path >/dev/null
	@touch $@

# Enforces what the comment on AENEAS_TAG describes. Cheap enough to run before
# every extraction, which is exactly when a mismatch would do damage.
check-toolchain: $(TC_STAMP)
	@set -euo pipefail; \
	for bin in '$(CHARON)' '$(AENEAS)'; do \
	  if [ ! -x "$$bin" ]; then \
	    echo "error: $$bin missing. Run \`make setup\`." >&2; exit 1; \
	  fi; \
	done; \
	got=$$('$(AENEAS)' -version | awk '{print $$NF}'); \
	case "$$got" in \
	  *$(AENEAS_COMMIT)) ;; \
	  *) echo "error: aeneas binary is $$got, expected commit $(AENEAS_COMMIT)." >&2; \
	     echo "       Generated.lean is only valid against the Aeneas version that" >&2; \
	     echo "       produced it. Either restore the pinned binaries (rm -rf toolchain" >&2; \
	     echo "       && make setup) or move AENEAS_TAG, the fork in cpoly/lakefile.lean" >&2; \
	     echo "       and Generated.lean together." >&2; \
	     exit 1 ;; \
	esac

# --- build, test, extract ----------------------------------------------------

# `lake build` alone is not enough to conclude the proofs go through: a `sorry`
# is a warning, not an error, so lake would still exit 0 on one. Hence the scan
# of the log, for both halves of the evidence -- Lean's per-declaration warning,
# and `sorryAx` turning up in an axiom dependency.
#
# Both halves are deliberately scoped to this development. Diagnostics from this
# library's own modules carry its srcDir, `lean/`, and a dependency's do not,
# which matters because Aeneas.Std ships a handful of `sorry`s of its own in
# definitions this development never reaches. `sorryAx` needs no such qualifier:
# Check.lean's `#print axioms` is the only thing in the whole build that prints
# axioms, so any occurrence is about a headline spec here -- and that is also the
# half that rules out reaching those upstream `sorry`s indirectly.
#
# The quote character around `sorry` in Lean's warning has changed between
# versions, so the pattern does not commit to which one it is.
SORRY_PATTERN := lean/[A-Za-z0-9_]+\.lean:[0-9]+:[0-9]+: declaration uses .sorry.|sorryAx

build: $(LEAN_STAMP) | $(STAMPS)
	@echo '==> lake build'
	@set -euo pipefail; cd $(PKG) && lake build 2>&1 | tee '$(BUILD_LOG)'
	@set -euo pipefail; \
	if grep -qE '$(SORRY_PATTERN)' '$(BUILD_LOG)'; then \
	  echo 'error: the build went through, but it contains a `sorry`:' >&2; \
	  grep -nE '$(SORRY_PATTERN)' '$(BUILD_LOG)' >&2; \
	  exit 1; \
	fi
	@echo '==> proofs check out: no errors, no `sorry`'

test:
	@set -euo pipefail; \
	if ! command -v cargo >/dev/null; then \
	  echo 'error: cargo not found. Run `make setup`.' >&2; exit 1; \
	fi; \
	cd $(PKG) && cargo test

# `--preset=aeneas` is mandatory: aeneas rejects an llbc emitted without it.
# `-- --lib` keeps cargo off the test targets, which are not part of the model.
# The previous model is kept aside only so that the run can report whether the
# model actually moved.
extract: check-toolchain | $(STAMPS)
	@echo '==> charon'
	@set -euo pipefail; cd $(PKG) && '$(CHARON)' cargo --preset=aeneas --dest-file '$(LLBC)' -- --lib
	@set -euo pipefail; \
	prev='$(STAMPS)/Generated.lean.prev'; \
	if [ -f '$(GENERATED)' ]; then cp '$(GENERATED)' "$$prev"; else rm -f "$$prev"; fi; \
	echo '==> aeneas'; \
	cd $(PKG) && '$(AENEAS)' -backend lean -dest lean '$(LLBC)'; \
	if [ -f "$$prev" ] && cmp -s "$$prev" '$(GENERATED)'; then \
	  echo '==> lean/Generated.lean unchanged'; \
	else \
	  echo '==> regenerated lean/Generated.lean'; \
	fi; \
	rm -f "$$prev"
	@echo '==> now re-check the proofs: make build'

# --- clean -------------------------------------------------------------------

# Build output only. Fetched dependencies (cpoly/.lake/packages, ./toolchain,
# the elan and rustup toolchains) are deliberately left alone: they are
# expensive to re-obtain and `make setup` is what manages them.
clean:
	@echo '==> clean'
	@-cd $(PKG) && lake clean
	@-cd $(PKG) && cargo clean
	@rm -f '$(BUILD_LOG)' '$(PKG)/$(LLBC)'
