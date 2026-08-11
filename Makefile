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

# One synopsis, then targets, then variables -- the usual shape for a command's
# --help. No per-target variable subsections: a variable on the command line
# applies to the whole invocation whichever target ends up reading it, so which
# one that is belongs in its description, not in a heading.
#
# Where a new target goes: `Targets` if someone who just cloned the repo would
# type it, `Advanced targets` if it exists so the optimization loop can check or
# regenerate something mid-iteration. A target with no listing in either is
# internal (`check-toolchain`, `bench-toolchain`) -- a prerequisite, not something
# to invoke.
#
# One line per entry, every list aligned on the same column, nothing past ~77
# characters. Anything that needs more than a line belongs in the comment above
# the target it describes, not here -- and a description must not promise what
# the target does not do.
help:
	@echo ''
	@echo '  Run `make setup` once after cloning; the other targets work from there.'
	@echo ''
	@echo '  Usage: make <target> [VAR=VALUE]...'
	@echo ''
	@echo '  Targets:'
	@echo '    setup          install elan, the Lean deps, charon/aeneas and rust'
	@echo '    build          check the Lean proofs -- fails on any error or `sorry`'
	@echo '    extract        regenerate cpoly/lean/Generated.lean from cpoly/src/'
	@echo '    test           run the Rust-side semantics tests'
	@echo '    clean          drop build output, keeping fetched dependencies'
	@echo '    run-bench      time every operation against its frozen first translation'
	@echo ''
	@echo '  Advanced targets (driven by the optimization loop, rarely by hand):'
	@echo '    bench-check    check the frozen baseline against git, and bench coverage'
	@echo '    bench-stamp    re-derive the @genesis stamps after adding a function'
	@echo ''
	@echo '  Variables:'
	@echo '    AENEAS=<path>  aeneas binary for `extract` (default ./toolchain/aeneas)'
	@echo '    BENCH=<regex>  bench only the cases whose id matches this regex'
	@echo '    CANDIDATE=1    also time the candidate slot, for the optimization loop'
	@echo '    CHARON=<path>  charon binary for `extract` (default ./toolchain/charon)'
	@echo '    JSON=<path>    also write the bench report as JSON, for an agent'
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

# --- benchmarks ---------------------------------------------------------------

# The fitness function of the optimization loop: criterion wall-clock time for
# every translated CompPoly operation, measured against the frozen first
# translation in ./cpoly/benches/genesis.
#
# The one thing worth understanding before reading a number out of this: the
# "vs genesis" column is not a remembered figure. `cpoly/benches/genesis` is a
# real crate holding the first translation of every operation, and every run measures
# it and `cpoly` back to back, in the same criterion session. So that column is
# always a comparison made *now*, on this machine, at this temperature, with this
# compiler.
#
# Nothing is ever compared across runs. A cross-run comparison inherits the
# difference in machine conditions between two moments possibly days apart, and
# on an ordinary desktop that dwarfs anything the code does -- the threshold it
# would imply swallows every verdict in the table. The error bar that remains
# is measured inside each run by the `_control/*` cases, one per bench binary,
# which run identical code as both variants. They are a sanity check on the
# run, not a per-case error bar: the worst of the three has to stay under 10%
# or the report refuses the run.
#
# The toolchain is pinned for the same reason the profile is (cpoly/Cargo.toml
# § profile.bench): a number is only comparable to another number produced by
# the same compiler. This is charon's channel, which `make setup` installs
# anyway, so benchmarking adds no toolchain the repository did not already need.
# Moving it makes any number kept from before the move incomparable with any
# number after, so treat a change to it as a re-baseline.
BENCH_TOOLCHAIN := nightly-2026-06-01
HARNESS         := $(PKG)/benches/harness.py

.PHONY: run-bench bench-check bench-stamp bench-toolchain

# Statistics cannot rescue a corrupted baseline, so this runs before any
# measurement and is a hard gate. Coverage is reported by `run-bench` but does
# not stop it: an unmeasured operation makes the picture incomplete, while an
# edited genesis makes every past and present "vs genesis" number wrong.
bench-check:
	@set -euo pipefail; \
	python3 '$(HARNESS)' check-genesis; \
	python3 '$(HARNESS)' check-candidate; \
	python3 '$(HARNESS)' coverage --strict

# Re-derive the `// @genesis <sha> <date>` annotations from git history. Run
# after copying a newly translated function into cpoly/benches/genesis/src/.
bench-stamp:
	@python3 '$(HARNESS)' stamp-genesis
	@python3 '$(HARNESS)' check-genesis

bench-toolchain:
	@set -euo pipefail; \
	if ! command -v python3 >/dev/null; then \
	  echo 'error: python3 not found; benches/harness.py needs it (stdlib only).' >&2; \
	  exit 1; \
	fi; \
	if ! command -v rustup >/dev/null; then \
	  echo 'error: rustup not found. Run `make setup`.' >&2; exit 1; \
	fi; \
	if ! rustup run '$(BENCH_TOOLCHAIN)' rustc --version >/dev/null 2>&1; then \
	  echo '==> installing rust $(BENCH_TOOLCHAIN) (pinned for benchmarks)'; \
	  rustup toolchain install --profile minimal --no-self-update '$(BENCH_TOOLCHAIN)' >/dev/null; \
	fi
#
#   make run-bench                  every bench, one full-rigour pass (~18 min)
#   make run-bench BENCH=univariate only cases whose id matches this regex
#   make run-bench JSON=out.json    also write the report as JSON, for an agent
#   make run-bench CANDIDATE=1      also time the candidate slot (benches/candidate)
#
# CANDIDATE=1 (exactly `1`: any other value, including 0, disables) is the
# optimization loop's mode: the slot holds a candidate's code (in the loop's
# worktree; at rest it is a byte-copy of cpoly/src) and the report gains
# `candidate` and `cand vs now` columns — the accept decision is made on the
# recentered `cand vs now`, within this run. Pass BENCH='<op>|_control' with
# it: each binary's `_control` measures the slot's signed lean, the verdicts
# are recentered by it, and the report exits 2 if a candidate case ran in a
# binary whose control did not — the filter advice is enforced, not hoped for.
#
# There is one mode and one pass. Two levers are deliberately not offered:
#
# * Reduced sampling, for a tight loop. On byte-identical code it produces
#   non-noise verdicts while printing the same "faster"/"slower" words as a full
#   run and the same `usable: true`. A mode whose output cannot be told apart
#   from a trustworthy one is not a shortcut.
#
# * Repeating the suite and taking the per-case median delta. It would assume
#   per-round error is independent, which it is not always: a machine can settle
#   into a slower state and hold it for several rounds, and the median across
#   rounds then selects the corrupted value rather than the correct one.
#
# What survives all of this is the `vs genesis` column, because a machine-state
# artefact lands on both variants at once. An absolute time does not: it is not
# comparable to another run's, and not comparable to another row's in the same
# run. Read the deltas.
#
# The start time is stamped before cargo runs so the report contains only what
# this invocation measured. Without it a `BENCH=` filter would silently republish
# stale rows for everything it skipped, which is the most plausible way this
# harness could come to lie.
run-bench: bench-toolchain | $(STAMPS)
	@set -euo pipefail; \
	python3 '$(HARNESS)' check-genesis
	@set -euo pipefail; \
	python3 '$(HARNESS)' coverage || true
	@set -euo pipefail; \
	started=$$(date +%s); \
	( cd $(PKG) && rustup run '$(BENCH_TOOLCHAIN)' cargo bench --benches \
	    $(if $(filter 1,$(CANDIDATE)),--features candidate,) -- \
	    $(if $(BENCH),'$(BENCH)',) ); \
	python3 '$(HARNESS)' report \
	  --toolchain '$(BENCH_TOOLCHAIN)' \
	  --since "$$started" \
	  $(if $(JSON),--json '$(JSON)',)

# --- clean -------------------------------------------------------------------

# Build output only. Fetched dependencies (cpoly/.lake/packages, ./toolchain,
# the elan and rustup toolchains) are deliberately left alone: they are
# expensive to re-obtain and `make setup` is what manages them.
clean:
	@echo '==> clean'
	@-cd $(PKG) && lake clean
	@-cd $(PKG) && cargo clean
	@rm -f '$(BUILD_LOG)' '$(PKG)/$(LLBC)'
