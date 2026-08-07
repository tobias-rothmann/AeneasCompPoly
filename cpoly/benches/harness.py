#!/usr/bin/env python3
"""Everything `make run-bench` needs that is not the measuring itself.

    stamp-genesis   fill in `// @genesis <sha> <date>` annotations by asking git
                    which commit first contained each frozen item
    check-genesis   prove every frozen item, attributes included, is byte-for-byte
                    what `cpoly/src` held at the commit its annotation names
    coverage        pair every `Mirrors CompPoly.X` item with a bench case or an
                    explicit, reasoned exclusion
    report          read criterion's output and compare each operation against
                    its frozen first translation, measured in the same run

There is one measurement mode and one round. Reduced sampling is not offered: on
byte-identical code it returns non-noise verdicts while printing exactly what a
full run prints, and a mode whose output cannot be told apart from a trustworthy
one is not a shortcut. Repeat-and-median is not offered either: it would assume
per-round errors are independent, which they are not when a machine settles into
a slower state and stays there -- in that case the median across rounds selects
the corrupted value.

Standard library only, on purpose: the benchmark harness must not need a package
install to work, and a dependency that changes under it is a dependency that can
move the numbers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import re
import subprocess
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rustitems as R  # noqa: E402

BENCHES = Path(__file__).resolve().parent      # cpoly/benches
PKG = BENCHES.parent                           # cpoly
ROOT = PKG.parent                              # the repository, for git
SRC = PKG / "src"
GENESIS_SRC = BENCHES / "genesis" / "src"
CRITERION = PKG / "target" / "criterion"
EXCLUSIONS = BENCHES / "exclusions.toml"

MODULES = ("field", "univariate", "multilinear")

# Items whose text is worth freezing and annotating. `impl` headers and
# associated `type`s are structure, not code that runs.
ANNOTATED_KINDS = ("fn", "const fn", "const", "struct", "enum")

ANNOT = re.compile(r"^\s*//\s*@genesis\s+(?P<sha>[0-9a-f]{7,40})\s+(?P<date>\d{4}-\d{2}-\d{2})\b")
# The rest of the line, not `\S+`: an item path here is a Rust type expression
# and half of them contain spaces (`field::<Fp as Add>::add`).
COVERS = re.compile(r"^\s*//\s*@covers\s+(?P<path>.+?)\s*$")
# `bench_case!(c, "<group>", <case fn>, [...])` -- the only form the bench files
# use, and the only thing a `@covers` marker is allowed to sit on.
BENCH_CASE = re.compile(r"^\s*bench_case!\(\s*c\s*,\s*\"(?P<group>[^\"]+)\"\s*,\s*(?P<fn>\w+)\s*,")
MIRRORS = re.compile(r"Mirrors\s+`?(?P<name>[A-Za-z0-9_.]+)")

# A change smaller than this is never called a win, however tight the intervals.
# It exists so that a long run of 1% "improvements" cannot ratchet the champion
# forward on noise alone.
#
# 5%, and the sampling does NOT currently deliver it. This is a target, not a
# description: on the last full run of byte-identical code -- where all 59 rows
# must read 0% -- the worst was `multilinear/poly_eval_horner/12` at 6.10%, with
# a p90 of 2.90% and a worst control of 3.40%. So expect one or two rows per run
# to cross this line with no code change behind them.
#
# 6% is the value that covered the observed noise. 5% was set deliberately as
# something for the sampling parameters in `benches/support/mod.rs §
# criterion_config` to be tuned towards; that tuning has not been done. Until it
# is, treat a verdict between 5% and 6% as unproven rather than as a result, and
# do not read this constant as evidence that the harness resolves 5% effects.
#
# What the residue is, so the tuning is not attempted blind: it is per-row and
# per-run, a different row each time (`evals_eval`, `poly_from_coeffs`,
# `poly_eval_horner` on three consecutive runs), so it is machine noise rather
# than one broken case -- with the exception of `poly_from_coeffs`, which has a
# separate documented allocator-state drift. Nothing computable from within a
# single run removes it.
#
# The price is paid by the base-field rows, and it is smaller than it looks:
# their timed loop is ~17 instructions per element of which the operation is 4,
# so a real 50% speedup of `Fp::add` only moves the row a few percent and was
# already unresolvable here (see `benches/field.rs`, the note on the loop
# scaffolding). Those rows localize; the polynomial rows score. If the field rows
# ever need to resolve an effect this small, the fix is to measure them at a
# length where they are not sub-microsecond, not to lower this floor.
MIN_EFFECT = 0.05

# Cases under this prefix run byte-identical code in both variants, so whatever
# they measure as a difference is the harness lying to itself. See the note in
# `cmd_report` and `benches/support/mod.rs § control_workload`.
CONTROL_PREFIX = "_control/"

# Above this A/B bias the run is thrown away rather than reported: if two copies
# of the same function disagree by more than this, nothing the run says about two
# *different* functions means anything.
USABLE_BIAS_MAX = 0.10


# ---------------------------------------------------------------------------
# git
# ---------------------------------------------------------------------------


def git(*args: str, check: bool = True) -> str:
    p = subprocess.run(
        ["git", "-C", str(ROOT), *args], capture_output=True, text=True, check=False
    )
    if check and p.returncode:
        raise RuntimeError(f"git {' '.join(args)} failed: {p.stderr.strip()}")
    return p.stdout


def commits_oldest_first() -> list[str]:
    return git("log", "--reverse", "--format=%H").split()


def commit_date(sha: str) -> str:
    return git("log", "-1", "--format=%cs", sha).strip()


def short(sha: str) -> str:
    return git("rev-parse", "--short", sha).strip()


def blob_at(sha: str, basename: str) -> str | None:
    """`<basename>.rs` as it stood at `sha`, wherever in the tree it lived then.

    The crate moved into `cpoly/` at commit eb6a80f, so a path-pinned lookup
    would blind the archaeology to everything before that.
    """
    out = git("ls-tree", "-r", "--name-only", sha, check=False)
    paths = [p for p in out.split() if p.endswith("/" + basename) or p == basename]
    if not paths:
        return None
    paths.sort(key=lambda p: (0 if p.startswith("cpoly/src/") else 1, len(p)))
    return git("show", f"{sha}:{paths[0]}", check=False)


def head_state() -> dict:
    """The commit the measured code came from, and whether it is really that commit.

    `cpoly/benches` counts as measured code -- it holds the cases *and* the frozen
    genesis crate, and editing either changes the number as surely as editing the
    function under test.
    """
    paths = ("cpoly/src", "cpoly/benches")
    dirty = bool(git("status", "--porcelain", "--", *paths).strip())
    return {"sha": short("HEAD"), "src_dirty": dirty}


# ---------------------------------------------------------------------------
# genesis: stamping and checking
# ---------------------------------------------------------------------------


def _frozen_text(lines: list[str], it: R.Item) -> str:
    """The bytes `check-genesis` holds against git: the item *and its attributes*.

    `rustitems.Item.text` starts at the signature line, so attributes sit outside
    it. They are not decoration -- `#[inline(never)]`, `#[cold]` and
    `#[repr(align(N))]` each change what a benchmark measures -- so a frozen item
    whose attributes went unchecked could be made arbitrarily slower while still
    passing the gate that exists to stop exactly that, and every "vs genesis"
    number would then report a speedup nobody wrote.

    Only the contiguous `#[...]` run immediately above the signature is taken.
    That is where rustfmt puts attributes and where all of this crate's are; the
    `// @genesis` annotation is inserted at the *top* of the lead, above the doc
    comment, so it never lands inside the run. Doc comments stay outside the
    check on purpose: they cannot move a measurement, and freezing prose would
    make the baseline unmaintainable.
    """
    k = it.start
    while k > it.lead_start and lines[k - 1].lstrip().startswith("#["):
        k -= 1
    return "".join(lines[k : it.start]) + it.text


def _annotated_items(
    path: Path, module: str
) -> list[tuple[R.Item, str | None, str | None, int | None, str]]:
    """Each annotatable item in a frozen file, with its annotation and frozen text.

    The annotation sits inside the item's lead block -- `_lead_start` walks up
    over it along with the doc comments -- so this searches the lead rather than
    the lines above it.
    """
    src = path.read_text()
    lines = src.splitlines(keepends=True)
    out = []
    for it in R.flatten(R.scan(src, module)):
        if it.kind not in ANNOTATED_KINDS:
            continue
        sha = date = None
        at = None
        for k in range(it.lead_start, it.start):
            m = ANNOT.match(lines[k])
            if m:
                sha, date, at = m.group("sha"), m.group("date"), k
                break
        out.append((it, sha, date, at, _frozen_text(lines, it)))
    return out


def _first_commit_containing(basename: str, text: str, history: list[str]) -> str | None:
    for sha in history:
        blob = blob_at(sha, basename)
        if blob and text in blob:
            return sha
    return None


def cmd_stamp_genesis(args) -> int:
    history = commits_oldest_first()
    head = git("rev-parse", "HEAD").strip()
    changed = 0
    for module in MODULES:
        path = GENESIS_SRC / f"{module}.rs"
        basename = f"{module}.rs"
        src = path.read_text()
        lines = src.splitlines(keepends=True)
        inserts: list[tuple[int, str]] = []
        deletes: list[int] = []
        for it, sha, _, at, frozen in _annotated_items(path, module):
            if sha and not args.force:
                continue
            if at is not None:
                deletes.append(at)
            found = _first_commit_containing(basename, frozen, history)
            if found is None:
                print(
                    f"  ! {it.path}: no commit contains this text verbatim. Either it is\n"
                    f"    uncommitted, or the frozen copy has been edited. Not stamping.",
                    file=sys.stderr,
                )
                continue
            if found == head and head_state()["src_dirty"]:
                print(f"  ! {it.path}: only matches the working tree, not a commit.", file=sys.stderr)
                continue
            indent = " " * it.indent
            inserts.append(
                (it.lead_start, f"{indent}// @genesis {short(found)} {commit_date(found)} — {it.path}\n")
            )
        # Bottom-up, so an edit never moves a line another edit still points at.
        edits = [(n, "del", "") for n in deletes] + [(n, "ins", t) for n, t in inserts]
        for at, kind, text in sorted(edits, key=lambda e: (-e[0], e[1])):
            if kind == "del":
                del lines[at]
            else:
                lines.insert(at, text)
        if inserts:
            path.write_text("".join(lines))
            changed += len(inserts)
            print(f"  {module}.rs: stamped {len(inserts)} item(s)")
    print(f"==> {changed} annotation(s) written" if changed else "==> nothing to stamp")
    return 0


def cmd_check_genesis(args) -> int:
    """The integrity check the whole design rests on.

    Every frozen item must (a) carry an annotation, (b) name a real commit, and
    (c) be byte-for-byte what `cpoly/src` held at that commit -- its attributes
    included, which is what `_frozen_text` is for. If any of the three fails, the
    baseline is not the baseline and every 'vs genesis' number printed since it
    broke is wrong.

    What is deliberately *not* checked: doc comments, `use` lines, `impl`
    headers, and anything in `lib.rs`. None of them can change what a benchmark
    measures without also changing an item's own text or failing to compile.
    """
    problems: list[str] = []
    checked = 0
    for module in MODULES:
        path = GENESIS_SRC / f"{module}.rs"
        if not path.exists():
            problems.append(f"{module}: frozen copy cpoly/benches/genesis/src/{module}.rs is missing")
            continue
        for it, sha, date, _, frozen in _annotated_items(path, module):
            if sha is None:
                problems.append(
                    f"{it.path}: no `// @genesis <sha> <date>` annotation. "
                    f"Run `make bench-stamp`, or add it by hand."
                )
                continue
            blob = blob_at(sha, f"{module}.rs")
            if blob is None:
                problems.append(f"{it.path}: commit {sha} has no {module}.rs")
                continue
            if frozen not in blob:
                what = "text or attributes" if frozen != it.text else "text"
                problems.append(
                    f"{it.path}: frozen {what} do NOT match {module}.rs at {sha}. "
                    f"Genesis is append-only and must never be edited "
                    f"(cpoly/benches/genesis/src/{module}.rs:{it.start + 1})."
                )
                continue
            actual = commit_date(sha)
            if date != actual:
                problems.append(f"{it.path}: annotation says {date}, commit {sha} is {actual}")
                continue
            checked += 1

    live = {it.path for m in MODULES for it in R.flatten(R.scan((SRC / f"{m}.rs").read_text(), m))
            if it.kind in ANNOTATED_KINDS}
    frozen = {it.path for m in MODULES if (GENESIS_SRC / f"{m}.rs").exists()
              for it, _, _, _, _ in _annotated_items(GENESIS_SRC / f"{m}.rs", m)}
    missing = sorted(live - frozen)
    if missing:
        problems.append(
            "these items exist in cpoly/src but have no frozen counterpart, so they have\n"
            "    no baseline to be measured against. Copy the FIRST translation of each into\n"
            "    cpoly/benches/genesis/src/ verbatim, then `make bench-stamp`:\n"
            + "".join(f"      {p}\n" for p in missing).rstrip()
        )

    if problems:
        print("==> genesis check FAILED", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1
    print(f"==> genesis intact: {checked} frozen item(s) verified against git")
    return 0


# ---------------------------------------------------------------------------
# coverage
# ---------------------------------------------------------------------------


def mirrored_items() -> dict[str, str]:
    """Live items whose doc comment claims to mirror a CompPoly definition."""
    out: dict[str, str] = {}
    for module in MODULES:
        src = (SRC / f"{module}.rs").read_text()
        lines = src.splitlines()
        for it in R.flatten(R.scan(src, module)):
            if it.kind not in ANNOTATED_KINDS:
                continue
            lead = "\n".join(lines[it.lead_start : it.start])
            m = MIRRORS.search(lead)
            if m:
                out[it.path] = m.group("name")
    return out


def covered_paths() -> tuple[dict[str, list[str]], list[str]]:
    """`// @covers <path>` markers, each bound to the `bench_case!` it sits on.

    A marker is a claim about one *row*, so it has to name one. A marker left
    behind after its case was deleted, or one that has drifted onto the wrong
    case, is the one failure mode a coverage check exists to catch.

    Returns a `{path: [file]}` mapping, plus the attachment problems, which
    `--strict` fails on. Three of them:

    * a marker with no `bench_case!` beneath it (blank lines are allowed between,
      anything else is not),
    * a `bench_case!` with no marker above it -- except `_control/*`, which
      measures the harness rather than the crate,
    * a marker whose module disagrees with its case's group id, e.g.
      `@covers multilinear::dot` sitting on `"univariate/..."`.

    What this still cannot check is that the case *body* calls the item named:
    that needs a Rust parser, which `rustitems` deliberately is not.
    """
    out: dict[str, list[str]] = {}
    problems: list[str] = []

    def orphan(name: str, at: int, path: str) -> None:
        problems.append(
            f"{name}:{at + 1}: `@covers {path}` is not attached to a `bench_case!`. "
            f"A marker claims one row, so it must sit directly above one."
        )

    for f in sorted(BENCHES.glob("*.rs")):
        pending: list[tuple[int, str]] = []
        for i, line in enumerate(f.read_text().splitlines()):
            m = COVERS.match(line)
            if m:
                pending.append((i, m.group("path")))
                continue
            b = BENCH_CASE.match(line)
            if b:
                group = b.group("group")
                if group.startswith(CONTROL_PREFIX):
                    for at, path in pending:
                        problems.append(
                            f"{f.name}:{at + 1}: `@covers {path}` sits on the control case "
                            f"`{group}`, which measures the harness, not the crate."
                        )
                elif not pending:
                    problems.append(
                        f"{f.name}:{i + 1}: `bench_case!` for `{group}` has no `// @covers` "
                        f"above it, so nothing records which item it measures."
                    )
                for at, path in pending:
                    out.setdefault(path, []).append(f.name)
                    mod, group_mod = path.split("::", 1)[0], group.split("/", 1)[0]
                    if mod != group_mod:
                        problems.append(
                            f"{f.name}:{at + 1}: `@covers {path}` is in module `{mod}` but "
                            f"sits on bench case `{group}`, which is in `{group_mod}`."
                        )
                pending = []
                continue
            if line.strip():
                for at, path in pending:
                    orphan(f.name, at, path)
                pending = []
        for at, path in pending:
            orphan(f.name, at, path)
    return out, problems


def exclusions() -> dict[str, str]:
    if not EXCLUSIONS.exists():
        return {}
    return tomllib.loads(EXCLUSIONS.read_text()).get("exclusions", {})


def all_item_paths() -> set[str]:
    return {
        it.path
        for m in MODULES
        for it in R.flatten(R.scan((SRC / f"{m}.rs").read_text(), m))
    }


def cmd_coverage(args) -> int:
    """Is every translated CompPoly definition accounted for?

    Two different questions, and only the first is about mirrors:

    * A **mirrored** item must be benched or excluded by name. Silence is not an
      exclusion -- an operation nobody measures is one the loop cannot notice a
      regression in.
    * A `@covers` path must **name a real item**, and must sit on a real
      `bench_case!` in the same module. Benching something that claims no
      `Mirrors` docstring is fine and often right (`Fp::mul` mirrors nothing and
      is the hottest code in the crate); pointing at an item that does not exist,
      or at no row at all, silently drops the coverage claim the marker made.
    """
    mirrors, (covers, bind_problems), excl = mirrored_items(), covered_paths(), exclusions()
    live = all_item_paths()

    uncovered = sorted(p for p in mirrors if p not in covers and p not in excl)
    stale_excl = sorted(p for p in excl if p not in live)
    both = sorted(p for p in excl if p in covers)
    dangling = sorted(p for p in covers if p not in live)
    extra = sorted(p for p in covers if p in live and p not in mirrors)

    print(
        f"==> coverage: {len(mirrors)} mirrored item(s), "
        f"{len([p for p in mirrors if p in covers])} benched, "
        f"{len([p for p in mirrors if p in excl])} excluded by name, "
        f"{len(uncovered)} UNACCOUNTED FOR"
        f"  (+{len(extra)} non-mirrored item(s) benched as well)"
    )
    for p in uncovered:
        print(f"  - {p}  (mirrors {mirrors[p]}) has no bench and no exclusion")
    for p in both:
        print(f"  - {p} is both benched and excluded; drop one")
    for p in stale_excl:
        print(f"  - exclusion {p} names no item in cpoly/src -- renamed or removed?")
    for p in dangling:
        print(f"  - `@covers {p}` in {', '.join(covers[p])} names no item in cpoly/src")
    for p in bind_problems:
        print(f"  - {p}")

    if args.verbose:
        for p in sorted(mirrors):
            where = "bench" if p in covers else ("excluded" if p in excl else "MISSING")
            print(f"    {where:9} {p}  ->  {mirrors[p]}")

    if args.strict and (uncovered or both or stale_excl or dangling or bind_problems):
        return 1
    return 0


# ---------------------------------------------------------------------------
# machine + toolchain fingerprint
# ---------------------------------------------------------------------------


def sysctl(key: str) -> str:
    p = subprocess.run(["sysctl", "-n", key], capture_output=True, text=True, check=False)
    return p.stdout.strip()


def machine() -> dict:
    cpu = sysctl("machdep.cpu.brand_string") or platform.processor() or "unknown"
    info = {
        "hostname": platform.node(),
        "os": f"{platform.system()} {platform.release()}",
        "arch": platform.machine(),
        "cpu": cpu,
        "cores": os.cpu_count(),
    }
    ident = "|".join(str(info[k]) for k in ("hostname", "arch", "cpu", "cores"))
    info["id"] = hashlib.sha256(ident.encode()).hexdigest()[:12]
    return info


def toolchain(name: str) -> dict:
    p = subprocess.run(
        ["rustup", "run", name, "rustc", "--version"], capture_output=True, text=True, check=False
    )
    return {"name": name, "rustc": p.stdout.strip() or "unknown"}


# ---------------------------------------------------------------------------
# criterion output
# ---------------------------------------------------------------------------


def read_criterion(root: Path | None = None) -> dict[str, dict[str, dict]]:
    """{case_id: {variant: stats}} for every benchmark criterion just wrote.

    `benchmark.json` carries the ids criterion itself parsed, so nothing here has
    to reverse-engineer a directory name.

    `slope_ns` is the **slope** of criterion's linear regression through the
    (iterations, time) samples, falling back to the mean when criterion used flat
    sampling and so produced no slope. It is the estimate criterion itself
    prints, and `lo_ns`/`hi_ns` are its interval, which is what `disjoint`
    compares. It is the better of criterion's own two -- the regression absorbs
    the fixed per-sample overhead and is far less sensitive to the occasional
    scheduler or thermal outlier than the mean -- so it is what `ns` falls back
    to when `_robust` cannot read `sample.json`. The reported `ns` itself comes
    from `_robust`.
    """
    root = root or CRITERION
    cases: dict[str, dict[str, dict]] = {}
    if not root.exists():
        return cases
    for bj in root.rglob("new/benchmark.json"):
        ej = bj.parent / "estimates.json"
        if not ej.exists():
            continue
        b = json.loads(bj.read_text())
        e = json.loads(ej.read_text())
        group, variant, value = b.get("group_id"), b.get("function_id"), b.get("value_str")
        if not group or not variant:
            continue
        est = e.get("slope") or e["mean"]
        case = f"{group}/{value}" if value else group
        stats = {
            "slope_ns": est["point_estimate"],
            "lo_ns": est["confidence_interval"]["lower_bound"],
            "hi_ns": est["confidence_interval"]["upper_bound"],
            "estimator": "slope" if e.get("slope") else "mean",
            "mean_ns": e["mean"]["point_estimate"],
            "std_dev_ns": e["std_dev"]["point_estimate"],
            "mtime": ej.stat().st_mtime,
        }
        stats.update(_robust(bj.parent / "sample.json"))
        stats.setdefault("ns", stats["slope_ns"])
        cases.setdefault(case, {})[variant] = stats
    return cases


def _robust(sample_json: Path) -> dict:
    """A contention-robust point estimate, from criterion's raw samples.

    Two decisions, and both were measured rather than argued.

    **Which end of the distribution.** Criterion's headline slope, and its mean,
    describe the *centre* of the sample distribution. On a developer's machine
    that centre is largely a description of what else was running: this
    repository's calibration run, taken at load average 7.75 on 8 cores, inflated
    every case by 50-180% and produced confidence intervals that were narrow,
    disjoint, and meaningless. Contention only ever makes code look *slower*, so
    the informative end is the fast one. Swept over a full run of byte-identical
    code, where every row must read 0%, the centre estimators are the worst of
    the lot -- worst row 24.5% for the mean, 22.3% for the median, 14.1% for
    criterion's slope, against 10.9% for the fast end.

    **Which samples.** Criterion samples *linearly*: sample `k` runs the routine
    `k * d` times. For a case near a millisecond the budget forces `d = 1`, so the
    first samples are single executions, and a percentile taken over all 100
    samples is dominated by exactly the observations with no averaging in them.

    So: keep the samples criterion gave at least half the maximum iteration
    count, then average the three fastest of those. Three rather than one because
    a single sample, even a 50-iteration one, should not decide a row; three
    rather than a percentile because the sweep put it ahead on the tail that
    matters -- over a full run of byte-identical code it leaves 2 rows above 3%,
    and a worst control of 0.12%.

    Falls back to the slope when `sample.json` is missing or malformed, which is
    the only reason the caller's `setdefault` exists.
    """
    try:
        s = json.loads(sample_json.read_text())
        pairs = [(t / i, i) for t, i in zip(s["times"], s["iters"]) if i]
    except (OSError, ValueError, KeyError, ZeroDivisionError):
        return {}
    if not pairs:
        return {}
    cutoff = max(i for _, i in pairs) / 2
    settled = sorted(p for p, i in pairs if i >= cutoff) or sorted(p for p, _ in pairs)
    per = sorted(p for p, _ in pairs)
    n = len(per)
    return {
        "ns": sum(settled[:3]) / len(settled[:3]),
        "min_ns": settled[0],
        "median_ns": per[(n - 1) // 2],
        "samples": n,
        "settled_samples": len(settled),
    }


def fmt_time(ns: float) -> str:
    for unit, scale in (("s", 1e9), ("ms", 1e6), ("µs", 1e3), ("ns", 1.0)):
        if ns >= scale:
            return f"{ns / scale:.3g}{unit}"
    return f"{ns:.3g}ns"


def rel(new: float, old: float) -> float:
    return (new - old) / old if old else math.inf


def disjoint(a: dict, b: dict) -> bool:
    """Do the two 95% confidence intervals for the mean fail to overlap?"""
    return a["hi_ns"] < b["lo_ns"] or b["hi_ns"] < a["lo_ns"]


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def cmd_report(args) -> int:
    cases = read_criterion()
    if not cases:
        print("error: no criterion output under cpoly/target/criterion.", file=sys.stderr)
        return 1

    mach = machine()
    tc = toolchain(args.toolchain)

    # Only look at cases this run actually refreshed. Criterion keeps the results
    # of benchmarks that a `BENCH=` filter skipped, and reporting one of those as
    # if it had just been measured is precisely the lie this harness exists to
    # prevent -- it would show a filtered-out case "unchanged" while its code was
    # being rewritten. `make run-bench` stamps the wall clock before it starts and
    # passes it here, so the cut is exact rather than a guess about mtimes.
    if args.since is not None:
        stale = {k for k, v in cases.items() if any(s["mtime"] < args.since for s in v.values())}
        cases = {k: v for k, v in cases.items() if k not in stale}
        if not cases:
            print(
                "error: criterion wrote no results after the run started. Did every\n"
                "       benchmark get filtered out by BENCH=?",
                file=sys.stderr,
            )
            return 1
        if stale:
            print(f"  (skipping {len(stale)} case(s) not measured in this run)")

    rows, control = [], []
    for case in sorted(cases):
        now, gen = cases[case].get("now"), cases[case].get("genesis")
        if now is None:
            rows.append({"case": case, "error": "no `now` measurement"})
            continue
        row: dict = {"case": case, "now_ns": now["ns"]}

        if gen is None:
            row["genesis_missing"] = True
        else:
            row["genesis_ns"] = gen["ns"]
            row["vs_genesis"] = rel(now["ns"], gen["ns"])
            # Criterion's own interval, on its own estimator. `vs_genesis` above
            # is a ratio of `_robust` estimates, so the two do not have to agree;
            # this is exported for a reader who wants criterion's view, and no
            # verdict is derived from it.
            row["vs_genesis_sig"] = disjoint(now, gen)

        (control if case.startswith(CONTROL_PREFIX) else rows).append(row)

    # There is exactly one comparison here, and it is made entirely within this
    # run: `now` against the frozen first translation, measured back to back on
    # the same machine at the same temperature by the same compiler.
    #
    # Nothing is compared across runs, and nothing is kept that would let it be:
    # a comparison across runs inherits the *difference* in machine conditions
    # between two moments possibly days apart, and on an ordinary desktop that
    # difference dwarfs anything the code does. A measurement that cannot resolve
    # the effect it exists to detect is not a conservative measurement, it is a
    # distraction with a number attached.
    #
    # `JSON=<path>` writes this run's full numbers if something downstream wants
    # to keep them; the harness itself keeps nothing between runs.
    #
    # What remains is the A/B bias: the `_control/*` cases, one per bench binary,
    # where BOTH variants run byte-identical code from `benches/support`. Whatever
    # they differ by is the harness itself -- criterion runs `now` to completion
    # before it starts `genesis`, so a CPU warming up across those seconds looks
    # exactly like a code change. It is measured every run rather than assumed.
    #
    # The **worst** control is taken, not the median. Three controls is not a
    # distribution to draw a central tendency from, and a single copy of one
    # function disagreeing with itself by more than the limit is exactly the
    # thing that should veto a run.
    #
    # It is a flat threshold, not a per-case one. Matching each case to the
    # control nearest its duration sounds careful and is not: with the real cases
    # spanning four orders of magnitude, most rows would be thresholded by
    # extrapolation from a control up to 100x away. One control, one number,
    # applied to everything, is the honest shape of what is known.
    biases = [abs(r["vs_genesis"]) for r in control if "vs_genesis" in r]
    bias = max(biases) if biases else None
    usable = bias is None or bias <= USABLE_BIAS_MAX
    t_genesis = max(MIN_EFFECT, bias or 0.0)

    for row in rows + control:
        row["threshold_vs_genesis"] = t_genesis
        if "vs_genesis" in row:
            d = row["vs_genesis"]
            row["vs_genesis_verdict"] = (
                "unusable" if not usable
                else ("faster" if d < 0 else "slower") if abs(d) >= t_genesis
                else "noise"
            )

    _print_report(rows, control, mach, tc, bias, t_genesis, usable, args)

    if args.json:
        Path(args.json).write_text(
            json.dumps({"rows": rows, "control": control, "machine": mach, "toolchain": tc,
                        "ab_bias": bias, "usable": usable,
                        "threshold_vs_genesis": t_genesis}, indent=2)
        )

    if not usable:
        print(
            f"\n==> RUN NOT USABLE. Identical code measured {bias * 100:.1f}% apart, over the "
            f"{USABLE_BIAS_MAX * 100:.0f}% limit.\n"
            f"    No verdict above should be acted on. Close what else is running and repeat;\n"
            f"    if it persists on an idle machine, the harness is at fault, not the machine.",
            file=sys.stderr,
        )
        return 2

    return 0


def _print_report(rows, control, mach, tc, bias, t_genesis, usable, args) -> None:
    print()
    print(f"  machine   {mach['cpu']} · {mach['cores']} cores · {mach['os']} · id {mach['id']}")
    print(f"  toolchain {tc['rustc']}")
    print(f"  rustflags {os.environ.get('RUSTFLAGS', '') or '(none)'}")
    g = head_state()
    print(f"  source    {g['sha']}{' +uncommitted' if g['src_dirty'] else ''}")
    print()

    w = max((len(r["case"]) for r in rows + control), default=10)
    print(f"  {'case'.ljust(w)}  {'genesis':>10}  {'now':>10}  {'vs genesis':>18}")
    print(f"  {'-' * w}  {'-' * 10}  {'-' * 10}  {'-' * 18}")
    for r in rows:
        if "error" in r:
            print(f"  {r['case'].ljust(w)}  {r['error']}")
            continue
        gen = fmt_time(r["genesis_ns"]) if "genesis_ns" in r else "—"
        now = fmt_time(r["now_ns"])
        print(f"  {r['case'].ljust(w)}  {gen:>10}  {now:>10}  "
              f"{_delta(r, 'vs_genesis'):>18}")

    print()
    print("  harness self-test — both variants run identical code, so these should read 0%")
    for r in control:
        gen = fmt_time(r["genesis_ns"]) if "genesis_ns" in r else "—"
        print(f"  {r['case'].ljust(w)}  {gen:>10}  {fmt_time(r['now_ns']):>10}  "
              f"{_delta(r, 'vs_genesis'):>18}")
    if not control:
        print("  (none ran — `vs genesis` is unvalidated for this run)")

    print()
    print("  times average the 3 fastest of criterion's settled samples (those given at least")
    print("  half the maximum iteration count), which is robust to background load; criterion's")
    print("  own output above reports its regression slope and reads higher.")
    print("  Only the `vs genesis` column is a comparison; an absolute time is not comparable")
    print("  to another run's, nor to another row's.")
    print()
    if bias is None:
        print("  A/B bias     unknown  — no `_control/*` case ran, so `vs genesis` is unvalidated")
    else:
        print(f"  A/B bias     {bias * 100:5.1f}%  worst of the identical-code controls, applied "
              f"as a flat threshold")
    if not usable:
        print(f"\n  FAILED: identical code measured {bias * 100:.1f}% apart within this run "
              f"(limit {USABLE_BIAS_MAX * 100:.0f}%).")
        print("  Every verdict above is marked unusable and nothing was recorded.")
    elif bias is not None and bias > MIN_EFFECT:
        print(f"\n  Note: {bias * 100:.1f}% is what a change has to beat on this run. "
              f"A quieter machine\n  brings it down; nothing inside the harness does.")
    if any(r.get("genesis_missing") for r in rows):
        missing = [r["case"] for r in rows if r.get("genesis_missing")]
        print(f"\n  {len(missing)} case(s) have no genesis variant: {', '.join(missing[:6])}")
        print("  Those rows have no baseline at all — freeze the operation into cpoly/benches/genesis.")


def _delta(row: dict, key: str) -> str:
    if key not in row:
        return "—"
    d, verdict = row[key], row.get(key + "_verdict", "")
    mark = {"faster": "▼", "slower": "▲", "noise": "·", "unusable": "✗"}.get(verdict, " ")
    return f"{d * 100:+7.1f}% {mark} {verdict}"


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("stamp-genesis")
    s.add_argument("--force", action="store_true", help="re-derive annotations that already exist")
    s.set_defaults(func=cmd_stamp_genesis)

    s = sub.add_parser("check-genesis")
    s.set_defaults(func=cmd_check_genesis)

    s = sub.add_parser("coverage")
    s.add_argument("--strict", action="store_true", help="exit non-zero if anything is unaccounted for")
    s.add_argument("-v", "--verbose", action="store_true", help="list every mirrored item and its status")
    s.set_defaults(func=cmd_coverage)

    s = sub.add_parser("report")
    s.add_argument("--toolchain", default="stable")
    s.add_argument("--json", help="also write the report as JSON here")
    s.add_argument("--since", type=float, default=None, metavar="EPOCH",
                   help="ignore criterion results written before this unix time "
                        "(the Makefile stamps it just before `cargo bench` starts)")
    s.set_defaults(func=cmd_report)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
