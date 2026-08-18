#!/usr/bin/env python3
"""Validate logs/ledger.jsonl: per-kind schema, run ids, notes discipline, and
append-only history. Owned by the skill-lab skill; invoked as `make ledger-check`.

Checks, per row:
  - the line parses as one JSON object;
  - `kind` is absent (candidate verdict) or one of campaign / bakeoff / ab;
  - required fields per kind are present, enums valid, `pins.repo` present;
  - a candidate row carrying measurements (a `rows` array) names its criterion
    session: `run` = "<compact ISO time with offset>-<machine id>" — the field
    that makes the no-cross-run-comparison rule mechanically checkable;
  - a bakeoff row's bench/reference claims name their provenance;
  - `notes` <= NOTES_MAX chars, and never references another row by POSITION
    ("row 3", "row above"): union merges interleave rows, so position is
    meaningless — cite `run` or `ts`.

Rows with ts before EXEMPT_BEFORE predate the discipline and are exempt from
the run/notes/position checks (append-only outranks retrofitting them); the
structural checks still apply to every row.

Append-only is checked against a committed revision (--against REV, default
HEAD): every ledger line present at REV must appear byte-identical in the
working file. Set-containment, not prefix, because union merges may reorder.
"""

import argparse
import json
import re
import subprocess
import sys

LEDGER = "logs/ledger.jsonl"
LEGACY_LEDGER = "ledger.jsonl"
EXEMPT_BEFORE = "2026-08-14"
NOTES_MAX = 1200
RUN_RE = re.compile(r"^\d{8}T\d{4}(\d{2})?([+-]\d{4}|Z)-[0-9a-f]{8,}$")
POSITIONAL_RE = re.compile(
    r"\b(row\s+(above|below|\d+)|(previous|next|following)\s+row)\b", re.I
)

CANDIDATE_VERDICTS = {
    "accepted", "rejected-slower", "rejected-noise", "rejected-mixed",
    "tests-failed", "lemma-failed", "not-translatable", "no-strategy-applies",
    "contract-violation", "bench-unusable", "reference",
}
REQUIRED = {
    None: ["ts", "target", "op", "strategy", "candidate", "verdict", "pins"],
    "campaign": ["ts", "op", "champion", "trigger", "specs", "effort",
                 "result", "axioms", "pins"],
    "bakeoff": ["ts", "op", "arm", "target", "champion", "bench", "effort",
                "result", "reference", "pins"],
    "ab": ["ts", "skill", "hypothesis", "input", "a", "b", "verdict", "pins"],
}
ENUMS = {
    "campaign": ("trigger", {"champion-accept", "regeneration", "from-scratch"}),
    "bakeoff": ("result", {"verified", "partial", "abandoned"}),
    "ab": ("verdict", {"a-kept", "b-folded", "inconclusive"}),
}


def fail(errors, n, msg):
    errors.append(f"  line {n}: {msg}")


def check_rows(lines):
    errors = []
    for n, line in enumerate(lines, 1):
        if not line.strip():
            fail(errors, n, "empty line")
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as e:
            fail(errors, n, f"not valid JSON ({e})")
            continue
        if not isinstance(row, dict):
            fail(errors, n, "not a JSON object")
            continue

        kind = row.get("kind")
        if kind not in REQUIRED:
            fail(errors, n, f"unknown kind {kind!r}")
            continue
        for field in REQUIRED[kind]:
            if field not in row:
                fail(errors, n, f"kind={kind or 'candidate'} missing `{field}`")
        if not isinstance(row.get("pins"), dict) or "repo" not in row.get("pins", {}):
            fail(errors, n, "pins.repo missing")

        if kind is None and row.get("verdict") not in CANDIDATE_VERDICTS:
            fail(errors, n, f"unknown candidate verdict {row.get('verdict')!r}")
        if kind in ENUMS:
            field, allowed = ENUMS[kind]
            if row.get(field) not in allowed:
                fail(errors, n, f"{field}={row.get(field)!r} not in {sorted(allowed)}")

        exempt = str(row.get("ts", "")) < EXEMPT_BEFORE
        if exempt:
            continue

        if kind is None and "rows" in row:
            run = row.get("run")
            if not (isinstance(run, str) and RUN_RE.match(run)):
                fail(errors, n, "measurement row without a valid `run` id")
        if kind == "bakeoff":
            for part in ("bench", "reference"):
                claims = row.get(part)
                if isinstance(claims, dict) and not claims.get("claim_provenance"):
                    fail(errors, n, f"{part}.claim_provenance missing")

        notes = row.get("notes", "")
        if len(notes) > NOTES_MAX:
            fail(errors, n, f"notes {len(notes)} chars > {NOTES_MAX} — durable "
                            "facts here, analysis in the responsible skill")
        if POSITIONAL_RE.search(notes):
            fail(errors, n, "notes reference a row by position — cite run/ts")
    return errors


def check_append_only(lines, rev):
    committed = None
    for ledger_path in (LEDGER, LEGACY_LEDGER):
        try:
            committed = subprocess.run(
                ["git", "show", f"{rev}:{ledger_path}"],
                capture_output=True, text=True, check=True,
            ).stdout.splitlines()
            break
        except subprocess.CalledProcessError:
            continue
    if committed is None:
        return []  # no ledger present at REV: nothing to preserve
    current = {l for l in lines if l.strip()}
    return [f"  committed row vanished or was edited (append-only): {l[:100]}…"
            for l in committed if l.strip() and l not in current]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--against", default="HEAD",
                    help="revision to verify append-only against (default HEAD)")
    ap.add_argument("--file", default=LEDGER)
    args = ap.parse_args()

    with open(args.file, encoding="utf-8") as f:
        lines = f.read().splitlines()

    errors = check_rows(lines)
    errors += check_append_only(lines, args.against)

    n_rows = sum(1 for l in lines if l.strip())
    if errors:
        print(f"==> ledger-check: {len(errors)} problem(s) in {n_rows} row(s)")
        print("\n".join(errors))
        return 1
    print(f"==> ledger-check: {n_rows} rows valid, append-only intact "
          f"against {args.against}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
