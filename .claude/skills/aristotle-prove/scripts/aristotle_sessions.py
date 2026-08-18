#!/usr/bin/env python3
"""Submit and harvest asynchronous Aristotle Lean-project sessions.

The repository's source of truth is the append-only
``logs/aristotle-sessions.jsonl`` file. API keys are read only from
ARISTOTLE_API_KEY in this process and are
never included in a log record or command-line argument.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import importlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


LOG_NAME = "aristotle-sessions.jsonl"
LOG_DIRECTORY = "logs"
ARTIFACT_DIR_NAME = ".aristotle-artifacts"
RUNNING_STATUSES = {"QUEUED", "IN_PROGRESS"}
TERMINAL_STATUSES = {
    "COMPLETE",
    "COMPLETE_WITH_ERRORS",
    "OUT_OF_BUDGET",
    "FAILED",
    "CANCELED",
}


class SessionError(RuntimeError):
    """Raise a user-facing, non-secret error."""


@dataclass(frozen=True)
class Target:
    path: str
    project_root: str
    sha256: str
    sorries: int


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def emit(value: Any) -> None:
    print(json.dumps(value, indent=2, sort_keys=True))


def git_root(candidate: str | None) -> Path:
    start = Path(candidate or Path.cwd()).expanduser().resolve()
    if not start.is_dir():
        raise SessionError(f"Repository directory does not exist: {start}")
    completed = subprocess.run(
        ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise SessionError(f"Not inside a Git repository: {start}")
    return Path(completed.stdout.strip()).resolve()


def log_path(root: Path) -> Path:
    return root / LOG_DIRECTORY / LOG_NAME


def artifact_root(root: Path) -> Path:
    return root / ARTIFACT_DIR_NAME


def append_record(root: Path, record: dict[str, Any]) -> None:
    destination = log_path(root)
    new_file = not destination.exists()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n")
    if new_file:
        destination.chmod(0o600)


def read_records(root: Path) -> list[dict[str, Any]]:
    destination = log_path(root)
    if not destination.exists():
        return []
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(destination.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise SessionError(f"Invalid JSON in {destination} at line {line_number}: {error.msg}") from error
        if not isinstance(record, dict):
            raise SessionError(f"Invalid session record in {destination} at line {line_number}")
        records.append(record)
    return records


def session_views(root: Path) -> dict[str, dict[str, Any]]:
    sessions: dict[str, dict[str, Any]] = {}
    for record in read_records(root):
        session_id = record.get("session_id")
        if not isinstance(session_id, str):
            continue
        if record.get("event") == "submitted":
            sessions[session_id] = {"submitted": record, "latest": record}
        elif session_id in sessions:
            sessions[session_id]["latest"] = record
    return sessions


def is_active(view: dict[str, Any]) -> bool:
    return view["latest"].get("state") == "running"


def scrub_error(error: BaseException, key: str | None = None) -> str:
    text = re.sub(r"\s+", " ", str(error)).strip()
    if key:
        text = text.replace(key, "[redacted]")
    return text[:500] or type(error).__name__


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def is_ident_char(character: str) -> bool:
    return character.isalnum() or character in "_'"


def count_sorries(text: str) -> int:
    """Count `sorry` tokens outside ordinary Lean comments and strings.

    This deliberately remains a conservative lexical counter rather than a
    Lean parser. It handles nested block comments, line comments, and escaped
    string characters, which avoids the common false positives in prose.
    """

    count = 0
    index = 0
    block_depth = 0
    in_string = False
    length = len(text)
    while index < length:
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            if text[index] == "\\":
                index += 2
            elif text[index] == '"':
                in_string = False
                index += 1
            else:
                index += 1
            continue
        if text.startswith("/-", index):
            block_depth = 1
            index += 2
        elif text.startswith("--", index):
            newline = text.find("\n", index + 2)
            index = length if newline < 0 else newline + 1
        elif text[index] == '"':
            in_string = True
            index += 1
        elif text.startswith("sorry", index):
            before = text[index - 1] if index else " "
            after_index = index + len("sorry")
            after = text[after_index] if after_index < length else " "
            if not is_ident_char(before) and not is_ident_char(after):
                count += 1
            index = after_index
        else:
            index += 1
    return count


def target_from_path(root: Path, raw_path: str) -> Target:
    candidate = Path(raw_path).expanduser()
    absolute = (root / candidate).resolve() if not candidate.is_absolute() else candidate.resolve()
    try:
        relative = absolute.relative_to(root)
    except ValueError as error:
        raise SessionError(f"Target is outside this repository: {raw_path}") from error
    if absolute.suffix != ".lean":
        raise SessionError(f"Target is not a Lean file: {raw_path}")
    if not absolute.is_file():
        raise SessionError(f"Target file does not exist: {raw_path}")
    project = find_lean_project_root(root, absolute)
    project_relative = project.relative_to(root).as_posix()
    content = absolute.read_bytes()
    return Target(relative.as_posix(), project_relative, sha256(content), count_sorries(content.decode("utf-8")))


def find_lean_project_root(root: Path, target: Path) -> Path:
    for candidate in (target.parent, *target.parents):
        if candidate == root.parent:
            break
        if (candidate / "lakefile.lean").is_file() or (candidate / "lakefile.toml").is_file():
            return candidate
    raise SessionError(f"No Lake project root found above target: {target.relative_to(root)}")


def common_project_root(root: Path, targets: list[Target]) -> Path:
    project_roots = {target.project_root for target in targets}
    if len(project_roots) != 1:
        raise SessionError(
            "All Aristotle targets must belong to one Lake project; submit separate sessions for: "
            + ", ".join(sorted(project_roots))
        )
    project_relative = next(iter(project_roots))
    return root if project_relative == "." else root / project_relative


def path_within_project(target: Target) -> Path:
    relative = Path(target.path)
    return relative if target.project_root == "." else relative.relative_to(target.project_root)


def targets_from_paths(root: Path, raw_paths: list[str]) -> list[Target]:
    targets = [target_from_path(root, raw_path) for raw_path in raw_paths]
    duplicate_paths = {target.path for target in targets if sum(t.path == target.path for t in targets) > 1}
    if duplicate_paths:
        raise SessionError(f"Duplicate target file(s): {', '.join(sorted(duplicate_paths))}")
    if not targets:
        raise SessionError("At least one --file target is required")
    return targets


def targets_from_record(record: dict[str, Any]) -> list[Target]:
    raw_targets = record.get("targets")
    if not isinstance(raw_targets, list):
        raise SessionError(f"Session {record.get('session_id')} has no valid targets")
    targets: list[Target] = []
    for raw_target in raw_targets:
        if not isinstance(raw_target, dict):
            raise SessionError(f"Session {record.get('session_id')} has an invalid target")
        path = raw_target.get("path")
        project_root = raw_target.get("project_root")
        digest = raw_target.get("sha256")
        sorries = raw_target.get("sorries")
        if (
            not isinstance(path, str)
            or not isinstance(project_root, str)
            or not isinstance(digest, str)
            or not isinstance(sorries, int)
        ):
            raise SessionError(f"Session {record.get('session_id')} has an invalid target")
        target = Target(path, project_root, digest, sorries)
        if Path(target.path).is_absolute() or ".." in Path(target.path).parts:
            raise SessionError(f"Session {record.get('session_id')} has an unsafe target path")
        if target.project_root != ".":
            if Path(target.project_root).is_absolute() or ".." in Path(target.project_root).parts:
                raise SessionError(f"Session {record.get('session_id')} has an unsafe Lake project path")
            try:
                path_within_project(target)
            except ValueError as error:
                raise SessionError(f"Session {record.get('session_id')} has a target outside its Lake project") from error
        targets.append(target)
    return targets


def active_overlap(root: Path, target_paths: set[str]) -> str | None:
    for session_id, view in session_views(root).items():
        if not is_active(view):
            continue
        existing_paths = {target.path for target in targets_from_record(view["submitted"])}
        if target_paths & existing_paths:
            return session_id
    return None


def require_key() -> str:
    key = os.environ.get("ARISTOTLE_API_KEY", "")
    if not key:
        raise SessionError(
            "ARISTOTLE_API_KEY is required for this invocation. Ask the user for a fresh one-time key; do not save it."
        )
    return key


def sdk() -> tuple[Any, Any, Any]:
    """Import aristotlelib, re-executing under the official CLI's venv if needed."""

    try:
        project_module = importlib.import_module("aristotlelib.project")
        task_module = importlib.import_module("aristotlelib.agent_task")
        return project_module.Project, project_module.AgentQuestionsSetting, task_module.TaskStatus
    except ModuleNotFoundError as initial_error:
        if os.environ.get("ARISTOTLE_SESSION_REEXEC"):
            raise SessionError(
                "aristotlelib is unavailable. Install the official client with `uv tool install aristotlelib`."
            ) from initial_error
        executable = shutil.which("aristotle")
        if not executable:
            raise SessionError(
                "aristotlelib is unavailable. Install the official client with `uv tool install aristotlelib`."
            ) from initial_error
        first_line = Path(executable).read_text(encoding="utf-8", errors="replace").splitlines()[0]
        if not first_line.startswith("#!"):
            raise SessionError(
                "Could not identify the Python environment behind `aristotle`. Reinstall with `uv tool install aristotlelib`."
            )
        command = shlex.split(first_line[2:])
        if not command or command[0].endswith("env"):
            raise SessionError(
                "Could not identify the Python environment behind `aristotle`. Reinstall with `uv tool install aristotlelib`."
            )
        os.environ["ARISTOTLE_SESSION_REEXEC"] = "1"
        os.execv(command[0], [command[0], str(Path(__file__).resolve()), *sys.argv[1:]])
        raise AssertionError("os.execv unexpectedly returned")


def snapshot_targets(root: Path, session_id: str, targets: list[Target]) -> None:
    destination_root = artifact_root(root) / session_id / "baseline"
    for target in targets:
        source = root / target.path
        destination = destination_root / target.path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def prompt_for(targets: list[Target]) -> str:
    rendered_targets = "\n".join(
        f"- {path_within_project(target)} ({target.sorries} existing `sorry`s)" for target in targets
    )
    return f"""Work only on these Lean files:
{rendered_targets}

Replace their existing `sorry` proof placeholders with valid Lean proofs. Preserve theorem and definition statements, public APIs, imports, and all files outside this target list unless a strictly necessary target-local helper is required. Do not introduce `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or other proof escapes. Do not change Lake configuration. Verify each target with `lake env lean <target>` before finishing. Return the project files even if only partial progress is possible."""


def target_payload(targets: list[Target]) -> list[dict[str, Any]]:
    return [
        {
            "path": target.path,
            "project_root": target.project_root,
            "sha256": target.sha256,
            "sorries": target.sorries,
        }
        for target in targets
    ]


async def submit_session(root: Path, targets: list[Target], allow_small: bool, parent_session: str | None = None) -> dict[str, Any]:
    total_sorries = sum(target.sorries for target in targets)
    if total_sorries == 0:
        raise SessionError("The selected files have no unresolved `sorry` placeholders")
    if total_sorries <= 3 and not allow_small:
        raise SessionError(
            f"Only {total_sorries} `sorry` placeholder(s) found. Aristotle is reserved for >3 proofs unless the scope is demonstrably complex; use --allow-small only for that exception."
        )
    conflict = active_overlap(root, {target.path for target in targets})
    if conflict:
        raise SessionError(f"Running Aristotle session {conflict} already overlaps these targets")

    session_id = str(uuid.uuid4())
    project_root = common_project_root(root, targets)
    key = require_key()
    Project, AgentQuestionsSetting, _ = sdk()
    snapshot_targets(root, session_id, targets)
    try:
        project = await asyncio.wait_for(
            Project.create_from_directory(
                prompt=prompt_for(targets),
                project_dir=project_root,
                agent_questions_setting=AgentQuestionsSetting.DISABLED,
            ),
            timeout=600,
        )
    except Exception as error:
        append_record(
            root,
            {
                "at": now(),
                "event": "submission_failed",
                "session_id": session_id,
                "state": "closed",
                "targets": target_payload(targets),
                "error": scrub_error(error, key),
            },
        )
        raise SessionError(f"Aristotle submission failed: {scrub_error(error, key)}") from error

    record: dict[str, Any] = {
        "at": now(),
        "event": "submitted",
        "project_id": str(project.project_id),
        "session_id": session_id,
        "state": "running",
        "targets": target_payload(targets),
        "total_sorries": total_sorries,
    }
    if parent_session:
        record["parent_session"] = parent_session
    append_record(root, record)
    return {
        "session_id": session_id,
        "project_id": str(project.project_id),
        "state": "running",
        "targets": [target.path for target in targets],
        "total_sorries": total_sorries,
    }


def safely_extract(archive: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    destination_resolved = destination.resolve()
    with tarfile.open(archive, "r:*") as bundle:
        for member in bundle.getmembers():
            member_path = (destination / member.name).resolve()
            if member.isdev() or member.issym() or member.islnk() or not member_path.is_relative_to(destination_resolved):
                raise SessionError(f"Refusing unsafe path in Aristotle archive: {member.name}")
        bundle.extractall(destination)


def candidate_paths(root: Path, result_root: Path, targets: list[Target]) -> dict[str, Path]:
    candidates: dict[str, Path] = {}
    for target in targets:
        candidate = result_root / path_within_project(target)
        if not candidate.is_file():
            raise SessionError(f"Downloaded Aristotle result does not contain target file: {target.path}")
        candidates[target.path] = candidate
    return candidates


def atomic_write(destination: Path, content: bytes) -> None:
    mode = destination.stat().st_mode & 0o777
    with tempfile.NamedTemporaryFile(prefix=f".{destination.name}.aristotle-", dir=destination.parent, delete=False) as handle:
        temporary = Path(handle.name)
        handle.write(content)
    temporary.chmod(mode)
    temporary.replace(destination)


def apply_result(root: Path, session_id: str, targets: list[Target], result_root: Path) -> tuple[bool, str]:
    candidates = candidate_paths(root, result_root, targets)
    original: dict[str, bytes] = {}
    for target in targets:
        source = root / target.path
        current = source.read_bytes()
        if sha256(current) != target.sha256:
            return False, f"{target.path} changed locally since Aristotle submission"
        original[target.path] = current

    backup_root = artifact_root(root) / session_id / "pre-incorporation"
    try:
        for target in targets:
            backup = backup_root / target.path
            backup.parent.mkdir(parents=True, exist_ok=True)
            backup.write_bytes(original[target.path])
            atomic_write(root / target.path, candidates[target.path].read_bytes())

        for target in targets:
            project_root = root if target.project_root == "." else root / target.project_root
            checked = subprocess.run(
                ["lake", "env", "lean", str(path_within_project(target))],
                cwd=project_root,
                text=True,
                capture_output=True,
                check=False,
                timeout=600,
            )
            if checked.returncode != 0:
                detail = (checked.stdout + "\n" + checked.stderr).strip()[-2000:]
                raise SessionError(f"`lake env lean {path_within_project(target)}` failed: {detail}")
    except Exception as error:
        for target in targets:
            atomic_write(root / target.path, original[target.path])
        return False, scrub_error(error)
    return True, "integrated and verified with lake env lean"


async def check_session(root: Path, session_id: str, restart: bool) -> dict[str, Any]:
    views = session_views(root)
    if session_id not in views:
        raise SessionError(f"Session is not recorded in {LOG_NAME}: {session_id}")
    submitted = views[session_id]["submitted"]
    if not is_active(views[session_id]):
        return {"session_id": session_id, "outcome": "already_settled"}

    Project, _, _ = sdk()
    key = require_key()
    project_id = submitted.get("project_id")
    if not isinstance(project_id, str):
        raise SessionError(f"Session {session_id} has no project ID")
    try:
        project = await asyncio.wait_for(Project.from_id(project_id), timeout=90)
        await asyncio.wait_for(project.refresh(), timeout=90)
        tasks, _ = await asyncio.wait_for(project.get_tasks(limit=1), timeout=90)
    except Exception as error:
        message = scrub_error(error, key)
        append_record(
            root,
            {"at": now(), "event": "check_error", "session_id": session_id, "state": "running", "error": message},
        )
        return {"session_id": session_id, "outcome": "check_error", "error": message}

    if not tasks:
        append_record(
            root,
            {"at": now(), "event": "checked", "session_id": session_id, "state": "running", "task_status": "NO_TASK"},
        )
        return {"session_id": session_id, "outcome": "running", "task_status": "NO_TASK"}

    task = tasks[0]
    task_status = task.status.name
    progress = task.percent_complete
    if task_status in RUNNING_STATUSES or task_status not in TERMINAL_STATUSES:
        append_record(
            root,
            {
                "at": now(),
                "event": "checked",
                "session_id": session_id,
                "state": "running",
                "task_status": task_status,
                "percent_complete": progress,
            },
        )
        return {"session_id": session_id, "outcome": "running", "task_status": task_status, "percent_complete": progress}

    targets = targets_from_record(submitted)
    if not project.has_files:
        append_record(
            root,
            {
                "at": now(),
                "event": "finished_without_result",
                "session_id": session_id,
                "state": "closed",
                "task_status": task_status,
            },
        )
        return {"session_id": session_id, "outcome": "finished_without_result", "task_status": task_status}

    session_artifacts = artifact_root(root) / session_id
    archive = session_artifacts / "result.tar.gz"
    result_root = session_artifacts / "result"
    try:
        if result_root.exists():
            shutil.rmtree(result_root)
        if archive.exists():
            archive.unlink()
        session_artifacts.mkdir(parents=True, exist_ok=True)
        await asyncio.wait_for(project.get_files(destination=archive), timeout=300)
        safely_extract(archive, result_root)
        candidates = candidate_paths(root, result_root, targets)
        after_sorries = sum(
            count_sorries(candidates[target.path].read_text(encoding="utf-8")) for target in targets
        )
    except Exception as error:
        message = scrub_error(error, key)
        append_record(
            root,
            {
                "at": now(),
                "event": "result_unavailable",
                "session_id": session_id,
                "state": "closed",
                "task_status": task_status,
                "error": message,
            },
        )
        return {"session_id": session_id, "outcome": "result_unavailable", "task_status": task_status, "error": message}

    before_sorries = sum(target.sorries for target in targets)
    if after_sorries > before_sorries:
        append_record(
            root,
            {
                "at": now(),
                "event": "result_regressed",
                "session_id": session_id,
                "state": "needs_review",
                "task_status": task_status,
                "before_sorries": before_sorries,
                "after_sorries": after_sorries,
            },
        )
        return {"session_id": session_id, "outcome": "result_regressed", "before_sorries": before_sorries, "after_sorries": after_sorries}

    incorporated, detail = apply_result(root, session_id, targets, result_root)
    if not incorporated:
        append_record(
            root,
            {
                "at": now(),
                "event": "integration_blocked",
                "session_id": session_id,
                "state": "needs_review",
                "task_status": task_status,
                "before_sorries": before_sorries,
                "after_sorries": after_sorries,
                "error": detail,
            },
        )
        return {"session_id": session_id, "outcome": "integration_blocked", "error": detail}

    if after_sorries == 0:
        append_record(
            root,
            {
                "at": now(),
                "event": "integrated_complete",
                "session_id": session_id,
                "state": "closed",
                "task_status": task_status,
                "before_sorries": before_sorries,
                "after_sorries": after_sorries,
            },
        )
        return {"session_id": session_id, "outcome": "integrated_complete", "detail": detail}

    if after_sorries == before_sorries:
        append_record(
            root,
            {
                "at": now(),
                "event": "integrated_no_progress",
                "session_id": session_id,
                "state": "closed",
                "task_status": task_status,
                "before_sorries": before_sorries,
                "after_sorries": after_sorries,
            },
        )
        return {"session_id": session_id, "outcome": "integrated_no_progress", "detail": detail}

    append_record(
        root,
        {
            "at": now(),
            "event": "partial_result_integrated",
            "session_id": session_id,
            "state": "closed",
            "task_status": task_status,
            "before_sorries": before_sorries,
            "after_sorries": after_sorries,
        },
    )
    if not restart:
        return {"session_id": session_id, "outcome": "integrated_partial", "detail": detail}

    new_targets = [target_from_path(root, target.path) for target in targets]
    try:
        restarted = await submit_session(root, new_targets, allow_small=True, parent_session=session_id)
    except Exception as error:
        message = scrub_error(error, key)
        append_record(
            root,
            {
                "at": now(),
                "event": "restart_failed",
                "session_id": session_id,
                "state": "closed",
                "error": message,
            },
        )
        return {"session_id": session_id, "outcome": "integrated_partial_restart_failed", "error": message}
    return {"session_id": session_id, "outcome": "integrated_partial_restarted", "restart": restarted}


def list_sessions(root: Path) -> list[dict[str, Any]]:
    listed: list[dict[str, Any]] = []
    for session_id, view in session_views(root).items():
        submitted = view["submitted"]
        latest = view["latest"]
        listed.append(
            {
                "session_id": session_id,
                "project_id": submitted.get("project_id"),
                "state": latest.get("state"),
                "event": latest.get("event"),
                "targets": [target.path for target in targets_from_record(submitted)],
                "updated_at": latest.get("at"),
            }
        )
    return sorted(listed, key=lambda item: str(item.get("updated_at", "")), reverse=True)


def parser() -> argparse.ArgumentParser:
    root_parser = argparse.ArgumentParser(description=__doc__)
    subparsers = root_parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="List locally logged sessions without contacting Aristotle")
    list_parser.add_argument("--repo", help="Repository root or a directory inside it")

    submit_parser = subparsers.add_parser("submit", help="Start an asynchronous Aristotle project")
    submit_parser.add_argument("--repo", help="Repository root or a directory inside it")
    submit_parser.add_argument("--file", action="append", required=True, help="Target Lean file; repeat for several files")
    submit_parser.add_argument(
        "--allow-small",
        action="store_true",
        help="Allow <=3 sorries only for a documented genuinely complex scope",
    )

    check_parser = subparsers.add_parser("check", help="Check logged sessions once; never wait for remote completion")
    check_parser.add_argument("--repo", help="Repository root or a directory inside it")
    check_parser.add_argument("--session", action="append", help="Check one recorded session; repeat if needed")
    check_parser.add_argument("--no-restart", action="store_true", help="Do not automatically restart a verified partial result")
    return root_parser


def main() -> int:
    args = parser().parse_args()
    try:
        root = git_root(getattr(args, "repo", None))
        if args.command == "list":
            emit({"log": str(log_path(root)), "sessions": list_sessions(root)})
            return 0
        if args.command == "submit":
            targets = targets_from_paths(root, args.file)
            result = asyncio.run(submit_session(root, targets, args.allow_small))
            emit({"action": "submitted", "log": str(log_path(root)), **result})
            return 0

        views = session_views(root)
        requested = args.session or [session_id for session_id, view in views.items() if is_active(view)]
        if not requested:
            emit({"action": "checked", "log": str(log_path(root)), "outcomes": []})
            return 0
        require_key()
        outcomes = [asyncio.run(check_session(root, session_id, restart=not args.no_restart)) for session_id in requested]
        emit({"action": "checked", "log": str(log_path(root)), "outcomes": outcomes})
        return 0
    except SessionError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
