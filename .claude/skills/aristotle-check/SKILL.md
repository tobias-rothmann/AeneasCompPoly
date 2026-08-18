---
name: aristotle-check
description: "Check repository-recorded Aristotle API proof sessions on request, without waiting for remote work. Use when a user asks for Aristotle status or when an Aristotle session may have finished: record each check in the centralized log, safely incorporate completed or no-progress results, and automatically restart a verified partial result on its remaining `sorry` placeholders."
---

# Aristotle Check

Use this skill whenever the user explicitly asks to check Aristotle. It checks
only sessions recorded in the repository's append-only
`logs/aristotle-sessions.jsonl`; it never discovers or touches unrelated account
projects.

## One-time credential rule

Run the local listing first. If no session remains in `running` state, report
that result without asking for a key. Otherwise ask the user for a fresh
Aristotle API key for this one check operation. Do not reuse a prior key, read
one from configuration, store it, export it, pass it through `--api-key`, or
echo it. Supply it only as an inline environment variable to the one helper
process. If an automatic restart is needed, it may use that same process-local
credential during this single check operation; it must never retain it.

## Check and integrate

1. See which logged sessions are still running:

   ```sh
   python3 .claude/skills/aristotle-check/scripts/aristotle_check.py list
   ```

2. If any are active, ask for the one-time key and invoke:

   ```sh
   ARISTOTLE_API_KEY='<key supplied for this one check>' \
     python3 .claude/skills/aristotle-check/scripts/aristotle_check.py check
   ```

   Do not use `aristotle show`: in the current CLI it waits on a running task.
   The helper uses the SDK status endpoint once per logged session and returns
   immediately after status retrieval.

3. For a terminal task, the helper downloads its result to
   `.aristotle-artifacts/`, compares the number of target-file `sorry`s to the
   pre-submission snapshot, and appends a check event to the central log. It
   refuses to overwrite a file changed locally since submission.

   - With zero remaining target `sorry`s, it atomically incorporates the
     returned target files after `lake env lean` verifies each one.
   - With the same number of target `sorry`s, it incorporates the returned
     files after the same validation, as requested. A result that introduces
     additional `sorry`s is instead retained as an artifact and marked for
     review.
   - With fewer but nonzero `sorry`s, it incorporates the verified partial
     result, appends the handoff event, and immediately creates a new async
     Aristotle session for the remaining obligations. This is the prove
     workflow's restart path; it does not wait for the new session.
   - With no downloadable result, a merge conflict, or a failed local Lean
     validation, it logs the reason and leaves repository sources unchanged.

4. Report concise facts only: still-running IDs/statuses, files incorporated,
   newly started restart IDs, and any review blockers. Never show the key or
   call a session complete unless the log says it was verified and integrated.
