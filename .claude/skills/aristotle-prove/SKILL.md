---
name: aristotle-prove
description: Start non-blocking Aristotle API sessions to discharge substantial Lean proof debt. Use when a selected set of Lean files has at least four unresolved `sorry` placeholders, or when the remaining obligations are demonstrably complex and worth a long remote run; do not use for one, two, or three straightforward proofs. Submit the proof run, record it in the repository-wide Aristotle session log, and immediately return control rather than polling or waiting for Aristotle to finish.
---

# Aristotle Prove

Use this skill only after ordinary local proof work is a poor fit: large proof
backlogs or hard, interconnected obligations. Resolve the exact target `.lean`
files first. The helper counts real `sorry` tokens while ignoring comments and
strings, and rejects a total of three or fewer unless `--allow-small` is used
for a genuinely complex scope.

## One-time credential rule

Ask the user for a fresh Aristotle API key immediately before submitting. Say
that it will be used for this one command only. Do not read a previously set
key, write a `.env` file, export it, pass `--api-key`, put it in shell config,
or repeat it in output, logs, patches, or the final response.

Pass the just-supplied key only as an inline environment assignment to the
single helper process. The helper does not save it. If the user has not
provided a key in the current request, stop at the credential request.

## Submit

1. Locate the Lean project root and the selected files. Check that no existing
   running Aristotle session already overlaps them:

   ```sh
   python3 .claude/skills/aristotle-prove/scripts/aristotle_sessions.py list
   ```

2. Ask for the one-time key. With that key available only in the current
   interaction, start the asynchronous session (repeat `--file` for each
   selected file):

   ```sh
   ARISTOTLE_API_KEY='<key supplied for this one submission>' \
     python3 .claude/skills/aristotle-prove/scripts/aristotle_sessions.py submit \
       --file path/to/First.lean --file path/to/Second.lean
   ```

   For one to three hard obligations, use `--allow-small` only after recording
   why local proof work is inappropriate. Never use it merely to outsource a
   simple proof.

3. Do not call `aristotle show`, add `--wait`, poll, or otherwise wait for the
   remote proof. The helper writes a `submitted` record with the remote project
   ID and `state: running` to `logs/aristotle-sessions.jsonl`.
   It stores only target paths, hashes, counts, IDs, and timestamps—never an API
   key. Downloaded response archives live in ignored `.aristotle-artifacts/`.

4. Tell the user that Aristotle has started, name the target files and session
   ID, point to `logs/aristotle-sessions.jsonl`, and suggest `$aristotle-check` for a
   later status check. Do not claim any proof is complete.

The helper uses the installed `aristotlelib` CLI environment when available. If
it is absent, install the official client with `uv tool install aristotlelib`
only after obtaining the user's permission for that networked installation.
