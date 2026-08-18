#!/usr/bin/env python3
"""Invoke the shared Aristotle session helper from the check skill."""

from __future__ import annotations

import os
import sys
from pathlib import Path


CORE = Path(__file__).resolve().parents[2] / "aristotle-prove" / "scripts" / "aristotle_sessions.py"

if not CORE.is_file():
    print(f"error: missing shared Aristotle helper: {CORE}", file=sys.stderr)
    raise SystemExit(2)

os.execv(sys.executable, [sys.executable, str(CORE), *sys.argv[1:]])
