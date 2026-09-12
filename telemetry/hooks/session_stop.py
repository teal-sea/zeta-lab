#!/usr/bin/env python3
"""Stop hook, close the run this session opened. Opt-in; see README.md.

If no marker exists the session was not instrumented, and that is left as it
is: inventing a run for a session nobody observed would be exactly the
fabrication this system refuses. Same swallow-everything rule as the start
hook, telemetry never blocks a session.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REPO = ROOT.parent
sys.path.insert(0, str(REPO))


def main() -> int:
    try:
        raw = sys.stdin.read() if not sys.stdin.isatty() else ""
        payload = json.loads(raw) if raw.strip() else {}
    except (ValueError, OSError):
        payload = {}

    try:
        session = (
            payload.get("session_id")
            or os.environ.get("CLAUDE_CODE_SESSION_ID")
            or "unknown-session"
        )
        marker = ROOT / ".active" / f"{session}.run"
        if not marker.exists():
            return 0
        run_id = marker.read_text(encoding="utf-8").strip()

        from telemetry.cli import main as cli_main

        cli_main(["--root", str(ROOT), "--repo", str(REPO), "finish", run_id,
                  "--status", "completed"])
        marker.unlink(missing_ok=True)
    except Exception as exc:  # noqa: BLE001
        print(f"telemetry session_stop: {exc}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
