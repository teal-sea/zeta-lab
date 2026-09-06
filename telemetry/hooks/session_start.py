#!/usr/bin/env python3
"""SessionStart hook, open a run for an agent session. Opt-in; see README.md.

Reads the harness's hook payload on stdin (JSON, best effort) and opens a run
whose ``agent_session_id`` is whatever the harness actually supplied. Writes
``telemetry/.active/<session>.run`` so the Stop hook can close the same run.

Three rules this file exists to honour:

* **It never fails the session.** Any exception is swallowed and reported on
  stderr. Telemetry that can block research is worse than no telemetry.
* **It never guesses the model.** The payload and the environment do not carry
  one here, so ``model`` is simply absent.
* **It never writes outside the telemetry root.**
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
        from telemetry.prompts import capture_text
        from telemetry.registry import append_event, new_run_id, probe_context, utc_now
        from telemetry.schema import Event

        session = (
            payload.get("session_id")
            or os.environ.get("CLAUDE_CODE_SESSION_ID")
            or "unknown-session"
        )
        active = ROOT / ".active"
        active.mkdir(parents=True, exist_ok=True)
        marker = active / f"{session}.run"
        if marker.exists():
            return 0  # already open; a resumed session is not a second run

        run_id = new_run_id()
        context = probe_context(REPO)
        env = context.pop("env", None)

        # The opening prompt, stored locally and referenced by digest. The text
        # lands in the gitignored private store (`telemetry/.gitignore` line
        # `prompts/*`); only the digest travels in the committed run record, so
        # provenance is public and wording is not. A session that declares no
        # prompt still records `store: absent` with a null digest, unknown
        # stays unknown, and an absent prompt is not a failed one.
        text = payload.get("prompt")
        if isinstance(text, str) and text.strip():
            ref = capture_text(ROOT, text, source="session-start-hook")
            prompt = {**ref.as_dict(), "captured_at": ref.captured_at or utc_now()}
        else:
            prompt = {"digest": None, "store": "absent", "ref": None,
                      "bytes": None, "source": "session-start-hook",
                      "captured_at": utc_now()}

        body = {
            "capture": "contemporaneous",
            "task": text or "(agent session; task not declared at start)",
            "role": "agent-session",
            "prompt": prompt,
            **context,
        }
        if env:
            body["provider_meta"] = {"env": env, "hook_payload_keys": sorted(payload)}
        append_event(ROOT, Event(kind="run_started", run_id=run_id, at=utc_now(),
                                 payload=body))
        marker.write_text(run_id, encoding="utf-8")
    except Exception as exc:  # noqa: BLE001 - never block a session
        print(f"telemetry session_start: {exc}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
