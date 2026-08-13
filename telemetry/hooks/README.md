# `telemetry/hooks/` — opt-in emission, deliberately not installed

Nothing in this directory is active. These files are **templates**, and the
reason is the isolation contract this system was built under
(`telemetry/PREFLIGHT-2026-08-13.md`): two frontier research sessions were live
when it was written, and both are grandfathered. Installing a git hook or
editing shared agent settings would have retrofitted instrumentation into
running research to make a log tidier — which is exactly the "observation
becomes control" failure the pass was told to avoid.

So: the mechanism ships, and turning it on is an operator decision, taken once
the live sessions have landed.

## What each file is

| File | Boundary | Installs into |
|---|---|---|
| `session_start.py` | opens a run when an agent session begins | a `SessionStart` hook |
| `session_stop.py` | closes it when the session ends | a `Stop` hook |
| `settings.telemetry.json` | the wiring for both | `.claude/settings.local.json` |
| `prepare-commit-msg` | appends `Run-Id:` to commit messages automatically | `.git/hooks/` |

## Turning it on (one worktree at a time)

`.claude/settings.local.json` is **gitignored** and per-checkout, so enabling
hooks there affects one worktree and cannot follow a merge into anyone else's
session. That is the whole reason the template targets it rather than the
tracked `.claude/settings.json`.

```bash
# from the worktree you want instrumented, and only that one
python3 - <<'PY'
import json, pathlib
p = pathlib.Path(".claude/settings.local.json")
existing = json.loads(p.read_text()) if p.exists() else {}
template = json.loads(pathlib.Path("telemetry/hooks/settings.telemetry.json").read_text())
existing.setdefault("hooks", {}).update(template["hooks"])
p.parent.mkdir(exist_ok=True)
p.write_text(json.dumps(existing, indent=2) + "\n")
print("wrote", p)
PY
```

The git hook is the one with a shared blast radius — `.git/hooks` is common to
every worktree of a clone — so it is **not** wired by the snippet above:

```bash
cp telemetry/hooks/prepare-commit-msg .git/hooks/ && chmod +x .git/hooks/prepare-commit-msg
```

Do that only when no other worktree of the same clone has a session running.

## What the hooks cannot capture

Neither hook can recover the model, the token counts or the cost: this
environment exports no model identifier and no usage figures to the session
(measured — see `RUN-TELEMETRY.md`). A hook-opened run therefore carries
`model: null` unless the agent declares one with
`python -m telemetry note` or the operator passes `--model` at start. Unknown
stays unknown.
