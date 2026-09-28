# `telemetry/hooks/`: opt-in emission, deliberately not installed

Nothing in this directory is active. These files are **templates**, and the
reason is the isolation contract this system was built under
(`telemetry/PREFLIGHT-2026-08-13.md`): two frontier research sessions were live
when it was written, and both are grandfathered. Installing a git hook or
editing shared agent settings would have retrofitted instrumentation into
running research to make a log tidier, which is exactly the "observation
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

```bash
python3 telemetry/hooks/install.py            # wire the session hooks here
python3 telemetry/hooks/install.py --status   # what is wired in this checkout
python3 telemetry/hooks/install.py --uninstall
```

It writes `.claude/settings.local.json`, which is **gitignored and
per-checkout**, so enabling telemetry in one worktree cannot follow a merge into
anyone else's session. The tracked `.claude/settings.json` is never touched.

The installer is idempotent, preserves any existing hook on the same event
(reporting it rather than clobbering it), and refuses outright on a malformed
settings file, a broken settings file silently disables every setting in it.

`settings.telemetry.json` is the same wiring as a readable template, for anyone
who would rather paste it than run a script.

**The commit-trailer git hook is separate and off by default**, because
`.git/hooks` is common to every worktree of a clone, the one blast radius here
that crosses the isolation boundary:

```bash
python3 telemetry/hooks/install.py --git-hook
```

It refuses while any other worktree of the clone exists, and names them.
`--force` overrides, and should be used only when nothing else is running.

**Hooks fire on the NEXT session in that worktree, never the current one.** If
they do not, open `/hooks` once, that reloads config, or restart.

## What the hooks cannot capture

Neither hook can recover the model, the token counts or the cost: this
environment exports no model identifier and no usage figures to the session
(measured, see `RUN-TELEMETRY.md`). A hook-opened run therefore carries
`model: null` unless the agent declares one with
`python -m telemetry note` or the operator passes `--model` at start. Unknown
stays unknown.
