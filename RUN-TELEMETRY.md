# RUN-TELEMETRY.md — the run registry

Operational reference for `telemetry/`. What a run is, where records live, how
they get written, what is authoritative, and what this cannot see.

This records **how research happened**, never what it found. `meta/README.md`'s
rule binds here unchanged: a session with no mathematics and a tidy log
produced nothing. Nothing in `telemetry/` is evidence about any subject.

---

## 1. What a run is

A **run** is one bounded unit of work by one actor, with a beginning and an
end: a wrapped command, an agent session, a prover submission, a suite
execution. It is not a task, not a decision, not a claim — those already live
in `ROADMAP.md`, `HANDOFF.md`, `hunts/*/MISSION.md` and the harness ledgers,
and this system does not replace any of them.

A run has a UUID. Nothing else identifies it.

## 2. Where records live

```
telemetry/runs/<run_id>.jsonl     one file per run, append-only events (TRACKED)
telemetry/prompts/<sha256>.txt    prompt text, content-addressed  (GITIGNORED)
telemetry/.active/<session>.run   live session → open run marker  (GITIGNORED)
```

**One file per run, not one shared ledger.** Two sessions writing at once touch
two files, so cross-run merge conflicts are structurally impossible. That was
chosen from this repository's own history: three avoidable collisions between
concurrent sessions in a single day (`hunts/frontier_math/ACTIVE-CLAIMS.md`),
and a private ledger that needed `merge=union` to survive two machines.

**The current state of a run is the fold of its events**, never a rewritten
record. Three event kinds: `run_started`, `run_note`, `run_finished`. A file
with a start and no finish folds to `interrupted` — which is a real answer, not
a missing one.

Ingesting the whole registry is one line, which is the point of the format:

```bash
python3 -c "
import json,glob
for f in sorted(glob.glob('telemetry/runs/*.jsonl')):
    for line in open(f):
        print(json.loads(line)['kind'])"
```

## 3. Emitting a run

### Automatic — prefer this

```bash
python3 -m telemetry wrap --task "regenerate figures" -- python scripts/make_figures.py --quick
```

`wrap` emits start and finish around any command: duration measured, exit code
recorded, status derived from it, commits and artifacts collected from git.
Nothing to remember.

### Explicit boundaries — for work no single command wraps

```bash
RUN=$(python3 -m telemetry start --task "close blocker 2" --task-ref hunts/frontier_math \
        --model claude-opus-5 --model-source declared-by-agent --prompt-file /path/to/brief.md)
# … work …
python3 -m telemetry note "$RUN" "route A refuted; switching to the dual"
python3 -m telemetry finish "$RUN" --status completed --outcome landed
```

### Hooks — shipped, **not installed**

`telemetry/hooks/` carries a `SessionStart`/`Stop` pair, a `prepare-commit-msg`
hook that appends the trailer, and a settings template. None is active.

Two frontier research sessions were live when this landed and are
**grandfathered**: no hook, wrapper, environment variable, prompt change or
provider configuration was injected into them. Turning hooks on is an operator
decision — `telemetry/hooks/README.md` has the procedure. The settings template
targets `.claude/settings.local.json`, which is gitignored and per-worktree, so
enabling it in one checkout cannot follow a merge into anyone else's session.
The git hook is the one with a shared blast radius (`.git/hooks` is common to
every worktree of a clone) and is deliberately left to a deliberate `cp`.

## 4. Fields, and which are authoritative

| Field | Source | Authoritative? |
|---|---|---|
| `run_id` | `uuid4()` at start | yes |
| `started_at` / `finished_at` | recorded instants, UTC with offset | yes |
| `duration_seconds` | wrapped-command measurement, else `finished_at − started_at` | yes |
| `status` | exit code, or explicit; `interrupted` = no finish event | yes |
| `outcome` | declared: `landed` / `no-change` / `killed` / `blocked` / `refused` / `crashed` | declared |
| `start_commit`, `branch`, `worktree` | `git` at start | yes |
| `commits` | `git rev-list start..HEAD` at finish, **plus** any commit whose `Run-Id` trailer names the run | yes (the trailer is primary — see §6) |
| `artifacts` | changed + dirty + untracked paths at finish, each with sha256 | yes |
| `agent_session_id` | `CLAUDE_CODE_SESSION_ID` | yes, where exported |
| `provider` | inferred from harness env vars | yes |
| `model`, `model_id` | **declared only** (`--model`), always with `model_source` | declared, never sniffed |
| `input/output/cache tokens` | provider-reported only | absent here (§7) |
| `provider_usd` | provider-reported only | absent here (§7) |
| `estimated_usd` | refused without `estimate_basis` | declared |
| `prompt` | `{digest, store, ref, bytes, source}` | digest yes, text local (§5) |
| `capture` | `contemporaneous` or `reconstructed` | yes |

**`worktree` is the directory's name, never its absolute path.** Run records
are tracked in a public repository, and `tests/test_repo_hygiene.py` scans
tracked `.jsonl` for home-directory shapes. The first smoke test of this system
recorded an absolute path; the guard caught it and `tests/test_telemetry.py`
now pins it.

### Unknown stays unknown

No field is ever filled in by inference. `Run.unknown_fields()` lists what was
never captured and travels inside `as_dict()`, so a reader asking what a run
cost gets either a number or the field's name — never a plausible blank. `0`
tokens and *no token data* are different values and stay different.

## 5. Prompt and context provenance

A digest answers "did this change?"; it does not answer "what was it?". Both
are recorded:

- text is stored **content-addressed** at `telemetry/prompts/<sha256>.txt`
  (idempotent — the same prompt across forty runs is stored once, and an
  existing file is never rewritten);
- the run record carries `{digest, store, ref, bytes, source}`;
- `store` is `local-private`, `external`, or `absent` — and `absent` is
  recorded rather than omitted, because a missing field cannot be told apart
  from a capture bug.

**The digest is public and durable; the text is local and mortal.** The prompt
store is gitignored: this repository is public, prompts routinely carry
strategy material, private paths and third-party context, and `HANDOFF.md`
already records why strategy documents are kept off-tree. A clone can verify a
prompt has not changed and cannot read it.

For material that must not enter even a gitignored directory in a public
checkout, use `--prompt-external DIGEST:REF` and keep the text in the
operator's private store — the arrangement `conjectures/` already uses.

`telemetry reconcile` recomputes every local digest and reports
`prompt_unrecoverable` when the stored text is not the text that ran.

## 6. Git linkage

```
Run-Id: 3f2a9c81-4b7e-4a11-9f30-8c1d5e6a7b90
```

Append that trailer to a commit message; `python3 -m telemetry trailer <run_id>`
prints it.

**Why a new trailer.** The two that already appear cannot carry the join:
`Co-Authored-By` names a model family, not an occasion (203 of 346 commits
share three values, and 143 carry none); `Claude-Session` names a provider-side
conversation that may span many runs and resolves to a service rather than an
artifact. Both are still read, as corroboration.

The trailer is the **primary** link and beats the run record's own `commits`
list where they disagree — a commit is a fact, a record is a claim about one.

## 7. What this environment does not expose

Measured on 2026-08-13, not assumed:

| Wanted | Status here |
|---|---|
| model identifier | **absent** — `ANTHROPIC_MODEL`, `CLAUDE_MODEL` unset. Must be declared |
| input / output / cache tokens | **absent** — no provider variable, no session API |
| provider dollar cost | **absent** |
| per-turn timing inside a session | **absent** — only run boundaries |
| tool-call trace | **not captured, by choice** (§9) |

Available and captured: `CLAUDE_CODE_SESSION_ID`, `CLAUDE_CODE_REMOTE_SESSION_ID`,
`CLAUDE_CODE_VERSION`, `CLAUDE_CODE_ENTRYPOINT`, `CLAUDE_EFFORT`,
`MAX_THINKING_TOKENS`, `AI_AGENT`.

Environment capture is an **allowlist** (`registry.ENV_ALLOWLIST`), so a
provider that starts exporting something sensitive cannot leak it into a public
repository by default. `registry.ENV_DENIED` names what is refused on purpose —
user email, account and organization UUIDs, and every credential.

Providers differ. `provider_meta` preserves provider-specific fields verbatim
rather than flattening them into a shared shape that would imply parity none of
them have.

## 8. Reconciliation

```bash
python3 -m telemetry reconcile                       # report
python3 -m telemetry reconcile --strict              # exit 1 on any defect
python3 -m telemetry reconcile --require-trailer-since <rev>
```

Thirteen findings, three severities, no aggregate and no score:

| Severity | Meaning |
|---|---|
| `defect` | the record and the repository contradict each other |
| `gap` | something was never captured — common, and not an error by itself |
| `note` | legal and worth seeing (one run, three commits) |

Detected: `corrupt_record`, `unfoldable_run`, `duplicate_run_id`,
`interrupted_run`, `run_without_commit`, `missing_commit`, `orphan_commit`,
`commit_mismatch`, `untrailered_commit`, `multi_commit_run`,
`prompt_unrecoverable`, `prompt_local_only`, `prompt_absent`.

Three deliberate defaults:

- **`untrailered_commit` is opt-in.** Every commit made before this system
  existed has no trailer; reporting all of them would bury the findings that
  matter. Grandfathered work is not a defect.
- **`missing_commit` says "absent from this checkout".** A shallow clone
  cannot distinguish a lost commit from an unfetched one, and this clone is
  shallow.
- **A prompt absent from this machine is a `gap`, not a `defect`.** The store
  is gitignored, so every fresh clone is in that state; grading it a defect
  would make `reconcile --strict` fail on a clean checkout, and a guard that
  fires on correct behaviour is one nobody reads. A *mismatching* digest stays
  a defect — that is tampering, not locality. Both are pinned by tests.

## 9. Reconstructed history

```bash
python3 -m telemetry reconstruct --task "…" --reconstructed-from "git log 32e4428..HEAD"
```

Writes `capture: "reconstructed"` and **refuses without `--reconstructed-from`**.
Reconstructed and contemporaneous records never render alike. Nothing has been
reconstructed yet; the pre-2026-08-13 history and the two grandfathered
sessions have no run records and are not going to grow fabricated ones.

## 10. Known blind spots

1. **Sessions are only instrumented if someone turns the hooks on**, and the
   hooks are off. Until then, coverage depends on `wrap` and `start`/`finish`
   being used — which is the failure mode this design is most exposed to.
2. **No model, no tokens, no cost from this provider** (§7). The most-wanted
   fields are the least available, and `--model` is a declaration a careless
   caller can get wrong.
3. **Within-session granularity is zero.** A six-hour agent session is one run.
4. **Artifact attribution is temporal, not causal** — `wrap` records what
   changed in the repository during the run, which for a run that overlaps
   manual editing will over-attribute.
5. **The prompt store does not survive a fresh clone.** Digests do, and
   reconciliation reports the difference as a gap rather than a defect.
6. **`reconcile` scans a bounded range** (default 200 commits).
7. **Nothing enforces truthfulness.** `--model`, `--outcome` and `--task` are
   declarations, in the same sense as `harness/provenance.py`: declared data,
   never attestation.

## 11. Later, without a database today

The format is deliberately trivial to ingest, and nothing about it needs a
database now:

```sql
CREATE TABLE run_event (run_id TEXT, at TEXT, kind TEXT, payload JSONB);
```

One row per line, one `COPY`, and the fold becomes a view. Adding storage later
is a load; adding it now would be a schema decision taken before the data
exists to justify one.

What would actually force a database: run counts past what a directory listing
handles comfortably, or a query pattern across runs that `jq` cannot serve. The
registry should be allowed to reach that point before anything is migrated.

## 12. Tests

```bash
python -m pytest tests/test_telemetry.py -q -o addopts=''
```

64 tests, stdlib + pytest only — they pass in a checkout with none of the
laboratory's numerical dependencies installed, because telemetry that needs
`mpmath` to run stops running exactly when a session is least able to fix it.
Every test uses a `tmp_path` root and a throwaway git repository; none reads or
writes the live registry, another worktree, or any research artifact.
