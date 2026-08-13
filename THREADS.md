# THREADS.md — things worth remembering that nobody is pursuing

A loose thread is something the lab noticed and deliberately did **not** chase,
because attention was elsewhere. Without this file they dissolve into HANDOFF
records, code comments and agent transcripts, and get rediscovered at full price.

`scripts/70_lab_state.py` derives *live* work from git — every branch ahead of
`origin/main`, right by construction. It cannot derive a parked thread, because
a parked thread has no branch. That gap is the only reason this file exists.

## How to use it

Add a block the moment you notice something and decide not to chase it. Five
fields, all required, no ceremony. Keep it to a few lines each — enough context
that a fresh agent can resume without reading your transcript.

```
### T-NNN  short name
**Noticed**   what was actually observed
**Matters**   why it might be worth something
**From**      where it came from — file, commit, run id, session
**Resume**    concrete first step, and the pointers to do it
**Status**    parked | pulling | dead — with a date and one clause of reason
```

`parked` is the normal state and needs no apology. `dead` blocks stay, with the
reason — a thread killed for a stated reason is worth more than a missing one,
because it stops the next agent re-opening it. Do not delete blocks; change
`Status`. Numbering is monotonic; never reuse an id.

`tests/test_threads.py` checks the format, that ids are unique and monotonic,
and that every status is one of the three words. It does not check the prose,
and it never will.

---

### T-001  Rung 3 refinement is unavailable, so compiler verdicts stop at a hand-written model
**Noticed**   `compiler/semantics.py` declares three rungs. Rung 3 — LLVM-native
refinement via Alive2 — reports `ABSENT: alive-tv not on PATH`, so every
compiler verdict rests on rung 2, a hand-written poison-aware model of the
LangRef rather than LLVM's own semantics.
**Matters**   Rung 2 is the thing that made the harness gate's traps decidable at
all. Its correctness is currently cross-checked only against clang on values the
model calls defined, which by construction cannot check the poison class — the
exact class it exists to see. An installed Alive2 would turn that into a real
two-backend check.
**From**      `compiler/semantics.py:209` `_alive2()`; surfaced by every gate v4
run (`harness/gate-evidence/gate4/`), each of which reported rung 3 absent.
**Resume**    Install `alive-tv`, then run the six gate v4 rewrites through it and
compare against `refinement()`. Disagreement on any of the three poison traps is
a real finding about the model.
**Status**    parked 2026-08-13 — needs a toolchain install, not a decision.

### T-002  Nothing automatically records a run outcome, so prompts cannot be scored
**Noticed**   `telemetry/schema.py` defines
`OUTCOMES = (landed, no-change, killed, blocked, refused, crashed)`, and
`python -m telemetry wrap --outcome ...` **does** record one correctly — verified
end to end this pass. What is missing is any *caller*: no script, hook or runner
passes it, so every real run record carries `status: completed` and no outcome.
**Matters**   The prompt store now captures what an agent was asked. Without an
outcome beside it there is no `(prompt, result)` pair, so "which prompts work"
stays unanswerable however many runs accumulate. Half the join key exists, and
the other half is a flag nobody passes rather than a feature nobody built.
**From**      `telemetry/cli.py` `wrap`; gap found while sizing hunt automation.
Corrected from an earlier version of this thread that wrongly said the outcome
mechanism did not exist.
**Resume**    Give it a caller — the hunt runner in T-005 is the obvious first
one. `landed` vs `no-change` is also mechanically derivable after the fact, since
commits already carry a `Run-Id:` trailer. The judgment outcomes
(`killed`, `blocked`, `refused`) must stay operator-declared; per `meta/README.md`
a system that grades its own output flatters itself.
**Status**    parked 2026-08-13 — blocked on having a caller, not on design.

### T-003  Gate v5 never ran its arms: does the harness help on the lab's own subject?
**Noticed**   Four gates tested the harness on croniter and LLVM IR — neither is
what this lab works on. A fifth was built for the mathematics: claimed structural
properties of ζ, scored by whether the Davenport–Heilbronn function (which shares
ζ's functional equation and violates RH) also satisfies them. Ground truth
reached 5 of 6 before the pass ended; the arms never ran.
**Matters**   The ground truth alone is worth keeping: the functional equation, a
real Hardy Z, and zeros on the critical line are each satisfied by **all three**
RH-violating rivals — worth nothing as evidence. Only multiplicativity kills
them. That is `docs/09` gate #3 confirmed numerically and it stands independently
of the harness question.
**From**      This pass; `zeta.epstein.battery`. P6 — "no zeros in a box strictly
off the critical line", via `count_zeros_box` — **ran to a 50-minute timeout**
without finishing, on four functions at working precision. P1–P5 completed in
under 20 minutes between them.
**Resume**    P6 as written is too expensive: argument-principle contour
integration over `Re ∈ [0.6,0.9], Im ∈ [80,90]` for ζ plus three rivals. Narrow
the box, lower `dps`, or drop P6 and rebalance — but choose before seeing any
truth value, not after. Then decide whether the A/B is worth 12 runs at all: it
cannot overturn four failures, since one six-item screen is grounds for a second
look rather than a verdict.
**Status**    parked 2026-08-13 — the ground-truth half is the part worth having.

### T-004  Two archaeology documents at the root are now partly superseded
**Noticed**   `ARCHITECTURE-ARCHAEOLOGY.md` and `INSTITUTION-FUTURES.md` both
describe `harness/` as an expanding central capability and an open question.
The question is now answered (`harness/VERDICT.md`).
**Matters**   Leaving them uncorrected misleads; rewriting them destroys the
record of a belief that was later tested and refuted, which is exactly the kind
of thing this lab should keep.
**From**      This pass. `INSTITUTION-FUTURES.md` §7 already called the harness an
unproven claim and named the measurement that settled it.
**Resume**    Resolved differently than planned: both documents **moved to the
private operating repository** (`fulcrum/strategy/`) rather than being annotated
here, because both are about how the laboratory is built and operated rather
than about any scientific claim. They remain in this repository's git history at
`d75d659~1`, unedited. Nothing further is owed here.
**Status**    dead 2026-08-13 — superseded by the public/private split; the
documents are preserved, in history and in fulcrum.

### T-005  Hunt Automation v0 — the loop exists in pieces and has no runner
**Noticed**   The concrete hunt workflow is already conventional and already runs
end to end by hand: `hunts/<name>/MISSION.md` + `probe.py` → `results.json`.
Four hunts carry all three (`flow_repair`, `golden_control`, `jensen_clock`,
`lehmer_pair`); twelve carry a MISSION. Separately,
`python -m telemetry wrap --outcome ...` already opens a run, hashes the
artifacts a command produced, and closes it with an outcome. **Nothing joins
them.** There is no `scripts/*hunt*` runner; every probe is invoked by a human.
**Matters**   This is the whole automatable loop — thread → bounded run →
artifacts + telemetry → outcome → new threads — and almost all of it exists. The
missing piece is one script, not a research operating system.
**From**      This pass, sizing goal E. Verified: `wrap --outcome landed`
records outcome and artifact hashes correctly.
**Resume**    See `AGENTS.md` → "Loose threads" and the v0 sketch in the pass
report: a `scripts/71_run_hunt.py <hunt>` that shells `probe.py` through
`telemetry wrap`, maps exit status to an outcome, and prints the `Run-Id`. Build
it against the four hunts that already have probes, and only for those — do not
generalize it to hunts that do not yet have a probe.
**Status**    parked 2026-08-13 — named as the next bounded engineering target,
deliberately not built in a pass whose job was demotion.

### T-006  CONTEXT.md is generated and committed, so every parallel branch conflicts on it
**Noticed**   `CONTEXT.md` is regenerated by `scripts/make_context.py` and
committed. Two branches live at the same moment this pass — `claude/o9-first-build`
and `claude/harness-demotion` — both regenerated it, guaranteeing a merge
conflict on a file whose contents are fully derived from the tree.
**Matters**   The conflict is trivial to resolve (regenerate after merging) but it
is unavoidable, recurs on every parallel session, and trains agents to resolve
`CONTEXT.md` conflicts by hand — which risks committing a stale index that then
reads as authoritative. `AGENTS.md` already says regenerate rather than edit; the
committed artifact is what makes that advice collide with itself.
**Matters more**   The same argument the lab already accepted for `70_lab_state.py`
applies: derived state should be derived, not stored.
**From**      This pass, merging `claude/harness-demotion`. `make_context.py --check`
already exists and exits non-zero when stale.
**Resume**    Options, cheapest first: leave it and always regenerate post-merge
(status quo); add a merge driver (`.gitattributes` `merge=ours` plus a regenerate
hook); or stop committing it and have `--check` run in the checks a session
already runs. The third is the honest one and the most disruptive — it changes
what a fresh clone gets without running anything.
**Status**    parked 2026-08-13 — needs an operator call on whether a fresh clone
must contain the index without running a command.

### T-007  A PROVED formal record is stale, and had been for six days unnoticed
**Noticed**   `tests/test_dossier_hardy_z.py` fails on main: the Hardy Z dossier
records a `FormalStatus.PROVED` obligation citing a dated kernel observation, and
`lean/ZetaLean/HardyZ.lean` was edited *after* that date (commit `d245381`, six
days ago, a dossier change). The guard's own words: "re-observe (re-run lake
build) and update the record".
**Matters**   This is the dossier's staleness guard doing exactly its job — a
citation to a kernel run that no longer covers the file it certifies. It is also
the clearest justification for the CI work: the very first full numerical run
surfaced a six-day-old defect in the formal record that no human had noticed,
because nothing ran the suite unless someone remembered to.
**From**      CI run on `3d138a78`, `tests` tier: 2416 passed, 1 failed, 19m44s.
Confirmed pre-existing — `HardyZ.lean` last changed in `d245381`; this session
never touched it.
**Resume**    Re-run `cd lean && lake build`, confirm zero sorrys, and update the
observation date in the Hardy Z dossier record to the real date of that run.
**Do not simply bump the date** — that records an observation that did not
happen, which is the failure this guard exists to catch. Needs a Lean toolchain;
this container has none.
**Status**    parked 2026-08-13 — blocked on a toolchain, not on a decision. The
`tests` tier stays red until it is re-observed.

### T-008  The "fast" CI tier takes 20 minutes, which is too slow to gate a PR
**Noticed**   `tests.yml` runs `pytest -m "not slow"` and took **19m44s** on a
GitHub runner (2416 tests). `CLAUDE.md` measures the same tier at ~115s locally
with `-n auto`.
**Matters**   A 20-minute gate is one people learn to ignore, which is the
failure mode CI tiering was supposed to avoid. The tier-1 gate is 7 seconds and
does its job; tier 2 is currently mis-sized for the cadence it runs at.
**From**      Same CI run, `3d138a78`. The gap is probably core count — a hosted
runner has far fewer than this container — but that is a hypothesis, not a
measurement.
**Resume**    Measure first: check the runner's core count and `--durations=10`
output already emitted by the job. Then choose — move tier 2 to merge-queue or
nightly, split it, or accept 20 minutes on pull requests only. Do not tune it by
guessing which tests are slow; the durations are already in the log.
**Status**    parked 2026-08-13 — wait for the HardyZ fix first, since a red tier
cannot be timed honestly.
