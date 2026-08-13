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
The question is now answered (`harness/VERDICT.md`), but the documents are
historical records of what was believed at the time.
**Matters**   Leaving them uncorrected misleads; rewriting them destroys the
record of a belief that was later tested and refuted, which is exactly the kind
of thing this lab should keep. The resolution is a pointer, not a rewrite.
**From**      This pass. `INSTITUTION-FUTURES.md` §7 already called the harness an
unproven claim and named the measurement that settled it.
**Resume**    Add a dated one-line header to each pointing at
`harness/VERDICT.md`. Do not edit their bodies.
**Status**    parked 2026-08-13 — deferred as out of scope for a demotion pass
that was asked not to produce more architecture documents.

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
