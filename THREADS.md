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

### T-002  Telemetry records no outcome, so prompts cannot be scored
**Noticed**   `telemetry/schema.py` defines
`OUTCOMES = (landed, no-change, killed, blocked, refused, crashed)` and nothing
in the tree ever writes one. Every run record carries `status: completed`, which
means the process exited, not that it produced anything.
**Matters**   The prompt store now captures what an agent was asked. Without an
outcome beside it there is no `(prompt, result)` pair, so "which prompts work" is
unanswerable no matter how many runs accumulate. Half the join key exists.
**From**      `telemetry/schema.py` `OUTCOMES`; the gap was found while fixing the
SessionStart hook to capture prompts at all (commit `35afd18`).
**Resume**    `landed` vs `no-change` is mechanically derivable — commits already
carry a `Run-Id:` trailer, so a run with commits landed and one without did not.
The judgment outcomes (`killed`, `blocked`, `refused`) must be operator-declared;
per `meta/README.md` a system that grades its own output flatters itself.
**Status**    parked 2026-08-13 — deliberately not built until enough runs exist
to score. Three run records is not a dataset.

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
**From**      This pass; `zeta.epstein.battery`. P6 (`count_zeros_box` off the
critical line) was still in contour integration when the pass ended.
**Resume**    Recompute the six properties through `zeta.epstein.battery`, then
decide whether the A/B is worth 12 runs. It cannot overturn four failures — one
six-item screen is grounds for a second look, not a verdict.
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
