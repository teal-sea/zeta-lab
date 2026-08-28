# Does the validation harness work? — evidence report

**Repository:** teal-sea/zeta-lab · **Date:** 2026-08-13
**Subsystem under test:** `harness/` — a subject-independent validation framework
**Question, as posed:** does using the harness improve the correctness of research-claim evaluation, versus the same agent workflow without it, at comparable budget?

## Answer

**No — not demonstrated.** Four pre-registered experiments, two subjects, 74 agent runs. The harness arm never once out-performed the control. The control was never wrong: 37 for 37.

Separately, and more cheaply decisive: **nothing in the repository uses the harness.**

## 1. Results

| | subject | design | control | harness | b − c | verdict |
|---|---|---|---|---|---|---|
| v1 | croniter | 12 items × 2 arms | 12/12 | 12/12 | 0 | FAIL (ceiling) |
| v2 | croniter | 14 items × 2 arms | 13/13 | 13/13 | 0 | FAIL (ceiling) |
| v3 | croniter | 12 items, control-only pilot | 6/6 | not run | — | ABORTED |
| v4 | LLVM IR rewrites | 6 items × 2 arms | 6/6 | 6/6 | 0 | FAIL |

Criterion, frozen before each run: **b** = items the harness arm got right and the control got wrong; **c** = the reverse. Pass required b − c ≥ 3 (v1–v3) or ≥ 2 (v4, a 6-item screen). A ceiling — both arms perfect — was pre-committed as a FAIL in every protocol and never reinterpreted afterwards.

Each protocol was committed and pushed BEFORE any arm ran; items and answer keys were held outside the repository during execution and their SHA-256 digests frozen in the protocol, then re-verified afterwards. Scoring was mechanical string comparison against the key — no scorer judgment.

## 2. Why the first three failed, and why v4 is the one that counts

v1 and v2 failed on **no headroom**: the subject was deterministic and fully enumerable, and neither arm was deprived of a shell, so any factual claim was settled by running it.

v3 failed on **no positive class**: the ground-truth key was built from 21 hand-written code mutations, and the control found valid counterexamples in four code paths that had not been considered. All six "sufficient evidence" items were refuted and voided. That is a defect in the experiment, not a finding about the harness, and it is recorded as such.

**v4 removed both defects, by measurement taken before the run.** The subject is LLVM IR rewrite validity, with correctness verified by complete enumeration of the entire 65,536-point input domain:

- 3 rewrites genuinely valid → a real positive class existed (v3's failure fixed)
- 3 rewrites achieving byte-identical output on all 65,536 inputs at two optimisation levels while being invalid — the defect is in LLVM poison semantics, which concrete execution provably cannot observe (v1/v2's failure fixed: running the artifact could not settle it)

The control settled it anyway, 6/6. It read the `nsw`/`nuw`/`exact` flags directly off the IR and stated why the evidence it had been handed was worthless: "65536/65536 agreement at -O0 and -O2 is exactly what an nsw violation looks like when observed by execution." Both arms produced identical counterexamples on all three traps.

## 3. The cheaper evidence, which the experiments were not needed to obtain

    call sites of run_battery / validate_battery / audit_department / ClaimReport
    outside harness/ and tests/ :   0

Zero — not few. Meanwhile ten files under `hunts/` (the repository's live research) implement the same concepts by hand. One carries comments reading `# control 1 — rival` and `# control 2/3 — surrogate and lesion` — the harness's own four-role vocabulary — then imports `math`, `mpmath`, `numpy` and `zeta.epstein`, and writes 167 lines of it from scratch.

Someone who needed exactly this abstraction, and had it installed, chose to rebuild it. That is the strongest adoption signal a codebase emits, and it predates every experiment above.

## 4. Cost, replicated three times

For identical correctness:

| | tokens | wall-clock (median) | tool uses (median) |
|---|---|---|---|
| v1 | 1.15× | 3.22× | 3.40× |
| v2 | 1.11× | 2.72× | 2.43× |
| v4 | 1.67× | 3.93× | 5.00× |

This is the most robust quantity the whole exercise produced: **3–5× the effort for the same answers**, across three independent claim sets.

## 5. Threats to validity — stated, not buried

- **Structural bias against finding an effect.** "I can construct an answer key" and "the control cannot work it out" are close to contradictory requirements. Every domain testable this way is therefore one favourable to controls. This does not rescue the harness, but it bounds the claim: no correctness headroom was found in domains that admit ground truth.
- **Single model, single workflow**, n = 6–14 items per experiment. Only a large, consistent effect was detectable — appropriate, since only a large effect would justify the complexity, but small n is real.
- **v4 declared confound**, stated in the protocol before the run: the compiler department ships the adequate detector, so a PASS could not have separated "the harness supplied the instrument" from "the harness instilled the habit of checking instrument adequacy." Moot given the FAIL.
- **v4 disclosed defect**: one item's source and target were byte-identical (a no-op edit from a register-name mismatch), so effective n = 5. Recorded rather than swapped, because items were frozen. The ceiling holds on the other five.
- **Outcome variable is verdict correctness only.** See §6.

## 6. What the harness demonstrably did, that the score does not capture

Recorded because it is true, not to soften the verdict — none of it changed an answer.

Every harness-arm run in v4 surfaced its own department's integrity grade `DETECTOR_INADEQUATE` and carried it with the verdict, and reported that the concrete detector has `has_power=False`, `blind_to=('nsw_flag_on_a_wrapping_shift',)` — i.e. the machinery told the agent, by measurement, that the evidence in its prompt was a known blind spot. On one item that grade caused the agent to refuse to stop at the model's verdict and obtain independent confirmation from real LLVM: `opt -passes=instcombine` folds the `nuw` variant to `ret i1 false` while the source variant stays live; compiled and executed, the two disagree at the predicted input.

That is a second independent line of evidence the control never produced. It is a contribution to evidence quality and declared scope, which this gate does not score, in a domain where the answers were already easy.

## 7. In flight: the mathematics venue

A fifth experiment tests the harness on the laboratory's actual subject. The discrimination question there is the lab's own doctrine: the Davenport–Heilbronn function shares ζ's functional equation, real coefficients and real Hardy Z, AND violates the Riemann Hypothesis. Any structural property it also satisfies is worth nothing as evidence.

Ground truth, 5 of 6 computed:

| claimed property of ζ | verdict | rivals surviving |
|---|---|---|
| functional equation | VACUOUS | 3 of 3 |
| real Hardy Z-function | VACUOUS | 3 of 3 |
| zeros on the critical line | VACUOUS | 3 of 3 |
| multiplicative coefficients | DISTINGUISHES | 0 of 3 |
| completely multiplicative | DISTINGUISHES | 0 of 3 |

Three of the structural properties most often cited as insight into ζ are worth nothing as evidence — every RH-violating look-alike has them. Only the prime structure kills the rivals. That is useful for the laboratory regardless of what the A/B returns, and is independent of the harness question.

It will not change the verdict. Even a pass would be one six-item screen against four failures — grounds for a second look, not a yes.

## 8. Scope — what was NOT tested

The experiments touched `harness/` only. Untouched, and unaffected:

- `zeta/` — 25 modules, the mathematics
- `tests/` — 1,754 test functions, cross-checked against mpmath's independent implementations as an oracle
- `lean/` — 45 files, kernel-checked, zero sorrys
- 390 commits of project history

The zero-call-sites finding cuts both ways: the harness was never in the causal path of any mathematical result in this repository, so none of those results depend on it.

## 9. Recommendation

1. **Stop developing `harness/`.** Six departments exist and nothing imports them. The adoption evidence is unambiguous and was available before any experiment.
2. **Keep `compiler/semantics.py` and the measured detector blind spots.** That is real knowledge about the limits of exhaustive testing, true regardless of whether anything imports it.
3. **Keep the negative results on the record.** Four pre-registered failures with an unmoved criterion is a stronger artifact than an untested framework.
4. **If anyone wants to argue the harness earns its complexity**, they need a different outcome variable than verdict correctness — evidence quality and scope discipline are where it visibly acted — and a domain where the control is not already at ceiling. Neither has been found in four attempts, and a cheap adoption test (does live research reach for it?) should pass before another correctness test is funded.

---

**Artifacts.** Branch `claude/harness-gate`, not merged to main. Each protocol frozen in its own commit before execution, results in a later commit: c77a5a3/aa0de70 (v1), 8bf77e2/445363e (v2), 548f3da/3773ed5 (v3), 0518847/0843188 (v4). Every prompt, item set, answer key, scorer and raw run record is committed under gate/, gate2/, gate3/, gate4/.

---

# Correction, added when the verdict was made operational (2026-08-13)

§3 above says the four framework symbols have **zero call sites**, and that is
exactly true. It is also, on its own, misleading, and acting on it without this
section would delete working research tooling.

`harness/` is not one thing. It is two, and only one of them failed the gate.

**Live, and load-bearing.** `scripts/70_lab_state.py` — the lab's read-only
research-state view — imports eight symbols from this package:

```
harness.departments.graveyard_ledger   GRAVES
harness.departments.guard_ledger       GUARDS
harness.departments.review_ledger      CLAIMS, OUTCOMES
harness.departments.zeta_department    rigor_backend_independence
harness.graveyard                      unguarded
harness.guards                         offensive_worklist, undemonstrated
harness.independence                   agreement_bounds
harness.review                         standing_reasons
```

These are ledgers and small readers over them — dead ends recorded so they are
not re-entered, guards recorded so they can be attacked, reviews recorded with
their standing reasons. They are *research bookkeeping*, they have a live
consumer, and nothing in the gate tested them or bears on them.

**Demoted, with zero live consumers.** The generalized framework:
`protocol.py`, `integrity.py`, `promotion.py`, `preregistration.py`,
`provenance.py`, `shams.py`, and the six subject packs under
`departments/` that exist to populate it.

Measured:

| | lines |
|---|---|
| live research tooling (consumed by `70_lab_state.py`) | 1,052 |
| framework with zero live consumers | 4,534 |
| department subject packs for that framework | 3,468 |

So the accurate statement is: **the generalized battery/department/integrity
framework did not earn core status and is no longer being developed. The
ledgers and their readers are ordinary lab tooling and stay.** The one live
consumer is named above; if it ever stops importing them, that is the moment to
revisit, and not before.

The four-experiment record, the cost finding and the adoption finding all stand
as written. This section narrows what may be concluded from them, and it was
found by grepping the tree during the demotion pass rather than by reasoning
from the report.


---

# How to read this verdict (added 2026-08-13)

Not as a blunder. The framework was a reasonable thing to build, it was built
carefully, it was tested against the practice it was meant to improve, and it
lost. Those are four separate facts and only the last one is negative.

What the record is worth keeping for: a thing the lab invested in was measured
against a preregistered criterion that was never moved, and then stopped. The
willingness to end an investment on evidence is the part to imitate. Retiring
this is a success of the method and a failure of the artifact — do not collapse
the two, in either direction.

What it does **not** license: any conclusion about verification in general, or
about work not tested here. Four experiments in two subjects measured one
framework's effect on verdict correctness. That is all they measured.


---

# Correction: §3's zero call sites has gone stale (added 2026-08-27)

**Believed, and exactly true on the day it was written.** §3 reports zero call
sites for `run_battery`, `validate_battery`, `audit_department` and `ClaimReport`
outside `harness/` and `tests/`, and offers that zero as adoption evidence
cheaper and more decisive than the four experiments.

**Invalidated by** two commits that landed on 2026-08-20, a week after this file
was written, neither of which came back to it:

- `meta/evals/asymmetry.py` calls `audit_department` at line 313, imported at
  line 307. The module arrived at `fd898d8` and the call at `1b45799`, the
  commit that corrected `docs/28` by replacing a ground truth read out of
  `SHAM_MODES` with one measured by running the audit. The measurement it needed
  was this framework's.
- `hunts/r_e2ee73/probe.py` (`f85e6d4`) imports `run_battery` at line 28.

**What is now true**, re-derived by grep on 2026-08-27 against `main` at
`6d169dc` rather than quoted from the block above:

    call sites of run_battery / validate_battery / audit_department / ClaimReport
    outside harness/ and tests/ :   1

    audit_department   1 call   meta/evals/asymmetry.py:313
    run_battery        0 calls  imported at hunts/r_e2ee73/probe.py:28, never used there
    validate_battery   0
    ClaimReport        0

**The four names also undercount, and that is the larger part.** The same probe
that imports `run_battery` without using it does call three other demoted
`harness/protocol.py` functions the four-name grep was never pointed at:
`run_power` at lines 122 and 125, `run_ablation` at 129, `run_nulls` at 137. It
imports the demoted `compiler_department` subject pack at line 26 as well.
Counted by what the demoted framework actually exports rather than by those four
names, live research outside `harness/` and `tests/` now makes **five calls**
into it across two files, not zero.

Not counted, and worth naming so nobody counts it twice: `hunts/r_365c6c/probe.py`
defines its own local `run_battery()` at line 284 and imports nothing from
`harness`. That is an instance of the hand-rebuilding §3 describes, not a call
site.

**This correction runs against the verdict, which is why it is recorded rather
than folded into §3.** The zero was the strongest adoption evidence in this file
and it was offered as standing on its own. It is no longer zero, so §3 is weaker
than it reads, and the Answer's "nothing in the repository uses the harness" is
now wrong about the demoted half too. The 2026-08-13 correction below §9 had
already narrowed that sentence to exclude the live ledgers and their reader in
`scripts/70_lab_state.py`; what is new here is that the framework half, the half
that failed the gate, has acquired consumers as well.

**What it does not change.** The demotion stands. Five calls from two files,
neither in the causal path of any mathematical result and one of them serving a
different experiment's measurement, is not the live consumer §9 asked for, and
§9's instruction to stop developing `harness/` is untouched. The four-experiment
record and the cost finding are unaffected. What moved is the size of the number
and what may be said with it, not the decision it supported.

**Not caught by anything.** Unlike the subject count, which
`tests/test_harness_verdict_subject_count.py` now derives from the gate protocols
and pins, this figure has no guard: it went stale in seven days and stayed stale
for another seven with nothing to notice. A grep against a moving tree is a
measurement with a date on it, and §3 should be read as carrying one.
