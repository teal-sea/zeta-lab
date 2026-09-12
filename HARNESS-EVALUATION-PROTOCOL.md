# HARNESS-EVALUATION-PROTOCOL.md

**Status when this file was committed: pre-registration only. No result in it.**
Everything below was written before any arm was run, any task was authored, or
any number was seen. The commit that adds this file adds no experiment and
changes nothing under `harness/`; that ordering is checkable in `git log` and is
the only reason the criteria below are worth anything. `docs/21` §1 and
`REDTEAM.md` W2 are what happens when it is not done.

This protocol follows the house pattern set by `docs/21` and `docs/23`: criteria,
thresholds and predictions frozen first, failures recorded as failures.

---

## 1. The claim under test

> **Does the generalized adversarial validation harness improve agentic research
> reliability enough to justify its complexity and cost?**

The harness is the **claim**, not the instrument. This experiment is designed to
be able to conclude that it should be simplified or deleted, and §12 lists the
observations that would say so.

Two prior findings shape the design and are not assumed to be correct:

- The four control **roles** have empirical support, `docs/17` (five claims
  refuted in one day), `NULLCONTROLS.md` (a matched null reclassified a
  research finding as generic), `docs/22` (detector strength measured against
  the Davenport–Heilbronn rival).
- The **generalized abstraction** over them does not, yet.
  `ARCHITECTURE-ARCHAEOLOGY.md` and `INSTITUTION-FUTURES.md` §7 measured that
  (both since moved to the private operating repository; they remain in this
  history at `d75d659`, unedited)
  `run_battery` / `validate_battery` / `audit_department` / `ClaimReport` have
  no call site outside `harness/` and `tests/`, that live hunts import
  `zeta.epstein.battery` directly, and that `hunts/wide_search/probe.py`
  re-implements the four roles by hand, including its own `null_band()`,
  rather than importing the harness.

**Those reports are input, not evidence.** This protocol re-derives what it
needs. Where a report's claim is load-bearing here it appears as a hypothesis
with an arm attached, never as a premise.

## 2. Hypotheses

| ID | Hypothesis | The arm contrast that tests it |
|---|---|---|
| **H1** | Adversarial controls in *any* form beat an ordinary strong-agent workflow. | `H-rival` vs `S1` |
| **H2** | **(primary)** Structure-matched rivals add reliability *beyond what a second independent agent adds at the same budget.* | `H-rival` vs `R2` |
| **H3** | The **generalized abstraction** adds value over the same four roles hand-rolled per subject. | `H-full` vs `H-hand` |
| **H4** | Decoys and surrogates add value beyond rivals alone. | `H-full` vs `H-rival` |
| **H5** | Lesions / measured detector power add value beyond rivals alone. | `H-lesion` vs `H-rival` |
| **H6** | The integrity audit (the referee) adds value beyond a full battery. | `H-audit` vs `H-full` |
| **H7** | An exact/formal oracle dominates every model-mediated control where one exists. | `H-formal` vs all |
| **H0** | **The null this experiment exists to be able to accept:** none of the above beats extra budget spent on more independent agents. | `S1`, `R2` vs everything |

**H2 is the primary hypothesis.** Everything else is secondary and is labelled
exploratory in the analysis.

## 3. Arms

Nine arms. The ladder A–G suggested in the commissioning brief was **rejected as
confounded**: each of its rungs adds a mechanism *and* resources at once, so a
rising curve would be unattributable. This design holds budget constant across
arms and separates mechanisms.

| Arm | What runs | Budget |
|---|---|---|
| `S0` | one agent, ordinary workflow, no controls | **B** |
| `S1` | one agent, ordinary workflow, **twice the budget** (more turns / higher effort) | 2B |
| `R2` | **two independent agents**, no shared context, each rebuilds the verdict from the claim + spec alone; disagreement surfaced, not resolved by either | 2B |
| `R3` | three independent agents, majority-report | 3B |
| `H-rival` | one agent + structure-matched rivals | ≈2B |
| `H-lesion` | one agent + planted lesions with detector power measured | ≈2B |
| `H-full` | one agent + full battery via `harness/protocol.py` (rivals, decoys, surrogates, lesions) | measured |
| `H-hand` | one agent + the **same four roles hand-rolled** for the subject, no `protocol.py`, no `Department`, no registry | measured |
| `H-audit` | `H-full` + `integrity.audit_department` + `ClaimReport` | measured |
| `H-formal` | one agent + an exact oracle (exhaustive enumeration / exact rational arithmetic / Lean where the task admits it) | measured |

`R2` and `R3` are **the matched-budget controls the whole experiment turns on.**
An expensive workflow beating a cheap naive baseline would demonstrate nothing;
the question is whether it beats the same money spent on another good agent.

`H-hand` is what makes H3 answerable. Without it the experiment measures the
roles and reports the result as if it were about the abstraction, the exact
conflation §1 flags.

## 4. Budget: four resources, measured separately

**The phrase "equal budget" is not used in this protocol without naming the
resource.** Four are tracked independently, because they are not
interchangeable and the tree's own economics say so (`HANDOFF.md`: verification
costs wall-clock, judgment costs tokens):

| Resource | Unit | Source |
|---|---|---|
| **model compute** | input / output / cache-read / cache-write tokens | provider usage response |
| **money** | USD, provider-reported | provider usage response |
| **operator time** | minutes of human attention (setup, adjudication, disagreement handling) | stopwatch, recorded per task |
| **wall-clock** | seconds | `telemetry` run records |

**Equalization rule, frozen:** arms are matched on **output tokens** as the
primary resource, within ±15%. Where an arm cannot be brought inside that band
without changing what it is (a full battery may simply cost more), it is **not
adjusted**; instead every endpoint is reported twice, raw, and normalized as
*endpoint per 1000 output tokens*. An arm that wins raw and loses normalized is
reported as winning raw and losing normalized. No composite "budget score" is
computed; there is no exchange rate between operator minutes and tokens, and
inventing one would hide the trade this experiment exists to expose.

### 4.1 Unresolved dependency, and it blocks execution

**This environment does not expose token counts or cost to a session.** Measured
2026-08-13 (`RUN-TELEMETRY.md` §7): no `ANTHROPIC_MODEL`, no usage variables,
nothing from the harness. The run registry landed in this pass captures
wall-clock, artifacts, commits and prompts, **not tokens, not dollars.**

Consequence, frozen here rather than discovered later: **the experiment must be
executed through an API runner that returns `usage` per request, not through
interactive agent sessions.** Until such a runner exists and emits into the run
registry, two of the four budget resources are unmeasurable and the primary
comparison is uninterpretable. Running the experiment before then is a protocol
violation, not a shortcut.

## 5. Tasks and ground truth

**n = 40 claims**, authored in two batches of 20 (§5.4).

### 5.1 Truth must be establishable without any arm

Every claim's ground truth is fixed at authoring time by a method **no arm has
access to**:

- exhaustive enumeration over a bounded domain (the technique
  `compiler/semantics.py` uses, applied to **new** fixtures);
- exact rational / integer arithmetic, verified in a CAS the arms do not run;
- a kernel-checked Lean proof of the claim or its negation, built by the task
  author before the arms see anything.

A claim whose truth cannot be established this way is **excluded at authoring**,
not adjudicated later.

### 5.2 Composition

| | Count | Purpose |
|---|---|---|
| Sound claims | 18 | false-rejection rate |
| Defective claims | 18 | detection rate |
| **Competence-floor controls** | 4 | 2 blatantly true, 2 blatantly false |

The competence floor is mandatory and comes from a recorded failure: the
resumption benchmark (`ROADMAP.md` 2026-08-09) had one model family fall below
its floor, and **its cells were voided**. Same rule here, see §9.

### 5.3 Defect classes

Nine classes, each instantiated twice, drawn from **this repository's own
incident record** so they are realistic rather than toy. They are
**re-instantiated on new surface, never restored verbatim**, same failure
class, new mathematics, new code, new prose:

| # | Class | Original incident |
|---|---|---|
| 1 | shared-layer false agreement between "independent" checks | `docs/25` §2.1, both rigor backends wrong from one parsing layer |
| 2 | a guard whose reference is the same technique at lower resolution | `docs/25` §2.4 |
| 3 | verdict-shaped default: "cannot decide" encoded as the favourable answer | `docs/25` §2.5 |
| 4 | precision-insensitive artifact, does not move when the approximation improves | the PSLQ relation stable at 300 digits |
| 5 | the test set *is* the rival set | Hunt #2 |
| 6 | a declared instrument whose precondition is never invoked | `online_list_is_complete` |
| 7 | scan-window artifact (extremum pinned at a window edge) | `docs/17` §2 |
| 8 | boundary/off-by-one inside a bound, at float grade on a thin margin | frontier defect #12, the k=3 boundary |
| 9 | a superseded constant restated as current | the Λ attribution defect `tests/test_claim_attribution.py` records |

**Difficulty is stratified and declared**: of each pair, one instance is
detectable from the artifact alone and one requires reconstructing the
computation. Balance is checked before freeze and reported.

### 5.4 Contamination policy

- **Nothing already in this tree is reused as a task.** Not the department
  reference claims (`functional_equation`, `multiplicativity`, and the
  finite-field/compiler/croniter/stateval pairs), not `SHAM_MODES`, not the
  existing lesions, not the calibration pairs, not `harness/blind_authoring_2026_08_09/`,
  that corpus is **spent** and `docs/23` §8.0 says so.
- **The task author is not the harness author and not the scorer.** Three
  separate parties, minimum.
- **The tasks live in a private repository until the experiment closes.** This
  repository is public and may be in training data; `docs/23` §8.0 records the
  method failure that comes from running against a live tree.
- **Batch 2 (20 claims) is authored after batch 1 runs but before batch 1 is
  scored**, by a different author, and is held out. If batch 1's effects do not
  replicate in batch 2, the primary conclusion is "not replicated", not an
  average of the two.
- **No task may be designed around a control the harness happens to own.** The
  check: each defect class must be, in principle, detectable by at least
  `R2` *and* by at least one harness arm. A class only the battery could catch
  is a class that measures the battery's catalogue, not its value.

## 6. Endpoints

### 6.1 "Useful outcome", defined before any data exists

A per-claim score, scored blind against a key written at authoring time:

| Score | Defective claim | Sound claim |
|---|---|---|
| **2** | correctly rejected **and the named mechanism matches the planted class** | correctly accepted with the load-bearing step identified |
| **1** | flagged as suspicious without the correct mechanism | accepted with hedging that does not identify why |
| **0** | accepted as sound | rejected |

**A useful outcome is a score of 2.** Scores of 1 are reported separately and
never pooled into the primary, "it smelled wrong" is not a verdict this
laboratory credits, and crediting it would flatter every arm that produces
volume.

### 6.2 Primary endpoint

**Youden's J = detection rate + sound-claim survival rate − 1**, computed on
score-2 outcomes only, per arm, over batch 1, replicated in batch 2.

J is primary rather than detection rate alone because **any workflow can drive
detection to 1.0 by rejecting everything**, and a referee that only ever says no
is the exact failure `harness/README.md`'s two-direction calibration rule exists
to catch. The (detection, false-rejection) pair is always reported beside J.

### 6.3 Secondary endpoints

- bad-claim escape rate; false-rejection rate (both reported raw)
- **calibration**: Brier score over each arm's stated confidence
- time-to-correct-verdict (wall-clock, from the run registry)
- output tokens; USD; operator minutes
- **efficiency**: J per 1000 output tokens; J per operator minute
- disagreement rate within `R2`/`R3`, and whether disagreement alone predicts a
  defect, this is the cheapest possible detector and it is measured, because if
  it works the whole apparatus is contestable

### 6.4 Multiple comparisons

Eight contrasts across nine arms. Frozen: **H2 is the only confirmatory
comparison.** Everything else is exploratory and labelled as such in every
table. No p-value gates any conclusion. Following the E2 precedent
(`docs/reviews/e1-e3-experiment-protocol.md` §7): *"18 runs is not a clinical
trial and pretending otherwise would be its own kind of sham"*, this protocol
declares itself **exploratory with pre-registered decision rules**, and can
honestly conclude only "large and consistent" / "absent" / "underpowered".

## 7. Randomization and blinding

- Claim order randomized per arm; seed committed at freeze, in this file's
  successor commit, before any run.
- Arm assignment: **every claim goes through every arm** (within-claim design),
  which removes claim-difficulty as a between-arm confound and is affordable at
  n=40.
- Agents do **not** know: whether a claim is sound, which defect class is
  planted, what any other arm concluded, which arm they are in, or the expected
  outcome.
- Scorers see **only the arm's final verdict text**, stripped of arm identity by
  a mechanical filter, in randomized order.
- **The scoring key is frozen before any arm runs.** Amendments are applied
  uniformly to all arms and logged; persistent scorer disagreement (>1 point on
  a claim) excludes that claim from the primary and is reported.
- Two scorers: one human, one agent that authored nothing. Disagreements go to
  the operator, **the system may not resolve a disagreement it is party to**
  (`meta/operator-functions.md`).

## 8. Procedure, prompts, and stopping rules

- One frozen prompt template per arm, committed at freeze. Arms differ **only**
  in the controls made available and the budget; the task statement is
  byte-identical across arms.
- The operator does not interact with any run after launch. Runs are launched
  from a checklist.
- Every run emits a `telemetry` record with `task_ref = harness-eval/<batch>/<claim>/<arm>`,
  so budget and wall-clock are read from the registry rather than reconstructed.
- **Stopping rules:** the experiment stops when batch 1 and batch 2 are complete,
  or on a kill condition in §9. No interim look at the primary endpoint. No
  arm is added, removed or retuned after the first run.

## 9. Failure handling and exclusions

| Condition | Consequence |
|---|---|
| An arm falls below the competence floor (misses a blatant control) | **that arm's cells are void** and support no conclusion in either direction, the resumption benchmark's rule |
| A claim's ground truth is found wrong after runs begin | claim excluded from all arms, logged, not silently re-keyed |
| A defect class turns out to be detectable by inspection alone (all arms score 2) | class reported at ceiling and excluded from the primary; a ceiling lesion is a design defect, recorded, batch 1's known risk |
| A run crashes or is interrupted | re-run once from the same frozen prompt; if it fails again the cell is void, never imputed. `telemetry` records both attempts |
| Contamination discovered (a task recognizable from this public tree) | that claim is excluded and the discovery is reported, not patched over |
| **`harness/` is modified during the experiment** | **the experiment is void.** A changed harness requires a new pre-registration and a new task set; re-running the same benchmark against a repaired harness and reporting it as confirmatory is the specific fraud this section exists to prevent |

## 10. Analysis, frozen

1. Per-arm J, detection, false-rejection, with exact counts. No smoothing.
2. The eight contrasts, each as a difference in J with a bootstrap interval,
   labelled confirmatory (H2) or exploratory (all others).
3. Efficiency table: J per 1000 output tokens, J per operator minute, per arm.
4. Batch 2 replication reported **separately**, never pooled with batch 1.
5. Every void cell listed with its reason.
6. The six possible conclusions in §11 stated explicitly, with which one the
   data supports and why the other five were not chosen.

## 11. The six conclusions this experiment can reach

Frozen so that none can be added afterwards to fit a result:

1. **The full harness materially helps**: `H-full`/`H-audit` beat `R2` on J at
   matched output tokens, replicated in batch 2.
2. **Only some components help**: one or more of `H-rival`/`H-lesion` beats
   `R2`, while `H-full` − `H-rival` ≈ 0 and `H-audit` − `H-full` ≈ 0.
3. **Independent replication captures most of the benefit**: `R2` ≈ `H-full`
   at matched tokens, and `R3` ≥ `H-full`.
4. **The generalized abstraction adds negligible value**: `H-hand` ≈ `H-full`
   on J *and* `H-full` costs more in operator minutes.
5. **The harness costs more than it contributes**: harness arms match on J but
   lose on J per 1000 output tokens and J per operator minute.
6. **The harness makes performance worse**: any harness arm's escape rate
   exceeds `S1`'s, or its false-rejection rate exceeds the ceiling while J does
   not improve.

## 12. Criteria that count AGAINST the harness

Stated as sharply as the supporting criteria, because the tree's own record
(`docs/21`, `docs/23`) is that the honest failures are the useful part.

| Observation | What it licenses |
|---|---|
| `R2` J ≥ `H-full` J at matched output tokens | **the primary result is negative.** Spend the budget on a second agent |
| `H-hand` J ≈ `H-full` J (within the bootstrap interval) *and* `H-full` costs more operator minutes | **delete the abstraction, keep the roles.** `protocol.py`, `Department`, `KNOWN_DEPARTMENTS` and the conformance suite lose their justification; the four roles move into subject code where the live hunts already put them |
| `H-audit` − `H-full` ≈ 0 | **the integrity layer is not earning its complexity.** Collapse five grades to "audited / not audited"; `promotion.py` and `preregistration.py` lose their remaining rationale |
| `H-full` − `H-rival` ≈ 0 | decoys and surrogates are ceremony *for this task class*; the admission rule's "decoy or surrogate" requirement should be re-derived, not assumed |
| Disagreement rate inside `R2` predicts defects as well as any battery | **the cheapest possible detector matches the apparatus.** Report it prominently; it is the most damaging single result available |
| Any harness arm's escape rate > `S1`'s | the harness is actively harmful on this task class and must be scoped or removed |
| Harness arms lose on J per operator minute | the cost lands on the scarcest resource the laboratory has |

**If two or more of these fire, the recorded conclusion is "simplify", and the
simplification is specified before the data exists**: keep rivals, nulls and
lesions as subject-level functions; keep `shams.py` (its value is that it
falsified the audit); delete or demote the department registry, the five-grade
integrity vocabulary, and the promotion gate.

## 13. What would make the harness *worth expanding*

Symmetry, so this is not a document that can only convict:

- `H-full` beats `R3` (three independent agents) on J at matched tokens →
  controls beat redundancy, and that is a strong result.
- `H-rival` beats `R2` specifically on defect classes 1 and 5 (shared-layer
  agreement; test-set-is-rival-set) → rivals catch what independence
  structurally cannot, which is the harness's own theory of itself and would be
  the first direct evidence for it.
- `H-audit` catches a defect no other arm catches, more than once.

## 14. Pre-registered predictions, recorded to be scored

Written before any data, to be scored right or wrong in the results section.
`docs/21` scored three of six wrong and recorded them; the same applies here.

| # | Prediction | Confidence |
|---|---|---|
| P1 | `H-rival` beats `S1` on J (H1 holds) | high |
| P2 | `H-rival` **does not** beat `R2` on J overall (H2 fails), but **does** on defect classes 1 and 5 | medium |
| P3 | `H-hand` ≈ `H-full`, the abstraction adds nothing on J, and costs more operator minutes | medium-high |
| P4 | `H-audit` − `H-full` ≈ 0 on this task class | medium |
| P5 | `R2` disagreement rate alone detects ≥60% of defects | medium |
| P6 | `H-formal` dominates every arm where an exact oracle exists, and is inapplicable to ≥half the claims | high |
| P7 | At least one defect class sits at ceiling in batch 1 and has to be excluded | medium |

## 15. Unresolved dependencies: the experiment cannot start until these close

1. **Token and cost accounting** (§4.1). Blocking. Needs an API-based runner
   emitting `usage` into the run registry.
2. **An independent task author**, not the harness author and not the scorer.
   Blocking for the contamination policy.
3. **A private repository** for the task set. Blocking.
4. **An independent scorer** who authored nothing.
5. **Operator sign-off on §6.2's primary endpoint and §4's equalization rule**,
   in writing, before batch 1 is authored.

## 16. What this protocol deliberately does not do

- It does not modify, improve, extend, migrate onto, or delete `harness/`.
  Nothing under `harness/` changed in the commit that adds this file.
- It does not migrate live research onto the harness.
- It does not test whether the harness is *correct*; it tests whether it is
  *worth its cost* on a claim-adjudication task.
- It does not generalize beyond that task class. A negative result is a result
  about adjudicating claims of this shape, not a proof that adversarial controls
  are worthless, `docs/17`'s five kills are not undone by anything measurable
  here.
- **It has not been run.** No arm exists, no task is authored, no number in this
  file is an observation.

---

**Freeze.** This file is the pre-registration point. Its commit contains this
document and nothing else. Any change to §§2–12 after the first run voids the
experiment and requires a new protocol at a new commit.
