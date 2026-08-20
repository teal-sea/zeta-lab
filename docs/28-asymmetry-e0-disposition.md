# 28. E0: the independent checker reproduced the audit's blind spots exactly

*Disposition of the cheapest informative slice of `meta/asymmetry-experiment.md`.
Run 2026-08-20, four checkers. Grade: **measured**, one run each. Nothing here is
a mathematical result; it is evidence about the laboratory.*

> **Corrected 2026-08-20, after first publication.** The first version of this
> document reported that foreign models caught an audit blind spot the audit
> could not see. That was wrong, and the error was mine: ground truth was read
> off `SHAM_MODES[...].caught_by` instead of measured by running the audit. See
> *The error* below. The corrected result is less flattering to every model
> checker and to this experiment.

## The question, and why it was worth asking

`harness/integrity.py` catalogs fifteen ways a test battery can be hollow. Six
carry `caught_by=None`: the audit declares it cannot detect them mechanically.
Read the `countermeasure` field on those six and the same remedy appears in every
one, in different words. *Independent authorship.* "A party that has not seen the
payloads." "A claim author who never saw the detectors."

This repository therefore concluded six separate times that independence is the
countermeasure to what its own audit cannot see, and never measured whether that
is true. `meta/asymmetry-experiment.md`, pre-registered 2026-08-10 (`5a666c0`),
named the cheapest test: show the batteries to an independent party and compare
its detection against the audit's.

## Method

Ten artifacts: one clean control and nine live `zeta_department` batteries, each
carrying one corruption planted by the matching mutator in `harness/shams.py`.
Ground truth read from `harness.integrity.SHAM_MODES`, not restated. Three of the
nine are modes the audit declares itself blind to.

| artifact | digest (first 16) | planted | audit catches |
|---|---|---|---|
| `clean` | 816672b4c412313e | no | n/a |
| `constant-true-detector` | c0308df5af6231af | yes | yes |
| `target-as-rival` | 43259f84f4116d00 | yes | yes |
| `inert-lesion` | 0c9d7fbd17bd44a3 | yes | yes |
| `dropped-hardest-lesion` | 38e6945873d76f22 | yes | **no** |
| `key-asymmetry-label-leak` | 825aca1b553ee727 | yes | yes |
| `co-designed-calibration` | aa63ddcfc8eebf7b | yes | **no** |
| `distant-rivals` | ff53b0f4a03f1da8 | yes | **no** |
| `detector-is-the-claim` | 7e6d7bb6a86dd5a3 | yes | yes |
| `agreeable-absent-field-oracle` | 32f1361d98b3011a | yes | yes |

Four checkers, all reached through Perplexity's Agent API at first-party rates
and driven by Inspect (`meta/evals/asymmetry.py`): `claude-opus-5`,
`openai/gpt-5.6-sol`, `google/gemini-3.1-pro-preview`, `xai/grok-4.6`. Every one
saw the battery text and nothing else, no audit and no author reasoning. Claude
is the same family that authored the batteries; the other three are foreign, so
the design's *independent* level is populated at model level and not only at
prompt level.

## Run 1 failed its positive control, and is kept

`meta/evals/logs/2026-08-20T17-02-38-*.eval`.

The checker called `constant-true-detector` **sound**. That battery contains a
detector named `constant-true` whose entire body is `return value`. Its written
reasoning never opened a detector at all; it argued from the rivals and the
reference claims, and weighed the battery's good components against the broken
one.

That is a defect in the instruction, not a fact about independence, and the run
is recorded as a failed calibration rather than a measurement. The prompt was
revised to name the components to examine and to state the weakest-link rule.
A `positive_control_detection` gate was added so a run like this cannot be
reported as a result again: below 1.0, the other numbers may not be quoted.

The revision is calibration and not outcome-tuning, and the distinction is worth
arguing rather than asserting. The positive control is blatant by construction
and independent of the hypothesis, so making the checker competent on it pushes
the result neither toward nor away from P1. A prompt revised after reading a
*blind-spot* number would be a different and illegitimate act. Run 1's log is
unchanged and shipped alongside run 2.

## The error, since it changes every number below

`harness.integrity.SHAM_MODES` marks six modes `caught_by=None`. I took that as
ground truth for whether the audit catches a given artifact. It is not, and the
gap is structural rather than a typo.

`caught_by` describes a sham mode in its **subtle** form: reference claims and
instruments co-authored so that every mechanical check passes. The mutators in
`harness/shams.py` plant a much **cruder** instance. `with_vacuous_calibration`,
for example, installs `lambda payload: True` as a claim declared to
distinguish. The audit's `calibration-rederived` check re-runs every claim
against the battery and compares the measured verdict to the declared one, so it
catches that immediately and grades the department HOLLOW.

Measured by running `audit_department` on each corrupted department:

| artifact | catalog said | audit actually grades | caught |
|---|---|---|---|
| `constant-true-detector` | catches | DETECTOR_INADEQUATE | yes |
| `target-as-rival` | catches | HOLLOW | yes |
| `inert-lesion` | catches | HOLLOW | yes |
| `key-asymmetry-label-leak` | catches | HOLLOW | yes |
| `detector-is-the-claim` | catches | DETECTOR_INADEQUATE | yes |
| `agreeable-absent-field-oracle` | catches | HOLLOW | yes |
| `co-designed-calibration` | **blind** | HOLLOW | **yes** |
| `distant-rivals` | **blind** | HOLLOW | **yes** |
| `dropped-hardest-lesion` | **blind** | CALIBRATED | **no** |

Two of three claimed blind spots are not blind spots. `meta/evals/asymmetry.py`
now pins measured verdicts and `tests/test_meta_evals.py` re-derives them under
`@pytest.mark.slow`, with a fast test that fails if anyone reads the catalog
again.

## Result

All four checkers passed the `positive_control_detection` gate. Ground truth as
measured above.

| checker | detection | false confidence | specificity (n=1) | true blind spot |
|---|---|---|---|---|
| **co-designed audit** | **0.889** | **0.111** | n/a | 0 of 1 |
| `claude-opus-5` | 0.667 | 0.333 | pass | 0 of 1 |
| `gemini-3.1-pro` | 0.556 | 0.444 | pass | 0 of 1 |
| `grok-4.6` | 0.333 | 0.556 | pass | 0 of 1 |
| `gpt-5.6-sol` | 1.000 | 0.000 | **FAIL** | 1 of 1, uninformative |

**GPT is disqualified, and the measure that disqualified it is the point.** It
answered *hollow* to all ten artifacts including the clean control: perfect on
detection and false confidence, distinguishing nothing. `specificity` caught it,
which is this repository's own admission rule applied to a checker instead of a
claim.

## Reading

**The co-designed audit beat every model checker, and not narrowly.** 0.889
against 0.667, 0.556 and 0.333. The hypothesis under test was that independent
checkers would do better. The mechanical checker written by the same process
that wrote the batteries did better than all three foreign models.

**No credible checker caught the one genuine blind spot.** `dropped-hardest-
lesion` was missed by Claude, Gemini and Grok. Only GPT flagged it, while
flagging everything.

**P1 is not supported and points the other way.** It predicted lower false
confidence from independence. Measured: 0.333, 0.444 and 0.556 for the model
checkers against 0.111 for the co-designed audit.

**P2 is refuted.** Conditional detection lift across every eligible pair of
model checkers is zero or negative; no checker beats its own base rate on what
another missed. Misses are correlated. Hard artifacts are hard for everyone.

**But E0 could not have discriminated P1 anyway, and that is the real finding.**
The question is whether independence helps against the modes the audit cannot
see. Of the six such modes in the catalog, only three have mutators at all, and
two of those three plant instances the audit catches. The dataset therefore
contained exactly **one** artifact that actually tests the question, and one
artifact cannot discriminate anything.

The binding constraint is not checker independence. It is that
**`harness/shams.py` cannot plant the modes `harness/integrity.py` says it is
blind to.** The sham catalog and the sham planter have drifted apart, nobody
noticed because nothing ever compared them, and this run is what compared them.

## What was done about it

The one true blind spot is now closed. `dropped-hardest-lesion` was carried as
mechanically uncatchable while its own `countermeasure` field said **"pin the
lesion set in tests."** That instruction had never been followed.
`tests/test_lesion_sets_are_pinned.py` follows it: every department's lesion set
pinned by name and magnitude, the minimum-magnitude lesion asserted separately
because it is the one the sham removes, a negative control that plants the sham
and asserts the pin goes red, and a coverage test so a later department cannot
escape the pin.

The mode stays in `AUDIT_BLIND_SPOTS`, which is accurate: the audit still cannot
see it, and it is now caught from outside the audit. Whether a lesion set was
*adequate* is a judgment and cannot be mechanised. Regression away from one is a
test, and always was.

## What this does not show

- **The subtle modes were never tested.** Nothing here says anything about
  genuine co-designed calibration or genuinely distant rivals, because no
  artifact instantiated them. The catalog's six blind spots remain untested.
- **n = 1 on the quantity of interest**, and n = 1 on every specificity figure.
- **Difficulty is confounded with blind-spot status**, and with only one blind
  spot the confound cannot even be examined.
- **Nothing here is about the mathematics.** It is evidence about the
  laboratory, and by this repository's own rule a session that produced no
  mathematics and a tidy ledger produced nothing.

## Cost

Five runs, 50 model calls, about $3.35, plus one audit sweep of nine corrupted
departments. Grok emitted 105,332 reasoning tokens by itself.

## Next

Write mutators that plant the *subtle* forms, or accept that the catalog's six
blind spots are untestable with the tooling that exists and say so in
`SHAM_MODES` rather than implying a planter exists. That is the prerequisite for
any further work on this question, and it is worth more than another checker.

A cheap and separate win: add a provenance check asking whether a reference
claim and the detector that tests it were authored by the same party in the same
commit. `harness/preregistration.py` already records the digests it would need,
and unlike an LLM checker it cannot be talked out of its answer.
