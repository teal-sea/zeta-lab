# 28. E0: the independent checker reproduced the audit's blind spots exactly

*Disposition of the cheapest informative slice of `meta/asymmetry-experiment.md`.
Run 2026-08-20. Grade: **measured** (one route, one model, one run). Nothing here
is a mathematical result; it is evidence about the laboratory.*

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

Checker: `claude-opus-5`, reached through Perplexity's Agent API at first-party
rates, driven by Inspect (`meta/evals/asymmetry.py`). Independence here is
prompt-level: the checker saw the battery text and nothing else, no audit, no
author reasoning. It is *not* model-level, and that limitation is load-bearing;
see below.

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

## Result

`meta/evals/logs/2026-08-20T17-07-26-*.eval`. Gate passed:
`positive_control_detection` = 1.000.

| measurement | independent checker | co-designed audit |
|---|---|---|
| detection rate | 0.667 | 0.667 |
| false confidence rate | 0.333 | 0.333 |
| specificity | 1.000 (n=1) | n/a |
| undecided rate | 0.000 | n/a |
| **blind-spot detection** | **0.000 (0 of 3)** | 0 by construction |

The overlap is not approximate. The checker caught the same six modes the audit
catches and missed the same three it misses, artifact for artifact.

## Reading

**P1 is not supported by this run.** P1 predicted that at matched cost and
decision procedure, independent checkers have a lower false confidence rate than
co-designed ones, with a large effect. The measured rates are identical.

**P2's mechanism is what was actually observed.** P2 defines shared blind spots
as B missing precisely what A misses. That is what happened, and the
pre-registration's own stopping rule applies: if the independent party also
misses them, independence is not the variable and the full factorial is
premature. It is premature.

The repository should stop writing *independent authorship* as the countermeasure
to those six sham modes as though it were established. On this evidence it is an
untested hope, and six `countermeasure` fields say otherwise with more confidence
than anyone has earned.

## What this does not show

- **n is small.** Three blind-spot artifacts, one run, no variance estimate. 0 of
  3 is consistent with a real effect that this slice is too small to see.
- **Difficulty is confounded with blind-spot status.** The modes the audit cannot
  catch may simply be *harder* for any reader, rather than shaped by co-design.
  Nothing here separates those, and it is the most likely alternative explanation.
- **Independence was prompt-level only.** The batteries were authored by Claude
  sessions and the checker is Claude. A genuinely foreign checker, on a
  non-Anthropic model, is the arm that would test the claim as stated. Until that
  runs, this measures whether a fresh context catches it, not whether a different
  mind does.
- **Specificity rests on one clean control.** A checker biased toward "sound"
  would score 1.000 here on n=1.

## Cost

Both runs, 20 model calls: 147,819 tokens (83,954 in, 56,117 out, of which 38,648
reasoning). Roughly $1.82 at Opus 5 rates. The reasoning tokens dominate and were
not in the pre-run estimate of $0.53.

## Next

The non-Anthropic arm, which is also the only way to measure conditional
detection lift, the quantity the design calls the most informative and the one
this repository has never taken. Adding clean controls is cheap and fixes the
weakest measurement here.
