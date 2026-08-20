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

## Result

Run 2, `claude-opus-5`: `meta/evals/logs/2026-08-20T17-07-26-*.eval`. Foreign
arms logged alongside. All four passed the `positive_control_detection` gate.

| checker | detection | false confidence | specificity (n=1) | blind spots |
|---|---|---|---|---|
| co-designed audit | 0.667 | 0.333 | n/a | 0 of 3 by construction |
| `claude-opus-5` | 0.667 | 0.333 | pass | **0 of 3** |
| `gemini-3.1-pro` | 0.556 | 0.444 | pass | 1 of 3 |
| `grok-4.6` | 0.333 | 0.556 | pass | 1 of 3 |
| `gpt-5.6-sol` | 1.000 | 0.000 | **FAIL** | 3 of 3, uninformative |

**GPT is disqualified, and the measure that disqualified it is the point.** It
answered *hollow* to all ten artifacts including the clean control. That scores
perfectly on detection and false confidence while distinguishing nothing, which
is exactly the degenerate checker `specificity` exists to catch. It caught it.
The repository's own admission rule, applied to a checker rather than a claim.

### Per artifact

| artifact | audit | claude | gemini | grok |
|---|---|---|---|---|
| `co-designed-calibration` | **blind** | sound | **hollow** | **hollow** |
| `distant-rivals` | **blind** | sound | sound | sound |
| `dropped-hardest-lesion` | **blind** | sound | sound | sound |
| `constant-true-detector` | catches | hollow | hollow | hollow |
| `detector-is-the-claim` | catches | hollow | hollow | hollow |
| `inert-lesion` | catches | hollow | hollow | sound |
| `target-as-rival` | catches | hollow | hollow | sound |
| `key-asymmetry-label-leak` | catches | hollow | sound | sound |
| `agreeable-absent-field-oracle` | catches | hollow | sound | sound |
| `clean` | n/a | sound | sound | sound |

## Reading

**Claude reproduced the audit exactly.** Same six caught, same three missed,
artifact for artifact. Prompt-level independence within the authoring model
family bought nothing at all.

**A foreign model caught one blind spot, and it is the on-point one.**
`co-designed-calibration` is the mode whose `countermeasure` field reads
*"independent authorship, held-out mutations authored by a party that has not
seen the detectors."* It is the mode most directly about co-design, the audit
cannot see it, Claude did not see it, and every foreign model did. That is the
single most encouraging observation in this run.

**P1 is not supported, and is contradicted on its own terms.** P1 predicted that
independent checkers have a *lower* false confidence rate. The foreign checkers
have higher ones: 0.444 and 0.556 against Claude's 0.333. They are not better
readers. They are differently blind.

**P2 is refuted, and P2 is the measurement that matters.** Conditional detection
lift asks whether B catches A's misses at more than B's own base rate. Across
every eligible pair it is zero or negative:

| pair | B on A's misses | B's base rate | lift |
|---|---|---|---|
| gemini on claude | 0.333 | 0.556 | -0.222 |
| grok on claude | 0.333 | 0.333 | 0.000 |
| claude on gemini | 0.500 | 0.667 | -0.167 |
| grok on gemini | 0.000 | 0.333 | -0.333 |
| claude on grok | 0.667 | 0.667 | 0.000 |
| gemini on grok | 0.333 | 0.556 | -0.222 |

No checker is better than its own average on what another missed. The misses are
correlated: hard artifacts are hard for everyone, and *that* is the structure,
not authorship.

**A panel helps, but not for the reason the repository assumed.** Claude alone
catches 6 of 9 and 0 of 3 blind spots; Claude plus Gemini catches 7 of 9 and 1
of 3; adding Grok adds nothing further. The gain is real and it is the ordinary
gain of running more checkers, not evidence that independent checkers cover each
other's blind spots. With lift at or below zero, that second claim has no support
here.

**What the repository should stop writing.** Six `countermeasure` fields name
independent authorship as the remedy for what the audit cannot see. On this
evidence that is one-third true at best, and the mechanism asserted for it,
independent parties failing in uncorrelated ways, is not observed at all. Say
"an additional checker sometimes catches co-designed calibration" and stop there.

## What this does not show

- **n is very small.** Three blind-spot artifacts, one run per checker, no
  variance estimate. One catch out of three is one artifact.
- **Specificity rests on a single clean control.** Every "pass" above is n=1.
  Gemini and Grok answered *sound* five and six times out of ten, so neither is
  degenerate, but that is reassurance rather than measurement. More clean
  controls is the cheapest improvement available.
- **Difficulty is confounded with blind-spot status.** The modes the audit cannot
  catch may simply be harder for any reader. The correlated-miss structure above
  is consistent with that and does not separate it.
- **Nothing here is about the mathematics.** It is evidence about the laboratory.

## Cost

Five runs, 50 model calls: about $3.35. Claude two runs ~$1.82, GPT $0.34,
Gemini $0.49, Grok $0.71. Reasoning tokens dominated throughout and were absent
from the pre-run estimate of $0.53; Grok alone emitted 105,332 of them.

## Next

More clean controls, which is cheap and fixes the weakest measurement here.
Repeat runs for variance, since every number above is a single draw. Neither
requires the full factorial, which the design's stopping rule now advises
against building.
