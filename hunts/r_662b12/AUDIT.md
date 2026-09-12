# Independent audit of the AIMO signal

Date: 2026-08-22

## Disposition

The all-False baseline reproduction survives: 19 of 28 public validation rows
are non-robust, so the constant classifier scores 67.86% with full coverage and
no invalid outputs.

The claimed +25.00 percentage point generalization result does not survive.
The 92.86% number is an in-sample score for a rule written after inspecting the
same 28 labels. It is not a cross-validated estimate, and it does not support a
technical-report or leaderboard submission.

## Failure mechanism

`are_robust_frontier_tier` hard-codes two model-name substrings, `gpt-5.2` and
`glm-5.1`. Those are exactly the two model families with perfect positive rates
in the public label inventory written earlier in `RESULTS.md`.

`run_cross_validations` then loops over held-out rows and calls that unchanged
rule. No model is fitted, no threshold or model-name set is selected from a
training fold, and no choice is repeated without the held-out labels. LOOCV,
leave-one-problem-out and five-fold partition the scoring operation, not the
rule-selection operation. Repeating an in-sample rule on subsets cannot turn
its score into out-of-sample evidence.

The hunt's own strongest control kills the structural interpretation. The
scrambled-text surrogate scores the same 26 of 28 as the proposed composite.
That equality shows the prediction is carried by model identity and coarse
length, not by mathematical meaning or a structure-matched verification pass.

The probe also reimplements the ingestion and scoring shape locally. It does
not execute the pinned official container or starter implementation. Therefore
the original statement that official ingestion was faithfully executed is
stronger than the recorded evidence.

## What remains useful

- The public sample contains 28 rows: 19 non-robust and 9 robust.
- The constant all-False baseline is 19/28, or 67.86%.
- Public labels are heavily associated with model identity in this small
  sample. That is a descriptive confound future evaluations must control.
- A model-name lookup can score 26/28 on this public sample. This is a warning
  about validation design, not an interpretability result.

## Next admissible experiment

Freeze a signal before reading evaluation labels, fit every learned component
inside each training fold, and hold out complete model families as well as
complete problems. The intervention must beat the constant baseline on those
out-of-family predictions and must change when mathematical content is replaced
by a structure-matched surrogate. Until then the prize lane is **NO-GO** on the
evidence from this hunt.

The original `HANDBACK.json`, probe and reported tables remain unchanged as the
run record. This audit supersedes their confidence and recommendation, not the
fact that the run occurred.
