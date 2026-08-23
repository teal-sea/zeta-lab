# Hunt AIMO-2 Results

**Status: report-ready; leaderboard-method arm killed at a free gate; no GPU spent.**
The cashable product is the technical report (`REPORT.md`). Three legal constant
submissions are prepared as the eligibility vehicle and control. Nothing here
rehabilitates the withdrawn R-662B12 +25pp claim.

## What was established (all from public data, graded "measured on public data")

1. **Curation finding (the report thesis).** The 28-row development sample
   `val-sample` is 9/28 = 32.1% robust; the same organizer label rule
   (`relative_accuracy_decay < 0.5`, verified to reproduce the shipped label on
   28/28 rows) applied to the 558-row `sample-full` gives 489/548 = 89.2%
   (all rows), 370/402 = 92.0% (base>=0.6), 238/246 = 96.7% (base solved),
   65/70 = 92.9% (pair level). The development sample's 19 non-robust cases are
   single-worst-perturbation rows from the decayed tail; its 9 robust cases are
   all-perturbation aggregates that never fail. The sample inverts the natural
   class balance by construction.
2. **The model-identity signal does not transfer.** On `val-sample` a per-model
   prior scores 26/28 under leave-problem-out but 19/28 (the better constant)
   under leave-model-out; on the natural pairs it never beats the constant
   (65/70 either way). The apparent signal, and the withdrawn R-662B12 result,
   is within-model memorization exposed by holding out problems but not models.
   The hidden test contains unseen models, so this is the binding split.
3. **Official container path replayed.** At starter commit `e46be92` the
   official importer writes `problem` as an object but the official ingestion
   requires a string, so the shipped tooling does not round-trip (a reportable
   defect, and the reason R-662B12 never ran the real path). Normalizing to the
   documented string interface, the official ingestion+scoring gives always-false
   0.6786 (19/28), always-true 0.3214, both coverage 1.0, 0 invalid. The
   perturbation type is not exposed to submissions.
4. **No leakage-free learned method is justified.** Preregistered free gate:
   the public 8B model (`qwen3-8b:low` -> DeepSeek-R1-8B) is robust on 10/10 of
   its public problems, so the better constant is already perfect and there is
   no minority class to fit; pooled across models the cheap-perturbation
   predictor only ties out of fold and loses under leave-model-out. GPU was not
   spent, per the preregistered kill rule.

## What was chosen and why

- **Report over method.** The $5,000 report pool is ranking-independent and
  names negative results as a criterion; the curation finding is a clean,
  reproducible negative result about the challenge's own validation design.
- **Constant submissions, not a fitted classifier.** Under the preregistration,
  nothing beat the better constant out of fold, so the honest submission is a
  calibrated constant prior (Small: always-robust, the 8B model is 10/10 robust
  on public problems; Main: always-robust, the natural distribution is ~90%
  robust). The official all-false reference is provided as a control.
- **No leaderboard probing.** We do not pick a constant from leaderboard
  feedback; that would infer the hidden balance, which is the exact anti-pattern
  the report warns against and is out of scope by the mission.

## What could not be settled

- The **hidden-set class balance** is unknowable from public data without
  probing (banned). The choice between always-robust (bets natural-like) and
  always-false (bets val-like) for a leaderboard score is therefore a judgment
  under uncertainty, left to the operator at upload.
- Whether a **white-box interpretability method** (SAE, residual-stream probe)
  could beat constants on the hidden set. It cannot be developed honestly on the
  public data because the public 8B distribution carries no minority class; this
  is a statement about the public data, not a claim the hidden problem is
  trivial.

## Reproduce

```
.venv/bin/python hunts/aimo2/reconstruct_curation.py   # curation.json
.venv/bin/python hunts/aimo2/free_gate.py              # free_gate.json
# official path (starter cloned at commit e46be92, normalized problem->string):
#   python3 scripts/run_local.py solutions/always-false  -> 0.6786, coverage 1.0, invalid 0
```

## Loose threads

1. **Balanced-metric re-scoring of the leaderboard.** *What:* if the hidden
   optimal predictor is near-constant, the accuracy leaderboard mostly ranks
   base rates. *Why it matters:* a team that reports balanced accuracy or
   per-class recall on its own public reconstruction has a sharper report
   figure than the raw leaderboard. *First step:* compute balanced accuracy for
   the constants and the identity prior on `sample-full` pairs and add the panel
   to the report if a reviewer asks for method-quality separation.
2. **The starter round-trip defect upstream.** *What:* importer/ingestion
   schema mismatch at `e46be92`. *Why it matters:* reporting it to the
   organizers is cheap goodwill and strengthens the "run the real path"
   section. *First step:* open a one-line issue on `aimo-interp/getting-started`
   (operator action, not automated here).
3. **Hidden-balance-robust submission.** *What:* a submission whose expected
   accuracy is flat in the hidden robust rate. *Why it matters:* it removes the
   coin-flip between the two constants. *First step:* a per-problem stochastic
   predictor calibrated to a stated prior is not obviously legal or better;
   price it against the constants before building.

Nothing in this hunt bears on the Riemann Hypothesis (docs/08).
