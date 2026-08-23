# Hunt AIMO-2: legal AIMO Interpretability submission + validation-design report

Successor to Hunt #72 (`hunts/r_662b12`, run `31e8a4f2`), whose reported +25pp
robustness signal was withdrawn by independent audit (in-sample rule on the 28
labels, scrambled-text control retained the full score, official container
never run). This hunt does NOT rehabilitate that claim. It builds the shortest
legal path from the current public evidence to cashable value in the AIMO
Interpretability Challenge at NeurIPS 2026 (Codabench competition 16180,
$12,500 pool, deadline 2026-11-01).

Money target, in priority order:
1. The $5,000 technical-report pool (awarded "regardless of ranking", explicit
   criteria include negative results and efficient methods). Thesis: the public
   development sample is curated so that model-identity / calibration signals
   look far more informative than they are on the larger public distribution.
2. A legal Small Models-track submission, only if a cheap gate then a held-out
   gate justify it.
3. A legal Main-track submission (a learned method only if it earns its way in
   under the preregistered protocol; otherwise a legal constant/control).

```huntspec
id: aimo2
question: Can we (a) reproduce, from public data alone, a validation-design finding about the AIMO sample worth a technical-report submission, and (b) build a legal Small/Main-track method that beats the better constant baseline out-of-fold under a preregistered leakage-controlled protocol?
frontier: R-662B12 reproduced the all-False baseline (19/28 = 0.6786 on the curated val-sample) and had its +25pp intervention withdrawn on audit; the official container ingestion/scoring path was never exercised; no legal held-out method and no report exist
proposed_attack: freeze a preregistration before fitting any predictor; reconstruct the curation finding deterministically from the public 28-row val-sample and 558-row sample-full; replay the model-free container path (always-true, always-false); run a free perturbation-transfer gate to decide whether a GPU session is justified; only then, in one GPU session, test a self-perturbation-stability estimator on the cached 8B model under leave-problem-out and leave-model-out controls
dead_routes:
  - any rule that reads the labels before it is frozen, or is fit outside training folds (the R-662B12 failure)
  - hard-coded model-name to label lookup tables
  - using the organizers' published decay/accuracy columns as inference-time features (they are the label and are absent in-container)
  - leaderboard probing designed to infer hidden labels
  - a second GPU attempt after the first honest estimator fails its preregistered gate
required_oracles:
  - the official ingestion and scoring programs from aimo-interp/getting-started, run locally on the committed public data
  - the committed public datasets data/val_sample.json (28 rows) and data/sample_full.json (558 rows)
  - a label-permutation null and a scrambled-text decoy control
kill_conditions:
  - the official model-free container path cannot be replayed after one honest debugging attempt (then report-only)
  - the free perturbation-transfer gate does not beat the better constant baseline out-of-fold (then no GPU, report-only)
  - the post-GPU estimator does not beat the better constant baseline out-of-fold under the preregistered controls (then stop, no second GPU, no threshold fishing)
  - $150 total external spend, 8 GPU-hours, or 2026-09-30 reached
agents_may:
  - import
  - benchmark
  - cross_validate
  - analyze
  - evaluate
agents_may_not:
  - submit to Codabench
  - perform account actions
  - probe the leaderboard to infer hidden labels
  - declare theorem status
  - use the reserved verification vocabulary of zeta/rigor.py or the Lean arm
```

Nothing in this hunt bears on the Riemann Hypothesis (docs/08).
