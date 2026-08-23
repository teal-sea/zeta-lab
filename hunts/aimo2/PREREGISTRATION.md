# Preregistration: AIMO-2 legal method and controls

Frozen 2026-08-22, before any predictor is fitted against the robustness
labels. The descriptive curation finding (reconstruct_curation.py) is not a
fitted predictor and does not depend on this document; this preregistration
governs the Small-track and Main-track ESTIMATORS and their evaluation. Its
purpose is to make the R-662B12 failure impossible to repeat: no rule is
chosen after reading the labels, everything learnable is fit inside folds, and
generalization is measured by holding out whole problems and whole models.

## Data of record (committed, offline)

- `data/val_sample.json`  : 28 rows, the public development sample. Curated.
- `data/sample_full.json` : 558 rows, the organizers' larger public sample.
  7 evaluated models, 10 problems, 8 perturbation types.
- Ground-truth label rule (inferred from and consistent with all 28 labelled
  val-sample rows): a (model, problem) case is **robust** iff its aggregate
  relative accuracy decay under the evaluated perturbations is < 0.5, i.e.
  `sum(n_detrimental_permutations) / sum(n_permuted_predictions) < 0.5`. On
  sample-full, which ships no label column, we reconstruct the label from the
  published decay columns by this exact rule.
- The container model for the Small track: the Codabench alias `qwen3-8b:low`
  resolves to the cached `deepseek-ai/DeepSeek-R1-0528-Qwen3-8B` (stated in the
  getting-started uncertainty-profiling baseline). The public 8B rows are the
  `qwen3-8b:low` rows of sample-full.

## Permitted inference-time features (in-container: model_id string + problem texts only)

Computable from the 8B model on the given problem and self-generated,
meaning-preserving perturbations of it:
1. self-perturbation answer agreement: fraction of K self-generated
   semantic-preserving perturbations on which the model's final answer equals
   its answer on the original problem;
2. self-consistency: agreement of the model's final answer across R repeated
   samples of the original problem;
3. response uncertainty statistics of the original response (token-logprob
   margin, entropy, answer-token confidence), the cheap end used by the
   official uncertainty baseline.
The `model_id` string may enter ONLY as a fitted categorical prior (per-model
intercept) with a mandatory out-of-model fallback, and only if it improves the
binding held-out metric (below). It may never be a hard-coded name to label map.

## Prohibited leakage (hard)

- No inference-time use of `base_accuracy`, `permuted_accuracy`,
  `absolute/relative_accuracy_decay`, `n_detrimental_permutations`,
  `permutations_causing_decay`, or `permutation_source`. These are the label or
  functions of it and are absent in-container. They are used only as offline
  ground truth for fitting and evaluation.
- No hard-coded model-name to robustness mapping.
- No fitting on the 28-row val-sample and reporting on the 28-row val-sample.
- No private/hidden labels (we do not have them) and no leaderboard probing to
  infer them.

## Fitting and evaluation

- Every threshold, regressor coefficient, and per-model intercept is fit only on
  the training rows of the current fold.
- **Small track** (hidden test = the same 8B model on unseen problems): binding
  metric is leave-one-problem-out (LOPO) accuracy over the 10 public problems,
  computed on the public 8B rows.
- **Main track** (hidden test = >= 8 models including unseen ones): binding
  metric is leave-one-model-out (LOMO) accuracy over the 7 public models.
- Both tracks also report the other split for context.

## Controls (all preregistered)

- **Constant baselines**: always-True and always-False. The "better constant" on
  a fold is the higher-accuracy of the two computed on that fold's training
  rows (so it too is chosen without the test labels).
- **Scrambled-text decoy**: recompute the estimator with the problem text
  token-shuffled. A content-based signal must degrade toward the better
  constant; a signal that survives scrambling is carried by length/identity,
  not content, and is reported as such (this is the exact control that killed
  R-662B12).
- **Label-permutation null**: the estimator's out-of-fold accuracy must exceed
  the 95th percentile of the accuracy distribution under 1000 random label
  permutations (stratified within the fold structure).

## Success and kill gates

- **Free gate (decides GPU spend), Phase 1**: split perturbation types into a
  cheap-syntactic probe set {typos, rephrase, rename, distract} and an
  expert/domain target set {expert_no_solution, expert_perturbations, domain}.
  A predictor that uses only cheap-set decay must predict the target-set-derived
  label out-of-fold (LOPO), on the public 8B rows, better than the better
  constant baseline. Rationale: a model's own noisy self-perturbations are, at
  best, a proxy for the cheap syntactic set; if even the organizers' clean
  cheap-set measurements do not transfer to the label out-of-fold, a
  self-generated version cannot, and no GPU is spent. PASS => the GPU session is
  justified. FAIL => kill Small-track engineering, report-only.
- **Small-track gate (post-GPU)**: LOPO accuracy on public 8B rows strictly
  exceeds the better constant baseline, and the margin survives both controls
  (does not survive scrambling and exceeds the permutation null). FAIL => stop,
  no second GPU, no post-hoc threshold search.
- **Main-track**: a learned method ships only if it beats the better constant
  under LOMO. Otherwise a legal constant/control ships; the report pool does not
  depend on leaderboard rank.
- **Container gate**: if the model-free ingestion/scoring path cannot be
  replayed after one honest debugging attempt, the leaderboard arm is killed and
  only the report arm continues.
- **Spend gate**: stop engineering at $150 total external spend, 8 GPU-hours, or
  2026-09-30.

## What a positive result would and would not mean

A method that beats constants out-of-fold on public 8B data is evidence for a
leaderboard submission, not a guarantee on the hidden set, because this hunt's
own curation finding shows the public sample's class balance is not the hidden
sample's. The report states this explicitly. Nothing here uses the reserved
verification vocabulary; every claim is "measured on public data" and graded as
such.

## Amendment, 2026-08-22 (recorded after the original freeze, text above unchanged)

1. **Main-track binding split.** The original text made leave-one-model-out
   binding on the assumption that the hidden set contains unseen models. The
   competition site ("The provided validation set covers all types of models
   contained in the test set") and the proposal paper (§1.6, "All model types
   included in the private test set will be covered in the public validation
   set") say otherwise. Leave-one-problem-out is therefore the binding split for
   the Main track; leave-one-model-out is still reported and is the prior's
   fallback case (unseen identifier -> non-robust). This is the split the
   original text already used for the Small track.
2. **Consequence for the permitted model_id prior.** The categorical per-model
   prior was permitted above "only if it improves the binding held-out metric".
   Under leave-one-problem-out it does, on every public set (26/28, 39/41, 43/56
   vs 19/28, 32/41, 32/56), so it ships as the Main-track entry. Its table is
   generated by `protocol_reconstruction.py` from the official `val-sample`
   labels, not written by hand, and the fallback is the better constant.
3. **Better constant.** The original text chose the constant on the natural
   public distribution. The evaluation distribution is the clear-cut protocol
   (proposal §1.4), reconstructed in `protocol_reconstruction.py`; on it and on
   every organizer-released labelled set the better constant is always
   non-robust. The always-robust bundles are superseded, not deleted.
4. **Free gate, re-run on more data.** The organizers' MATH releases
   (`augmented-sample-math*`, public, organizer-made, so not "extra labeled
   data" under the rules) give the 8B a minority class the AIMO sample lacks.
   The gate still fails: no single cheap perturbation type predicts failure
   under another out of fold. The Small-track GPU kill stands; no second attempt.
