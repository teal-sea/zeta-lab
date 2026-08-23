# The AIMO robustness development sample is curated in a way that inflates model-identity and calibration signals

**AIMO Interpretability Challenge at NeurIPS 2026 (Codabench competition 16180) technical report.**
All numbers below are reproducible from public data by `hunts/aimo2/reconstruct_curation.py`,
`hunts/aimo2/free_gate.py`, and the official starter container at commit `e46be92`. No hidden
labels and no leaderboard feedback were used.

## Contribution

The public development sample the challenge ships (`aimo-interp/val-sample`, 28 cases) is 32.1 percent
robust. The organizers' larger public sample (`aimo-interp/aimo-interp-challenge-sample-full`, 558
rows), scored by the identical label rule, is 89 to 97 percent robust. The development sample is not a
random draw from the evaluation distribution: it is built by contrasting single worst perturbation
failures against all perturbation aggregates that never fail, which both inverts the class balance and
manufactures separability. We show that this makes a model-identity prior look strong (it scores
26 of 28 on the sample under leave-one-problem-out cross validation) while it carries no transferable
signal at all: under leave-one-model-out it drops to the constant baseline, and on the natural
distribution it never beats the constant. We reproduce the finding end to end, exercise the official
scoring path (which uncovers a schema defect in the pinned starter), and show that under a preregistered
leakage-free protocol no learned method beats the better constant baseline out of fold on the public
data, so the honest submission for both tracks is a calibrated constant prior. The lesson for the
organizers is concrete: development-sample accuracy is not an estimator of hidden-set accuracy, and the
public leaderboard number is largely a readout of the hidden-set class balance.

Our own first internal attempt fell into exactly the trap this report describes: a rule chosen after
reading the 28 labels scored 26 of 28 in sample and was reported as a plus 25 point gain, before an
audit found the score was carried by two hard-coded model-name substrings, that no fold ever refit the
rule, and that scrambling the problem text left the score unchanged. That failure is the motivation, and
the report stands on the public evidence independently of it.

## 1. Setup and the label rule

Each case is a (model, problem) pair. The challenge asks a submission to return, through
`are_robust(model_id, problems) -> list[bool]`, whether the model answers each problem robustly.
The label is derived from perturbations: a case is **robust** iff its relative accuracy decay under the
evaluated perturbations is below one half. We verified this rule against the shipped `model_is_robust`
column of `val-sample`: `relative_accuracy_decay < 0.5` reproduces the shipped label on all 28 of 28
rows. A detrimental-count rule `n_detrimental / n_permuted < 0.5` does not (it disagrees on 10 of 28),
because a single high-impact perturbation can flip a case even when few perturbations are detrimental.
We use the decay rule everywhere, so the label we apply to the 558-row sample (which ships no label
column) is exactly the one the organizers apply to the 28-row sample.

The two public datasets share seven `:low` models, ten problems, and seven perturbation families
(`typos, rephrase, rename, distract, domain, expert_no_solution, expert_perturbations`). The Small
Models track evaluates one cached model: the Codabench alias `qwen3-8b:low` resolves to
`deepseek-ai/DeepSeek-R1-0528-Qwen3-8B`.

## 2. Finding 1: the development sample inverts the natural class balance

| dataset | scope | robust rate |
| --- | --- | --- |
| `val-sample` (development) | 28 cases | **9 / 28 = 32.1%** |
| `sample-full` | 548 rows, same decay rule | 489 / 548 = **89.2%** |
| `sample-full` | rows where the model solved the original (base >= 0.6) | 370 / 402 = **92.0%** |
| `sample-full` | rows where the model fully solved the original (base = 1.0) | 238 / 246 = **96.7%** |
| `sample-full` | (model, problem) pair level, pooled decay | 65 / 70 = **92.9%** |

The development sample reports a minority-robust world (about one in three). Every representative public
cut of the same models and problems reports a strongly majority-robust world (roughly nine in ten). The
gap is not noise; it is construction.

**The construction.** The 28 development cases split cleanly into two kinds. Nineteen are
single-perturbation-type rows, and all nineteen are non-robust: they are drawn from the decayed tail of
`sample-full`, one hard perturbation type at a time. Nine are aggregated rows whose perturbation field
lists all seven families at once, and all nine are robust with zero detrimental perturbations of 70 to
120. So the development sample pits "the single worst perturbation of a hard case" against "the pooled
average over all perturbations of an easy case." Those are not the same measurement, and contrasting
them both inflates the apparent robust/spurious separability and inverts the base rate. A classifier
tuned on this contrast is tuned on an artifact of the sampling, not on a property of the evaluation
distribution.

## 3. Finding 2: the apparent model-identity signal does not transfer

In the development sample the seven models have near-deterministic labels (for example
`gpt-5.2:low` is 3 of 3 robust and `gpt-oss-120b:low` is 0 of 7). A predictor that simply learns each
model's base rate therefore looks excellent, but only if the evaluation lets it memorize that base rate.

| evaluation | development sample (28) | natural pairs (70) |
| --- | --- | --- |
| better constant baseline | 19 / 28 = 0.679 | 65 / 70 = 0.929 |
| model-identity prior, leave-one-problem-out | **26 / 28 = 0.929** | 65 / 70 = 0.929 |
| model-identity prior, leave-one-model-out | 19 / 28 = 0.679 | 65 / 70 = 0.929 |

Under leave-one-problem-out the identity prior gains seven points on the development sample, which is the
entire apparent effect that our withdrawn internal result had rediscovered by hand. Under
leave-one-model-out, where the held-out model's base rate cannot be memorized, the same prior falls back
to the constant and the gain is zero. On the natural distribution the prior never beats the constant at
all, because that distribution is nearly single-class. The identity "signal" is within-model
memorization exposed by an evaluation split that holds out problems but not models. Since the hidden test
contains at least eight models including unseen ones, this is the split that matters, and identity buys
nothing on it.

## 4. Finding 3: a leakage-free method has nothing to learn on the public 8B data

We preregistered (`hunts/aimo2/PREREGISTRATION.md`, committed before any predictor was fit) a
self-perturbation stability estimator for the Small Models track, with fitting inside folds,
leave-one-problem-out and leave-one-model-out evaluation, a scrambled-text decoy, a label-permutation
null, and a free pre-GPU gate. The free gate asks whether the cheap syntactic perturbations a small model
could generate for itself predict the label out of fold. It fails, for a decisive reason: the public 8B
model is robust on 10 of 10 of its public problems. There is no minority class to fit and the better
constant is already perfect on the public 8B data. Pooled across all seven models the cheap-perturbation
predictor only ties the constant out of fold and loses under leave-one-model-out. We therefore spent no
GPU, in accordance with the preregistered kill rule.

This is the same finding from the method side: the representative public distribution does not contain
the balanced, separable classification problem that the development sample advertises.

## 5. The official scoring path, and a defect in the pinned starter

The earlier internal run reproduced the scoring shape locally but never ran the official container. We
did. At the pinned starter commit `e46be92` the official dataset importer writes each case `problem` as
an object `{original_problem, permutation_type}`, but the official ingestion program's validator requires
`problem` to be a string and rejects the object, so the shipped tooling does not round-trip. This is a
reportable defect in the starter kit. Normalizing `problem` to the `original_problem` string (which is
also what the documented `list[str]` interface promises, and which confirms that the perturbation type is
not exposed to submissions) makes the official ingestion and scoring run. Through that path:

| submission | accuracy | coverage | invalid |
| --- | --- | --- | --- |
| always-false (official reference) | 0.6786 (19/28) | 1.0 | 0 |
| always-true | 0.3214 (9/28) | 1.0 | 0 |

The all-false 0.6786 matches the organizers' documented baseline, now confirmed through the real
ingestion and scoring programs rather than a local re-implementation.

## 6. What we submit, and why it is a constant

No leakage-free learned method earns its way in under the preregistered protocol, so the honest
submission is a calibrated constant prior, chosen on public data without touching the hidden labels:

- **Small track:** always-robust. On the representative public data the Small-track model is robust on
  every public problem; the maximum-likelihood prior for it is robust.
- **Main track:** always-robust, the maximum-likelihood prior on the 89 to 97 percent robust natural
  public distribution. We also provide the official all-false reference as a conservative control.

We deliberately do not choose between these on leaderboard feedback: doing so would infer the hidden
class balance from the score, which is both against the competition's anti-overfitting intent and the
exact failure this report warns against. The value we claim is the analysis, not a leaderboard rank.

## 7. Consequences for validation design

1. **Development-sample accuracy is not an estimator of hidden-set accuracy.** A method can score 0.93 on
   `val-sample` and encode nothing that transfers. Report per-model and per-perturbation breakdowns, and
   evaluate with models held out, not only problems held out.
2. **The public leaderboard number is largely a readout of the hidden class balance.** With near-constant
   optimal predictors, accuracy mostly reflects the fraction of robust cases in the hidden set. A balanced
   metric (balanced accuracy, or per-class recall) would measure method quality rather than base rate.
3. **Match the sampling of the two classes.** Contrasting single-worst-perturbation failures with
   all-perturbation-pooled successes builds separability into the sample. Draw both classes by the same
   aggregation.
4. **Fix the starter round-trip** so participants exercise the real ingestion path, which is where the
   earlier public confusion about "reproducing the baseline" came from.

## 8. Limitations

The public data is small (28 labelled cases, 558 rows, 7 models, 10 problems), so the natural robust rate
is estimated, not pinned, and the hidden set may differ. Our reconstruction of the pair-level label on
`sample-full` pools permuted accuracy by count and could differ from the organizers' internal
aggregation; the row-level rule is the exact shipped rule and does not depend on that choice, and the
qualitative gap (32 percent versus roughly 90 percent) is far larger than any pooling ambiguity. We did
not run the models; every number is derived from the organizers' published measurements and the constant
submissions. The claim is about the public sample and the public distribution, and is graded as measured
on public data, nothing stronger.

## Reproducibility

```
# curation finding and identity cross-validation
.venv/bin/python hunts/aimo2/reconstruct_curation.py      # writes artifacts/curation.json
# free pre-GPU gate
.venv/bin/python hunts/aimo2/free_gate.py                 # writes artifacts/free_gate.json
# official ingestion + scoring at commit e46be92 (starter cloned separately)
python3 scripts/run_local.py solutions/always-false       # 0.6786, coverage 1.0, invalid 0
```

Datasets are committed under `hunts/aimo2/data/` with SHA-256 recorded in `hunts/aimo2/CHECKSUMS.sha256`.
