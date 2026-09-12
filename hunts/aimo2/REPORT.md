# Base rates first: what the AIMO robustness label is made of, and the floor an interpretability method has to clear

**AIMO Interpretability Challenge at NeurIPS 2026 (Codabench competition 16180), technical report.**
Every number below is reproducible from the organizers' public datasets by
`hunts/aimo2/protocol_reconstruction.py` and `hunts/aimo2/free_gate.py`, and every submission
figure was obtained through the official ingestion and scoring programs (starter commit `e46be92`).
No hidden labels and no leaderboard feedback were used.

## Summary of contributions

1. **The evaluation protocol, reconstructed from public data.** The challenge proposal says the test
   set keeps only clear-cut cases. We show exactly what that means on the public data: the 9 robust
   rows of the development sample (`val-sample`, 28 rows) are precisely the 9 (model, problem) pairs of
   the larger public sample (`sample-full`, 558 rows) whose original answer is correct on 10 of 10
   samples and which lose nothing under any of 67 to 120 perturbations; its 19 non-robust rows are
   single-perturbation-type rows with relative accuracy decay of at least one half, matched number for
   number in `sample-full`. Three consequences follow and all three matter for how to read the
   leaderboard: the class balance is a parameter of the filter, not of the models (22 to 43 percent
   robust on the public problems depending on the robust-side filter; 32 percent in `val-sample`; 20
   percent for the Small-track model on the organizers' MATH release); a pair that breaks under several
   perturbation types is counted once per type, so two pairs supply 6 of the 19 non-robust rows; and
   about half of the non-robust class rests on a single human-written variant (10 of 19 rows in
   `val-sample`, 12 of 32 in the reconstruction, all `expert_no_solution`).
2. **A zero-compute baseline that every public evaluation puts far above the constant.** Under that
   protocol the label is mostly a property of the model. A per-model majority prior, fitted only on the
   official `val-sample` labels, scores 26 of 28 leave-one-problem-out on `val-sample`, 39 of 41 on the
   strict reconstruction and 43 of 56 on the loose one, against 19 of 28, 32 of 41 and 32 of 56 for the
   always-non-robust constant. Fitted on one public set and scored on the other it gets 26 of 28 and
   39 of 41, and the two fits agree on every model. The organizers' own probing and uncertainty
   baselines (58 and 69 percent in their proposal) do not clear this floor. The prior is legal under the
   published rules, uses nothing but the organizers' labels, and runs in constant time; we submit it as
   the Main-track entry and state plainly that it is a base-rate method, not an interpretability method.
3. **Negative results that save compute.** Black-box self-consistency adds nothing once the protocol is
   applied, because robust rows have base accuracy 1.0 by construction and most non-robust rows do too
   (38 of 41 versus 39 of 41 for the prior alone). On the organizers' 69-problem MATH release for the
   8B model, failure under one generic perturbation type does not predict failure under another (40 of
   41 failing problems fail under exactly one type; no single-type predictor beats the majority), so a
   self-generated-perturbation estimator has nothing to transfer. Under a preregistered gate we
   therefore spent no GPU on the Small track and submit the constant there.
4. **A round-trip defect in the starter kit** and concrete recommendations for the final analysis.

Our own first attempt fell into the trap that motivates this report: a rule chosen after reading the 28
labels scored 26 of 28 in sample and was described as a structural signal, before an audit found the score
was carried by two model-name substrings and that scrambling the problem text changed nothing. The
number was right and the interpretation was wrong. This report keeps the number, drops the
interpretation, and measures it properly.

## 1. Setup and the label rule

Each case is a (model, problem) pair; a submission implements `are_robust(model_id, problems) ->
list[bool]` and sees only the model identifier and the original problem text. The perturbation type is
not exposed. The shipped label is reproduced on all 28 of 28 `val-sample` rows by
`relative_accuracy_decay < 0.5`; a count rule `n_detrimental / n_permuted < 0.5` disagrees on 10 of 28
because a single high-impact variant can flip a case. We use the decay rule throughout, including on the
three organizer releases that ship no label column. The Small Models track evaluates one cached model,
`qwen3-8b:low`, which resolves to `deepseek-ai/DeepSeek-R1-0528-Qwen3-8B`.

## 2. The clear-cut protocol and what it produces

The proposal states that cases are dropped when the original answer is not robustly correct or when
the perturbations do not cause a consistent deterioration. On the public data this resolves to:

| class | rule that reproduces `val-sample` exactly | rows in `val-sample` |
| --- | --- | --- |
| robust | pair with base accuracy 1.0 on every row and zero detrimental perturbations over all evaluated types | 9 of 9 match the 9 such pairs in `sample-full` |
| non-robust | single-type row with relative decay >= 0.5 (base >= 0.6) | 19 of 19 present in `sample-full` with identical numbers; 30 such rows exist on the same 8 problems |

Applying the same rule to all 10 public problems and 7 models:

| public set | rows | robust | robust rate | always-non-robust |
| --- | --- | --- | --- | --- |
| `val-sample` (shipped labels) | 28 | 9 | 32.1% | 19 / 28 = 0.679 |
| reconstruction, strict robust side (base 1.0) | 41 | 9 | 22.0% | 32 / 41 = 0.780 |
| reconstruction, loose robust side (zero detrimental only) | 56 | 24 | 42.9% | 32 / 56 = 0.571 |
| `augmented-sample-math-agg-filtered`, DeepSeek-R1-8B on MATH (shipped labels) | 54 | 11 | 20.4% | 43 / 54 = 0.796 |
| `augmented-sample-math`, Llama-3.1-8B on MATH (shipped labels) | 156 | 0 | 0.0% | 156 / 156 |

The balance moves by twenty points with one filter choice the submission cannot see, which is why the
accuracy leaderboard will be dominated by whichever constant matches the hidden balance, and why we
recommend reporting lift over the identity prior and a balanced metric (Section 6). Two further
structural facts: **(a)** the importer keys cases by (model, problem, perturbation type), so a pair that
breaks under k types appears k times with the same text and label; in `val-sample` two pairs appear three
times each and supply 6 of 19 non-robust rows. **(b)** `expert_no_solution` rows carry one variant
sampled ten times (`n_detrimental` is 0 or 1 on all 49 such rows), so 10 of the 19 non-robust rows in
`val-sample` and 12 of 32 in the reconstruction rest on one human-written variant each. Whether that
variant is answer-preserving is the entire label for those rows.

## 3. The model-identity prior

Under the protocol the per-model label is close to deterministic: in `val-sample` two models are robust
on 7 of 7 cases and three are robust on 0 of 17. The prior predicts robust for a model iff the majority
of its public labelled cases are robust, and non-robust for any identifier it has not seen.

| evaluation | prior, leave-one-problem-out | prior, leave-one-model-out | always-non-robust |
| --- | --- | --- | --- |
| `val-sample` (28) | **26 / 28 = 0.929** | 19 / 28 = 0.679 | 19 / 28 = 0.679 |
| reconstruction, strict (41) | **39 / 41 = 0.951** | 32 / 41 = 0.780 | 32 / 41 = 0.780 |
| reconstruction, loose (56) | **43 / 56 = 0.768** | 32 / 56 = 0.571 | 32 / 56 = 0.571 |
| fit on `val-sample`, score on strict (41) | **39 / 41** | | 32 / 41 |
| fit on strict, score on `val-sample` (28) | **26 / 28** | | 19 / 28 |

Two readings are possible and the competition design decides between them. If the hidden set contains
models absent from the public data, the leave-one-model-out column applies and the prior is worth nothing
beyond its fallback. The organizers state that the provided validation set covers all types of models in
the test set, and the per-model column is one of the four dissections they plan for the final report; in
that case the leave-one-problem-out column applies and the prior is a 17 to 25 point floor above the
constant, at zero cost. We submit it for the Main track with the constant as its fallback, so its
downside relative to the constant is bounded by the unseen-model case.

We want to be exact about what this is. It is not an interpretability result; it reads no text and runs no
model. It is the base rate the task carries once the protocol is fixed, and it is the number an
interpretability method must beat to have shown anything about mechanisms rather than about which model
it was handed. The organizers' proposal reports 58.4 and 69.2 percent for their probing and uncertainty
baselines in cross-validation; on every public set above those numbers sit at or below the constant.

## 4. Negative results

**Self-consistency.** A natural black-box feature is whether the model answers the original problem
consistently. Under the protocol it carries almost nothing: robust rows have base accuracy 1.0 by
construction, 8 of 19 non-robust rows in `val-sample` also do, and on the MATH release 52 of 54 rows do.
Adding the rule "base accuracy below 1 implies non-robust" to the prior scores 38 of 41 against 39 of 41
for the prior alone.

**Self-generated perturbations for the Small track.** We preregistered (`PREREGISTRATION.md`, frozen
before any predictor was fitted) a self-perturbation-stability estimator with a free gate: if the
organizers' own clean cheap-perturbation measurements do not predict the label out of fold, a noisier
self-generated version cannot. On the AIMO public problems the gate fails because the 8B rows carry no
minority class (10 of 10 pairs robust at the pair level). The organizers' MATH release provides the
minority class the AIMO sample lacks (43 failing rows over 69 problems) and the gate fails there too, for
a sharper reason: failures do not transfer across perturbation types. 28 problems fail under no type, 40
under exactly one, 1 under three, and `domain` alone accounts for 32 of the 43 failing rows in the
labelled release. Predicting "fails under some other type" from "fails under type t" never beats the
majority for any t (accuracies 0.33 to 0.43 against majorities 0.56 to 0.92). A submission can only emit
one verdict per problem, so the attainable Small-track signal is "does this problem break under
anything," and the public data says the generic types do not forecast that for one another. No GPU was
spent, in accordance with the preregistered kill rule, and the Small-track submission is the constant.

## 5. The official scoring path and a starter-kit defect

At starter commit `e46be92` (HEAD at the time of writing, titled "Simplify problem validation in
ingestion.py"), `scripts/import_hf_dataset.py` writes each case's `problem` as an object
`{original_problem, permutation_type}` while `components/ingestion_program/ingestion.py` line 45 rejects
any `problem` that is not a string, so the documented local round-trip fails on its own output.
Normalizing `problem` to the `original_problem` string, which is what the `list[str]` interface promises,
makes the official ingestion and scoring run. Through that path on `val-sample`:

| submission | accuracy | coverage | invalid |
| --- | --- | --- | --- |
| always-non-robust (official reference) | 0.6786 (19/28) | 1.0 | 0 |
| always-robust (starter example) | 0.3214 (9/28) | 1.0 | 0 |
| model-identity prior (this report) | 0.9286 (26/28) | 1.0 | 0 |

The 26 of 28 here is in-sample for the prior (it was fitted on these labels); the out-of-fold figures are
in Section 3.

## 6. Recommendations for the final analysis

1. **Report lift over the identity prior, per model,** alongside raw accuracy. A method that does not beat
   the per-model base rate has not used the problem. The organizers already plan a per-model dissection;
   this is the baseline that makes it interpretable.
2. **Report a balanced metric** (balanced accuracy or per-class recall). With a filter-determined class
   balance, raw accuracy ranks constants.
3. **Deduplicate or weight (model, problem) pairs.** One verdict per pair is what submissions can give;
   scoring a pair k times for k breaking perturbation types rewards nothing a submission can do.
4. **Ship more than one variant per expert perturbation,** or report which rows rest on a single variant.
5. **Fix the starter round-trip** so participants exercise the real ingestion path.

## 7. Limitations

The public data is small: 28 labelled AIMO cases, 558 AIMO rows over 10 problems, and the MATH releases
cover two small models. The reconstruction of the robust side on `sample-full` is ours, although it
reproduces the shipped robust set exactly and the non-robust rows number for number. The hidden set may be
filtered differently from `val-sample`, and may contain models we have not seen; both would move the
numbers, and the second would reduce the prior to its constant fallback. We ran no model; every figure
derives from the organizers' published measurements, the official scoring programs, and the constant and
prior submissions. Claims are about the public data and are graded as such.

## Reproducibility

```
.venv/bin/python hunts/aimo2/protocol_reconstruction.py   # artifacts/protocol.json, artifacts/identity_prior.json
.venv/bin/python hunts/aimo2/free_gate.py                  # artifacts/free_gate.json
.venv/bin/python hunts/aimo2/reconstruct_curation.py       # artifacts/curation.json (row-level census)
# official path: starter at e46be92, val-sample written as string problems, then
python3 scripts/run_local.py <bundle_dir>                   # identity prior 0.9286, always-false 0.6786
```

Datasets are committed under `hunts/aimo2/data/` with SHA-256 in `hunts/aimo2/CHECKSUMS.sha256`.
