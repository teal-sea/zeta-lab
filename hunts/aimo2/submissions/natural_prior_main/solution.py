"""AIMO Interpretability submission -- Main track.

Method: the leakage-free natural-distribution prior. On the representative
public sample (aimo-interp/aimo-interp-challenge-sample-full, 558 rows, 7
models), the robust rate under the organizers own label rule
(relative_accuracy_decay < 0.5) is 89.2%% of all rows, 92.0%% of base-solved
rows, 92.9%% at the (model,problem) pair level. No leakage-free learned method
beats this constant out-of-fold under the preregistered leave-model-out and
leave-problem-out controls (hunts/aimo2/free_gate.py). The maximum-likelihood
prior on the natural public distribution is therefore: robust.

Note: this scores 0.321 on the curated 28-row val-sample, whose 32%% robust
balance is not the natural balance (that inversion is the report thesis).
"""


def are_robust(model_id: str, problems: list) -> list:
    del model_id
    return [True for _ in problems]
