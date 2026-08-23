"""Reconstruct the organizers' clear-cut evaluation protocol from public data and
measure what it implies: class balance, row weighting, the single-variant share of
the non-robust class, and the out-of-fold accuracy of a model-identity prior.

Reads only the committed public datasets under data/. No network, no labels
other than the organizers' own. Writes artifacts/protocol.json and the fitted
prior table artifacts/identity_prior.json (fit on the official val-sample labels
only; sample-full agreement is reported, not used for fitting).

Run: .venv/bin/python hunts/aimo2/protocol_reconstruction.py
"""
import collections
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    with open(os.path.join(HERE, "data", name), encoding="utf-8") as handle:
        return json.load(handle)


def as_bool(value):
    return str(value).lower() == "true"


VAL = load("val_sample.json")
FULL = [r for r in load("sample_full.json") if r["model_id"].endswith(":low")]
AUG_LLAMA = load("augmented_sample_math.json")
AUG_8B_AGG = load("augmented_sample_math_agg_filtered.json")
AUG_8B_FULL = load("augmented_sample_math_full_filtered.json")

out = {}

# ---------------------------------------------------------------- val-sample anatomy
val_pairs = collections.Counter((r["model_id"], r["problem_id"]) for r in VAL)
val_robust = [r for r in VAL if as_bool(r["model_is_robust"])]
val_nonrobust = [r for r in VAL if not as_bool(r["model_is_robust"])]
out["val_sample"] = {
    "rows": len(VAL),
    "robust": len(val_robust),
    "pair_multiplicity": dict(collections.Counter(val_pairs.values())),
    "duplicated_pairs": [list(k) for k, c in val_pairs.items() if c > 1],
    "robust_rows_all_base_1": all(float(r["base_accuracy"]) >= 0.999 for r in val_robust),
    "robust_rows_all_zero_detrimental": all(int(r["n_detrimental_permutations"]) == 0 for r in val_robust),
    "nonrobust_rows_all_single_type": all(not r["permutation_type"].startswith("[") for r in val_nonrobust),
    "nonrobust_by_type": dict(collections.Counter(r["permutation_type"] for r in val_nonrobust)),
    "nonrobust_by_problem": dict(collections.Counter(r["problem_id"] for r in val_nonrobust)),
    "nonrobust_single_variant": sum(int(r["n_detrimental_permutations"]) <= 1 for r in val_nonrobust),
    "nonrobust_base_lt_1": sum(float(r["base_accuracy"]) < 0.999 for r in val_nonrobust),
}

# ------------------------------------------- reconstruct the protocol on sample-full
by_pair = collections.defaultdict(list)
for r in FULL:
    by_pair[(r["model_id"], r["problem_id"])].append(r)


def protocol_rows(strict_base):
    """Non-robust: a single-type row whose relative decay >= 0.5 with base >= 0.6.
    Robust: a (model, problem) pair with zero detrimental perturbations over every
    evaluated type (strict: and base accuracy 1.0 on every row, which is the
    filter that reproduces the val-sample robust set exactly)."""
    rows = []
    for r in FULL:
        if float(r["relative_accuracy_decay"]) >= 0.5 and float(r["base_accuracy"]) >= 0.6:
            rows.append((r["model_id"], r["problem_id"], False, r["permutation_type"], float(r["base_accuracy"])))
    for key, rs in by_pair.items():
        if sum(int(r["n_detrimental_permutations"]) for r in rs) == 0 and (
            not strict_base or all(float(r["base_accuracy"]) >= 0.999 for r in rs)
        ):
            rows.append((key[0], key[1], True, "ALL", min(float(r["base_accuracy"]) for r in rs)))
    return rows


val_rows = [
    (r["model_id"], r["problem_id"], as_bool(r["model_is_robust"]), r["permutation_type"], float(r["base_accuracy"]))
    for r in VAL
]
val_problems = {r["problem_id"] for r in VAL}
strict = protocol_rows(True)
loose = protocol_rows(False)
val_robust_pairs = {(r["model_id"], r["problem_id"]) for r in val_robust}
strict_robust_pairs = {(m, p) for m, p, y, *_ in strict if y}
out["reconstruction"] = {
    "strict_robust_pairs_equal_val_robust_pairs": val_robust_pairs == strict_robust_pairs,
    "val_nonrobust_rows_present_in_sample_full": sum(
        1 for r in val_nonrobust if any(
            f["model_id"] == r["model_id"] and f["problem_id"] == r["problem_id"]
            and f["permutation_type"] == r["permutation_type"] for f in FULL)
    ),
    "val_nonrobust_rows_with_identical_numbers": sum(
        1 for r in val_nonrobust if any(
            f["model_id"] == r["model_id"] and f["problem_id"] == r["problem_id"]
            and f["permutation_type"] == r["permutation_type"]
            and float(f["permuted_accuracy"]) == float(r["permuted_accuracy"])
            and int(f["n_detrimental_permutations"]) == int(r["n_detrimental_permutations"]) for f in FULL)
    ),
    "candidate_nonrobust_rows_on_val_problems": sum(
        1 for m, p, y, *_ in strict if not y and p in val_problems),
}


def per_model(rows):
    table = collections.defaultdict(lambda: {"robust": 0, "nonrobust": 0})
    for m, _p, y, *_ in rows:
        table[m]["robust" if y else "nonrobust"] += 1
    return dict(sorted(table.items()))


def fit_prior(rows):
    """Per-model majority label; unseen model or tie -> False (the better constant
    on every public set)."""
    table = collections.defaultdict(lambda: [0, 0])
    for m, _p, y, *_ in rows:
        table[m][int(bool(y))] += 1
    return {m: (t > f) for m, (f, t) in table.items()}


def apply_prior(prior, rows):
    return sum(prior.get(m, False) == y for m, _p, y, *_ in rows)


def lopo(rows):
    correct = 0
    for held in sorted({p for _m, p, *_ in rows}):
        prior = fit_prior([d for d in rows if d[1] != held])
        correct += apply_prior(prior, [d for d in rows if d[1] == held])
    return correct


def lomo(rows):
    correct = 0
    for held in sorted({m for m, *_ in rows}):
        prior = fit_prior([d for d in rows if d[0] != held])
        correct += apply_prior(prior, [d for d in rows if d[0] == held])
    return correct


def self_consistency_lopo(rows):
    """base accuracy < 1 -> non-robust, else the identity prior (fit on base-1 rows)."""
    correct = 0
    for held in sorted({p for _m, p, *_ in rows}):
        prior = fit_prior([d for d in rows if d[1] != held and d[4] >= 0.999])
        for m, p, y, _t, base in rows:
            if p != held:
                continue
            pred = False if base < 0.999 else prior.get(m, False)
            correct += pred == y
    return correct


def summarize(name, rows):
    n = len(rows)
    robust = sum(1 for d in rows if d[2])
    return {
        "n": n,
        "robust": robust,
        "robust_frac": round(robust / n, 4),
        "always_false": n - robust,
        "identity_prior_lopo": lopo(rows),
        "identity_prior_lomo": lomo(rows),
        "base_lt_1_then_prior_lopo": self_consistency_lopo(rows),
        "per_model": per_model(rows),
    }


out["val_sample_eval"] = summarize("val", val_rows)
out["protocol_full_strict"] = summarize("strict", strict)
out["protocol_full_loose"] = summarize("loose", loose)
out["protocol_full_strict"]["nonrobust_by_type"] = dict(
    collections.Counter(t for _m, _p, y, t, _b in strict if not y))
out["protocol_full_strict"]["nonrobust_single_variant"] = sum(
    1 for r in FULL if float(r["relative_accuracy_decay"]) >= 0.5 and float(r["base_accuracy"]) >= 0.6
    and int(r["n_detrimental_permutations"]) <= 1)

# cross-dataset transfer of the prior (fit on one public set, score the other)
prior_val = fit_prior(val_rows)
prior_strict = fit_prior(strict)
out["transfer"] = {
    "prior_fit_on_val": {m: bool(v) for m, v in sorted(prior_val.items())},
    "prior_fit_on_strict": {m: bool(v) for m, v in sorted(prior_strict.items())},
    "val_prior_on_strict": f"{apply_prior(prior_val, strict)}/{len(strict)}",
    "val_prior_on_loose": f"{apply_prior(prior_val, loose)}/{len(loose)}",
    "strict_prior_on_val": f"{apply_prior(prior_strict, val_rows)}/{len(val_rows)}",
    "priors_agree_on_all_models": all(prior_val[m] == prior_strict[m] for m in prior_val),
}

# ------------------------------------------------ organizer-released augmented sets
def aug_summary(rows):
    labelled = "model_is_robust" in rows[0]
    summary = {
        "rows": len(rows),
        "models": dict(collections.Counter(r["model_id"] for r in rows)),
        "problems": len({r["problem_id"] for r in rows}),
        "dataset_id": sorted({r["dataset_id"] for r in rows}),
        "base_accuracy_is_1": sum(float(r["base_accuracy"]) >= 0.999 for r in rows),
    }
    if labelled:
        robust = sum(as_bool(r["model_is_robust"]) for r in rows)
        summary.update({
            "robust": robust,
            "robust_frac": round(robust / len(rows), 4),
            "decay_rule_mismatches": sum(
                (float(r["relative_accuracy_decay"]) < 0.5) != as_bool(r["model_is_robust"]) for r in rows),
            "nonrobust_by_type": dict(collections.Counter(
                r["permutation_type"] for r in rows if not as_bool(r["model_is_robust"]))),
        })
    return summary


out["augmented_llama_3_1_8b"] = aug_summary(AUG_LLAMA)
out["augmented_deepseek_r1_8b_agg_filtered"] = aug_summary(AUG_8B_AGG)
out["augmented_qwen3_8b_full_filtered"] = aug_summary(AUG_8B_FULL)

# cross-type failure transfer on the unlabelled 8B set (protocol label reconstructed)
by_problem = collections.defaultdict(dict)
for r in AUG_8B_FULL:
    by_problem[r["problem_id"]][r["permutation_type"]] = float(r["relative_accuracy_decay"]) >= 0.5
failing_count = collections.Counter(sum(v.values()) for v in by_problem.values())
nonrobust_rows = sum(sum(v.values()) for v in by_problem.values())
robust_pairs = sum(1 for v in by_problem.values() if not any(v.values()))
loto = {}
for held in sorted({t for v in by_problem.values() for t in v}):
    tp = fp = fn = tn = 0
    for v in by_problem.values():
        if held not in v:
            continue
        others = {t: f for t, f in v.items() if t != held}
        if not others:
            continue
        x, y = v[held], any(others.values())
        tp += x and y
        fp += x and not y
        fn += (not x) and y
        tn += (not x) and (not y)
    n = tp + fp + fn + tn
    loto[held] = {"n": n, "acc": round((tp + tn) / n, 3), "majority": round(max(tp + fn, fp + tn) / n, 3),
                  "tp": tp, "fp": fp, "fn": fn, "tn": tn}
out["cross_type_transfer_8b_math"] = {
    "problems": len(by_problem),
    "failing_types_per_problem": {str(k): v for k, v in sorted(failing_count.items())},
    "protocol_nonrobust_rows": nonrobust_rows,
    "protocol_robust_pairs": robust_pairs,
    "protocol_robust_frac": round(robust_pairs / (nonrobust_rows + robust_pairs), 4),
    "single_type_predicts_other_types_lopo": loto,
    "any_single_type_beats_majority": any(v["acc"] > v["majority"] for v in loto.values()),
}

os.makedirs(os.path.join(HERE, "artifacts"), exist_ok=True)
with open(os.path.join(HERE, "artifacts", "protocol.json"), "w", encoding="utf-8") as handle:
    json.dump(out, handle, indent=2, sort_keys=True)
with open(os.path.join(HERE, "artifacts", "identity_prior.json"), "w", encoding="utf-8") as handle:
    json.dump({
        "fit_on": "aimo-interp/val-sample official model_is_robust labels, per-model majority",
        "fallback": False,
        "prior": {m: bool(v) for m, v in sorted(prior_val.items())},
    }, handle, indent=2, sort_keys=True)

v, s, l = out["val_sample_eval"], out["protocol_full_strict"], out["protocol_full_loose"]
print(f"val-sample: robust {v['robust']}/{v['n']}; identity prior LOPO {v['identity_prior_lopo']}/{v['n']}, LOMO {v['identity_prior_lomo']}/{v['n']}, always-False {v['always_false']}/{v['n']}")
print(f"protocol strict: robust {s['robust']}/{s['n']}; prior LOPO {s['identity_prior_lopo']}/{s['n']}, LOMO {s['identity_prior_lomo']}/{s['n']}, always-False {s['always_false']}/{s['n']}, base<1 rule {s['base_lt_1_then_prior_lopo']}/{s['n']}")
print(f"protocol loose:  robust {l['robust']}/{l['n']}; prior LOPO {l['identity_prior_lopo']}/{l['n']}, LOMO {l['identity_prior_lomo']}/{l['n']}, always-False {l['always_false']}/{l['n']}, base<1 rule {l['base_lt_1_then_prior_lopo']}/{l['n']}")
print("transfer:", out["transfer"]["val_prior_on_strict"], out["transfer"]["val_prior_on_loose"], out["transfer"]["strict_prior_on_val"], "agree:", out["transfer"]["priors_agree_on_all_models"])
print("reconstruction:", out["reconstruction"])
print("val nonrobust single-variant:", out["val_sample"]["nonrobust_single_variant"], "/", len(val_nonrobust), "; strict:", s["nonrobust_single_variant"], "/", s["always_false"])
a = out["augmented_deepseek_r1_8b_agg_filtered"]
print(f"8B on MATH (agg-filtered): robust {a['robust']}/{a['rows']}; Llama: {out['augmented_llama_3_1_8b']['robust']}/{out['augmented_llama_3_1_8b']['rows']}")
print("cross-type transfer 8B:", out["cross_type_transfer_8b_math"]["failing_types_per_problem"], "any beats majority:", out["cross_type_transfer_8b_math"]["any_single_type_beats_majority"])
print("wrote artifacts/protocol.json and artifacts/identity_prior.json")
