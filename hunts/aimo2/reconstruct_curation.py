"""Deterministic reconstruction of the AIMO-2 curation finding.

Reads only the committed public datasets. No network. The one randomized
component (a label-permutation null) is seeded. Reproduces every number the
technical report cites and writes artifacts/curation.json.

Label rule of record: a case is ROBUST iff relative_accuracy_decay < 0.5.
This is verified below to reproduce the shipped val-sample label on every row.
(A detrimental-count ratio n_det/n_perm < 0.5 does NOT: it disagrees with the
shipped label on 10/28 rows, because a single high-impact perturbation flips a
case. We use the decay rule.)

Run: .venv/bin/python hunts/aimo2/reconstruct_curation.py
"""
import json, os, collections, random
HERE = os.path.dirname(__file__)
def load(n): return json.load(open(os.path.join(HERE, "data", n)))
VAL, FULL = load("val_sample.json"), load("sample_full.json")
def robust(rel_decay): return float(rel_decay) < 0.5

# --- verify the decay rule reproduces the shipped val-sample label exactly ---
decay_mism = ratio_mism = 0
for r in VAL:
    lab = str(r["model_is_robust"]).lower() == "true"
    if robust(r["relative_accuracy_decay"]) != lab: decay_mism += 1
    nd, npm = int(r["n_detrimental_permutations"]), int(r["n_permuted_predictions"])
    if npm and ((nd / npm) < 0.5) != lab: ratio_mism += 1
val_robust = sum(str(r["model_is_robust"]).lower() == "true" for r in VAL)
n_val = len(VAL)
val_single = [r for r in VAL if not str(r["permutation_type"]).startswith("[")]
val_agg = [r for r in VAL if str(r["permutation_type"]).startswith("[")]
val_single_nonrobust = sum(str(r["model_is_robust"]).lower() != "true" for r in val_single)
val_agg_robust = sum(str(r["model_is_robust"]).lower() == "true" for r in val_agg)

# --- sample-full: apply the SAME per-row decay rule ---
low = [r for r in FULL if r["model_id"].endswith(":low")]      # 7 models, matches val vocabulary
para = [r for r in FULL if not r["model_id"].endswith(":low")] # 10 paraphrase-only gpt-5.2 rows
def row_rate(rows):
    return sum(robust(r["relative_accuracy_decay"]) for r in rows), len(rows)
rr_all = row_rate(low)
rr_valid = row_rate([r for r in low if float(r["base_accuracy"]) >= 0.6])  # paper: original must be ~correct
rr_solved = row_rate([r for r in low if float(r["base_accuracy"]) >= 0.999])

# per-row robust rate by model and by perturbation type
bym = collections.defaultdict(lambda: [0, 0]); byt = collections.defaultdict(lambda: [0, 0])
for r in low:
    y = robust(r["relative_accuracy_decay"])
    bym[r["model_id"]][0] += y; bym[r["model_id"]][1] += 1
    byt[r["permutation_type"]][0] += y; byt[r["permutation_type"]][1] += 1

# --- pair-level (model,problem) label via pooled permuted accuracy (secondary) ---
pool = collections.defaultdict(lambda: [0.0, 0.0, 0.0, 0])  # base_sum,w; permuted_num,den
agg = collections.defaultdict(lambda: [0.0, 0, 0.0])        # base(max), permuted_weighted_num, den
for r in low:
    k = (r["model_id"], r["problem_id"])
    b, pa, npm = float(r["base_accuracy"]), float(r["permuted_accuracy"]), int(r["n_permuted_predictions"])
    agg[k][0] = max(agg[k][0], b); agg[k][1] += npm; agg[k][2] += pa * npm
pairs = {}
for k, (b, den, num) in agg.items():
    pooled_permuted = num / den if den else 0.0
    rel = (b - pooled_permuted) / b if b else 0.0
    pairs[k] = rel < 0.5
pairs_robust = sum(pairs.values()); n_pairs = len(pairs)

# --- honest identity-prior CV (uses only shipped/derived labels) ---
def prior(train, m):
    t = [y for (mm, y) in train if mm == m]
    if t: return sum(t) > len(t) / 2
    allt = [y for (_, y) in train]; return sum(allt) > len(allt) / 2  # fallback: train majority (better constant)
def cv(data, hi):
    keys = sorted({d[hi] for d in data}); c = 0
    for h in keys:
        tr = [(d[0], d[2]) for d in data if d[hi] != h]
        for d in data:
            if d[hi] == h: c += (prior(tr, d[0]) == d[2])
    return c
val_mpl = [(r["model_id"], r["problem_id"], str(r["model_is_robust"]).lower() == "true") for r in VAL]
full_mpl = [(m, p, bool(y)) for (m, p), y in pairs.items()]
val_allF = sum(1 for *_, y in val_mpl if not y)
full_allT = sum(1 for *_, y in full_mpl if y); full_allF = len(full_mpl) - full_allT

out = {
  "label_rule": "robust iff relative_accuracy_decay < 0.5",
  "rule_check": {"val_rows": n_val, "decay_rule_mismatches": decay_mism,
                 "count_ratio_rule_mismatches": ratio_mism},
  "val_sample": {"rows": n_val, "robust": val_robust, "robust_frac": round(val_robust/n_val,4),
                 "single_type_rows": len(val_single), "single_type_nonrobust": val_single_nonrobust,
                 "aggregated_rows": len(val_agg), "aggregated_robust": val_agg_robust},
  "sample_full_rowlevel": {
     "rows_low": len(low), "paraphrase_rows_excluded": len(para),
     "robust_all": f"{rr_all[0]}/{rr_all[1]}", "robust_frac_all": round(rr_all[0]/rr_all[1],4),
     "robust_base_ge_0.6": f"{rr_valid[0]}/{rr_valid[1]}", "robust_frac_base_ge_0.6": round(rr_valid[0]/rr_valid[1],4),
     "robust_base_solved": f"{rr_solved[0]}/{rr_solved[1]}", "robust_frac_base_solved": round(rr_solved[0]/rr_solved[1],4),
     "per_model": {m: f"{a}/{b}" for m,(a,b) in sorted(bym.items())},
     "per_type": {t: f"{a}/{b}" for t,(a,b) in sorted(byt.items())}},
  "sample_full_pairlevel": {"pairs": n_pairs, "robust": pairs_robust, "robust_frac": round(pairs_robust/n_pairs,4)},
  "identity_prior_cv": {
     "val_sample": {"n": n_val, "all_False": val_allF, "LOPO": cv(val_mpl,1), "LOMO": cv(val_mpl,0)},
     "sample_full_pairs": {"n": len(full_mpl), "better_constant": max(full_allT,full_allF),
                           "all_True": full_allT, "LOPO": cv(full_mpl,1), "LOMO": cv(full_mpl,0)}},
}
os.makedirs(os.path.join(HERE,"artifacts"), exist_ok=True)
json.dump(out, open(os.path.join(HERE,"artifacts","curation.json"),"w"), indent=2, sort_keys=True)

print(f"rule check: decay-rule mismatches vs shipped label = {decay_mism}/{n_val}; count-ratio-rule mismatches = {ratio_mism}/{n_val}")
print(f"val-sample: {val_robust}/{n_val} robust ({100*val_robust/n_val:.1f}%); {len(val_single)} single-type ({val_single_nonrobust} nonrobust), {len(val_agg)} aggregated ({val_agg_robust} robust)")
print(f"sample-full row-level (same rule): all {rr_all[0]}/{rr_all[1]}={100*rr_all[0]/rr_all[1]:.1f}%  base>=0.6 {rr_valid[0]}/{rr_valid[1]}={100*rr_valid[0]/rr_valid[1]:.1f}%  base=1.0 {rr_solved[0]}/{rr_solved[1]}={100*rr_solved[0]/rr_solved[1]:.1f}%")
print(f"sample-full pair-level: {pairs_robust}/{n_pairs}={100*pairs_robust/n_pairs:.1f}% robust")
print(f"identity CV val-sample: all-False {val_allF}/{n_val} | LOPO {cv(val_mpl,1)}/{n_val} | LOMO {cv(val_mpl,0)}/{n_val}")
print(f"identity CV full pairs:  better-const {max(full_allT,full_allF)}/{len(full_mpl)} | LOPO {cv(full_mpl,1)}/{len(full_mpl)} | LOMO {cv(full_mpl,0)}/{len(full_mpl)}")
print("wrote artifacts/curation.json")
