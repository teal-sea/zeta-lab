"""Evaluate the omega-grid rerun of target B exactly as PREREG_B2.md fixes it.

    .venv/bin/python hunts/skewes_enclosure/evaluate_b2.py --shards <dir with 220 shard JSONs> \
        --out hunts/skewes_enclosure/shards_b2/evaluation.json

Order, as pre-registered: completeness; the control at 727.95134 against the
recorded S; then the rule at the two decisive points; lower bounds and planted
faults only at decisive points; every grid point reported as a value.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import flint
from flint import arb

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import skewes_terms as st  # noqa: E402
import zero_layer as zl  # noqa: E402

SHARD = 100_000
K = 220
#: the recorded production-B ball at the control omega (RESULTS.md section 6)
RECORDED_CONTROL = "[-0.99067672 +/- 1.89e-9]"
BUDGET = "2.60111e-5"
ETAS = ["0.0000228", "0.00002", "0.000018", "0.000016", "0.0000159", "0.0000158"]


def evaluate(shard_dir: Path) -> dict:
    flint.ctx.prec = st.PREC
    grid = json.loads((HERE / "omega_grid.json").read_text())
    decisive, control, omegas = grid["decisive"], grid["control"], grid["omegas"]
    p = st.SAOUTER_DEMICHEL
    shards = [json.loads((shard_dir / f"shard_{k:03d}.json").read_text())
              for k in range(1, K + 1)]

    checks = {
        "contiguous_indices": all(d["n0"] == (k - 1) * SHARD + 1 and d["num"] == SHARD
                                  for k, d in enumerate(shards, start=1)),
        "ordered_within_shards": all(d["ordered_disjoint"] for d in shards),
        "ordered_across_shards": all(bool(arb(a["last"]) < arb(b["first"]))
                                     for a, b in zip(shards, shards[1:])),
        "last_zero_below_T": bool(arb(shards[-1]["last"]) < arb(p.T)),
        "turing_count_N(T)": zl.count_below(p.T),
        "route2_all_sign_changes": all(d["route2_sample"]["all_sign_changes"] for d in shards),
        "route2_sample_size": sum(d["route2_sample"]["size"] for d in shards),
        "grid_alpha_is_6e12": all(d.get("grid_alpha") == p.alpha for d in shards),
        "every_shard_has_every_omega": all(set(d["grid_sums"]) == set(omegas) for d in shards),
    }
    checks["complete"] = checks["turing_count_N(T)"] == K * SHARD

    S = {w: arb(0) for w in omegas}
    for d in shards:
        for w in omegas:
            S[w] += arb(d["grid_sums"][w])

    ctrl = S[control]
    control_res = {"S": ctrl.str(12), "recorded": RECORDED_CONTROL,
                   "overlaps_recorded": bool(ctrl.overlaps(arb(RECORDED_CONTROL)))}

    s_star, budget = arb(st.REVERS_S_STAR["saouter_demichel"]), arb(BUDGET)
    rule = {}
    for w in decisive:
        far = abs(S[w] - s_star) + S[w].rad()
        rule[w] = {"S": S[w].str(15), "abs_diff_plus_rad": far.str(6),
                   "meets_rule": bool(far <= budget)}
    h_supported = rule["727.951335792"]["meets_rule"]

    lower, faults = {}, {}
    g1 = flint.acb.zeta_zero(1).imag
    for w in decisive:
        lower[w] = {}
        for eta in ETAS:
            q = st.LehmanParams(w, eta, p.alpha, p.A, p.T)
            assert all(st.check_hypotheses(q).values()), (w, eta)
            lb = st.lower_bound_I(S[w], q)
            lower[w][eta] = {"lower_bound_I": lb.str(10), "positive": bool(lb > 0)}
        q = st.LehmanParams(w, ETAS[0], p.alpha, p.A, p.T)
        R = st.revers_R(q)
        moved = (S[w] - st.lehman_sum([g1], w, p.alpha)
                 + st.lehman_sum([g1 + arb("1e-6")], w, p.alpha))
        faults[w] = {
            "drop_R4_moves_bound_by": R["R4"].str(6),
            "gamma1_plus_1e-6_shift": abs(moved - S[w]).str(5),
            "gamma1_fault_leaves_own_ball": not bool(moved.overlaps(S[w])),
        }

    descriptive = {w: S[w].str(12) for w in omegas}
    return {"prereg": "PREREG_B2.md (commit e5b33dc90)", "checks": checks,
            "control": control_res, "decisive_rule": rule, "H_supported": h_supported,
            "lower_bounds_at_decisive_points": lower, "planted_faults": faults,
            "descriptive_grid": descriptive,
            "seconds_isolation_total": sum(d["seconds_zeros"] for d in shards)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--shards", type=Path, required=True)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    res = evaluate(a.shards)
    text = json.dumps(res, indent=1)
    if a.out:
        a.out.parent.mkdir(parents=True, exist_ok=True)
        a.out.write_text(text + "\n")
    print(json.dumps({k: v for k, v in res.items() if k != "descriptive_grid"}, indent=1))


if __name__ == "__main__":
    main()
