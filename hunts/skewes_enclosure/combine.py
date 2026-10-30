"""Combine shard JSONs into the full zero sum, check completeness, apply the gate.

    .venv/bin/python hunts/skewes_enclosure/combine.py --target chao_plymen

Checks, each decided on balls or exact integers:

1. shards 1..K are present and contiguous (n0 = (k-1)*1e5 + 1, 1e5 zeros each,
   balls ordered and disjoint within each shard, and shard k's last zero below
   shard k+1's first);
2. the last zero is below T, and Arb's Turing count gives N(T) = K*1e5, so the
   sum is over exactly the zeros with 0 < gamma <= T (rigorous completeness on
   route 1 only; mpmath ``nzeros``, code-disjoint and float grade, agrees on N(T)
   at both cutoffs, see ``test_cutoffs_by_the_mpmath_route``);
3. every route-2 sampled bracket showed a sign change;
4. the gate: Revers's printed S* against the ball sum;
5. the lower bound -1 - S - R at each eta of Revers's resizing table;
6. planted faults at full scale: R4 dropped, and gamma_1 replaced by gamma_1 + 1e-6
   (the sum is a sum of terms, so the faulted S is S - term(gamma_1) +
   term(gamma_1 + 1e-6) exactly). Each must visibly move the result.
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
ETAS = {
    "chao_plymen": ["0.00016", "0.00014", "0.00012", "0.0001063", "0.0001061", "0.000106"],
    "saouter_demichel": ["0.0000228", "0.00002", "0.000018", "0.000016", "0.0000159",
                         "0.0000158"],
}
#: [Rev25]'s worst-case zero-error budgets Delta S1 + Delta S2 at each target.
REVERS_BUDGET = {"chao_plymen": "1.89856e-5", "saouter_demichel": "2.60111e-5"}


def combine(target: str, shard_dir: Path) -> dict:
    flint.ctx.prec = st.PREC
    p = st.CHAO_PLYMEN if target == "chao_plymen" else st.SAOUTER_DEMICHEL
    n_total = st.N_ZEROS[target]
    k_max = n_total // SHARD
    shards = []
    for k in range(1, k_max + 1):
        f = shard_dir / f"shard_{k:03d}.json"
        if not f.is_file():
            raise SystemExit(f"missing {f}")
        shards.append(json.loads(f.read_text()))

    checks = {}
    checks["contiguous_indices"] = all(
        d["n0"] == (k - 1) * SHARD + 1 and d["num"] == SHARD
        for k, d in enumerate(shards, start=1))
    checks["ordered_within_shards"] = all(d["ordered_disjoint"] for d in shards)
    checks["ordered_across_shards"] = all(
        bool(arb(a["last"]) < arb(b["first"])) for a, b in zip(shards, shards[1:]))
    checks["last_zero_below_T"] = bool(arb(shards[-1]["last"]) < arb(p.T))
    n_T = zl.count_below(p.T)
    checks["turing_count_N(T)"] = n_T
    # Complete means every structural check holds and Arb's count agrees: the
    # count alone says nothing about what the shards contain. (Review, 2026-10-30.)
    checks["complete"] = (n_T == n_total and checks["contiguous_indices"]
                          and checks["ordered_within_shards"]
                          and checks["ordered_across_shards"]
                          and checks["last_zero_below_T"])
    checks["route2_all_sign_changes"] = all(d["route2_sample"]["all_sign_changes"]
                                             for d in shards)
    checks["route2_sample_size"] = sum(d["route2_sample"]["size"] for d in shards)

    S = arb(0)
    for d in shards:
        S += arb(d["partial_sums"][target])
    s_star = arb(st.REVERS_S_STAR[target])
    diff = abs(S - s_star)
    gate = {
        "S": S.str(25),
        "S_radius": S.rad().str(5),
        "revers_S_star": st.REVERS_S_STAR[target],
        "abs_difference": diff.str(5),
        "S_star_inside_ball": bool(S.overlaps(s_star)),
        "within_revers_budget": bool(diff <= arb(REVERS_BUDGET[target])),
    }
    lower = {}
    for eta in ETAS[target]:
        q = st.LehmanParams(p.omega, eta, p.alpha, p.A, p.T)
        assert all(st.check_hypotheses(q).values()), eta
        lb = st.lower_bound_I(S, q)
        lower[eta] = {"lower_bound_I": lb.str(10), "positive": bool(lb > 0)}
    faults = {}
    eta_edge = ETAS[target][-1]
    q = st.LehmanParams(p.omega, eta_edge, p.alpha, p.A, p.T)
    R = st.revers_R(q)
    no_r4 = -1 - S - (R["R"] - R["R4"])
    faults["drop_R4"] = {"eta": eta_edge, "R4": R["R4"].str(6),
                         "lower_bound_without_R4": no_r4.str(8),
                         "sign_flips_to_positive": bool(no_r4 > 0)}
    g1 = flint.acb.zeta_zero(1).imag
    moved = (S - st.lehman_sum([g1], p.omega, p.alpha)
             + st.lehman_sum([g1 + arb("1e-6")], p.omega, p.alpha))
    faults["perturb_gamma_1_by_1e-6"] = {
        "S_faulted": moved.str(15),
        "shift": abs(moved - S).str(5),
        "faulted_S_still_contains_revers_S_star": bool(moved.overlaps(s_star)),
    }
    return {"target": target, "params": p.__dict__, "checks": checks, "gate": gate,
            "lower_bounds": lower, "planted_faults": faults,
            "seconds_isolation_total": sum(d["seconds_zeros"] for d in shards)}


def failed_checks(checks: dict) -> list[str]:
    """Names of the boolean checks that did not hold."""
    return [k for k, v in checks.items() if v is False]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", choices=["chao_plymen", "saouter_demichel"], required=True)
    ap.add_argument("--shards", type=Path, default=HERE / "shards")
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    res = combine(a.target, a.shards)
    text = json.dumps(res, indent=1)
    if a.out:
        a.out.write_text(text + "\n")
    print(text)
    bad = failed_checks(res["checks"])
    if bad:
        raise SystemExit(f"checks failed: {bad}")


if __name__ == "__main__":
    main()
