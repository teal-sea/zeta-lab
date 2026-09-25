"""Collect the numbers RESULTS.md quotes from the run JSONs into summary.json.

No computation of the form happens here; this only reads grid_*.json,
crossing.json, edge_*.json, repro.json, precision_check.json, factA_check.json,
and the theory-handoff files (epstein_crossing.json, epstein_offline.json, zeta_pole_N*.json).
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
mp.dps = 40


def m(s):
    s = str(s).strip()
    if s.startswith("["):
        s = s[1:].split("+/-")[0].strip().rstrip("]").strip()
    return mp.mpf(s) if s else mp.mpf(0)


def load(name):
    p = os.path.join(HERE, name)
    return json.load(open(p)) if os.path.exists(p) else None


def grid_summary(kind, N):
    d = load(f"grid_{kind}_N{N}.json")
    if d is None:
        return None
    cells = d["cells"]
    ks = sorted(cells, key=Fraction)
    out = {"n_cells": len(ks), "hardened_all": d["meta"].get("hardened_all")}
    # edge law
    kap, K, cancel = [], [], []
    for k in ks:
        h = d["hf"].get(k)
        if not h:
            continue
        mu = m(cells[k]["mu0"])
        hv = m(h["total_dlam_dL"])
        lam = m(cells[k]["lam1"])
        pieces = [abs(m(h[p])) for p in ("pole", "arch", "prime") if p in h]
        cancel.append(float(mp.log10(max(pieces) / abs(hv))))
        if abs(mu) > 0:
            kap.append((float(Fraction(k)), float(-hv / mu**2), float(mu)))
        if lam > 0:
            K.append((float(Fraction(k)), float(-hv / lam)))
    mus = [abs(x[2]) for x in kap]
    mu_med = sorted(mus)[len(mus) // 2]
    good = [x[1] for x in kap if abs(x[2]) > 0.2 * mu_med]
    out["kappa_all_range"] = [min(x[1] for x in kap), max(x[1] for x in kap)]
    out["kappa_where_mu0_gt_0.2_median"] = {"n": len(good), "min": min(good), "max": max(good),
                                            "median": sorted(good)[len(good) // 2]}
    out["neg_dlogLam_dL_on_positive_cells"] = {"min": min(x[1] for x in K), "max": max(x[1] for x in K),
                                               "by_c": [[c, round(v, 2)] for c, v in K]}
    out["hf_piece_cancellation_digits"] = {"min": min(cancel), "max": max(cancel)}
    # monotonicity in c at fixed N (midpoint comparison; DH also hardened brackets)
    inc = []
    for a, b in zip(ks, ks[1:]):
        if m(cells[b]["lam1"]) > m(cells[a]["lam1"]):
            inc.append([a, b])
    out["lambda_increases_between_neighbours"] = inc
    hard = d.get("hardened", {})
    hinc = []
    for a, b in zip(ks, ks[1:]):
        if a in hard and b in hard and hard[b].get("lower") and hard[a].get("upper"):
            if mp.mpf(hard[b]["lower"]) > mp.mpf(hard[a]["upper"]):
                hinc.append([a, b])
    out["hardened_increases"] = hinc
    # transports by step
    steps = {}
    for pk, p in d["pairs"].items():
        a, b = pk.split("->")
        h = Fraction(b) - Fraction(a)
        dL = math.log(float(Fraction(b)) / float(Fraction(a)))
        s = steps.setdefault(str(h), {"ze_1mov": [], "dil_1mov": [], "dil_up_over_dL2": [],
                                      "ze_rq_minus_lam": [], "dlam": [], "prime_new_lower": [],
                                      "sandwich_violations": 0})
        s["ze_1mov"].append(float(m(p["zero_ext"]["one_minus_overlap"])))
        s["dil_1mov"].append(float(m(p["dilation"]["one_minus_overlap"])))
        s["dil_up_over_dL2"].append(float(m(p["dilation"]["upper_bracket_Rc2(v)-lam(c)"])) / dL**2)
        s["ze_rq_minus_lam"].append(float(m(p["zero_ext"]["rq_minus_lam_c"])))
        s["dlam"].append(float(m(p["dlam"])))
        pn = p["dilation"]["lower_parts"]["prime_new"]
        if pn != "0" and not pn.startswith("[+/-"):
            s["prime_new_lower"].append([pk, float(m(pn)), float(m(p["dlam"]))])
        s["sandwich_violations"] += int(p["sandwich_violated"])
    for h, s in steps.items():
        for q in ("ze_1mov", "dil_1mov", "dil_up_over_dL2", "ze_rq_minus_lam", "dlam"):
            v = s[q]
            s[q] = {"min": min(v), "max": max(v), "max_abs": max(abs(x) for x in v)}
        s["dlam_max_abs"] = s["dlam"]["max_abs"]
    out["steps"] = steps
    if kind == "dh":
        zs = []
        for k in ks:
            z = cells[k]["zero_side"]
            zs.append([float(Fraction(k)), float(m(cells[k]["lam1"])), float(m(z["Q1"])),
                       float(m(z["S_on_T120"])), float(m(z["rest_lam_minus_Q1_Q2_Son"]))])
        out["zero_side_c_lam_Q1_Son_rest"] = zs
    return out


def main():
    s = {}
    r = load("repro.json")
    if r:
        s["repro_max_rel_dev"] = max(float(x["rel_dev"]) for x in r["recorded"])
        s["repro_route_b_max_rel_dev"] = max(float(x["rel_dev"]) for x in r["route_b"])
        s["repro_all_temple_conclusive"] = all(x["temple"]["conclusive"] for x in r["recorded"])
    c = load("crossing.json")
    if c:
        s["crossing"] = {N: {k: v[k] for k in ("c_pos_float", "c_neg_float", "hardened_negative",
                                               "hardened_positive", "c_neg_rq_upper", "linear_interp_c_star")}
                         | {"zeta_ldl": v["zeta_control_at_c_neg"]["ldl"]["inertia_at_0"]}
                         for N, v in c["by_N"].items()}
    for kind, N in (("dh", 64), ("dh", 128), ("zeta", 64), ("zeta", 128)):
        g = grid_summary(kind, N)
        if g:
            s[f"grid_{kind}_N{N}"] = g
    for kind in ("dh", "zeta"):
        e = load(f"edge_{kind}.json")
        if e:
            s[f"edge_{kind}"] = {k: {"lam1": v["lam1"][:18], "mu0": v["mu0"][:16], "kappa": v["kappa"][:12],
                                     "neg_dlogLam_dL": v["neg_dlogLam_dL"][:12]} for k, v in e["cells"].items()}
    p = load("precision_check.json")
    if p:
        s["precision_check"] = {k: {"prec_x2": v["prec_x2"], "eps_x2^-24": v["eps_x2^-24"]} for k, v in p["cells"].items()}
    fa = load("factA_check.json")
    if fa:
        s["factA_check"] = {k: {"lam_c": v["lam_c"][:18],
                                "rows": {n: {"rel_to_lam_c": r["rel_to_lam_c"],
                                             "one_minus_proj_norm2": r["one_minus_proj_norm2"][:12],
                                             "dev_over_missing_norm": float(m(r["rq_minus_lam_c"]) / m(r["one_minus_proj_norm2"]))}
                                         for n, r in v["rows"].items()}}
                            for k, v in fa["cases"].items()}
    # theory handoff (s9)
    ec = load("epstein_crossing.json")
    if ec:
        s["epstein_crossing"] = {k: {q: v[q] for q in ("c_pos_float", "c_neg_float", "lam1_at_c_neg",
                                                       "hardened_negative_two_routes", "dedekind_n_neg_at_c_neg")}
                                 for k, v in ec["runs"].items()}
    eo = load("epstein_offline.json")
    if eo:
        s["epstein_offline"] = {"boxes": eo["boxes"], "roots": [r for r in eo["roots"] if "root" in r]}
    for N in (64, 128):
        zp = load(f"zeta_pole_N{N}.json")
        if zp:
            cells = zp["cells"]
            r5 = [v["mu2_over_lam2"] for k, v in cells.items() if Fraction(k) >= 5]
            s[f"zeta_pole_N{N}"] = {
                "n_cells": len(cells),
                "mu2_over_lam2_c_ge_5": [min(r5), max(r5)],
                "mu2_over_lam1": [min(v["mu2_over_lam1"] for v in cells.values()), max(v["mu2_over_lam1"] for v in cells.values())],
                "interlacing_all": all(v["interlacing_mid"] for v in cells.values()),
                "full_pd_all_hardened": all(v["inertia_full_at_0"][2] and v["inertia_full_at_0"][1] == 0 for v in cells.values()),
                "polefree_one_negative_all_hardened": all(v["inertia_polefree_at_0"][2] and v["inertia_polefree_at_0"][1] == 1 for v in cells.values()),
            }
    with open(os.path.join(HERE, "summary.json"), "w") as f:
        json.dump(s, f, indent=1)
    print(json.dumps({k: v for k, v in s.items() if not k.startswith("grid")}, indent=1)[:6000])
    for k, v in s.items():
        if k.startswith("grid"):
            print(k, {q: v[q] for q in ("n_cells", "hardened_all", "kappa_all_range", "kappa_where_mu0_gt_0.2_median",
                                        "hf_piece_cancellation_digits", "lambda_increases_between_neighbours",
                                        "hardened_increases")})
            for h, st in v["steps"].items():
                print("   step", h, {q: st[q] for q in ("ze_1mov", "dil_1mov", "dil_up_over_dL2", "ze_rq_minus_lam", "sandwich_violations")},
                      "dlam_max_abs", st["dlam_max_abs"])


if __name__ == "__main__":
    main()
