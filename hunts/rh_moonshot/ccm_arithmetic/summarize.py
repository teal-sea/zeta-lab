"""Print the NOTES.md tables from the data/ JSON files (no computation).

Usage: .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/summarize.py [kind ...]
"""

from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")


def _f(s):
    try:
        return float(s)
    except (TypeError, ValueError):
        return float("nan")


def _c(cs):
    return float(Fraction(cs))


def _sat(c, N):
    """band edge om_N over the Nyquist height 2 pi c (degree 1)."""
    L = math.log(c)
    return (2 * math.pi * N / L) / (2 * math.pi * c)


def table(kind):
    path = os.path.join(DATA, f"measure_{kind}.json")
    if not os.path.exists(path):
        print(f"(no {path})")
        return
    d = json.load(open(path))["cells"]
    rows = sorted(d.values(), key=lambda r: (_c(r["c"]), r["N"]))
    q = {"zeta": 1, "dh": 5}.get(kind)
    print(f"\n### {kind}\n")
    hdr = "| c | N | lambda_1 | lambda_2 | misfit r | dist^2 R_2 | dist^2 R_4 | a2 | kappa | sup abs err [0,T] | rel err Im 0.45 | zeros matched / Xi zeros | Sturm | mu_2 (bottom on R_2^perp) |"
    print(hdr)
    print("|" + "---|" * (hdr.count("|") - 1))
    for r in rows:
        c = _c(r["c"])
        lam = r["lambda_mid"]
        a2 = _f(r.get("fit_a2"))
        if q is not None:
            kappa = a2 * 4 * math.pi**2 * c / q
        elif kind in ("dedekind", "epstein"):
            tstar = 2 * math.pi * math.sqrt(c / 23)
            kappa = a2 * math.pi * tstar
        else:
            kappa = float("nan")
        z = r.get("zeros")
        zs = f"{z['n_matched_1e-8']}/{z['n_Xi']} (max {z['max_dev']})" if z else "-"
        st = r.get("sturm_extra_zeros", "-")
        cap = r.get("capture_m2", {})
        print(
            f"| {r['c']} | {r['N']} | {_f(lam[0]):.3e} | {_f(lam[1]):.3e} | {_f(r['misfit0']):.2e} | "
            f"{_f(r['proj_residual'][2]):.2e} | {_f(r['proj_residual'][4]):.2e} | {a2:.3e} | {kappa:.2f} | "
            f"{_f(r['compact']['0']['abs']):.2e} | {_f(r['compact']['0.45']['rel']):.2e} | {zs} | {st} | {_f(cap.get('mu')):.2e} |"
        )
    if kind == "dh":
        print("\nDH real zeros of F_v1 and F_v2 inside the on-line gap (83.109, 87.647):\n")
        for r in rows:
            if "dh_gap_zeros_v1_v2" in r:
                print(f"- c = {r['c']}, N = {r['N']}: v1 {r['dh_gap_zeros_v1_v2'][0]}, v2 {r['dh_gap_zeros_v1_v2'][1]}")


def rigidity():
    for name in sorted(os.listdir(DATA)):
        if not name.startswith("rigidity_") or not name.endswith(".json"):
            continue
        d = json.load(open(os.path.join(DATA, name)))
        print(f"\n### rigidity c = {d['c']}, N = {d['N']}, atom at log {d['q']}\n")
        print(
            f"lambda_1 = {d['lambda1']}, lambda_2 = {d['lambda2']}, dlambda_1/dy = {d['dlam_dy']}, "
            f"eps_pos = lambda_1/|dlam/dy| = {d['eps_positivity_scale']}, eps_gap = (lambda_2 - lambda_1)/||dA||_F = {d['eps_gap_scale']}\n"
        )
        print("| eps | lambda_1 (ball) | first-order prediction | LDL inertia at 0 (pos, neg, conclusive) | dist^2 to R_4 | misfit r | Sturm |")
        print("|---|---|---|---|---|---|---|")
        for r in sorted(d["runs"], key=lambda r: (-int(r["eps"].split("e-")[1]), r["eps"][0])):
            print(
                f"| {r['eps']} | {r['lambda1']} | {r['predicted_lambda1']} | {tuple(r['ldl_inertia_at_0'])} | "
                f"{r['proj_residual_R4']} | {r['misfit0']} | {r['sturm_extra_zeros']} |"
            )


def main(argv):
    kinds = argv[1:] or ["zeta", "dh", "dedekind", "epstein", "wa"]
    for k in kinds:
        if k == "rigidity":
            rigidity()
        else:
            table(k)


if __name__ == "__main__":
    main(sys.argv)
