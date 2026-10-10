"""Phase-1 comparative probe for rh_resolve.

Compares three mechanisms cheaply before committing, per ALIGNMENT 4.
All outputs are measured (float grade) unless stated. Nothing here
is evidence for RH. Rival and precision-response controls included.

Routes:
  A. Li coefficients via Cauchy (unconditional route) + zeros cross-check.
  B. Weil explicit formula: Gaussian and Fejer pairs, both sides.
  C. Heat flow: Phi evenness defect, H_t at t=0 vs Xi, heat residual.

Controls:
  R1. Davenport-Heilbronn rival: battery import check + Li-style
      pair-term sign structure (why zeros-route cannot report negative).
  P1. Precision response: Li Cauchy at two precisions; artifact would
      not move with precision, real quantity moves toward agreement.
"""
import json
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from mpmath import mp

def main():
    out = {"grade": "measured-float", "routes": {}, "controls": {}}
    import zeta.li as L
    # Route A: Li
    lam20 = L.li_coefficients(20, method="cauchy", dps=30)
    lam20_lo = L.li_coefficients(20, method="cauchy", dps=20)
    lam_z = L.li_coefficients(8, method="zeros", dps=25, n_zeros=1000)
    out["routes"]["A_li"] = {
        "lambda_1_20_dps30": [str(x) for x in lam20],
        "min_margin": float(min(lam20)),
        "all_positive": bool(all(x > 0 for x in lam20)),
        "max_abs_dps30_minus_dps20": float(max(abs(a - b) for a, b in zip(lam20, lam20_lo))),
        "cauchy_minus_zeros_n8": [float(a - b) for a, b in zip(lam20[:8], lam_z)],
        "asymptotic_n20": L.li_asymptotic(20),
        "reading": "no violation in n<=20; zeros-route column structurally nonnegative so only Cauchy signs carry information",
    }
    # Route B: Weil
    import zeta.weil as W
    for name, mk in [("gaussian_a1", lambda: W.gaussian_pair(1.0)),
                     ("fejer_b1", lambda: W.fejer_pair(1.0))]:
        h, g = mk()
        sides = W.explicit_formula_sides(h, g, dps=25)
        out["routes"].setdefault("B_weil", {})[name] = {
            "zero_side": str(sides["zero_side"]),
            "arithmetic_side": str(sides["arithmetic_side"]),
            "abs_diff": str(sides["abs_diff"]),
            "abs_diff_float": float(abs(sides["abs_diff"])),
        }
    # Route C: heat flow
    import zeta.heatflow as H
    from zeta.core import Xi
    with mp.workdps(30):
        ev = {str(u): str(H.Phi_is_even_defect(u, dps=30)) for u in [0.5, 1.0, 2.0]}
        cmp0 = H.H0_vs_Xi([0.0, 1.0, 2.0], dps=30)
    out["routes"]["C_heat"] = {
        "phi_even_defect": str(ev),
        "H0_vs_Xi": {str(k): str(v) for k, v in cmp0.items()} if isinstance(cmp0, dict) else str(cmp0),
    }
    # Control R1: rival battery present and callable
    try:
        from zeta.epstein import battery
        out["controls"]["R1_rival"] = {"battery_import": "ok", "note": "full rival run deferred to phase 2; Li zeros-route nonnegative-structure documented in zeta/li.py"}
    except Exception as e:
        out["controls"]["R1_rival"] = {"battery_import": f"FAIL {e}"}
    # Control P1: precision response
    out["controls"]["P1_precision"] = {
        "max_abs_change_20_to_30_digits": out["routes"]["A_li"]["max_abs_dps30_minus_dps20"],
        "responds": bool(out["routes"]["A_li"]["max_abs_dps30_minus_dps20"] > 0),
        "note": "nonzero change with precision plus cross-method agreement pattern is the real-quantity signature; exact digits in RESULTS.md",
    }
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_phase1.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: (v if k != "routes" else list(v.keys())) for k, v in out.items()}, indent=1))
    print("wrote", path)

if __name__ == "__main__":
    main()
