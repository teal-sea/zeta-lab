"""Validation battery for the Vasyunin Gram implementation.

Four independent routes to the same numbers, plus external anchors.
Writes results/validation.json and prints a human-readable summary.

Routes:
  A. arb balls, Vasyunin formula, reduced cotangent sums (production arm).
  B. mpmath, Vasyunin formula, unreduced O(q) sums (independent library and
     independent summation: no pairing trick, no reflection identity).
  C. mpmath quadrature of int_0^infty {u/j}{u/k} u^-2 du: piecewise closed
     form + exact trigamma tail. No cotangent anywhere.
  D. same as C but with adaptive mp.quad on every piece (slowest, most
     literal-minded independent check).

Run: .venv/bin/python validate.py
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mpmath import mp  # noqa: E402

from vasyunin import (  # noqa: E402
    GramBuilder,
    d2_mp,
    gram_entry_mp,
    gram_entry_quad,
    rhs_quad,
    solve_d2,
)

HERE = Path(__file__).resolve().parent


def arb_to_mpf(a, dps: int = 90):
    """Exact midpoint of an arb ball as an mpf (mantissa * 2^exponent).

    Created inside a high-precision context: mp.mpf construction rounds at
    the ambient precision, and the ambient default (53 bits) would floor
    every comparison at ~1e-17.
    """
    man, exp = a.mid().man_exp()
    with mp.workdps(dps):
        return +(mp.mpf(int(man)) * mp.power(2, int(exp)))


PAIRS = [
    (1, 1), (1, 2), (1, 3), (2, 3), (3, 4), (2, 5), (5, 7), (5, 13),
    (4, 6), (6, 9), (8, 12), (12, 35), (9, 64), (17, 101), (64, 81),
]
ADAPTIVE_PAIRS = [(2, 3), (5, 7)]


def main() -> None:
    out: dict = {"pairs": [], "b": [], "d2_cross": [], "external": {}}
    gb = GramBuilder(prec=256)
    gb.extend(128)

    print("== Gram entries: four routes ==")
    for (j, k) in PAIRS:
        va = gb.entry(j, k)
        vb = gram_entry_mp(j, k, dps=50)
        vc = gram_entry_quad(j, k, dps=35, M=80)
        rec = {
            "j": j, "k": k,
            "arb": va.str(40),
            "mp_vasyunin": mp.nstr(vb, 40),
            "quad_closed": mp.nstr(vc, 25),
        }
        with mp.workdps(90):
            rec["diff_arb_mp"] = float(abs(arb_to_mpf(va) - vb))
            rec["diff_arb_quad"] = float(abs(arb_to_mpf(va) - vc))
        if (j, k) in ADAPTIVE_PAIRS:
            vd = gram_entry_quad(j, k, dps=25, M=60, adaptive=True)
            rec["quad_adaptive"] = mp.nstr(vd, 20)
            with mp.workdps(90):
                rec["diff_arb_quad_adaptive"] = float(abs(arb_to_mpf(va) - vd))
        out["pairs"].append(rec)
        print(f"  ({j:3d},{k:3d}) arb-vs-mp {rec['diff_arb_mp']:.2e}  "
              f"arb-vs-quad {rec['diff_arb_quad']:.2e}", flush=True)

    print("== b_k: closed form vs quadrature ==")
    for k in (1, 2, 3, 5, 12, 64):
        with mp.workdps(45):
            closed = (1 - mp.euler + mp.log(k)) / k
        q = rhs_quad(k, dps=30)
        with mp.workdps(60):
            dv = float(abs(closed - q))
        rec = {"k": k, "closed": mp.nstr(closed, 30), "quad": mp.nstr(q, 20),
               "diff": dv}
        out["b"].append(rec)
        print(f"  b_{k}: diff {rec['diff']:.2e}", flush=True)

    print("== d_N^2: arb pipeline vs mpmath pipeline ==")
    for N in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32):
        t0 = time.time()
        G, _ = gb.gram(N, want_float=False)
        b = gb.rhs(N)
        s = solve_d2(G, b, prec_solve=192)
        vm = d2_mp(N, dps=50)
        with mp.workdps(90):
            diff = float(abs(arb_to_mpf(s["d2"]) - vm))
        contained = bool(diff <= float(s["d2"].rad()) + 1e-45)
        rec = {"N": N, "arb": s["d2"].str(40), "mp": mp.nstr(vm, 40),
               "diff": diff, "mp_inside_ball_or_1e-45": contained,
               "t": round(time.time() - t0, 1)}
        out["d2_cross"].append(rec)
        print(f"  N={N}: diff {diff:.2e} (ball rad {float(s['d2'].rad()):.1e})",
              flush=True)

    # external anchors
    with mp.workdps(30):
        C = mp.mpf("0.046191417932242067628620495813")
        out["external"]["sqrt_C"] = mp.nstr(mp.sqrt(C), 10)
    out["external"]["landreau_richard"] = {
        "fit_aN_at_20000": 0.21377,
        "sqrt_C": 0.21492,
        "figure1_range": "d_n from ~0.10 down to ~0.066 over n = 1..20000",
        "figure2_window": "d_n crosses [0.07, 0.08] during n ~ 2000..10000",
    }

    (HERE / "results" / "validation.json").write_text(json.dumps(out, indent=1))
    print("written results/validation.json")


if __name__ == "__main__":
    main()
