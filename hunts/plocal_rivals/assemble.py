"""Assemble zeros.json from the two merged census files, the abscissa bounds,
and a PARI recomputation of the lowest off-line zero of each F_q.

    .venv/bin/python hunts/plocal_rivals/assemble.py MERGED_Q17.json MERGED_Q73.json

Writes ``zeros.json`` next to this file.  Grades are recorded inside it.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

OUT = os.path.join(HERE, "zeros.json")

#: the decided headline rationals of the phase abscissa (test_rivals.py pins them)
SIGMA_STAR = {17: "1.09896904163", 73: "1.0445906373"}
PHASE_ROOT = {17: ("1.0989690416287099417", "1.0989690416290103236"),
              73: ("1.0445906372787647953", "1.044590637279698182")}
DOMINATION = {17: ("1.5842597817", "1.5842597818"), 73: ("1.6148802929", "1.6148802930")}


def pari_zero(q: int, re: float, im: float) -> dict:
    """PARI's own Newton iteration on A L(s, chi) + conj(A) L(s, chi-bar)."""
    import cypari2

    pari = cypari2.Pari()
    pari.set_real_precision(45)
    pari(f"G = znstar({q}, 1); g = lift(znprimroot({q}))")
    pari("C = 0; forvec(v = vector(#G.cyc, j, [0, G.cyc[j] - 1]), "
         "if(chareval(G, v~, g) == 1/4 && charorder(G, v~) == 4, C = v~; break))")
    pari("Cb = vector(#C, j, (G.cyc[j] - C[j]) % G.cyc[j])~")
    pari("L = lfuncreate([G, C]); Lb = lfuncreate([G, Cb]); k = tan(arg(lfunrootres(L)[3])/2)")
    pari("A = (1 - I*k)/2")
    pari("Fp(s) = A*lfun(L, s) + conj(A)*lfun(Lb, s)")
    pari("dFp(s) = A*lfun(L, s, 1) + conj(A)*lfun(Lb, s, 1)")
    t0 = time.time()
    pari(f"z = {re!r} + {im!r}*I; for(i = 1, 12, z = z - Fp(z)/dFp(z))")
    return {
        "re": str(pari("real(z)")).replace(" E", "e"),
        "im": str(pari("imag(z)")).replace(" E", "e"),
        "abs_F": str(pari("abs(Fp(z))")).replace(" E", "e"),
        "seconds": round(time.time() - t0, 2),
        "route": "PARI/GP lfun on the two characters of lfuncreate([znstar(q,1), chi]), "
                 "k from lfunrootres, Newton with lfun(L, s, 1)",
    }


def summarise(m: dict) -> dict:
    zs = m["zeros"]
    betas = [z["re_A"] for z in zs]
    return {
        "height": m["height"],
        "n_windows": m["n_windows"],
        "N_total_A": m["N_total_A"],
        "N_total_B": m["N_total_B"],
        "n_line_sign_changes_A": m["n_line_A"],
        "n_line_sign_changes_B": m["n_line_B"],
        "n_zeros_right_of_line": m["n_right"],
        "all_windows_close_A": m["all_windows_close_A"],
        "all_windows_close_B": m["all_windows_close_B"],
        "unit_boxes_disjoint_B": m["unit_boxes_disjoint_B"],
        "parity_A": m["parity_A"],
        "parity_B": m["parity_B"],
        "every_zero_in_decided_unit_box_B": all(z["unit_N_B"] == 1 for z in zs),
        "every_zero_in_decided_tiny_box_B": all(z["tiny_N_B"] == 1 for z in zs),
        "lowest_offline_height": min((z["im_A"] for z in zs), default=None),
        "max_real_part_found": max(betas, default=None),
        "min_real_part_found": min(betas, default=None),
    }


def main() -> None:
    merged = {}
    for path in sys.argv[1:]:
        with open(path) as fh:
            d = json.load(fh)
        merged[int(d["q"])] = d
    out = {
        "hunt": "plocal_rivals",
        "hunt_number": 149,
        "assembled": time.strftime("%Y-%m-%d"),
        "function": "F_q(s) = c L(s, chi) + conj(c) L(s, chi-bar), c = (1 - i k)/2, "
                    "chi of order 4 mod q with chi(g) = i at the least primitive root g",
        "grades": {
            "route_A": "measured: mpmath fp evaluation, folded argument principle, "
                       "right-box winding counts, Newton to |F| < 1e-11",
            "route_B": "enclosure-carrying given the classical functional equation, the "
                       "Gauss-sum root number and the cited Rademacher bound: Arb balls, "
                       "winding.py's chord-tube rule, decided sign changes and decided boxes",
            "pari": "measured: one zero per q recomputed by PARI's own Newton iteration",
            "abscissa": "enclosure-carrying (Arb), strip2.py's Euler-phase method ported to q",
        },
        "accounting": "per window n_box = n_line + 2 n_right; n_box from the folded count "
                      "N(0, T) = Psi(T)/pi at the window ends, n_line from sign changes of Z "
                      "on the route's own grid plus its own signs at the ends, n_right from "
                      "right-box counts (route A) or decided unit boxes (route B)",
        "abscissa": {
            str(q): {
                "phase_root_bracket": list(PHASE_ROOT[q]),
                "decided_sigma_star": SIGMA_STAR[q],
                "domination_bracket": list(DOMINATION[q]),
                "statement": f"every zero of F_{q} has 1 - {SIGMA_STAR[q]} < Re s < {SIGMA_STAR[q]}",
            } for q in sorted(merged)
        },
        "cases": {},
    }
    for q, m in sorted(merged.items()):
        case = {"summary": summarise(m), "zeros": m["zeros"], "windows": m["windows"],
                "base_B": m["base_B"]}
        if m["zeros"]:
            z0 = min(m["zeros"], key=lambda z: z["im_A"])
            pz = pari_zero(q, z0["re_A"], z0["im_A"])
            x0, x1, y0, y1 = (Fraction(v) for v in z0["tiny_box_B"])
            pz["inside_route_B_tiny_box"] = bool(
                x0 < Fraction(pz["re"]) < x1 and y0 < Fraction(pz["im"]) < y1)
            case["third_route"] = pz
        out["cases"][str(q)] = case
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
