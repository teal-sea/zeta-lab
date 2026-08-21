"""Render the final RESULTS.md table and placeholder values from the JSONs.

Prints (a) the markdown table block to results/table.md, (b) every value the
RESULTS.md placeholders need, so no digit is ever transcribed by hand.
"""

from __future__ import annotations

import json
from math import log, sqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
C = 0.046191417932242067628620495813


def sig(x: float, n: int = 12) -> str:
    return f"{x:.{n}g}"


def main() -> None:
    ladder = json.loads((HERE / "results" / "ladder.json").read_text())["records"]
    supp_path = HERE / "results" / "ladder_supplement.json"
    supp = json.loads(supp_path.read_text())["records"] if supp_path.exists() else []
    have = {r["N"] for r in ladder}
    recs = [r for r in ladder if "d2" in r] + [r for r in supp if r["N"] not in have]
    recs.sort(key=lambda r: r["N"])

    lines = [
        "| N | d_N^2 (ball midpoint) | ball radius | d_N^2 log N / C | cond(G) |",
        "|---|---|---|---|---|",
    ]
    for r in recs:
        N = r["N"]
        star = "*" if r["headline_prec"] == 128 else ""
        mid = sig(r["d2"]["mid"], 15)
        rad = f"{r['d2']['rad']:.1e}"
        ratio = f"{r['d2_logN_over_C']['mid']:.6f}" if N > 1 else "(log 1 = 0)"
        cond = f"{r['cond_float64']:.1e}" if r.get("cond_float64") else "1.0"
        lines.append(f"| {N}{star} | {mid} | {rad} | {ratio} | {cond} |")
    table = "\n".join(lines)
    (HERE / "results" / "table.md").write_text(table + "\n")
    print(table)
    print()

    an = json.loads((HERE / "results" / "analysis.json").read_text())
    for N in (2048, 3072, 4096):
        r = next((x for x in recs if x["N"] == N), None)
        if r:
            print(f"N={N}: d2={sig(r['d2']['mid'],15)} rad={r['d2']['rad']:.1e} "
                  f"ratio={r['d2_logN_over_C']['mid']:.6f} "
                  f"cond={r['cond_float64']:.3e} dN={sqrt(r['d2']['mid']):.6f} "
                  f"dNsqrtlogN={sqrt(r['d2']['mid']*log(N)):.6f}")
    big = max(r["N"] for r in recs)
    r = next(x for x in recs if x["N"] == big)
    if "bcf_upper" in r:
        print(f"BCF at N={big}: U/d2={r['bcf_upper']['mid']/r['d2']['mid']:.3f} "
              f"UlogN={r['bcf_upper_logN']['mid']:.4f}")
    else:
        rb = max((x for x in recs if "bcf_upper" in x), key=lambda x: x["N"])
        print(f"BCF at N={rb['N']}: U/d2={rb['bcf_upper']['mid']/rb['d2']['mid']:.3f} "
              f"UlogN={rb['bcf_upper_logN']['mid']:.4f}")
    print("conditioning:", an["conditioning"]["prefactor"],
          an["conditioning"]["power_law_exponent"])
    print("coeff_shape:", an.get("coeff_shape"))
    print("anchors:", an.get("external_anchors"))
    print("fits:", json.dumps(an.get("fits"), indent=1))
    # A(N) for the solve-radius law at the largest ladder N with solves
    for r in ladder:
        if r.get("solves") and r["N"] in (64, 1024, 4096):
            for s in r["solves"]:
                if s.get("ok"):
                    print(f"A({r['N']}) from P={s['prec']}: "
                          f"{s['d2_rad'] * 2**s['prec']:.3g}")


if __name__ == "__main__":
    main()
