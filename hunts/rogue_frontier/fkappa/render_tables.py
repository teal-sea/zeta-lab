"""Render the extended coefficient tables from coefficients.json as
markdown fragments (used to fill RESULTS.md), plus the growth analysis of
the corrected diagonal.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/render_tables.py
"""

import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bian_engine import load_ckpt


def table(d, key, imax, label):
    print(f"\n### {label}\n")
    print("| i | value |")
    print("|---|---|")
    for i in range(1, imax + 1):
        if str(i) in d[key]:
            print(f"| {i} | {d[key][str(i)]} |")


def row_table(d, rk, kappas, imax, label):
    print(f"\n### {label}\n")
    header = "| i | " + " | ".join(f"kappa={k}" for k in kappas) + " |"
    print(header)
    print("|" + "---|" * (len(kappas) + 1))
    for i in range(1, imax + 1):
        cells = [d[rk].get(str(k), {}).get(str(i), "") for k in kappas]
        print(f"| {i} | " + " | ".join(cells) + " |")


def growth(d, key, label):
    seq = {int(k): Fraction(v) for k, v in d[key].items()}
    keys = sorted(seq)
    print(f"\n### growth analysis: {label}\n")
    print("| i | ratio r_i = C_{i+1}/C_i | a_i = i(|r_i|/2 - 1) |")
    print("|---|---|---|")
    for i in keys[3:-1]:
        r = seq[i + 1] / seq[i]
        a = (i + Fraction(1, 2)) * (abs(r) / 2 - 1)
        print(f"| {i} | {float(r):.5f} | {float(a):.4f} |")


def main():
    data = load_ckpt()
    skip = data["skip"]
    imax_s = max(int(k) for k in skip["diagonal"])
    table(skip, "diagonal_figure", imax_s,
          "published stable diagonal, extended (figure assembly, skip "
          "mode): C_{i-2,i}")
    row_table(skip, "rows_figure", [2, 3, 4], imax_s,
              "published table extension (figure assembly, skip mode)")
    if "corrected" in data:
        corr = data["corrected"]
        imax_c = max(int(k) for k in corr["diagonal"])
        table(corr, "diagonal", imax_c,
              "corrected stable diagonal (eq (10.1) assembly, corrected "
              "mode): C_{i-2,i}")
        row_table(corr, "rows", [2, 3, 4], imax_c,
                  "corrected table (eq (10.1) assembly, corrected mode)")
        growth(corr, "diagonal", "corrected stable diagonal")
    print("\n### cost scaling (seconds per level, both assemblies + six "
          "kappa rows, one core)\n")
    print("| i | skip mode | corrected mode |")
    print("|---|---|---|")
    for i in range(11, 21):
        ts = skip.get("timing", {}).get(str(i), "")
        tc = data.get("corrected", {}).get("timing", {}).get(str(i), "")
        print(f"| {i} | {ts} | {tc} |")


if __name__ == "__main__":
    main()
