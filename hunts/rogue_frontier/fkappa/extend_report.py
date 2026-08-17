"""Trajectory report for the extended corrected tables.

Prints, per target: the new terms, the partial simple-zeros bound
1 - 2 sum_{i<=I} C_{kappa,i}/((i+1)(i+2)) with 12 digits, and the root
growth |C_i|^{1/i}; for the diagonal also the successive ratios.

Run:  .venv/bin/python hunts/rogue_frontier/fkappa/extend_report.py
"""

import json
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name, key=None):
    with open(os.path.join(HERE, "coefficients.json")) as f:
        base = json.load(f)["corrected"]
    ext = {}
    p = os.path.join(HERE, "coefficients_ext.json")
    if os.path.exists(p):
        with open(p) as f:
            ext = json.load(f).get("corrected", {})
    if name == "diagonal":
        d = dict(base["diagonal"])
        d.update(ext.get("diagonal", {}))
    else:
        d = dict(base["rows"][key])
        d.update(ext.get("rows", {}).get(key, {}))
    keys = sorted(int(k) for k in d)
    return [(k, Fraction(d[str(k)])) for k in keys]


def report_row(kappa):
    seq = load("rows", str(kappa))
    print(f"\n=== corrected kappa = {kappa} row (i up to "
          f"{seq[-1][0]}) ===")
    partial = Fraction(0)
    print(f"{'i':>3} {'C_i':>44} {'bound thru i':>16} {'|C_i|^(1/i)':>12}")
    for i, c in seq:
        partial += Fraction(2) * c / ((i + 1) * (i + 2))
        bound = Fraction(1) - partial
        root = float(abs(c)) ** (1.0 / i) if c else 0.0
        cs = str(c)
        if len(cs) > 44:
            cs = cs[:20] + "..." + cs[-20:]
        print(f"{i:>3} {cs:>44} {float(bound):16.12f} {root:12.6f}")


def report_diag():
    seq = load("diagonal")
    print(f"\n=== corrected stable diagonal C_(i-2,i) (i up to "
          f"{seq[-1][0]}) ===")
    print(f"{'i':>3} {'C_i':>44} {'ratio C_i/C_(i-1)':>18} "
          f"{'|C_i|^(1/i)':>12} {'(i+.5)(|r|/2-1)':>16}")
    prev = None
    for i, c in seq:
        root = float(abs(c)) ** (1.0 / i) if c else 0.0
        cs = str(c)
        if len(cs) > 44:
            cs = cs[:20] + "..." + cs[-20:]
        if prev and prev != 0:
            r = float(c / prev)
            a = (i - 0.5) * (abs(r) / 2 - 1)
            print(f"{i:>3} {cs:>44} {r:18.6f} {root:12.6f} {a:16.4f}")
        else:
            print(f"{i:>3} {cs:>44} {'':>18} {root:12.6f}")
        prev = c


def alpha_optimum(kappa):
    """Scan b(alpha) = 2 - 1/alpha - 2 sum C_i alpha^i/((i+1)(i+2)) over
    alpha in (0,1]; confirm the peak exactly at a nearby rational."""
    seq = load("rows", str(kappa))

    def b_float(al):
        return 2 - 1 / al - 2 * sum(float(c) * al ** i / ((i + 1) * (i + 2))
                                    for i, c in seq)

    best_al, best_b = 1.0, b_float(1.0)
    n = 2000
    for j in range(300, n + 1):
        al = j / n
        v = b_float(al)
        if v > best_b:
            best_al, best_b = al, v
    ar = Fraction(round(best_al * 1000), 1000)
    exact = (Fraction(2) - 1 / ar
             - 2 * sum(c * ar ** i / ((i + 1) * (i + 2)) for i, c in seq))
    print(f"\nkappa={kappa}: b(1) = "
          f"{float(Fraction(2) - 1 - 2 * sum(c / ((i + 1) * (i + 2)) for i, c in seq)):.12f}, "
          f"sup_(0,1] b = {best_b:.9f} at alpha = {best_al:.4f}")
    print(f"  exact at alpha = {ar}: b = {exact} = {float(exact):.9f}")
    print(f"  (truncation at I = {seq[-1][0]}; tail of the i-sum not "
          f"bounded here)")


if __name__ == "__main__":
    report_row(2)
    report_row(3)
    report_diag()
    alpha_optimum(2)
    alpha_optimum(3)
