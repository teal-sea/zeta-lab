"""Locate the 2.0e-13 discrepancy in the quoted n=7, p=3000 floor.

`hunts/ainta_seven_point/RESULTS.md` quotes 0.0038262312115073 as the Arb value.
`artifacts/modal-results.json` shows what that number actually is: `F6_at_point`,
an Arb evaluation of F6 at the argmin *rounded to six decimals*,
(1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002).  A value at a point
is an upper bound on the infimum, and RESULTS.md says exactly that when it writes
the bracket `0.003826 <= inf F6 <= 0.0038262312115073`.

The independent audit reports 0.00382623121130447424828... at a 30-digit refined
minimiser, 2.0e-13 lower.  This script evaluates F6 at both points in 60-digit
arithmetic and shows the difference is the rounding of the argmin, not a
disagreement about the functional.

Run:  .venv/bin/python hunts/family_wall/f7_point_check.py
"""
import mpmath as mp

mp.mp.dps = 60

P = mp.mpf(3000)

ROUNDED = [mp.mpf(x) for x in ("1.046081", "1.989132", "1.986415",
                               "1.041603", "1.977024", "1.045002")]

# the audit's refined minimiser, results/REPORT.md section "F_7,3000"
AUDIT = [mp.mpf(x) for x in ("1.04608035577143543724508620334",
                             "1.98913202062119593163024512345",
                             "1.98641493610882775469506115045",
                             "1.04160329372111326218470199081",
                             "1.97702352233741593883693409703",
                             "1.04500209461784484467937259671")]

# this repository's own float minimiser, hunts/ainta_seven_point/artifacts/
# modal-results.json -> seven_point.best.argmin
REPO_FLOAT = [mp.mpf(repr(x)) for x in (1.0460805871716363, 1.9891321320254813,
                                        1.9864148322287916, 1.0416031596050614,
                                        1.9770234943997285, 1.0450019353434357)]


def Kraw(x):
    q = 1 / mp.sqrt(2)
    return (mp.sincpi(x - q / mp.pi) + mp.sincpi(x + q / mp.pi)) / 2


K0 = Kraw(mp.mpf(0))


def w(x):
    return (Kraw(x) / K0) ** 2


def F(g, p):
    k = len(g)
    n = k + 1
    cs = [mp.mpf(0)] * (k + 1)
    for i, gi in enumerate(g):
        cs[i + 1] = cs[i] + gi
    tot = cs[k] / p
    for s in range(1, n):
        acc = mp.mpf(0)
        for i in range(0, k - s + 1):
            acc += w(cs[i + s] - cs[i])
        tot += (mp.mpf(2) / (n - s)) * acc
    return tot


def main():
    print("K(0) =", mp.nstr(K0, 50))
    print("H    =", mp.nstr(mp.mpf(3) / 2 - mp.cot(1 / mp.sqrt(2)) / mp.sqrt(2), 50))
    print()
    for name, g in (("six-decimal argmin (the quoted Arb point)", ROUNDED),
                    ("this repo's float minimiser", REPO_FLOAT),
                    ("the audit's 30-digit minimiser", AUDIT)):
        v = F(g, P)
        print(f"{name:44s} F_7,3000 = {mp.nstr(v, 25)}")
    print()
    print("quoted in hunts/ainta_seven_point/RESULTS.md:  0.0038262312115073")
    print("audit's value:                                0.00382623121130447424828548285770795421")
    print("difference:", mp.nstr(F(ROUNDED, P) - F(AUDIT, P), 6))


if __name__ == "__main__":
    main()
