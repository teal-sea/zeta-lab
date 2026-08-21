"""Identify the lambda dependence of m_k(lambda) from the exact sweep data.

Reads exact_trTk_values.json (lambda = 1) and exact_trTk_values_lambda.json
(lambda = p/q families, N = q t, d = p t), extracts each m_k(lambda) as an
exact rational (leading coefficient of the identified degree-(k+1)
polynomial in t, overdetermination checks re-run here), and then tests the
piecewise structure the data suggested:

  m_k(lambda) = 1 + sum_{j=1}^{J} a_{k,j} lambda^{2j}
                - sum_{j=2}^{J} [lambda > 1/j] (j lambda - 1)^{2j+1}
                                 g_{k,j}(lambda) / lambda,
  J = floor(k/2), and g_{k,j} a polynomial of degree k - 2j.

The even part (the Wick piece) is fitted from the J smallest
lambda <= 1/J values and must reproduce every other lambda <= 1/J value
exactly.  Then, walking j downward from J to 2, g_{k,j} is fitted from the
first k - 2j + 1 lambda values in the window (1/j, 1/(j-1)] (with the
previously identified defects subtracted; each defect formula stays
subtracted for all larger lambda) and must reproduce the remaining window
values exactly.

Every fit is exact rational linear algebra; PASS means exact equality of
fractions, not closeness.  Nothing here is established for lambda outside
the sampled grid; the script prints which lambda were fitted and which were
reproduced, and the piecewise model is an observed identification on that
grid only.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from fast_moments import (  # noqa: E402
    JSON_LAMBDA_PATH,
    JSON_PATH,
    identify_polynomial,
)


def mk_table(k: int) -> dict[Fraction, Fraction]:
    """m_k(lambda) as exact rationals, re-running the polynomial checks."""
    out: dict[Fraction, Fraction] = {}
    if os.path.exists(JSON_LAMBDA_PATH):
        with open(JSON_LAMBDA_PATH) as f:
            data = json.load(f)
        for lam_s, per_k in data.items():
            p, q = map(int, lam_s.split("/"))
            vals = per_k.get(str(k))
            if not vals:
                continue
            vt = {int(N) // q: int(v) for N, v in vals.items()}
            res = identify_polynomial(vt, k + 1, min_extra=2)
            if res is None:
                print(f"  [warn] no validated polynomial for lambda={lam_s}, k={k}")
                continue
            _, coeffs, _, _ = res
            assert len(coeffs) == k + 2, (lam_s, k)
            out[Fraction(p, q)] = coeffs[-1] / (q ** k * p)
    with open(JSON_PATH) as f:
        main = json.load(f).get(str(k))
    if main:
        vt = {int(N): int(v) for N, v in main.items()}
        res = identify_polynomial(vt, k + 1, min_extra=2)
        if res is not None:
            out[Fraction(1)] = res[1][-1]
    return out


def solve_exact(rows: list[list[Fraction]]) -> list[Fraction]:
    """Gaussian elimination over the rationals; rows are [A | b]."""
    n = len(rows)
    m = [[Fraction(x) for x in r] for r in rows]
    for i in range(n):
        piv = next(r for r in range(i, n) if m[r][i] != 0)
        m[i], m[piv] = m[piv], m[i]
        inv = m[i][i]
        m[i] = [x / inv for x in m[i]]
        for r in range(n):
            if r != i and m[r][i] != 0:
                f = m[r][i]
                m[r] = [a - f * b for a, b in zip(m[r], m[i])]
    return [m[i][n] for i in range(n)]


def poly_in_lambda(coeffs, exps, var="lam") -> str:
    parts = []
    for c, e in zip(coeffs, exps):
        if c == 0:
            continue
        mono = "1" if e == 0 else (var if e == 1 else f"{var}^{e}")
        parts.append(f"({c})*{mono}")
    return " + ".join(parts) if parts else "0"


def analyze_k(k: int) -> None:
    tab = mk_table(k)
    lams = sorted(tab)
    print(f"\n===== k = {k}: m_k(lambda) at {len(lams)} lambda values =====")
    for lam in lams:
        print(f"  m_{k}({lam}) = {tab[lam]} = {float(tab[lam]):.10f}")

    J = k // 2
    pieces = []  # (label, callable Fraction -> Fraction)

    # Wick piece on lambda <= 1/J
    low = [(lam, tab[lam] - 1) for lam in lams if lam <= Fraction(1, J)]
    exps = [2 * j for j in range(1, J + 1)]
    if len(low) < J:
        print(f"  [need at least {J} lambda <= 1/{J} values, have {len(low)}]")
        return
    rows = [[lam ** e for e in exps] + [v] for lam, v in low[:J]]
    wick_co = solve_exact(rows)
    print(f"  Wick piece (lambda <= 1/{J}), fitted on "
          f"lambda = {[str(l) for l, _ in low[:J]]}:")
    print(f"    W_{k}(lam) = 1 + {poly_in_lambda(wick_co, exps)}")
    fails = [(l, v) for l, v in low[J:]
             if sum(c * l ** e for c, e in zip(wick_co, exps)) != v]
    if fails:
        print(f"    FAIL at: {[(str(l), str(v)) for l, v in fails]}")
        return
    print(f"    exactly reproduced at lambda = {[str(l) for l, _ in low[J:]]}"
          f"  [{len(low) - J} spare]")

    def model(lam: Fraction) -> Fraction:
        val = 1 + sum(c * lam ** e for c, e in zip(wick_co, exps))
        for _, piece in pieces:
            val += piece(lam)
        return val

    # defect pieces, j = J down to 2, fitted on the window (1/j, 1/(j-1)]
    for j in range(J, 1, -1):
        top = Fraction(1) if j == 2 else Fraction(1, j - 1)
        win = [lam for lam in lams if Fraction(1, j) < lam <= top]
        ncoef = k - 2 * j + 1
        if len(win) < ncoef + 1:
            print(f"  [window (1/{j}, {top}]: need {ncoef + 1}+ lambda values, "
                  f"have {len(win)}; cannot identify g_{k},{j}]")
            return
        g_exps = list(range(ncoef))
        pts = []
        for lam in win:
            resid = tab[lam] - model(lam)
            g = -resid * lam / (j * lam - 1) ** (2 * j + 1)
            pts.append((lam, g))
        rows = [[lam ** e for e in g_exps] + [g] for lam, g in pts[:ncoef]]
        g_co = solve_exact(rows)
        print(f"  defect j={j} (appears for lambda > 1/{j}), fitted on "
              f"lambda = {[str(l) for l, _ in pts[:ncoef]]}:")
        print(f"    D_{j}(lam) = -({j} lam - 1)^{2 * j + 1} * "
              f"[{poly_in_lambda(g_co, g_exps)}] / lam")
        fails = [(l, g) for l, g in pts[ncoef:]
                 if sum(c * l ** e for c, e in zip(g_co, g_exps)) != g]
        if fails:
            print(f"    FAIL at: {[(str(l), str(v)) for l, v in fails]}")
            return
        print(f"    exactly reproduced at lambda = "
              f"{[str(l) for l, _ in pts[ncoef:]]}  [{len(pts) - ncoef} spare]")

        def piece(lam: Fraction, j=j, g_co=tuple(g_co), g_exps=tuple(g_exps)):
            if lam <= Fraction(1, j):
                return Fraction(0)
            g = sum(c * lam ** e for c, e in zip(g_co, g_exps))
            return -((j * lam - 1) ** (2 * j + 1)) * g / lam

        pieces.append((f"D_{j}", piece))

    if Fraction(1) in tab:
        print(f"  model at lambda = 1: {model(Fraction(1))} "
              f"(= m_{k}(1) directly computed: {tab[Fraction(1)]})")


if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [2, 3, 4, 5, 6]
    for k in ks:
        analyze_k(k)
