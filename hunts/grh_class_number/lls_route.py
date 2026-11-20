"""The route of Lamzouri, Li and Soundararajan evaluated numerically (a door, not adopted).

    .venv/bin/python -m hunts.grh_class_number.lls_route

Derived by the proof reviewer of 2026-11-20 and committed here by the repair
pass as the measurement behind the first door of RESULTS.md.  FLOAT GRADE: no
enclosure, no written proof in this hunt, unreviewed; no theorem of the hunt
uses it.  Under H(1/2) for chi_D, real primitive odd of conductor q:

  log L(1) >= S1(x1) + A/log x1 - c(x1) F_ub(x2),   A = (1/2) log(q/pi) + (1/2) psi(1)
  c(x) = 1/log x + 2/(sqrt(x) log^2 x)
  F = sum_rho Re 1/rho <= F_ub = [A (1 - 1/x2) + log 2 / x2 - S2(x2)] / (1 + 1/x2 - 2/sqrt(x2))
  S1(x) = sum_{n<=x} Lambda(n) chi(n) (1 - log n/log x)/(n log n)
  S2(x) = sum_{n<=x} Lambda(n) chi(n) (1 - n/x)/n

with the worst case over chi(p) in {-1, 0, 1} taken prime by prime for the
combination S1 + (c/D) S2.  It uses Re 1/(1 - rho) = Re 1/rho and
|x^rho| = x^(1/2), so it exists only at abscissa 1/2: the sibling hunt at 7/8
could not have it.  LLS's Theorem 1.5 is a closed form of this route with
x fixed at (log q)^2/4.
"""

from __future__ import annotations

import math

import numpy as np

EULER = 0.5772156649015329


def _primes(n: int):
    s = np.ones(n + 1, bool)
    s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0].tolist()


def log_L_lower(q: float, x1: float, x2: float) -> float:
    """The route's lower bound for log L(1, chi) at conductor q (float)."""
    A = 0.5 * math.log(q / math.pi) - 0.5 * EULER
    c = 1 / math.log(x1) + 2 / (math.sqrt(x1) * math.log(x1) ** 2)
    Dn = 1 + 1 / x2 - 2 / math.sqrt(x2)
    if Dn <= 0:
        return -math.inf
    lam = c / Dn
    xm = max(x1, x2)
    tot = 0.0
    for p in _primes(int(xm)):
        lp = math.log(p)
        plus = minus = 0.0
        k, pk = 1, p
        while pk <= xm:
            w1 = (1 - k * lp / math.log(x1)) / (k * pk) if pk <= x1 else 0.0
            w2 = lam * lp * (1 - pk / x2) / pk if pk <= x2 else 0.0
            plus += w1 + w2
            minus += (-1) ** k * (w1 + w2)
            k += 1
            pk *= p
        tot += min(0.0, plus, minus)
    return tot + A / math.log(x1) - lam * (A * (1 - 1 / x2) + math.log(2) / x2)


def optimise(q: float):
    """Grid over (x1, x2) in units of (log q)^2, then a coordinate search."""
    lq = math.log(q)
    grid = [lq**2 * f for f in (0.1, 0.15, 0.25, 0.4, 0.6, 1, 1.5, 2.5, 4, 6, 10, 16, 25)]
    best = (-math.inf, None)
    for x1 in grid:
        for x2 in grid:
            if x1 < 5 or x2 < 5 or max(x1, x2) > 1.9e6:
                continue
            v = log_L_lower(q, x1, x2)
            if v > best[0]:
                best = (v, (x1, x2))
    v0, (x1, x2) = best
    for _ in range(40):
        moved = False
        for f1, f2 in ((1.1, 1), (1 / 1.1, 1), (1, 1.1), (1, 1 / 1.1),
                       (1.03, 1), (1 / 1.03, 1), (1, 1.03), (1, 1 / 1.03)):
            v = log_L_lower(q, x1 * f1, x2 * f2)
            if v > v0 + 1e-9:
                v0, x1, x2, moved = v, x1 * f1, x2 * f2, True
        if not moved:
            break
    return v0, (x1, x2)


if __name__ == '__main__':
    for e in (4, 6, 8, 10, 11, 20, 50):
        v, (x1, x2) = optimise(10.0**e)
        print(f'q = 1e{e}: L >= {math.exp(v):.5f} at x1 = {x1:.0f}, x2 = {x2:.0f}')
