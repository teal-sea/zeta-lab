"""Circularity challenger's recomputation for li_arithmetic (hunt #150).

Written by the circularity challenger, sharing no code with ``li_arith_*.py``.
Writes nothing into the tree.

1. Provenance of P_n. The artifact's ``P_exact`` is M(n) - lambda_n with lambda_n
   from the xi side (``run_li_arith_prime.py``: ``Pn = M - L``). This module
   computes the prime integral itself, truncated at X, in closed form:

       P_n(X) = psi(X) F(log X) + sum_{m <= X} Lambda(m) m^(-1) L_{n-1}^{(1)}(log m)
                + L_n^{(1)}(log X) - L_n^{(1)}(log 2),     F(u) = -e^(-u) L_{n-1}^{(1)}(u),

   from d/du[e^(-u) L_k^{(1)}] = -e^(-u) L_k^{(2)} and d/du L_{k+1}^{(1)} = -L_k^{(2)},
   with its own sieve, and says up to which n the primes below X reproduce P_n.
2. lambda_n of xi(s - delta), zeta's completion shifted off its line, by a Cauchy
   integral: every zero has real part 1/2 + delta, so |1 - 1/rho| < 1 for each and
   lambda_n = sum_rho [1 - (1 - 1/rho)^n] > 0 for every n, although RH fails for it.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.special import eval_genlaguerre

HERE = Path(__file__).resolve().parent
ART = HERE.parent / "artifacts" / "prime_side.json"


def prime_powers(X: int) -> tuple[np.ndarray, np.ndarray]:
    """(m, Lambda(m)) for prime powers 2 <= m <= X, sorted."""
    sieve = np.ones(X + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(X ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    primes = np.nonzero(sieve)[0]
    ms, ls = [primes.astype(np.float64)], [np.log(primes.astype(np.float64))]
    small = primes[primes <= int(X ** 0.5) + 1]
    for p in small:
        q = int(p) * int(p)
        while q <= X:
            ms.append(np.array([float(q)]))
            ls.append(np.array([math.log(p)]))
            q *= int(p)
    m = np.concatenate(ms)
    lam = np.concatenate(ls)
    order = np.argsort(m)
    return m[order], lam[order]


def prime_integral(n: int, X: int, m: np.ndarray, lam: np.ndarray, alpha: int = 1) -> float:
    """P_n truncated at X; ``alpha`` other than 1 is a planted fault (wrong antiderivative)."""
    sel = m <= X
    mm, ll = m[sel], lam[sel]
    U = math.log(X)
    psiX = float(ll.sum())
    F_U = -math.exp(-U) * eval_genlaguerre(n - 1, alpha, U)
    s = float(np.sum(ll / mm * eval_genlaguerre(n - 1, alpha, np.log(mm))))
    return psiX * F_U + s + eval_genlaguerre(n, 1, U) - eval_genlaguerre(n, 1, math.log(2))


def compare(ns=range(1, 61), Xs=(10**6, 10**7, 10**8), pp=None) -> dict:
    art = json.loads(ART.read_text())
    P_art = art["P_exact"]
    M = art["margin_M"]
    m, lam = pp if pp is not None else prime_powers(max(Xs))
    rows = {}
    for n in ns:
        rows[n] = {"P_artifact": P_art[n - 1], "M": M[n - 1],
                   **{str(X): prime_integral(n, X, m, lam) for X in Xs}}
    return rows


def first_failure(rows: dict, X: int, tol: float) -> int | None:
    """First n where the truncated prime integral misses the artifact's P_n by > tol."""
    for n in sorted(rows):
        if abs(rows[n][str(X)] - rows[n]["P_artifact"]) > tol:
            return n
    return None


def shifted_li(delta, n_max: int = 30, r: str = "0.7", nodes: int = 256, dps: int = 40) -> list:
    """lambda_n of xi(s - delta), s = 1/(1 - z), by a Cauchy integral on |z| = r."""
    with mp.workdps(dps):
        R = mp.mpf(r)
        d = mp.mpf(delta)

        def xi(s):
            return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

        vals = []
        prev = None
        for j in range(nodes):
            z = R * mp.expj(2 * mp.pi * j / nodes)
            w = mp.log(xi(1 / (1 - z) - d))
            if prev is not None:
                k = mp.nint((mp.im(prev) - mp.im(w)) / (2 * mp.pi))
                w += 2j * mp.pi * k
            vals.append(w)
            prev = w
        wind = mp.nint((mp.im(mp.log(xi(1 / (1 - R) - d))) - mp.im(prev)) / (2 * mp.pi))
        assert wind == 0, "zeros inside the contour"
        out = []
        for n in range(1, n_max + 1):
            c = sum(vals[j] * mp.expj(-2 * mp.pi * j * n / nodes) for j in range(nodes)) / nodes
            out.append(mp.re(n * c / R ** n))
        return out


def main() -> int:
    pp = prime_powers(10**8)
    rows = compare(pp=pp)
    print(" n   P_artifact     P(1e6)        P(1e7)        P(1e8)        M(n)")
    for n in (1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40, 50, 60):
        r = rows[n]
        print("%3d %12.6f %12.6f %12.6f %12.6f %12.4f" % (n, r["P_artifact"], r["1000000"], r["10000000"], r["100000000"], r["M"]))
    for tol in (1e-2, 1e-1, 1.0):
        print("first n where P(1e8) misses P_artifact by more than %g:" % tol, first_failure(rows, 10**8, tol))
    far = compare(ns=range(100, 1001, 50), Xs=(10**8,), pp=pp)
    print(" n   P_artifact   P(1e8)   |diff|/M(n)")
    for n in sorted(far):
        r = far[n]
        print("%4d %10.4f %10.4f %8.4f" % (n, r["P_artifact"], r["100000000"], abs(r["100000000"] - r["P_artifact"]) / r["M"]))
    for tol in (1e-2, 1e-1, 1.0):
        print("first n in 100..1000 (step 50) with |P(1e8) - P_artifact| > %g:" % tol, first_failure(far, 10**8, tol))
    for delta in ("0", "0.25"):
        lam = shifted_li(delta)
        print("xi(s - %s): lambda_1..3 = %s; min over n <= 30 = %s" % (
            delta, [mp.nstr(x, 12) for x in lam[:3]], mp.nstr(min(lam), 8)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
