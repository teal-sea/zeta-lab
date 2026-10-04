"""Measured illustration of Theorem 3 (RESULTS.md section 3), float64, one route.

For each L it prints, divided by e^L:
  A_L          Zhu's comb mass (the constant with H = 0),
  S_sep        per-prime out-of-band infimum, sum_p lambda_max(Toeplitz_p),
  gal          piecewise-constant Galerkin value of lambda_max(P) (from below),
  rayleigh     the explicit lower bound l(L) of section 3.3 (h = cosh(x/2)),
  cw           Collatz-Wielandt value sup_x (P h)(x)/h(x), h = cosh(kappa_L x),
               sampled on a grid (an estimate of an upper bound, not a bound),
  model        lambda_model(L) = 1/(kappa_L^2 - 1/4), kappa_L tanh(kappa_L L) = 1/2.
Theorem 3 says gal -> 1 (and so do rayleigh, cw, model); S_sep -> 2; A_L -> 4.
"""
import math
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from duality_check import comb_terms  # noqa: E402


def lam_galerkin(L, terms, M):
    h = 2 * L / M
    left = -L + h * np.arange(M)
    A = np.zeros((M, M))
    for p, m, w in terms:
        s = m * math.log(p)
        for sgn in (1, -1):
            a0 = left[:, None]
            a1 = left[None, :] + sgn * s
            ov = np.clip(np.minimum(a0 + h, a1 + h) - np.maximum(a0, a1), 0, None)
            A += w * ov / h
    return float(np.linalg.eigvalsh(0.5 * (A + A.T))[-1])


def kappa(L):
    lo, hi = 0.5, 5.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if mid * math.tanh(mid * L) < 0.5:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def rayleigh_lower(L, terms):
    num = 0.0
    for p, m, w in terms:
        y = m * math.log(p)
        num += 2 * w * (math.sinh(L - y / 2) + (L - y / 2) * math.cosh(y / 2))
    return num / (L + math.sinh(L))


def collatz_wielandt(L, terms, k, grid=20001):
    x = np.linspace(-L, L, grid)
    h = np.cosh(k * x)
    Ph = np.zeros_like(x)
    for p, m, w in terms:
        y = m * math.log(p)
        Ph += w * np.where(x - y >= -L, np.cosh(k * (x - y)), 0.0)
        Ph += w * np.where(x + y <= L, np.cosh(k * (x + y)), 0.0)
    return float((Ph / h).max())


def s_sep(terms):
    S = 0.0
    for p in sorted({q for q, _, _ in terms}):
        ts = [w for q, _, w in terms if q == p]
        T = np.array([[0.0 if i == j else ts[abs(i - j) - 1] for j in range(len(ts) + 1)]
                      for i in range(len(ts) + 1)])
        S += float(np.linalg.eigvalsh(T)[-1])
    return S


if __name__ == "__main__":
    print(f"{'L':>5} {'e^L':>9} | {'A_L':>6} {'S_sep':>6} {'gal':>6} {'rayl':>6} {'cw':>6} {'model':>6}  (all / e^L)   gal M=400,800")
    for L in (0.8, 1.0, 1.19, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0):
        terms = comb_terms(L)
        eL = math.exp(L)
        k = kappa(L)
        model = 1.0 / (k * k - 0.25)
        g400 = lam_galerkin(L, terms, 400)
        g800 = lam_galerkin(L, terms, 800)
        vals = [sum(2 * w for _, _, w in terms), s_sep(terms), g800,
                rayleigh_lower(L, terms), collatz_wielandt(L, terms, k), model]
        print(f"{L:5.2f} {eL:9.3f} | " + " ".join(f"{v / eL:6.3f}" for v in vals)
              + f"   {g400:.5g} {g800:.5g}")
        sys.stdout.flush()
