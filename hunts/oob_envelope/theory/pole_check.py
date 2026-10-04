"""Measured checks (float64, one route) of two identities in RESULTS.md section 1.

1. Pole term for complex f: g_hat(i/2) + g_hat(-i/2) computed from the
   time-domain autocorrelation g = f * f~ agrees with
   2 Re[F(i/2) conj F(-i/2)] = 2|int f cosh(u/2)|^2 - 2|int f sinh(u/2)|^2.
2. Lemma 1 (K3 shape): for a complex window function f,
   int |F(t)|^2 cos(lambda t) dt vanishes for lambda = 2L and 2L + 0.3,
   and equals pi (g(lambda) + g(-lambda)) != 0 for the in-band lambda = 2L - 0.05.

f(x) = (L^2 - x^2)^3 * (complex polynomial) on [-L, L], so |F|^2 decays like
t^-8 and the real-line integral can be truncated at |t| = 300 with a tail
below 1e-12. Not a proof; the proofs are in RESULTS.md.
"""
import math

import numpy as np

L = 0.8
rng = np.random.default_rng(7)
coef = rng.normal(size=6) + 1j * rng.normal(size=6)


def f(x):
    return (L * L - x * x) ** 3 * np.polyval(coef, x)


xg, wg = np.polynomial.legendre.leggauss(400)
X, W = L * xg, L * wg          # nodes on [-L, L]
FX = f(X)

# 1. pole term
c = np.sum(W * FX * np.cosh(X / 2))
s = np.sum(W * FX * np.sinh(X / 2))
F_plus = np.sum(W * FX * np.exp(-X / 2))    # F(i/2)  = int f e^{-u/2}
F_minus = np.sum(W * FX * np.exp(X / 2))    # F(-i/2) = int f e^{+u/2}
formula_a = 2 * np.real(F_plus * np.conj(F_minus))
formula_b = 2 * abs(c) ** 2 - 2 * abs(s) ** 2


def g(x):
    """g(x) = int f(y) conj f(y - x) dy over [max(-L, x-L), min(L, x+L)]."""
    lo, hi = max(-L, x - L), min(L, x + L)
    if hi <= lo:
        return 0.0
    yn, yw = np.polynomial.legendre.leggauss(200)
    y = 0.5 * (hi - lo) * yn + 0.5 * (hi + lo)
    return np.sum(0.5 * (hi - lo) * yw * f(y) * np.conj(f(y - x)))


xn, xw = np.polynomial.legendre.leggauss(300)
gh_plus = gh_minus = 0.0
for half in (-1, 1):                       # split at 0 where g has a corner
    xs = L * (xn + half)                   # [-2L, 0] and [0, 2L]
    gs = np.array([g(x) for x in xs])
    gh_plus += np.sum(L * xw * gs * np.exp(-xs / 2))     # g_hat(i/2)
    gh_minus += np.sum(L * xw * gs * np.exp(xs / 2))     # g_hat(-i/2)
direct = gh_plus + gh_minus
print("pole term, direct time-domain :", direct)
print("2 Re[F(i/2) conj F(-i/2)]      :", formula_a)
print("2|c|^2 - 2|s|^2                :", formula_b)
print("imag part of direct (should be 0):", abs(np.imag(direct)))
print("wrong formulas: 2F(i/2)^2 =", 2 * F_plus ** 2, " 2|F(i/2)|^2 =", 2 * abs(F_plus) ** 2)

# 2. Lemma 1 on the real line
T, dt = 300.0, 0.004
t = np.arange(-T, T + dt / 2, dt)
F = np.array([np.sum(W * FX * np.exp(1j * tt * X)) for tt in t])
absF2 = np.abs(F) ** 2
print("Plancherel check: int|F|^2 / (2 pi ||f||^2) =",
      np.trapezoid(absF2, t) / (2 * math.pi * np.sum(W * np.abs(FX) ** 2)))
for lam in (2 * L, 2 * L + 0.3, 2 * L - 0.05):
    val = np.trapezoid(absF2 * np.cos(lam * t), t)
    pred = math.pi * (g(lam) + g(-lam))
    print(f"lambda = {lam:.3f}: int |F|^2 cos = {val:+.3e}   pi(g(l)+g(-l)) = {np.real(pred):+.3e}")
