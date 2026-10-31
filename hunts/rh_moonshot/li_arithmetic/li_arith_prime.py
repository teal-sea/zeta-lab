"""The arithmetic part of lambda_n as a prime integral with a Laguerre kernel.

Hunt #150 (`rh_moonshot`), mechanism `li_arithmetic`.  Not a result about RH.

Derivation (self-reviewed; every identity below is pinned by a test)
---------------------------------------------------------------------
With s = 1/(1-z) and p^{-s} = p^{-1} exp(-(log p) z/(1-z)), the Laguerre
generating function sum_n L_n^{(-1)}(x) z^n = exp(-x z/(1-z)) gives

    n [z^n] p^{-ks} = n p^{-k} L_n^{(-1)}(k log p) = -(k log p) p^{-k} L_{n-1}^{(1)}(k log p).

So, formally, the local factor of p contributes
-sum_k (log p) p^{-k} L_{n-1}^{(1)}(log p^k) to T(n).  The sum over p diverges
(it is a prime sum at the critical scale m^{-1/2}); Bombieri and Lagarias
regularize it, and with L_n' = -L_{n-1}^{(1)} the regularized form is

    T(n) = lim_{X->oo} [ sum_{m<=X} (Lambda(m)/m) L_n'(log m) - L_n(log X) + 1 ].

Integrating by parts against E(x) = psi(x) - x, and using
L_n'' - L_n' = L_{n-1}^{(2)}:

    T(n) = -n - int_1^oo E(x) L_{n-1}^{(2)}(log x) dx / x^2.

On [1, 2) psi vanishes, so E(x) = -x there and that piece is elementary
(d/du L_n^{(1)} = -L_{n-1}^{(2)}, L_n^{(1)}(0) = n + 1):

    lambda_n = A(n) + 1 - L_n^{(1)}(log 2) - P_n,
    P_n      = int_2^oo (psi(x) - x) L_{n-1}^{(2)}(log x) dx / x^2.

So lambda_n >= 0 is exactly  P_n <= M(n) := A(n) + 1 - L_n^{(1)}(log 2),  with
A(n) ~ (n/2) log n explicit and |L_n^{(1)}(log 2)| <= sqrt(2)(n+1).  This is
the target inequality (the "star" inequality of `NOTES.md`).  The Euler
product enters only through psi.

At finite X the sharp sum differs from the integrated form by the boundary
term h(X) E(X), h(x) = L_n'(log x)/x; ``prime_side_T`` subtracts it, which
turns an O(X^{-1/2} poly(log X)) error with 1/|rho| weights into one with
1/|rho|^2 weights.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_ROOT))

#: Schoenfeld (1976), conditional on RH: |psi(x) - x| < sqrt(x) log^2 x / (8 pi)
#: for x >= 73.2.  Used only as the strongest pointwise input one could hope
#: for, never as an unconditional fact.
SCHOENFELD_CONST = 1.0 / (8.0 * math.pi)

#: sum over all nontrivial zeros of 1/|rho|^2 under RH, = 2 lambda_1 =
#: 2 + gamma - log(4 pi); Cramer's mean square of (psi(e^u) - e^u) e^{-u/2}.
CRAMER_MEAN_SQUARE = 2.0 + 0.5772156649015329 - math.log(4.0 * math.pi)


# ---------------------------------------------------------------------------
# primes
# ---------------------------------------------------------------------------


def von_mangoldt_table(X: int) -> tuple[np.ndarray, np.ndarray]:
    """Prime powers m <= X (sorted) and Lambda(m) = log p, by a numpy sieve."""
    X = int(X)
    sieve = np.ones(X + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(math.isqrt(X)) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    primes = np.nonzero(sieve)[0].astype(np.int64)
    del sieve
    ms = [primes]
    lams = [np.log(primes.astype(np.float64))]
    small = primes[primes <= int(math.isqrt(X))]
    for p in small:
        q = int(p) * int(p)
        lp = math.log(int(p))
        powers = []
        while q <= X:
            powers.append(q)
            q *= int(p)
        if powers:
            ms.append(np.array(powers, dtype=np.int64))
            lams.append(np.full(len(powers), lp))
    m = np.concatenate(ms)
    lam = np.concatenate(lams)
    order = np.argsort(m, kind="stable")
    return m[order], lam[order]


def psi_at(x: np.ndarray, m: np.ndarray, lam: np.ndarray) -> np.ndarray:
    """psi(x) = sum_{m <= x} Lambda(m), at the points x (any order)."""
    cum = np.concatenate([[0.0], np.cumsum(lam)])
    idx = np.searchsorted(m, np.asarray(x, dtype=np.float64), side="right")
    return cum[idx]


def laguerre(n: int, alpha: float, u):
    """L_n^{(alpha)}(u) by the three-term recurrence, float64, vectorized in u."""
    u = np.asarray(u, dtype=np.float64)
    if n == 0:
        return np.ones_like(u)
    a, b = np.ones_like(u), 1.0 + alpha - u
    for k in range(1, n):
        a, b = b, ((2 * k + 1 + alpha - u) * b - (k + alpha) * a) / (k + 1)
    return b


def prime_side_T(n_values, X: int, m: np.ndarray, lam: np.ndarray) -> dict:
    """T_X(n) = sum_{m<=X} (Lambda(m)/m) L_n'(log m) - L_n(log X) + 1 - h(X) E(X).

    The last term is the integration-by-parts boundary term (module docstring);
    without it the same sum converges with the slower 1/|rho| weights.  Uses
    math.fsum over the prime powers below X.
    """
    sel = m <= X
    mm = m[sel].astype(np.float64)
    ll = lam[sel]
    logm = np.log(mm)
    logX = math.log(X)
    E = float(np.sum(ll)) - X
    out = {}
    for n in n_values:
        n = int(n)
        dL = -laguerre(n - 1, 1.0, logm)  # L_n' = -L_{n-1}^{(1)}
        head = math.fsum((ll / mm) * dL)
        LnX = float(laguerre(n, 0.0, np.array([logX]))[0])
        dLX = -float(laguerre(n - 1, 1.0, np.array([logX]))[0])
        sharp = head - LnX + 1.0
        out[n] = {"sharp": sharp, "integrated": sharp - dLX * E / X}
    return out


# ---------------------------------------------------------------------------
# the kernel and the bounds a prime-side argument could use
# ---------------------------------------------------------------------------


def scaled_laguerre(u: np.ndarray, k_max: int, alpha: float = 2.0):
    """Yield ell_k(u) = e^{-u/2} L_k^{(alpha)}(u) for k = 0..k_max, without under/overflow.

    The recurrence runs on unscaled values with a per-point log scale that is
    renormalized whenever a value passes 1e150, so e^{-u/2} never underflows
    at u ~ 4 k_max ~ 2e4 while L_k(u) itself would overflow.
    """
    u = np.asarray(u, dtype=np.float64)
    a = np.ones_like(u)
    b = 1.0 + alpha - u
    ls = -u / 2.0
    yield np.exp(ls)
    if k_max == 0:
        return
    with np.errstate(divide="ignore"):
        yield np.sign(b) * np.exp(np.log(np.abs(b)) + ls)
    for k in range(1, k_max):
        a, b = b, ((2 * k + 1 + alpha - u) * b - (k + alpha) * a) / (k + 1)
        big = np.abs(b) > 1e150
        if big.any():
            f = np.abs(b[big])
            a[big] /= f
            b[big] /= f
            ls[big] += np.log(f)
        with np.errstate(divide="ignore"):
            yield np.sign(b) * np.exp(np.log(np.abs(b)) + ls)


def _grid(n_max: int, u_lo: float, u_mid: float, du_fine: float = 1e-4) -> np.ndarray:
    """u-grid: uniform step du_fine on [u_lo, u_mid], uniform in sqrt(u) beyond.

    Beyond u_mid the kernel e^{-u/2} L_{n-1}^{(2)}(u) oscillates with phase
    about 2 sqrt(n u), so a grid uniform in v = sqrt(u) with 14 points per
    period pi/sqrt(n_max) resolves it; it runs to past the turning point 4n.
    """
    fine = np.arange(u_lo, u_mid, du_fine)
    v_lo = math.sqrt(u_mid)
    v_hi = math.sqrt(4.0 * n_max + 12.0 * n_max ** (1.0 / 3.0) + 400.0)
    dv = 0.22 / math.sqrt(max(n_max, 1))
    v = np.arange(v_lo, v_hi + dv, dv)
    return np.concatenate([fine, v * v])


def kernel_bounds(
    n_max: int,
    m: np.ndarray,
    lam: np.ndarray,
    X0: int,
    du_fine: float = 1e-4,
) -> dict:
    """For n = 1..n_max, the numbers that decide whether a prime-side bound can work.

    With ell_k(u) = e^{-u/2} L_k^{(2)}(u) and Delta(u) = E(e^u) e^{-u/2}:

    * ``B_pointwise[n]`` = int_{log 2}^oo beta(u) |ell_{n-1}(u)| du, where
      beta(u) = |Delta(u)| exactly for e^u <= X0 (sieve) and the RH-conditional
      Schoenfeld envelope u^2/(8 pi) beyond.  |P_n| <= B_pointwise[n] under RH.
    * ``K2[n]`` = int_{log 2}^oo ell_{n-1}(u)^2 du (the kernel's L^2 mass away
      from the elementary piece on [0, log 2)).
    * ``D2[n]`` = int_{log 2}^{U_n} Delta(u)^2 du with U_n = 4n + 6 n^{1/3} + 20:
      exact up to log X0 and Cramer's RH mean square beyond (a model).
    * ``tail[n]`` = Schoenfeld-envelope integral of |ell_{n-1}| beyond U_n.

    So the mean-square (Cauchy-Schwarz) route gives |P_n| <= sqrt(D2 K2) + tail.
    Trapezoid rule on the grid of ``_grid``; the integrands are sampled, not
    integrated exactly, which is enough for the factor-of-many comparisons
    these numbers are used for.
    """
    u_lo = math.log(2.0)
    u_mid = math.log(float(X0))
    u = _grid(n_max, u_lo, u_mid, du_fine)
    x_fine_mask = u <= u_mid
    beta = np.empty_like(u)
    xs = np.exp(u[x_fine_mask])
    Ex = psi_at(xs, m, lam) - xs
    delta_exact = Ex * np.exp(-u[x_fine_mask] / 2.0)
    beta[x_fine_mask] = np.abs(delta_exact)
    beta[~x_fine_mask] = SCHOENFELD_CONST * u[~x_fine_mask] ** 2
    delta2 = np.empty_like(u)
    delta2[x_fine_mask] = delta_exact**2
    delta2[~x_fine_mask] = CRAMER_MEAN_SQUARE
    w = np.zeros_like(u)  # trapezoid weights
    du = np.diff(u)
    w[:-1] += du / 2.0
    w[1:] += du / 2.0
    cum_delta2 = np.concatenate([[0.0], np.cumsum((delta2[:-1] + delta2[1:]) / 2.0 * du)])
    B, K2, D2, tail = [], [], [], []
    for n, cur in enumerate(scaled_laguerre(u, n_max - 1, 2.0), start=1):
        U = 4.0 * n + 6.0 * n ** (1.0 / 3.0) + 20.0
        inside = u <= U
        a = np.abs(cur)
        B.append(float(np.sum(w * beta * a)))
        K2.append(float(np.sum(w * cur * cur)))
        iU = int(np.searchsorted(u, U))
        D2.append(float(cum_delta2[min(iU, len(u) - 1)]))
        tail.append(float(np.sum((w * beta * a)[~inside])))
    return {
        "u_grid_points": int(len(u)),
        "X0": int(X0),
        "B_pointwise": B,
        "K2": K2,
        "D2": D2,
        "tail": tail,
    }


def laguerre1_at_log2(n_max: int) -> list:
    """L_n^{(1)}(log 2) for n = 1..n_max (float64 recurrence; |.| <= sqrt 2 (n+1))."""
    u = np.array([math.log(2.0)])
    out = []
    a, b = np.ones(1), 2.0 - u  # L_0^{(1)}, L_1^{(1)}
    out.append(float(b[0]))
    for k in range(1, n_max):
        a, b = b, ((2 * k + 2 - u) * b - (k + 1) * a) / (k + 1)
        out.append(float(b[0]))
    return out
