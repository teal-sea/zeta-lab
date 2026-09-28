"""
zeta.explicit, the explicit formula: **primes reconstructed from the zeros**.

This is the payoff of the whole theory.  The zeros ρ = ½ + iγ of ζ(s) are not a
curiosity attached to the primes; they *are* the primes, written in a different
basis.  Two dual statements are implemented here.

1.  **Prime side ← zero side (von Mangoldt, 1895).**  For x > 1,

        ψ₀(x) = x − Σ_ρ x^ρ/ρ − log(2π) − ½ log(1 − x⁻²)

    where ψ(x) = Σ_{p^k ≤ x} log p is Chebyshev's function and ψ₀ is ψ with the
    jumps halved.  The sum runs over the nontrivial zeros in conjugate pairs;
    the last term is exactly the contribution of the *trivial* zeros ρ = −2n:

        − Σ_{n≥1} x^(−2n)/(−2n) = ½ Σ_{n≥1} x^(−2n)/n = −½ log(1 − x⁻²).

    Real form of the pair sum.  Write ρ = ½ + iγ (γ > 0), ρ̄ = ½ − iγ.  Then

        x^ρ/ρ + x^ρ̄/ρ̄ = 2 Re(x^ρ/ρ),
        x^ρ = x^½ · e^{iγ log x},      1/ρ = e^{−i arg ρ}/|ρ|,
        ⟹ x^ρ/ρ = x^½ e^{i(γ log x − arg ρ)}/|ρ|,

        ⟹  x^ρ/ρ + x^ρ̄/ρ̄ = 2 x^½ cos(γ log x − arg ρ) / |ρ| ,

    with |ρ| = √(¼ + γ²) and arg ρ = atan2(γ, ½) = arctan(2γ).  Every zero
    contributes one pure harmonic in log x, of amplitude 2√x/|ρ|, the primes
    are the interference pattern of these waves.

2.  **Zero side ← prime side ("the music of the primes").**  Differentiating the
    formula above with respect to u = log x turns the staircase into a comb:

        Σ_{n≥2} Λ(n) δ(u − log n) = e^u − 2 e^{u/2} Σ_{γ>0} cos(γu) − 1/(e^{2u}−1)

    so the *oscillatory spectrum*  D(u) = −2 Σ_{γ>0} cos(γu)  has spikes exactly
    at u = log p^k with weight Λ(n)/√n.  See :func:`prime_spectrum`.

3.  **Riemann's π(x) (1859).**  With J(y) = Σ_{k≥1} π(y^{1/k})/k,

        J₀(y) = li(y) − Σ_ρ li(y^ρ) − log 2 + ∫_y^∞ dt/(t(t²−1) log t)

    and Möbius inversion π(x) = Σ_n μ(n)/n · J(x^{1/n}) (a *finite* sum, since
    J(y) = 0 for y < 2) gives the practical form

        π(x) ≈ R(x) − Σ_ρ R(x^ρ),      R(x) = Σ_{n≥1} μ(n)/n · li(x^{1/n}).

    See :func:`pi_from_zeros`, :func:`R`.

Every function that takes ``zeros`` accepts either an int (= use the first N
zeros, computed with mpmath and cached to ``data/``), an array of ordinates γ,
or an array of complex ρ.
"""

from __future__ import annotations

import math
import os
from functools import lru_cache
from typing import Callable, Iterable, Literal, Sequence

import numpy as np
from mpmath import mp

__all__ = [
    # exact prime-side objects
    "mangoldt",
    "psi_true",
    "theta_cheb",
    "pi_true",
    "psi_staircase",
    # integrals / Riemann R
    "li",
    "Li",
    "R",
    # zeros
    "first_zeros",
    "as_gammas",
    # the explicit formulae
    "psi_from_zeros",
    "psi_curve",
    "J_from_zeros",
    "pi_from_zeros",
    # duality + diagnostics
    "prime_spectrum",
    "spectrum_peaks",
    "convergence_table",
    # constants
    "LI2",
]

# ----------------------------------------------------------------------------
# constants
# ----------------------------------------------------------------------------

#: li(2) = 1.045163780117492784844588889194…  (the offset in Li(x) = li(x) − li(2))
LI2: float = 1.0451637801174927848445888891946131365226155781512

_LOG_2PI = math.log(2.0 * math.pi)
_DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")
_ZEROS_CACHE = os.path.join(_DATA_DIR, "explicit_zeros.npz")


# ----------------------------------------------------------------------------
# 1. the exact prime side:  ψ, θ, π
# ----------------------------------------------------------------------------


@lru_cache(maxsize=8)
def _primes_upto(n: int) -> np.ndarray:
    """Sieve of Eratosthenes: all primes p ≤ n as an int64 array."""
    if n < 2:
        return np.empty(0, dtype=np.int64)
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.flatnonzero(sieve).astype(np.int64)


def mangoldt(n: int) -> float:
    """
    Von Mangoldt function

        Λ(n) = log p   if n = p^k for a prime p and k ≥ 1,
             = 0       otherwise.

    ψ(x) = Σ_{n ≤ x} Λ(n).
    """
    n = int(n)
    if n < 2:
        return 0.0
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return math.log(p) if m == 1 else 0.0
        p += 1 if p == 2 else 2
    return math.log(n)  # n is itself prime


def psi_true(x: float) -> float:
    """
    Chebyshev's second function

        ψ(x) = Σ_{p^k ≤ x} log p = Σ_{n ≤ x} Λ(n) = log lcm(1, 2, …, ⌊x⌋).

    Computed exactly by sieving and stepping through integer prime powers, so
    there is no floating-point ambiguity at the jump points (e.g. x = 8, 9, 121).

        ψ(10) = log(2³·3²·5·7) = log 2520 = 7.8320141805…
    """
    n = int(math.floor(x))
    if n < 2:
        return 0.0
    total = 0.0
    for p in _primes_upto(n):
        p = int(p)
        lp = math.log(p)
        pk = p
        while pk <= n:
            total += lp
            pk *= p
    return total


def theta_cheb(x: float) -> float:
    """
    Chebyshev's first function

        θ(x) = Σ_{p ≤ x} log p = log( ∏_{p ≤ x} p ) .

    (Named ``theta_cheb``, never ``theta``, to keep it clear of the Jacobi theta
    function used in the functional-equation machinery.)

    Relation to ψ:   ψ(x) = Σ_{k ≥ 1} θ(x^{1/k}).

        θ(10) = log(2·3·5·7) = log 210 = 5.34710…
    """
    n = int(math.floor(x))
    if n < 2:
        return 0.0
    primes = _primes_upto(n)
    return float(np.sum(np.log(primes.astype(np.float64))))


def pi_true(x: float) -> int:
    """
    Exact prime-counting function  π(x) = #{ p prime : p ≤ x }.

        π(10) = 4,  π(100) = 25,  π(1000) = 168.
    """
    n = int(math.floor(x))
    if n < 2:
        return 0
    return int(_primes_upto(n).size)


def psi_staircase(x_grid: Sequence[float] | np.ndarray) -> np.ndarray:
    """
    ψ(x) on a whole grid (vectorised), the exact staircase to plot underneath
    :func:`psi_curve`.  Jumps of size Λ(n) = log p at every prime power n ≤ x.
    """
    xg = np.asarray(x_grid, dtype=float)
    flat = np.atleast_1d(xg).ravel()
    hi = int(math.floor(float(flat.max()))) if flat.size else 0
    if hi < 2:
        return np.zeros_like(xg)
    pp: list[int] = []
    lam: list[float] = []
    for p in _primes_upto(hi):
        p = int(p)
        lp = math.log(p)
        pk = p
        while pk <= hi:
            pp.append(pk)
            lam.append(lp)
            pk *= p
    order = np.argsort(np.asarray(pp))
    ppa = np.asarray(pp)[order]
    cum = np.cumsum(np.asarray(lam)[order])
    idx = np.searchsorted(ppa, np.floor(flat), side="right")
    out = np.where(idx > 0, cum[np.clip(idx - 1, 0, None)], 0.0)
    return out.reshape(xg.shape)


# ----------------------------------------------------------------------------
# 2. logarithmic integral and Riemann's R
# ----------------------------------------------------------------------------


def li(x: float, offset: bool = False) -> float:
    """
    Logarithmic integral.  Both conventions are exposed.

    * **full li** (default, ``offset=False``), the Cauchy principal value

          li(x) = PV ∫₀^x dt / log t = Ei(log x),        x > 0, x ≠ 1

      li(1) = −∞, and li has its real zero at the Ramanujan–Soldner constant
      μ = 1.45136923488…

    * **offset / Gauss Li** (``offset=True``, or use :func:`Li`)

          Li(x) = ∫₂^x dt / log t = li(x) − li(2),   li(2) = 1.04516378011749278…

    Numbers:  li(2) = 1.0451637801,  li(100) = 30.1261415841,
    li(10⁶) = 78627.5491595 versus π(10⁶) = 78498.
    """
    xv = float(x)
    if xv <= 0.0:
        raise ValueError("li(x) requires x > 0")
    if xv == 1.0:
        return float("-inf")
    with mp.workdps(30):
        val = mp.ei(mp.log(mp.mpf(xv)))
    out = float(mp.re(val))
    return out - LI2 if offset else out


def Li(x: float) -> float:
    """Offset (Gauss) logarithmic integral  Li(x) = ∫₂^x dt/log t = li(x) − li(2)."""
    return li(x, offset=True)


@lru_cache(maxsize=4096)
def _inv_zeta_kp1(k: int, dps: int) -> mp.mpf:
    with mp.workdps(dps):
        return +(mp.mpf(1) / mp.zeta(k + 1))


@lru_cache(maxsize=4096)
def _mobius(n: int) -> int:
    """Möbius μ(n): 0 if n has a squared factor, else (−1)^(#prime factors)."""
    if n == 1:
        return 1
    result = 1
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            result = -result
        p += 1 if p == 2 else 2
    if m > 1:
        result = -result
    return result


def R(x: float, terms: int | None = None, dps: int = 30) -> float:
    """
    Riemann's prime-counting approximation

        R(x) = Σ_{n ≥ 1} μ(n)/n · li(x^{1/n})
             = li(x) − ½ li(x^{1/2}) − ⅓ li(x^{1/3}) − ⅕ li(x^{1/5}) + ⅙ li(x^{1/6}) − …

    That Möbius series converges only conditionally, so R is evaluated with
    **Gram's series** (identical value, geometric-fast convergence):

        R(x) = 1 + Σ_{k ≥ 1} (log x)^k / ( k · k! · ζ(k+1) ).

    ``terms`` caps the number of Gram terms; the default adapts until the
    contribution drops below 10^(3−dps) relative.

        R(100)   = 25.66163  (π(100)   = 25)
        R(10⁶)   = 78527.40  (π(10⁶)   = 78498, li(10⁶) = 78627.55)
    """
    xv = float(x)
    if xv <= 0.0:
        raise ValueError("R(x) requires x > 0")
    kmax = 10_000 if terms is None else int(terms)
    with mp.workdps(dps):
        L = mp.log(mp.mpf(xv))
        total = mp.mpf(1)
        term = mp.mpf(1)  # holds L^k / k!
        eps = mp.mpf(10) ** (-(dps - 3))
        for k in range(1, kmax + 1):
            term = term * L / k
            contrib = term / k * _inv_zeta_kp1(k, dps)
            total += contrib
            if terms is None and k > 4 and abs(contrib) < eps * max(abs(total), mp.mpf(1)):
                break
        return float(total)


def _R_mobius(x: float, n_terms: int = 40, dps: int = 30) -> float:
    """Σ_{n=1}^{n_terms} μ(n)/n li(x^{1/n}), the literal Möbius form (cross-check of R)."""
    with mp.workdps(dps):
        L = mp.log(mp.mpf(float(x)))
        tot = mp.mpf(0)
        for n in range(1, n_terms + 1):
            mu = _mobius(n)
            if mu:
                tot += mp.mpf(mu) / n * mp.ei(L / n)
        return float(tot)


# ----------------------------------------------------------------------------
# 3. the zeros
# ----------------------------------------------------------------------------


def first_zeros(n: int, dps: int = 25, cache: bool = True) -> np.ndarray:
    """
    Ordinates γ₁ < γ₂ < … < γ_n of the first ``n`` nontrivial zeros ρ = ½ + iγ.

        γ₁ = 14.134725141734693790,  γ₂ = 21.022039638771554993, …

    Computed with ``mpmath.zetazero`` (used here purely as a supplier/oracle) and
    cached to ``data/explicit_zeros.npz``; the cache is extended in place when
    more zeros are requested, so demos are instant on re-run.
    """
    n = int(n)
    if n <= 0:
        return np.empty(0, dtype=float)
    have = np.empty(0, dtype=float)
    if cache and os.path.exists(_ZEROS_CACHE):
        try:
            have = np.asarray(np.load(_ZEROS_CACHE)["gammas"], dtype=float)
        except Exception:  # pragma: no cover - a corrupt cache must not be fatal
            have = np.empty(0, dtype=float)
    if have.size >= n:
        return have[:n].copy()

    from mpmath import zetazero

    out = [float(v) for v in have]
    with mp.workdps(dps):
        for k in range(len(out) + 1, n + 1):
            out.append(float(mp.im(zetazero(k))))
    arr = np.asarray(out, dtype=float)
    if cache:
        os.makedirs(_DATA_DIR, exist_ok=True)
        np.savez_compressed(_ZEROS_CACHE, gammas=arr, dps=np.int64(dps))
    return arr[:n].copy()


def as_gammas(zeros: int | Iterable[float] | Iterable[complex] | np.ndarray) -> np.ndarray:
    """
    Normalise the several ways one may hand over "the zeros" into a sorted array
    of *distinct* positive ordinates γ > 0, each standing for the conjugate
    **pair** ρ = ½ ± iγ.

    Accepts
      * ``int``            → the first N zeros (see :func:`first_zeros`)
      * real array-like    → already ordinates γ
      * complex array-like → zeros ρ; |Im ρ| is taken

    Every consumer of this array (:func:`psi_curve`, :func:`J_from_zeros`,
    :func:`prime_spectrum`, …) already adds the ρ̄ term itself, so handing over a
    conjugate-symmetric list {½+iγ, ½−iγ, …} must **not** double the answer.
    After folding by |·| the ordinates are therefore de-duplicated: consecutive
    values within a relative 10⁻⁹ of each other collapse to one.  Real zeros are
    never that close: the notorious Lehmer pair γ₆₇₀₉ = 7005.0628662 and
    γ₆₇₁₀ = 7005.1005647 is 0.0377 apart: 5.4·10³ times the 7·10⁻⁶ threshold
    there, so no genuine zero is ever merged away.
    """
    if isinstance(zeros, (int, np.integer)) and not isinstance(zeros, bool):
        return first_zeros(int(zeros))
    arr = np.asarray(zeros if isinstance(zeros, np.ndarray) else list(zeros))
    if arr.size == 0:
        return np.empty(0, dtype=float)
    g = np.abs(arr.imag).astype(float) if np.iscomplexobj(arr) else np.abs(arr.astype(float))
    g = np.sort(g[g > 0.0])
    if g.size > 1:  # collapse ρ and ρ̄ (or any exact repeat) to a single pair
        keep = np.concatenate(([True], np.diff(g) > 1e-9 * np.maximum(1.0, g[1:])))
        g = g[keep]
    return g


# ----------------------------------------------------------------------------
# 4. ψ from the zeros, the von Mangoldt explicit formula
# ----------------------------------------------------------------------------


def psi_curve(
    x_grid: Sequence[float] | np.ndarray,
    zeros: int | Iterable[float] | np.ndarray,
    include_trivial: bool = True,
    chunk: int = 4096,
) -> np.ndarray:
    """
    Vectorised :func:`psi_from_zeros`, the reconstructed staircase on a grid:

        ψ₀(x) ≈ x − 2√x Σ_{γ>0} cos(γ log x − arg ρ)/|ρ| − log 2π − ½ log(1 − x⁻²)

    Memory is bounded by processing ``chunk`` grid points at a time, so a
    20 000-point plot against 2 000 zeros is fine.
    """
    g = as_gammas(zeros)
    xg = np.asarray(x_grid, dtype=float)
    flat = np.atleast_1d(xg).ravel()
    if flat.size and np.any(flat <= 1.0):
        raise ValueError("the explicit formula for psi requires x > 1")

    out = np.empty_like(flat)
    if g.size:
        mod = np.hypot(0.5, g)  # |ρ| = √(¼ + γ²)
        arg = np.arctan2(g, 0.5)  # arg ρ = arctan(2γ)
    for i in range(0, flat.size, chunk):
        xs = flat[i : i + chunk]
        lx = np.log(xs)
        if g.size:
            osc = np.cos(lx[:, None] * g[None, :] - arg[None, :]) / mod[None, :]
            s = 2.0 * np.sqrt(xs) * osc.sum(axis=1)
        else:
            s = np.zeros_like(xs)
        out[i : i + chunk] = xs - s - _LOG_2PI
    if include_trivial:
        out = out - 0.5 * np.log1p(-(flat**-2.0))
    return out.reshape(xg.shape)


def psi_from_zeros(
    x: float,
    zeros: int | Iterable[float] | np.ndarray,
    include_trivial: bool = True,
) -> float:
    """
    Von Mangoldt's explicit formula for Chebyshev's ψ (x > 1):

        ψ₀(x) = x − Σ_ρ x^ρ/ρ − log(2π) − ½ log(1 − x⁻²)

    The ρ-sum is over nontrivial zeros taken in conjugate **pairs**.  With
    ρ = ½ + iγ, |ρ| = √(¼ + γ²), arg ρ = atan2(γ, ½):

        x^ρ/ρ + x^ρ̄/ρ̄ = 2 Re(x^ρ/ρ)
                        = 2 x^½ cos(γ log x − arg ρ) / |ρ| ,

    since x^ρ = x^½ e^{iγ log x} and 1/ρ = e^{−i arg ρ}/|ρ|.  Hence the working
    real form actually evaluated:

        ψ₀(x) ≈ x − 2√x Σ_{γ>0} cos(γ log x − arg ρ)/|ρ| − log 2π − ½ log(1 − x⁻²).

    The last term is exactly the trivial zeros ρ = −2n, because
    −Σ_{n≥1} x^{−2n}/(−2n) = −½ log(1 − x⁻²); pass ``include_trivial=False`` to
    drop it (it is only 5·10⁻³ at x = 10, 5·10⁻⁵ at x = 100).

    What it converges to is ψ₀, the *normalised* ψ: equal to ψ(x) away from
    prime powers, and to ψ(x) − Λ(x)/2 (the midpoint of the jump) at a prime
    power.  Convergence is conditional and slow, the tail beyond γ_N has
    amplitude ~ 2√x/γ_N per zero, but it is real convergence; see
    :func:`convergence_table`.

    **Honest accuracy.**  Over 179 equally spaced points of [10.25, 99.75]
    (step 0.5028; the only integer it hits is 55 = 5·11, not a prime power, so
    the staircase is unambiguous), error versus the exact staircase:

        zeros      0       1      10      50     100     200     500    1000
        RMS     1.6263  1.3882  1.0362  0.6725  0.5462  0.4315  0.2767  0.2007
        max     5.42    4.08    2.98    2.19    2.04    1.90    1.78    1.60

    The RMS falls monotonically, but the *max* barely moves: it is Gibbs
    overshoot pressed against the big jumps (at 500 zeros the worst points are
    x ≈ 52.99, 59.02, 61.03, 67.07, 46.96, right beside the primes 53, 59, 61,
    67, 47).  Away from a jump, 500 zeros give 0.01–0.10 at x ~ 100.

    Parameters
    ----------
    x       : float > 1
    zeros   : int (use the first N), ordinates γ, or complex ρ
    """
    return float(psi_curve(np.asarray([float(x)]), zeros, include_trivial)[0])


# ----------------------------------------------------------------------------
# 5. π from the zeros: Riemann's formula
# ----------------------------------------------------------------------------


def _tail_integral(y: float, dps: int = 30) -> float:
    """∫_y^∞ dt / ( t (t²−1) log t ), the trivial-zero term of J₀(y), y > 1."""
    with mp.workdps(dps):
        yv = mp.mpf(float(y))
        return float(mp.quad(lambda t: 1 / (t * (t * t - 1) * mp.log(t)), [yv, 2 * yv, mp.inf]))


def J_from_zeros(
    y: float,
    zeros: int | Iterable[float] | np.ndarray,
    include_tail: bool = True,
    dps: int = 30,
) -> float:
    """
    Riemann's explicit formula for the weighted prime counter

        J(y) = Σ_{k ≥ 1} π(y^{1/k})/k = Σ_{p^k ≤ y} 1/k
             ( J(10)  = π(10) + π(√10)/2 + π(10^⅓)/3 = 4 + 2/2 + 1/3 = 16/3 = 5.33333…
               J(100) = 25 + 4/2 + 2/3 + 2/4 + 1/5 + 1/6 = 28.53333… )

    namely

        J₀(y) = li(y) − Σ_ρ li(y^ρ) − log 2 + ∫_y^∞ dt/(t(t²−1) log t),

    where li(y^ρ) := Ei(ρ log y) on the principal branch and the ρ-sum is taken
    in conjugate pairs, so

        Σ_ρ li(y^ρ) = 2 Re Σ_{γ>0} Ei( (½ + iγ) log y ).

    The −log 2 is the constant of integration; the integral is the trivial
    zeros (0.1400 at y = 2, 1.840·10⁻³ at y = 10, 9.876·10⁻⁶ at y = 100).

    Like every truncation of an explicit formula this converges to the
    *normalised* J₀ (jumps halved) and only conditionally.  Measured |error| at
    y = 100 (J = 28.53333): 0.088 with 50 zeros, 0.082 with 100, 0.070 with 200,
    0.012 with 500, 0.0074 with 1000, non-monotone, roughly O(1/γ_N).
    """
    g = as_gammas(zeros)
    yv = float(y)
    if yv <= 1.0:
        raise ValueError("J_from_zeros requires y > 1")
    with mp.workdps(dps):
        L = mp.log(mp.mpf(yv))
        zsum = mp.mpf(0)
        for gam in g:
            zsum += 2 * mp.re(mp.ei(mp.mpc(0.5, float(gam)) * L))
        out = float(mp.ei(L) - zsum - mp.log(2))
    if include_tail:
        out += _tail_integral(yv, dps)
    return out


def pi_from_zeros(
    x: float,
    zeros: int | Iterable[float] | np.ndarray,
    terms: int | None = None,
    form: Literal["mobius", "R"] = "mobius",
    dps: int = 30,
) -> float:
    """
    Riemann's formula for π(x), driven entirely by the zeros:

        π(x) ≈ R(x) − Σ_ρ R(x^ρ),        R(z) = Σ_n μ(n)/n · li(z^{1/n}).

    **How it is evaluated.**  Möbius inversion of J(x) = Σ_k π(x^{1/k})/k is a
    *finite* sum, because J(y) = 0 for y < 2:

        π(x) = Σ_{n=1}^{N} μ(n)/n · J(x^{1/n}),        N = ⌊log₂ x⌋,

    and each J comes from :func:`J_from_zeros`.  Expanded term by term this is
    literally  R_N(x) − Σ_ρ R_N(x^ρ) − log 2 · Σ_{n≤N} μ(n)/n + Σ_{n≤N} μ(n)/n ·
    (tail integral), i.e. the headline formula with every constant kept.

    ``form``
      * ``"mobius"`` (default), the exact finite inversion above.  Nothing is
        dropped, so this is the accurate one.
      * ``"R"``: the literal headline R(x) − Σ_ρ R_N(x^ρ), with the *full* R(x)
        from Gram's series and the −log 2 / tail bookkeeping discarded.  Kept
        because that is the form usually quoted.

      The two differ by exactly three bookkeeping pieces (verified to 1.5·10⁻¹⁵
      at x = 100, N = 6):

          mobius − R  =  [Σ_{n≤N} μ(n)/n li(x^{1/n}) − R(x)]   ( +0.11956 )
                       − log 2 · Σ_{n≤N} μ(n)/n               ( −0.09242 )
                       + Σ_{n≤N} μ(n)/n · tail(x^{1/n})       ( −0.00026 )
                       =  +0.02688 .

      So at x = 100 the "R" form sits ≈ 0.027 *below* the Möbius form, not 0.07
      below: the −log 2 term is largely cancelled by replacing the truncated
      li-head Σ_{n≤N} μ(n)/n li(x^{1/n}) with the full R(x).

    ``terms`` overrides N and is clamped to ⌊log₂ x⌋: beyond that x^{1/n} < 2 and
    li(x^{1/n}) runs into its logarithmic singularity at 1.

    Accuracy is limited by how many zeros you supply, the ρ-sum tail decays only
    like 1/(γ log x).  Measured error of the default ``"mobius"`` form:

        zeros:        100        500       1000
        x = 50     −0.0020    −0.0103    −0.0010
        x = 100    −0.0853    −0.0101    −0.0087
        x = 500    −0.2844    −0.0381    +0.0725
        x = 1000   −0.4049    +0.0103    +0.0430
        x = 10⁴    +0.6633    +0.6198    +0.5107

    i.e. ~0.01–0.07 for x ≤ 1000 with 500–1000 zeros, but still ~0.5 at x = 10⁴,
    where 1000 zeros is simply not enough (one needs γ_N ≫ √x log x).
    """
    xv = float(x)
    if xv < 2.0:
        raise ValueError("pi_from_zeros requires x >= 2")
    nmax = max(1, int(math.floor(math.log(xv) / math.log(2.0))))
    N = nmax if terms is None else max(1, min(int(terms), nmax))
    g = as_gammas(zeros)

    if form == "R":
        with mp.workdps(dps):
            L = mp.log(mp.mpf(xv))
            zsum = mp.mpf(0)
            for gam in g:
                rho = mp.mpc(0.5, float(gam))
                inner = mp.mpf(0)
                for n in range(1, N + 1):
                    mu = _mobius(n)
                    if mu:
                        inner += mp.mpf(mu) / n * mp.re(mp.ei(rho * L / n))
                zsum += 2 * inner
        return R(xv, dps=dps) - float(zsum)

    total = 0.0
    for n in range(1, N + 1):
        mu = _mobius(n)
        if mu:
            total += mu / n * J_from_zeros(xv ** (1.0 / n), g, include_tail=True, dps=dps)
    return total


# ----------------------------------------------------------------------------
# 6. the dual view: the music of the primes
# ----------------------------------------------------------------------------


def _window_weights(
    g: np.ndarray, window: str | Callable[[np.ndarray], np.ndarray] | None, gmax: float | None = None
) -> np.ndarray:
    if g.size == 0:
        return g
    T = float(g.max()) if gmax is None else float(gmax)
    if callable(window):
        return np.asarray(window(g), dtype=float)
    if window is None or window == "none":
        return np.ones_like(g)
    if window == "gauss":
        return np.exp(-2.0 * (g / T) ** 2)
    if window == "fejer":
        return np.clip(1.0 - g / T, 0.0, None)
    raise ValueError(f"unknown window {window!r} (use 'none', 'gauss', 'fejer', or a callable)")


def prime_spectrum(
    zeros: int | Iterable[float] | np.ndarray,
    u_grid: Sequence[float] | np.ndarray,
    window: str | Callable[[np.ndarray], np.ndarray] | None = "gauss",
    normalize: bool = True,
    chunk: int = 2048,
) -> np.ndarray:
    """
    "The music of the primes", the **dual** of the explicit formula: read the
    primes straight off the zeros as a Fourier spectrum.

    Differentiate ψ₀(e^u) = e^u − Σ_ρ e^{ρu}/ρ − log 2π − ½ log(1 − e^{−2u})
    with respect to u = log x.  The staircase becomes a comb:

        Σ_{n≥2} Λ(n) δ(u − log n) = e^u − 2 e^{u/2} Σ_{γ>0} cos(γu) − 1/(e^{2u}−1)

    so the purely oscillatory piece

        D(u) = −2 Σ_{γ>0} w(γ) cos(γ u)

    is a spike train with a peak at every u = log p^k, and no peak anywhere
    else.  Rearranging the display above, the *exact* statement is

        D(u) = Σ_{n≥2} (Λ(n)/√n) δ(u − log n) − e^{u/2} + e^{−u/2}/(e^{2u}−1),

    a comb sitting on a smooth negative background −e^{u/2}; the comb's own mean
    density is exactly +e^{u/2}, so the two cancel on average.

    Truncating at T = γ_N (with taper w) replaces δ by the kernel

        W(v) = (1/π) ∫₀^T w(r) cos(r v) dr,   W(0) = (1/π) ∫₀^T w(r) dr,

    so each spike acquires height (Λ(n)/√n)·W(0) and width ≈ 1/T.  With
    ``normalize=True`` (the default, divide by W(0)) the returned density is

        D(u) ≈ Σ_n (Λ(n)/√n) · W(u − log n)/W(0)  −  e^{u/2}/W(0) ,

    i.e. it reads off Λ(n)/√n directly *in the limit T → ∞*:

        log 2 → 0.4901   log 3 → 0.6343   log 4 → 0.3466   log 5 → 0.7198
        log 7 → 0.7355   log 8 → 0.2451   log 9 → 0.3662

    **Honest accuracy at finite T.**  Two systematic effects, both O(1/T):

    * at a non-prime-power u the value is not 0 but ≈ −e^{u/2}/W(0).  Measured
      with 500 zeros ('gauss', T = 811.18, W(0) = 154.45): u = log 6 → −0.0162
      (law: −0.0159), log 10 → −0.0196 (−0.0205), log 20 → −0.0326 (−0.0290),
      log 100 → −0.0615 (−0.0647), all within ~10 % of −√x/W(0).
    * peak heights come out systematically **low**.  Relative deficit versus
      Λ(n)/√n, measured:

          n            2      3      4      5      7      8      9     16     25     49     81
          500 zeros  −1.3%  −1.6%  −4.0%  −2.0%  −2.2%  −6.3%  −5.1% −17.0% −10.9% −14.6% −38.8%
          1000       −0.7%  −1.1%  −2.2%  −1.0%  −1.2%  −4.0%  −3.1% −10.1%  −6.4%  −9.2% −30.1%

      The deficit halves when T doubles, exactly as the O(1/T) analysis says;
      it grows with x because resolving the comb near x needs T ≫ x/log x.
      Peak *positions*, by contrast, are excellent: |u_peak − log n| < 4.5·10⁻⁵
      for the top 14 peaks with 500 zeros.

    Parameters
    ----------
    zeros    : int / ordinates γ / complex ρ (see :func:`as_gammas`)
    u_grid   : where to evaluate.  u = log x, so log 2 = 0.693 … log 100 = 4.605.
    window   : ``'gauss'`` (default, w = exp(−2(γ/T)²)) tapers the truncation and
               kills side-lobes; ``'fejer'`` = triangular; ``'none'`` = sharp
               cut-off (tallest, narrowest peaks but heavy ringing); or a
               callable γ ↦ w(γ).
    normalize: divide by W(0) so peak heights are Λ(n)/√n.

    Returns
    -------
    np.ndarray, same shape as ``u_grid``.
    """
    g = as_gammas(zeros)
    ug = np.asarray(u_grid, dtype=float)
    flat = np.atleast_1d(ug).ravel()
    out = np.zeros_like(flat)
    if g.size == 0:
        return out.reshape(ug.shape)

    T = float(g.max())
    w = _window_weights(g, window, T)
    for i in range(0, flat.size, chunk):
        us = flat[i : i + chunk]
        out[i : i + chunk] = -2.0 * (np.cos(np.outer(us, g)) * w[None, :]).sum(axis=1)

    if normalize:
        # W(0) = (1/2π) ∫_{−∞}^{∞} w(|r|) dr = (1/π) ∫₀^T w(r) dr
        rr = np.linspace(0.0, T, 4001)
        w0 = float(np.trapezoid(_window_weights(rr, window, T), rr)) / math.pi
        if w0 > 0.0:
            out = out / w0
    return out.reshape(ug.shape)


def spectrum_peaks(
    u_grid: np.ndarray,
    spectrum: np.ndarray,
    n_peaks: int = 12,
    prominence: float | None = None,
) -> list[dict]:
    """
    Locate the tallest peaks of a :func:`prime_spectrum` and identify them.

    Peak positions are refined by fitting a parabola to the three samples around
    each local maximum.  Returns a list of dicts sorted by decreasing height::

        {'u': 0.69315, 'height': 0.4886, 'x': 2.0000, 'nearest_n': 2,
         'lambda_over_sqrt_n': 0.4901, 'is_prime_power': True}

    where ``x = e^u`` should land on a prime power and ``height`` approaches
    ``lambda_over_sqrt_n`` as the number of zeros grows.  ``height`` is the raw
    grid sample at the local maximum (only ``u`` is parabola-refined), and at
    finite T it is systematically a few percent low, see the accuracy table in
    :func:`prime_spectrum`.  Positions are far more accurate than heights.
    """
    from scipy.signal import find_peaks

    ug = np.asarray(u_grid, dtype=float)
    sp = np.asarray(spectrum, dtype=float)
    if prominence is None:
        top = float(np.nanmax(sp)) if sp.size else 0.0
        prominence = 0.25 * top if top > 0.0 else None
    idx, _ = find_peaks(sp, prominence=prominence)
    if idx.size == 0:
        return []
    keep = idx[np.argsort(sp[idx])[::-1]][:n_peaks]
    res: list[dict] = []
    for j in keep:
        u0 = float(ug[j])
        if 0 < j < ug.size - 1:
            y0, y1, y2 = float(sp[j - 1]), float(sp[j]), float(sp[j + 1])
            denom = y0 - 2.0 * y1 + y2
            if denom != 0.0:
                u0 = float(ug[j]) + 0.5 * (y0 - y2) / denom * float(ug[j + 1] - ug[j])
        xv = math.exp(u0)
        n = int(round(xv))
        lam = mangoldt(n)
        res.append(
            {
                "u": u0,
                "height": float(sp[j]),
                "x": xv,
                "nearest_n": n,
                "lambda_over_sqrt_n": float(lam / math.sqrt(n)) if n >= 2 else 0.0,
                "is_prime_power": bool(lam > 0.0),
            }
        )
    res.sort(key=lambda d: -d["height"])
    return res


# ----------------------------------------------------------------------------
# 7. convergence diagnostics
# ----------------------------------------------------------------------------


def convergence_table(
    x: float,
    zeros: int | Iterable[float] | np.ndarray,
    counts: Sequence[int] = (0, 1, 10, 50, 100, 200, 500),
    include_trivial: bool = True,
) -> list[dict]:
    """
    How fast do the zeros rebuild ψ(x)?

    For each N in ``counts`` (number of conjugate zero *pairs* used) return::

        {'n_zeros': N, 'gamma_max': γ_N, 'psi_est': …, 'psi_true': ψ(x),
         'psi0_true': ψ₀(x), 'error': psi_est − ψ₀(x), 'abs_error': |…|}

    The explicit formula converges to ψ₀, ψ with the jumps halved,
    ψ₀(x) = ψ(x) − Λ(x)/2 at a prime power, so ``error`` is measured against
    ψ₀, which matters when x itself is a prime power.

    The omitted tail has amplitude ≈ 2√x Σ_{γ>γ_N} 1/|ρ|; since the zeros have
    density (1/2π)log(γ/2π), the residual oscillation shrinks only like
    √x·log γ_N / γ_N per unit of γ.  Slow, but genuinely convergent, and *not*
    monotone in N: at x = 63.7 the |error| runs 0.218 (N=0), 0.691 (1), 1.028
    (10), 0.058 (50), 0.334 (100), 0.058 (500), 0.018 (1000).

    Each N is clipped to the number of zeros supplied, so asking for more zeros
    than you passed silently repeats the last row rather than extrapolating.
    """
    g = as_gammas(zeros)
    xv = float(x)
    psi_x = psi_true(xv)
    lam = mangoldt(int(round(xv))) if abs(xv - round(xv)) < 1e-12 else 0.0
    psi0 = psi_x - 0.5 * lam
    rows: list[dict] = []
    for N in counts:
        N = int(min(int(N), g.size))
        est = psi_from_zeros(xv, g[:N], include_trivial=include_trivial)
        rows.append(
            {
                "n_zeros": N,
                "gamma_max": float(g[N - 1]) if N > 0 else 0.0,
                "psi_est": est,
                "psi_true": psi_x,
                "psi0_true": psi0,
                "error": est - psi0,
                "abs_error": abs(est - psi0),
            }
        )
    return rows
