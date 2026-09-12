"""Zero statistics of ζ(s) and the random-matrix (GUE) connection.

The Riemann zeros ρ = 1/2 + iγ are not just *there*; once you rescale them so
that they have unit mean density, their local statistics are, to every test
anyone has run, identical to the eigenvalue statistics of a large random
Hermitian matrix drawn from the **Gaussian Unitary Ensemble**.  That empirical
fact (Montgomery 1973 for the pair correlation, Odlyzko 1987 for the
nearest-neighbour spacings) is the Montgomery–Odlyzko law, and it is the single
strongest piece of evidence for the Hilbert–Pólya idea that the γ's are the
spectrum of some self-adjoint operator.

This module implements the machinery to *see* that, from scratch:

Unfolding
    The mean density of zeros at height t is (1/2π)·log(t/2π), so raw ordinates
    γₙ have a slowly growing density.  We rescale by the smooth part of the
    counting function,

        N(T) = θ(T)/π + 1 + S(T),        θ = Riemann–Siegel theta,

    i.e. we set  γ̃ₙ = θ(γₙ)/π.  Then γ̃ₙ = n − 1 − S(γₙ) has unit mean spacing
    and the fluctuation S carries all the statistics.

Nearest-neighbour spacings
    sₙ = γ̃ₙ₊₁ − γ̃ₙ.  Uncorrelated ("Poisson") levels would give p(s) = e^{−s},
    which is *maximal* at s = 0.  GUE gives p(s) ∝ s² e^{−4s²/π} (Wigner
    surmise), quadratic level repulsion, p(0) = 0.  The zeros do the latter.

Pair correlation
    Montgomery: the density of differences γ̃ᵢ − γ̃ⱼ = r is 1 − (sin πr / πr)²,
    exactly the GUE/sine-kernel two-point function.

Everything here is checked against an actual random GUE matrix
(``compare_to_random_matrix``) and against the exact sine-kernel Fredholm
determinant (``gue_spacing_exact``), not just against the Wigner surmise.

What the numbers actually are, so nothing here has to be taken on trust
(10142 zeros with 0 < γ < 10⁴; every figure measured in this build):

    D_KS(zeros, exact GUE/Gaudin)      = 0.0287
    D_KS(zeros, Poisson)               = 0.3065      ← 10.7× larger
    D_KS(GUE matrix, exact GUE)        = 0.0071  (p = 0.69)
    Var(spacings): zeros 0.1542, GUE matrix 0.1815, GUE theory 0.1800

The zeros are *not* a perfect GUE fit at this height and this module does not
pretend otherwise, see ``level_repulsion_report`` for the honest reading of
the 0.0287, and for the measured convergence towards GUE with height.

Conventions
-----------
* ``mp.dps`` is set explicitly wherever mpmath is used.
* Bulk numerics are float64 numpy; mpmath is used only as an oracle / for the
  high-precision Taylor data of the Riemann–Siegel remainder.
* Zero ordinates are produced by a self-contained vectorised Riemann–Siegel
  Z-function scan (``zero_ordinates``) because ``mpmath.zetazero`` costs
  ~0.1–0.2 s per zero, i.e. ~30 min for 10⁴ zeros.  Results are cached to
  ``data/`` and cross-checked against ``mpmath.zetazero``.

References
----------
H. L. Montgomery, "The pair correlation of zeros of the zeta function",
    Proc. Sympos. Pure Math. 24 (1973), 181–193.
A. M. Odlyzko, "On the distribution of spacings between zeros of the zeta
    function", Math. Comp. 48 (1987), 273–308.
M. L. Mehta, *Random Matrices*, 3rd ed., Elsevier 2004 (Ch. 6: the sine kernel).
M. Gaudin, "Sur la loi limite de l'espacement des valeurs propres d'une matrice
    aléatoire", Nucl. Phys. 25 (1961), 447–458.
F. Bornemann, "On the numerical evaluation of Fredholm determinants",
    Math. Comp. 79 (2010), 871–915  (the Nyström/Gauss–Legendre method used here).
H. M. Edwards, *Riemann's Zeta Function*, §7.4 (Riemann–Siegel remainder).
"""

from __future__ import annotations

import json
import time
from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import ArrayLike, NDArray
from scipy.interpolate import make_interp_spline
from scipy.special import erf as _erf
from scipy.special import loggamma as _loggamma
from scipy.stats import ks_2samp, kstest

__all__ = [
    # Riemann–Siegel machinery (used for unfolding and for finding zeros fast)
    "riemann_siegel_theta",
    "riemann_siegel_z",
    "zero_ordinates",
    # unfolding + spacings
    "unfold",
    "nearest_neighbour_spacings",
    # spacing laws
    "wigner_surmise_gue",
    "wigner_surmise_gue_cdf",
    "gue_gap_probability",
    "gue_spacing_exact",
    "gue_spacing_exact_cdf",
    "poisson_spacing",
    "poisson_spacing_cdf",
    # two-point statistics
    "pair_correlation",
    "montgomery_prediction",
    "form_factor",
    # reports
    "level_repulsion_report",
    "compare_to_random_matrix",
    # random matrices
    "gue_eigenvalues",
    "unfold_gue",
]

# --------------------------------------------------------------------------- #
# paths
# --------------------------------------------------------------------------- #

_REPO_ROOT = Path(__file__).resolve().parent.parent
_DATA_DIR = _REPO_ROOT / "data"

_TWO_PI = 2.0 * np.pi


def _data_dir() -> Path:
    _DATA_DIR.mkdir(parents=True, exist_ok=True)
    return _DATA_DIR


# --------------------------------------------------------------------------- #
# 1. Riemann–Siegel theta and Z  (vectorised float64)
# --------------------------------------------------------------------------- #


def riemann_siegel_theta(t: ArrayLike) -> NDArray[np.float64]:
    """Riemann–Siegel theta function

        θ(t) = arg Γ(1/4 + it/2) − (t/2)·log π

    (the continuous branch, θ(t) ~ (t/2)log(t/2π) − t/2 − π/8 as t → ∞).

    ``ζ(1/2 + it) = e^{−iθ(t)} Z(t)`` with Z real, so θ is exactly the phase
    that makes the Hardy Z-function real.  θ(T)/π + 1 is the smooth part of the
    zero-counting function N(T), which is what we unfold by.

    Computed with ``scipy.special.loggamma`` on the complex plane, which returns
    the continuous branch of log Γ directly (no unwrapping needed).

    Measured accuracy (this build, against ``mpmath.siegeltheta`` at 30 dps):
    **relative error ≤ 2.6e-16, i.e. float64 machine precision, for every
    t ∈ {1, 5, 10, 14.13, 10², 10³, 10⁴, 10⁵, 10⁶}** (absolute error 9.3e-10 at
    t = 10⁶ simply because θ(10⁶) ≈ 5.5e6).  θ is odd, and that is reproduced
    exactly.
    """
    t_arr = np.asarray(t, dtype=np.float64)
    return np.imag(_loggamma(0.25 + 0.5j * t_arr)) - 0.5 * t_arr * np.log(np.pi)


@lru_cache(maxsize=1)
def _psi_derivative_polys(n_taylor: int = 60) -> tuple[NDArray[np.float64], ...]:
    """Taylor coefficients (about p = 1/2) of Ψ and its derivatives Ψ⁽ᵏ⁾, k ≤ 9.

        Ψ(p) = cos(2π(p² − p − 1/16)) / cos(2πp)

    Ψ looks singular at p = 1/4, 3/4 but is in fact **entire**: at every zero
    p = (2k+1)/4 of the denominator the numerator vanishes too (one checks
    p² − p − 1/16 = (k²−k−1)/4, and k²−k−1 is always odd, so the cosine of
    π(k²−k−1)/2 vanishes).  Evaluating the quotient in float64 near p = 1/4
    loses digits to cancellation, so instead we build the Taylor series about
    p = 1/2 **once, in 60-digit mpmath**, and evaluate that polynomial
    (|p − 1/2| ≤ 1/2) in float64.  Ψ is entire of order 2, so its coefficients
    decay super-geometrically and 60 terms is far below float64 resolution.

    Returns a tuple (Ψ, Ψ', Ψ'', …, Ψ⁽⁹⁾) of polynomial-coefficient arrays in
    u = p − 1/2, ascending order.
    """
    from mpmath import cos as mp_cos
    from mpmath import mp, mpf
    from mpmath import pi as mp_pi

    dps_before = mp.dps
    mp.dps = 60
    try:

        def psi(p: Any) -> Any:
            p = mpf(p)
            return mp_cos(2 * mp_pi * (p * p - p - mpf(1) / 16)) / mp_cos(2 * mp_pi * p)

        taylor = mp.taylor(psi, mpf(1) / 2, n_taylor)
    finally:
        mp.dps = dps_before

    c0 = np.array([float(c) for c in taylor], dtype=np.float64)
    polys = [c0]
    cur = c0
    for _ in range(9):
        cur = cur[1:] * np.arange(1, cur.size, dtype=np.float64) if cur.size > 1 else np.zeros(1)
        polys.append(cur)
    return tuple(polys)


def _polyval_ascending(coeffs: NDArray[np.float64], u: NDArray[np.float64]) -> NDArray[np.float64]:
    """Horner evaluation of  Σ_j c_j u^j  (``coeffs`` ascending in j)."""
    out = np.zeros_like(u)
    for c in coeffs[::-1]:
        out = out * u + c
    return out


def _rs_remainder_terms(u: NDArray[np.float64], k_terms: int) -> list[NDArray[np.float64]]:
    """C₀(p), …, C_K(p) of the Riemann–Siegel remainder, with u = p − 1/2.

    Edwards §7.4 / Haselgrove, expressed through Ψ = C₀:

        C₀ =  Ψ
        C₁ = −Ψ⁽³⁾ / (2⁵·3·π²)
        C₂ =  Ψ⁽²⁾ / (2⁶·π²)  +  Ψ⁽⁶⁾ / (2¹¹·3²·π⁴)
        C₃ = −Ψ⁽¹⁾ / (2⁶·π²)  −  Ψ⁽⁵⁾ / (2⁸·3·5·π⁴)  −  Ψ⁽⁹⁾ / (2¹⁶·3⁴·π⁶)

    These were verified empirically against ``mpmath.siegelz``: adding C_k
    divides the error of Z(t) by a further factor a = √(t/2π), exactly as the
    asymptotic series demands (max |Z − Z_mpmath| over 40 points near t = 10⁴:
    4.9e-6, 2.3e-7, 2.9e-10, 2.8e-11 for K = 0,1,2,3).
    """
    d = _psi_derivative_polys()
    pi2, pi4, pi6 = np.pi**2, np.pi**4, np.pi**6
    terms = [_polyval_ascending(d[0], u)]
    if k_terms >= 1:
        terms.append(-_polyval_ascending(d[3], u) / (96.0 * pi2))
    if k_terms >= 2:
        terms.append(
            _polyval_ascending(d[2], u) / (64.0 * pi2)
            + _polyval_ascending(d[6], u) / (18432.0 * pi4)
        )
    if k_terms >= 3:
        terms.append(
            -_polyval_ascending(d[1], u) / (64.0 * pi2)
            - _polyval_ascending(d[5], u) / (3840.0 * pi4)
            - _polyval_ascending(d[9], u) / (5308416.0 * pi6)
        )
    return terms


def riemann_siegel_z(t: ArrayLike, k_terms: int = 3, chunk: int = 20000) -> NDArray[np.float64]:
    """Hardy's Z-function via the Riemann–Siegel formula (vectorised, float64).

        Z(t) = e^{iθ(t)} ζ(1/2 + it)          (real for real t)

             = 2 Σ_{n=1}^{N} n^{−1/2} cos(θ(t) − t log n)
               + (−1)^{N−1} a^{−1/2} Σ_{k=0}^{K} C_k(p) a^{−k} + O(a^{−K−3/2})

    with  a = √(t/2π),  N = ⌊a⌋,  p = a − N.

    ``k_terms`` = K.  Measured max |Z − ``mpmath.siegelz``| over 40 points, K=3:

        t    = 10      20      50      100     500     10³     10⁴     10⁵
        err  = 9.4e-5  1.7e-5  1.6e-6  4.6e-8  2.6e-9  4.6e-9  2.9e-11 2.6e-10

    Honest caveats.  (i) The series is *asymptotic*: below t ≈ 50 adding C₃
    barely helps and the error is ~1e-5, which is why ``_polish_low_roots``
    hands the low roots to mpmath.  (ii) Above t ≈ 5·10⁴ the error stops
    improving, it is no longer the truncation but float64 argument reduction
    in cos(θ(t) − t log n), whose argument reaches ~5·10⁵ so its ulp is ~6e-11.
    K = 2 and K = 3 are indistinguishable there (2.6e-10 vs 2.6e-10 at t = 10⁵).
    The resulting worst-case *ordinate* error is 5.4e-9 (see ``zero_ordinates``).

    Requires t ≳ 2π for N ≥ 1; for t < 2π the main sum is empty and only the
    remainder survives, verified to still give the right sign and ~1e-4
    accuracy on [5, 2π), which is all the zero scan needs there (Z < 0
    throughout, no zero below γ₁ = 14.13).

    Returns an array of the same shape as ``t`` (0-d for scalar input, matching
    ``riemann_siegel_theta``).
    """
    t_arr = np.atleast_1d(np.asarray(t, dtype=np.float64))
    in_shape = np.shape(t)
    out = np.empty(t_arr.shape, dtype=np.float64)
    log_n_all: NDArray[np.float64] | None = None
    inv_sqrt_all: NDArray[np.float64] | None = None

    for start in range(0, t_arr.size, chunk):
        tc = t_arr[start : start + chunk]
        a = np.sqrt(tc / _TWO_PI)
        n_main = np.floor(a).astype(np.int64)
        u = (a - n_main) - 0.5
        theta = riemann_siegel_theta(tc)

        n_max = int(n_main.max()) if n_main.size else 0
        if n_max >= 1:
            if log_n_all is None or log_n_all.size < n_max:
                n_grid = np.arange(1, n_max + 1, dtype=np.float64)
                log_n_all = np.log(n_grid)
                inv_sqrt_all = 1.0 / np.sqrt(n_grid)
            assert inv_sqrt_all is not None
            log_n = log_n_all[:n_max]
            inv_sqrt = inv_sqrt_all[:n_max]
            phase = theta[:, None] - tc[:, None] * log_n[None, :]
            keep = np.arange(1, n_max + 1)[None, :] <= n_main[:, None]
            main = 2.0 * np.sum(np.where(keep, np.cos(phase) * inv_sqrt[None, :], 0.0), axis=1)
        else:
            main = np.zeros_like(tc)

        terms = _rs_remainder_terms(u, k_terms)
        rem = terms[0].copy()
        inv_a = 1.0 / a
        pw = np.ones_like(a)
        for term in terms[1:]:
            pw = pw * inv_a
            rem = rem + term * pw
        rem = rem * np.where(n_main % 2 == 1, 1.0, -1.0) / np.sqrt(a)

        out[start : start + chunk] = main + rem
    return out.reshape(in_shape)


# --------------------------------------------------------------------------- #
# 2. Zero ordinates:  fast Riemann–Siegel scan, cached to data/
# --------------------------------------------------------------------------- #


def _zeros_cache_path(t_max: float) -> Path:
    """Cache file for a scan up to ``t_max``.

    ``%g`` rather than ``int(round(t_max))``: rounding to an integer made
    t_max = 9999.6, 10000.0 and 10000.4 share a single cache file, so a request
    for one silently returned the zeros of another (short by any zeros in
    (10⁴, 10000.4), or over-long by zeros above 9999.6).  The ``t_max`` stored
    inside the ``.npz`` is re-checked on load as a second line of defence.
    """
    return _data_dir() / f"zeros_rs_scan_T{t_max:g}.npz"


def _polish_low_roots(
    roots: NDArray[np.float64], t_polish: float, dps: int = 30
) -> NDArray[np.float64]:
    """Re-solve Z(t) = 0 in mpmath for the roots below ``t_polish``.

    The Riemann–Siegel asymptotic series is only *asymptotic*: at t ≈ 14
    (a = √(t/2π) ≈ 1.5) truncating after C₃ still leaves |Z| ≈ 8e-5 at the true
    root.  So we hand the handful of low-lying roots to ``mpmath.siegelz`` at
    30 digits.  Cheap (≈80 roots below t = 200) and it makes γ₁ … γ₁₀ agree with
    the published ordinates *exactly* in float64 (measured |Δ| = 0.0).

    Measured residual error of the *unpolished* roots above the cutoff, against
    ``mpmath.zetazero``: 5.4e-9 at n = 100 (γ ≈ 236.5, the worst case in the
    whole range, it sits just above the cutoff), 4.1e-9 at n = 250, 1.8e-9 at
    n = 500, then ≤ 1.1e-11 for every n ≥ 1000 and ≤ 4e-12 for n ≥ 2000.  That
    is ~10⁻⁹ of a mean spacing, i.e. irrelevant to any statistic here.

    A refinement is rejected if it moves the root by more than a quarter of the
    local mean gap 2π/log(t/2π), which would mean the solver jumped to a
    neighbour.
    """
    from mpmath import findroot, mp, siegelz

    idx = np.nonzero(roots < t_polish)[0]
    if idx.size == 0:
        return roots
    out = roots.copy()
    dps_before = mp.dps
    mp.dps = dps
    try:
        for i in idx:
            t0 = float(roots[i])
            tol = 0.25 * _TWO_PI / np.log(max(t0, 7.0) / _TWO_PI)
            try:
                refined = float(findroot(siegelz, mp.mpf(t0)))
            except Exception:  # pragma: no cover - solver hiccup
                continue
            if abs(refined - t0) < tol:
                out[i] = refined
    finally:
        mp.dps = dps_before
    return out


def _bisect_brackets(
    lo: NDArray[np.float64],
    hi: NDArray[np.float64],
    f_lo: NDArray[np.float64],
    steps: int,
) -> NDArray[np.float64]:
    """Vectorised bisection of many sign-change brackets at once."""
    lo, hi, f_lo = lo.copy(), hi.copy(), f_lo.copy()
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        f_mid = riemann_siegel_z(mid)
        same = np.signbit(f_mid) == np.signbit(f_lo)
        lo = np.where(same, mid, lo)
        f_lo = np.where(same, f_mid, f_lo)
        hi = np.where(same, hi, mid)
    return 0.5 * (lo + hi)


def _roots_inside_intervals(
    a: NDArray[np.float64],
    b: NDArray[np.float64],
    n_samples: int,
    bisection_steps: int,
    edge_frac: float = 1e-4,
) -> NDArray[np.float64]:
    """Find all roots of Z strictly inside each interval (aᵢ, bᵢ), vectorised.

    The endpoints are themselves zeros, so each interval is shrunk by
    ``edge_frac`` of its length before sampling, otherwise the ~1e-5 truncation
    noise of the Riemann–Siegel series at low t produces spurious sign flips
    immediately next to the known roots.
    """
    if a.size == 0:
        return np.empty(0, dtype=np.float64)
    pad = edge_frac * (b - a)
    lo_e, hi_e = a + pad, b - pad
    frac = np.linspace(0.0, 1.0, n_samples)
    pts = lo_e[:, None] + (hi_e - lo_e)[:, None] * frac[None, :]
    z = riemann_siegel_z(pts.ravel()).reshape(pts.shape)
    sb = np.signbit(z)
    rows, cols = np.nonzero(sb[:, :-1] != sb[:, 1:])
    if rows.size == 0:
        return np.empty(0, dtype=np.float64)
    return _bisect_brackets(pts[rows, cols], pts[rows, cols + 1], z[rows, cols], bisection_steps)


def _find_zeros_by_scan(
    t_max: float,
    t_min: float = 5.0,
    samples_per_spacing: int = 14,
    bisection_steps: int = 52,
    t_polish: float = 200.0,
    gap_threshold: float = 1.6,
    refine_samples: int = 1500,
) -> NDArray[np.float64]:
    """Locate every t ∈ (t_min, t_max) with Z(t) = 0, by sign change + bisection.

    Step 1 (coarse scan).  The mean gap between consecutive zeros at height t is
    2π/log(t/2π); we sample Z on a uniform grid of step
    (2π/log(t_max/2π)) / ``samples_per_spacing``, which is at least
    ``samples_per_spacing`` samples per mean gap everywhere in the range, then
    bisect all bracketed sign changes simultaneously (52 halvings drives every
    bracket below 1e-14).

    Step 2 (adaptive refinement).  A sign-change scan misses a pair of zeros
    that both fall inside one grid cell, and such close pairs do occur.  A
    missed pair inflates the *unfolded* gap between its surviving neighbours
    from ≈1 to ≈3, so we re-scan every unfolded gap larger than
    ``gap_threshold`` with ``refine_samples`` points, a ~10³× finer resolution,
    and merge whatever we find.

    How much this actually does, measured (count vs θ/π + 1 + backlunds):

        T = 2·10³, default sampling : coarse alone is already complete
        T = 10⁴,   default sampling : coarse alone is already complete
        T = 10⁵,   default sampling : coarse alone misses 14; refinement
                                      recovers exactly those 14

        T = 10⁴, samples_per_spacing = 6 / 4 / 3 / 2:
              coarse alone misses 10 / 30 / 96 / 326, refinement recovers
              *all* of them in every case, restoring the exact count.

    So at the default ``samples_per_spacing`` = 14 this step is a no-op below
    T ≈ 10⁴, the earlier claim that it is "necessary, not cosmetic" is only
    true from T ≈ 10⁵ up.  It is kept because it is what makes the scan robust
    when either the height or the sampling density changes, and
    ``tests/test_statistics.py`` exercises it with a deliberately crippled grid
    rather than leaving it as untested code.

    ``gap_threshold`` = 1.6 is empirical, not proved: at T = 10⁵ the coarse
    scan's unfolded gaps exceed 2.7 in 19 places, which covers all 14 genuine
    misses, so 1.6 has a wide margin.  What actually *certifies* completeness is
    the Riemann–von Mangoldt count check in the test suite, not this threshold.

    Step 3 (polish).  Roots below ``t_polish`` are re-solved in mpmath, where the
    truncated Riemann–Siegel series is least accurate.

    The result is validated *by index* against ``mpmath.zetazero`` and against
    the Riemann–von Mangoldt count in ``tests/test_statistics.py``.
    """
    step = (_TWO_PI / np.log(t_max / _TWO_PI)) / samples_per_spacing
    grid = np.arange(t_min, t_max + step, step)
    z = riemann_siegel_z(grid)

    sign = np.signbit(z)
    idx = np.nonzero(sign[:-1] != sign[1:])[0]
    roots = _bisect_brackets(grid[idx], grid[idx + 1], z[idx], bisection_steps)
    roots = np.sort(roots[(roots > t_min) & (roots < t_max)])

    # --- step 2: hunt for pairs hidden inside a single coarse cell ---------- #
    flagged = np.nonzero(np.diff(riemann_siegel_theta(roots) / np.pi) > gap_threshold)[0]
    extra = _roots_inside_intervals(
        roots[flagged], roots[flagged + 1], refine_samples, bisection_steps
    )
    if extra.size:
        roots = np.sort(np.concatenate([roots, extra]))
        roots = roots[np.concatenate([[True], np.diff(roots) > 1e-6])]

    return _polish_low_roots(roots, t_polish)


def zero_ordinates(
    n: int | None = None,
    *,
    t_max: float = 10000.0,
    use_cache: bool = True,
    source: str = "auto",
) -> NDArray[np.float64]:
    """Ordinates γₙ > 0 of the non-trivial zeros ρ = 1/2 + iγₙ, ascending.

    Parameters
    ----------
    n
        Return only the first ``n`` ordinates.  ``None`` → every zero below
        ``t_max``.
    t_max
        Height to scan to.  T = 10⁴ contains 10142 zeros.
    use_cache
        Read/write ``data/zeros_rs_scan_T<t_max>.npz``.
    source
        ``"auto"`` (default), cache if present, else the vectorised
        Riemann–Siegel scan (a few seconds for T = 10⁴), then cache.
        ``"zeta.zeros"``: delegate to ``zeta.zeros.first_n_zeros`` (an mpmath
        ``zetazero`` driver, ~0.1–0.2 s per zero; use only for small ``n``).

    Notes
    -----
    ``mpmath.zetazero`` costs ~0.1 s/zero at n ~ 10³ (measured), i.e. ≈ 30
    minutes for 10⁴ zeros, so it is *not* the bulk source here.  It is used as
    an independent oracle instead.

    Verified accuracy and completeness (measured, not asserted):

    * T = 10⁴ → 10142 zeros in ≈5 s;  T = 10⁵ → 138069 zeros in ≈21 s.
    * **Completeness.**  N(T) from this list equals θ(T)/π + 1 + backlunds(T)
      at 400 heights spaced 25 apart across [20, 10⁴], 0 mismatches, and at
      400 heights across [200, 10⁵]: 0 mismatches.  Independently, writing
      S(γₙ) = n − 1 − θ(γₙ)/π, a single missed or spurious zero would shift
      every later value by 1; the mean of S over consecutive blocks of 250
      stays inside [0.4965, 0.5036] for T = 10⁴ and [0.4966, 0.5028] for
      T = 10⁵ (½ is the correct value, since S evaluated *at* a zero is the
      mid-jump average).
    * **Index alignment.**  N(midpoint(γₙ₋₁, γₙ)) = n verified at 295 indices
      (all of n ≤ 39 plus 260 random n ≤ 10142): 0 mismatches.
    * **Ordinate error** vs ``mpmath.zetazero``: exactly 0.0 for n ≤ 50
      (mpmath-polished), worst case 5.4e-9 at n = 100, ≤ 1.1e-11 for n ≥ 1000.
    """
    if source == "zeta.zeros":
        if n is None:
            raise ValueError("source='zeta.zeros' requires an explicit n")
        from zeta.zeros import first_n_zeros  # type: ignore[import-not-found]

        return np.asarray([float(g) for g in first_n_zeros(n)], dtype=np.float64)
    if source != "auto":
        raise ValueError(f"unknown source {source!r}")

    path = _zeros_cache_path(t_max)
    gammas: NDArray[np.float64] | None = None
    if use_cache and path.exists():
        with np.load(path) as fh:
            cached, cached_t_max = fh["gammas"], float(fh["t_max"])
        # Never trust the file name alone: a cache written for a different
        # height must be rebuilt, not silently reused.
        if cached_t_max == float(t_max):
            gammas = cached
    if gammas is None:
        gammas = _find_zeros_by_scan(t_max)
        if use_cache:
            np.savez_compressed(path, gammas=gammas, t_max=np.float64(t_max))
    if n is not None:
        if n > gammas.size:
            raise ValueError(
                f"only {gammas.size} zeros are available below T={t_max}; "
                f"raise t_max to obtain {n}"
            )
        gammas = gammas[:n]
    return np.ascontiguousarray(gammas, dtype=np.float64)


# --------------------------------------------------------------------------- #
# 3. Unfolding
# --------------------------------------------------------------------------- #


def unfold(gammas: ArrayLike) -> NDArray[np.float64]:
    """Rescale ordinates to unit mean spacing:  γ̃ₙ = θ(γₙ)/π.

    Why θ/π rather than the asymptotic formula?
    -------------------------------------------
    The Riemann–von Mangoldt formula is *exact*:

        N(T) = θ(T)/π + 1 + S(T),        S(T) = (1/π)·arg ζ(1/2 + iT),

    with θ the Riemann–Siegel theta function and S(T) = O(log T) of mean zero.
    So θ(T)/π is precisely the smooth (mean) part of the counting function, and
    using it as the unfolding map gives

        γ̃ₙ = θ(γₙ)/π = n − 1 − S(γₙ),

    which has *exactly* unit mean density with no residual drift: all the
    statistics live in S.

    The commonly quoted alternative

        γ̃ₙ ≈ (γₙ/2π)·log(γₙ/2π) − γₙ/2π

    is just the first two terms of θ(T)/π  (θ(T)/π = that − 1/8 + 1/(8πT) + …).
    It differs by a constant plus O(1/T), so it gives the same *spacings* up to
    O(1/T²), but at the heights we work at (γ ~ 10–10⁴) the exact θ costs
    nothing and removes a systematic bias, so we use θ/π.

    Returns
    -------
    np.ndarray of unfolded ordinates, same length as the input.
    """
    g = np.asarray(gammas, dtype=np.float64)
    return riemann_siegel_theta(g) / np.pi


def nearest_neighbour_spacings(gammas: ArrayLike) -> NDArray[np.float64]:
    """Consecutive spacings sₙ = γ̃ₙ₊₁ − γ̃ₙ of the *unfolded* ordinates.

    By construction ⟨s⟩ → 1.  Length is len(gammas) − 1.
    """
    return np.diff(unfold(gammas))


# --------------------------------------------------------------------------- #
# 4. Spacing laws
# --------------------------------------------------------------------------- #


def wigner_surmise_gue(s: ArrayLike) -> NDArray[np.float64]:
    """Wigner surmise for β = 2 (GUE) nearest-neighbour spacings:

        p(s) = (32/π²) s² exp(−4s²/π),      s ≥ 0

    Normalised so ∫₀^∞ p = 1 and ∫₀^∞ s·p = 1.  Note p(s) ~ s² as s → 0:
    quadratic level repulsion, so P(s < ε) ~ ε³, eigenvalues (and zeros)
    actively avoid one another.  This is the *exact* spacing law of a 2×2 GUE
    matrix and an astonishingly good (≲ 2%) approximation to the N → ∞ answer.
    """
    x = np.asarray(s, dtype=np.float64)
    return np.where(x >= 0.0, (32.0 / np.pi**2) * x**2 * np.exp(-4.0 * x**2 / np.pi), 0.0)


def wigner_surmise_gue_cdf(s: ArrayLike) -> NDArray[np.float64]:
    """CDF of the GUE Wigner surmise.

    With a = 4/π,  F(s) = ∫₀ˢ (32/π²) x² e^{−a x²} dx
                        = erf(√a·s) − (2/√π)·√a·s·e^{−a s²}.
    """
    x = np.clip(np.asarray(s, dtype=np.float64), 0.0, None)
    a = 4.0 / np.pi
    val = _erf(np.sqrt(a) * x) - (2.0 / np.sqrt(np.pi)) * np.sqrt(a) * x * np.exp(-a * x * x)
    return np.where(np.asarray(s, dtype=np.float64) > 0.0, val, 0.0)


def poisson_spacing(s: ArrayLike) -> NDArray[np.float64]:
    """Spacing density of *uncorrelated* levels of unit mean density:

        p(s) = e^{−s},      s ≥ 0

    The null hypothesis: what one would see if the zeros were sprinkled at
    random with the right mean density and no interaction.  It is *maximal* at
    s = 0, random points clump.  The Riemann zeros emphatically do not.
    """
    x = np.asarray(s, dtype=np.float64)
    return np.where(x >= 0.0, np.exp(-np.clip(x, 0.0, None)), 0.0)


def poisson_spacing_cdf(s: ArrayLike) -> NDArray[np.float64]:
    """CDF F(s) = 1 − e^{−s} of the Poisson (uncorrelated) spacing law."""
    x = np.asarray(s, dtype=np.float64)
    return np.where(x > 0.0, 1.0 - np.exp(-np.clip(x, 0.0, None)), 0.0)


# --- exact (N → ∞) GUE spacing law via the sine-kernel Fredholm determinant --- #


def _sine_kernel_gap(s_values: NDArray[np.float64], n_quad: int = 60) -> NDArray[np.float64]:
    """E(0;s) = det(I − K_s) for the sine kernel, by Nyström–Gauss–Legendre.

        K(x,y) = sin(π(x−y)) / (π(x−y))   acting on   L²[−s/2, s/2]

    Bornemann (2010): discretise with m-point Gauss–Legendre nodes xᵢ and
    weights wᵢ, form the symmetric matrix Aᵢⱼ = √(wᵢwⱼ)·K(xᵢ,xⱼ); its
    eigenvalues converge *exponentially* to those of the integral operator, and
    E(0;s) = Π (1 − λᵢ).  60 nodes is machine precision for s ≤ 6.
    """
    nodes, weights = np.polynomial.legendre.leggauss(n_quad)
    out = np.empty(s_values.shape, dtype=np.float64)
    for i, s in enumerate(s_values):
        if s <= 0.0:
            out[i] = 1.0
            continue
        x = 0.5 * s * nodes  # map [-1, 1] -> [-s/2, s/2]
        w = 0.5 * s * weights
        k = np.sinc(x[:, None] - x[None, :])  # np.sinc(z) = sin(πz)/(πz), = 1 at 0
        sw = np.sqrt(w)
        a = sw[:, None] * k * sw[None, :]
        lam = np.linalg.eigvalsh(a)
        out[i] = float(np.prod(np.clip(1.0 - lam, 0.0, None)))
    return out


@lru_cache(maxsize=4)
def _gue_gap_spline(s_max: float = 6.0, h: float = 0.0025) -> Any:
    """Cached quintic B-spline of E(0;s) on [0, s_max]; persisted to ``data/``.

    A quintic spline is used so that the *second* derivative (the spacing
    density p = E'') is still a smooth cubic and accurate to O(h⁴).
    """
    path = _data_dir() / f"gue_gap_sinekernel_smax{s_max:g}_h{h:g}.npz"
    if path.exists():
        with np.load(path) as fh:
            grid, gap = fh["s"], fh["E"]
    else:
        grid = np.arange(0.0, s_max + 0.5 * h, h)
        gap = _sine_kernel_gap(grid)
        np.savez_compressed(path, s=grid, E=gap)
    return make_interp_spline(grid, gap, k=5)


def gue_gap_probability(s: ArrayLike) -> NDArray[np.float64]:
    """E(0;s): probability that an interval of length s of the unit-density GUE
    spectrum contains **no** eigenvalue.  Exact N → ∞ sine-kernel answer.

        E(0;s) = det(I − K_s),      K = sine kernel

    E(0;0) = 1, dE/ds(0) = −1, and E decays like exp(−π²s²/8) (Dyson).
    """
    x = np.asarray(s, dtype=np.float64)
    spl = _gue_gap_spline()
    hi = float(spl.t[-1])
    return np.where(x <= 0.0, 1.0, np.where(x >= hi, 0.0, spl(np.clip(x, 0.0, hi))))


def gue_spacing_exact(s: ArrayLike) -> NDArray[np.float64]:
    """Exact GUE nearest-neighbour spacing density (the Gaudin distribution).

        p(s) = d²E(0;s)/ds²

    with E(0;s) = det(I − K_s) the sine-kernel gap probability above.  This is
    the true N → ∞ law; ``wigner_surmise_gue`` is the 2×2 approximation to it.
    Measured difference between the two (this build):

    * max |p_exact − p_Wigner| = 0.00516, at s = 1.106;
    * max |F_exact − F_Wigner| = 0.00155;
    * the exact peak is at s = 0.88251 with height 0.93369, the Wigner peak at
      s = 0.88623 with height 0.93680, so the exact law's peak is slightly
      **lower and slightly LEFT of** Wigner's (an earlier version of this
      docstring said "right"; it is left, by 0.0037);
    * the exact law has the fatter tail: p_exact/p_Wigner = 1.07, 1.15, 1.27,
      1.42 at s = 2.5, 3, 3.5, 4.

    Both have cubic level repulsion; the exact small-s law is F(s) → (π²/9)s³
    (module reproduces 1.09654 vs π²/9 = 1.09662 at s = 0.01), while Wigner
    gives 32/(3π²) = 1.08076.

    Source: Gaudin (1961); Mehta, *Random Matrices* 3rd ed. §6.  Computed here
    by the Nyström–Gauss–Legendre Fredholm-determinant method of Bornemann
    (2010), no tabulated constants.
    """
    x = np.asarray(s, dtype=np.float64)
    spl = _gue_gap_spline()
    hi = float(spl.t[-1])
    d2 = spl.derivative(2)
    return np.where((x <= 0.0) | (x >= hi), 0.0, d2(np.clip(x, 0.0, hi)))


def gue_spacing_exact_cdf(s: ArrayLike) -> NDArray[np.float64]:
    """CDF of the exact GUE (Gaudin) spacing law.

    Since p = E'' and E'(0) = −1,      F(s) = ∫₀ˢ E'' = 1 + E'(s).
    """
    x = np.asarray(s, dtype=np.float64)
    spl = _gue_gap_spline()
    hi = float(spl.t[-1])
    d1 = spl.derivative(1)
    return np.where(x <= 0.0, 0.0, np.where(x >= hi, 1.0, 1.0 + d1(np.clip(x, 0.0, hi))))


# --------------------------------------------------------------------------- #
# 5. Pair correlation and form factor
# --------------------------------------------------------------------------- #


def montgomery_prediction(r: ArrayLike) -> NDArray[np.float64]:
    """Montgomery's pair-correlation function (= GUE / sine-kernel two-point):

        R₂(r) = 1 − (sin πr / πr)²

    R₂(0) = 0, the *correlation hole*: no two zeros want to coincide.  R₂ → 1
    with damped oscillations of period 1, and R₂(k) = 1 exactly at every
    non-zero integer k because sin(πk) = 0.
    """
    x = np.asarray(r, dtype=np.float64)
    return 1.0 - np.sinc(x) ** 2  # np.sinc(x) = sin(πx)/(πx), = 1 at x = 0


def pair_correlation(
    gammas: ArrayLike,
    r_max: float = 3.0,
    bins: int = 60,
) -> tuple[NDArray[np.float64], NDArray[np.float64]]:
    """Empirical pair correlation of the unfolded zeros.

    Histograms every positive difference γ̃ᵢ − γ̃ⱼ < r_max and normalises so the
    result estimates R₂(r).  The unfolded process has unit density, so the
    expected number of ordered pairs with difference in [r, r+Δ) is
    (L − r)·∫ R₂ over that bin, where L = γ̃_N − γ̃_1 is the observation window;
    dividing by Δ·(L − r) removes both the bin width and the O(r/L) edge effect.

    Returns
    -------
    (r_centres, R2_empirical), compare against ``montgomery_prediction(r)``.
    """
    g = np.sort(unfold(gammas))
    if g.size < 3:
        raise ValueError("need at least 3 zeros")
    span = float(g[-1] - g[0])

    # Collect all pairs closer than r_max using an index-offset window; grow the
    # window until it provably reaches beyond r_max everywhere.
    width = max(2, int(np.ceil(2.0 * r_max)))
    while width < g.size - 1 and float(np.min(g[width:] - g[:-width])) < r_max:
        width = min(2 * width, g.size - 1)

    chunks = []
    for k in range(1, width + 1):
        d = g[k:] - g[:-k]
        chunks.append(d[d < r_max])
    all_diffs = np.concatenate(chunks) if chunks else np.empty(0)

    counts, edges = np.histogram(all_diffs, bins=bins, range=(0.0, r_max))
    centres = 0.5 * (edges[:-1] + edges[1:])
    delta = float(edges[1] - edges[0])
    density = counts / (delta * (span - centres))
    return centres, density


def form_factor(
    gammas: ArrayLike,
    tau_grid: ArrayLike,
    smooth: int = 0,
) -> NDArray[np.float64]:
    """Spectral form factor of the unfolded zeros,

        K(τ) = (1/N) · |Σ_{n=1}^{N} exp(2πi τ γ̃ₙ)|²

    The GUE prediction for the connected form factor is

        K_GUE(τ) = min(|τ|, 1),

    i.e. a linear "ramp" up to the Heisenberg time τ = 1 followed by a
    "plateau".  A Poisson process instead gives K(τ) ≡ 1 for every τ > 0, no
    ramp at all, which is what makes the ramp the signature of level repulsion.

    Caveats, stated honestly: K(τ) from one finite sample is (asymptotically)
    an exponential random variable with mean ≈ K_GUE(τ) and *unit relative
    variance*, so a single realisation is very noisy; pass ``smooth=k`` to
    boxcar-average over 2k+1 neighbouring τ values, which is the standard fix.
    There is also a large disconnected contribution as τ → 0, and, this being
    the zeta function and not a generic system, genuine arithmetic structure
    (peaks near τ = log p / 2π · …) on top of the RMT curve.

    Parameters
    ----------
    smooth
        Half-width, in grid points, of a boxcar average applied to K.  0 = raw.
    """
    g = unfold(gammas)
    tau = np.atleast_1d(np.asarray(tau_grid, dtype=np.float64))
    n = g.size
    k = np.empty(tau.shape, dtype=np.float64)
    step = max(1, int(4_000_000 // max(n, 1)))  # bound temporary memory
    for i in range(0, tau.size, step):
        block = tau[i : i + step]
        phase = np.exp(2j * np.pi * np.outer(block, g))
        k[i : i + step] = np.abs(phase.sum(axis=1)) ** 2 / n
    if smooth > 0:
        kernel = np.ones(2 * smooth + 1)
        k = np.convolve(k, kernel, mode="same") / np.convolve(np.ones_like(k), kernel, mode="same")
    return k


# --------------------------------------------------------------------------- #
# 6. Random matrices
# --------------------------------------------------------------------------- #


def gue_eigenvalues(n: int, seed: int | None = None) -> NDArray[np.float64]:
    """Eigenvalues of one n×n matrix drawn from the Gaussian Unitary Ensemble.

    Construction: draw A with iid complex entries, Re A_ij, Im A_ij ~ N(0,1),
    and set H = (A + A†)/2.  Then H is Hermitian with

        E[H_ii²] = 1,     E[|H_ij|²] = 1   (i ≠ j),

    which is the GUE with density ∝ exp(−½ Tr H²).  Its spectrum fills the
    semicircle of radius R = 2√n with density ρ(x) = √(R² − x²)/(2π)
    (normalised to ∫ρ = n).

    Returns the n eigenvalues in ascending order.
    """
    rng = np.random.default_rng(seed)
    a = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    h = 0.5 * (a + a.conj().T)
    return np.linalg.eigvalsh(h)


def unfold_gue(eigenvalues: ArrayLike, n: int) -> NDArray[np.float64]:
    """Unfold GUE eigenvalues with the exact integrated semicircle law.

        F(λ) = ∫_{−R}^{λ} √(R²−x²)/(2π) dx
             = [ (λ/2)√(R²−λ²) + (R²/2)·arcsin(λ/R) ] / (2π) + n/4·…

    concretely, with R = 2√n,

        F(λ) = ( (λ/2)√(R²−λ²) + (R²/2)·arcsin(λ/R) ) / (2π) + n/2.

    This is the random-matrix analogue of γ̃ = θ(γ)/π: it maps the eigenvalues
    onto a sequence of unit mean density, so the resulting spacings are directly
    comparable with the unfolded zeta spacings.
    """
    lam = np.asarray(eigenvalues, dtype=np.float64)
    r = 2.0 * np.sqrt(n)
    x = np.clip(lam, -r, r)
    integ = 0.5 * x * np.sqrt(np.maximum(r * r - x * x, 0.0)) + 0.5 * r * r * np.arcsin(x / r)
    return integ / (2.0 * np.pi) + 0.5 * n


def _gue_bulk_spacings(
    n_spacings: int,
    matrix_size: int = 800,
    bulk_fraction: float = 0.6,
    seed: int | None = 0,
) -> NDArray[np.float64]:
    """Accumulate unfolded *bulk* spacings from independent GUE matrices.

    Only the middle ``bulk_fraction`` of each spectrum is used: near the
    semicircle edge the density vanishes like a square root and the local
    statistics are Airy, not sine-kernel.
    """
    rng = np.random.default_rng(seed)
    keep = int(matrix_size * bulk_fraction)
    lo = (matrix_size - keep) // 2
    out: list[NDArray[np.float64]] = []
    total = 0
    while total < n_spacings:
        lam = gue_eigenvalues(matrix_size, seed=int(rng.integers(0, 2**31 - 1)))
        s = np.diff(unfold_gue(lam[lo : lo + keep], matrix_size))
        out.append(s)
        total += s.size
    return np.concatenate(out)[:n_spacings]


# --------------------------------------------------------------------------- #
# 7. Reports
# --------------------------------------------------------------------------- #


def level_repulsion_report(gammas: ArrayLike) -> dict[str, Any]:
    """Kolmogorov–Smirnov the empirical spacings against GUE and against Poisson.

    Returns a dict holding, for each of three fully-specified null hypotheses
    (exact GUE / Gaudin, the GUE Wigner surmise, and Poisson), the KS statistic
    D = sup_s |F_emp(s) − F(s)| and its p-value; plus summary moments and the
    observed fraction of very small spacings, the sharpest single signature of
    repulsion, since Poisson predicts ≈ 9.5% of spacings below 0.1 whereas GUE
    predicts ≈ 0.11%.

    Caveat stated up front: consecutive spacings are *not* independent, so KS
    p-values are indicative rather than exact.  The statistic D itself is
    model-free and is the meaningful comparison.

    What this actually returns for the 10142 zeros below T = 10⁴ (measured):
    D_GUE(Gaudin) = 0.0287, D_Wigner = 0.0273, D_Poisson = 0.3065, a ratio of
    10.7, and 0.049 % of spacings below 0.1 against Poisson's 9.52 %.

    Do **not** read D_GUE = 0.029 as "GUE fits perfectly": with 10141 spacings
    the KS noise floor is ~0.014, so the residual is real, and the observed
    variance is 0.1542 against the GUE value 0.1800: 14 % low.  That is a
    genuine finite-height effect (the corrections to Montgomery–Odlyzko are
    O(1/log γ), and log(10⁴/2π) is only 7.4), not a numerical artefact: the
    variance climbs monotonically with height, 0.1442 in the lowest decile of
    our range to 0.1578 in the highest, and at matched sample size (2000
    spacings each) D falls from 0.0427 in the lowest band to 0.0280 in the
    highest.  A random GUE *matrix* run through the identical pipeline gives
    D = 0.007 (p = 0.69), which is what proves the pipeline itself is sound.
    """
    s = np.asarray(nearest_neighbour_spacings(gammas), dtype=np.float64)
    ks_gue = kstest(s, gue_spacing_exact_cdf)
    ks_wig = kstest(s, wigner_surmise_gue_cdf)
    ks_poi = kstest(s, poisson_spacing_cdf)

    grid = np.linspace(1e-9, 6.0, 60001)
    p_exact = gue_spacing_exact(grid)
    m1 = float(np.trapezoid(grid * p_exact, grid))
    m2 = float(np.trapezoid(grid**2 * p_exact, grid))

    g = np.asarray(gammas, dtype=np.float64)
    return {
        "n_zeros": int(g.size),
        "n_spacings": int(s.size),
        "gamma_min": float(g.min()),
        "gamma_max": float(g.max()),
        "mean_spacing": float(s.mean()),
        "var_spacing": float(s.var(ddof=1)),
        "min_spacing": float(s.min()),
        "max_spacing": float(s.max()),
        "ks_gue_exact": {"statistic": float(ks_gue.statistic), "pvalue": float(ks_gue.pvalue)},
        "ks_gue_wigner": {"statistic": float(ks_wig.statistic), "pvalue": float(ks_wig.pvalue)},
        "ks_poisson": {"statistic": float(ks_poi.statistic), "pvalue": float(ks_poi.pvalue)},
        "ks_ratio_poisson_over_gue": float(ks_poi.statistic / ks_gue.statistic),
        "frac_spacing_below_0.1": {
            "observed": float(np.mean(s < 0.1)),
            "gue_exact": float(gue_spacing_exact_cdf(0.1)),
            "poisson": float(poisson_spacing_cdf(0.1)),
        },
        "variance_reference": {"gue_exact": m2 - m1 * m1, "poisson": 1.0},
        "verdict": (
            f"{'GUE' if ks_gue.statistic < ks_poi.statistic else 'Poisson'} "
            f"(D_GUE={ks_gue.statistic:.4f} vs D_Poisson={ks_poi.statistic:.4f})"
        ),
    }


def compare_to_random_matrix(
    n_zeros: int = 10000,
    seed: int = 0,
    *,
    matrix_size: int = 800,
    bins: int = 60,
    s_max: float = 4.0,
    gammas: ArrayLike | None = None,
) -> dict[str, Any]:
    """The headline experiment: zeta zeros vs an *actual* random GUE matrix.

    Draws enough independent GUE matrices to yield ~``n_zeros`` bulk eigenvalue
    spacings, unfolds them with the semicircle law, unfolds the first
    ``n_zeros`` zeta ordinates with θ/π, and compares the two spacing samples
    with a **two-sample** KS test, no fitted parameters, no model in between.
    For contrast the same comparison is made against a Poisson (exponential)
    sample of the same size.

    Returns a dict with both histograms on identical bins, the two-sample KS
    results, and the one-sample KS of each sample against the exact Gaudin law.
    """
    g = zero_ordinates(n_zeros) if gammas is None else np.asarray(gammas, dtype=np.float64)
    s_zeta = nearest_neighbour_spacings(g)
    s_gue = _gue_bulk_spacings(s_zeta.size, matrix_size=matrix_size, seed=seed)
    rng = np.random.default_rng(seed + 1)
    s_poi = rng.exponential(1.0, size=s_zeta.size)

    edges = np.linspace(0.0, s_max, bins + 1)
    centres = 0.5 * (edges[:-1] + edges[1:])
    h_zeta, _ = np.histogram(s_zeta, bins=edges, density=True)
    h_gue, _ = np.histogram(s_gue, bins=edges, density=True)
    h_poi, _ = np.histogram(s_poi, bins=edges, density=True)

    ks_zeta_gue = ks_2samp(s_zeta, s_gue)
    ks_zeta_poi = ks_2samp(s_zeta, s_poi)
    ks_gue_gaudin = kstest(s_gue, gue_spacing_exact_cdf)
    ks_zeta_gaudin = kstest(s_zeta, gue_spacing_exact_cdf)

    return {
        "n_spacings": int(s_zeta.size),
        "matrix_size": int(matrix_size),
        "seed": int(seed),
        "gamma_max": float(np.asarray(g).max()),
        "mean_spacing_zeta": float(s_zeta.mean()),
        "mean_spacing_gue": float(s_gue.mean()),
        "var_spacing_zeta": float(s_zeta.var(ddof=1)),
        "var_spacing_gue": float(s_gue.var(ddof=1)),
        "bin_centres": centres,
        "hist_zeta": h_zeta,
        "hist_gue_matrix": h_gue,
        "hist_poisson": h_poi,
        "hist_gue_exact": gue_spacing_exact(centres),
        "max_hist_abs_diff_zeta_vs_gue": float(np.max(np.abs(h_zeta - h_gue))),
        "max_hist_abs_diff_zeta_vs_poisson": float(np.max(np.abs(h_zeta - h_poi))),
        "ks2_zeta_vs_gue_matrix": {
            "statistic": float(ks_zeta_gue.statistic),
            "pvalue": float(ks_zeta_gue.pvalue),
        },
        "ks2_zeta_vs_poisson": {
            "statistic": float(ks_zeta_poi.statistic),
            "pvalue": float(ks_zeta_poi.pvalue),
        },
        "ks_gue_matrix_vs_gaudin": {
            "statistic": float(ks_gue_gaudin.statistic),
            "pvalue": float(ks_gue_gaudin.pvalue),
        },
        "ks_zeta_vs_gaudin": {
            "statistic": float(ks_zeta_gaudin.statistic),
            "pvalue": float(ks_zeta_gaudin.pvalue),
        },
    }


# --------------------------------------------------------------------------- #
# CLI demo
# --------------------------------------------------------------------------- #


def _demo() -> None:  # pragma: no cover - convenience entry point
    t0 = time.time()
    gammas = zero_ordinates()
    print(f"zeros: {gammas.size} up to T = {gammas[-1]:.3f}   ({time.time() - t0:.2f} s)")

    rep = level_repulsion_report(gammas)
    print(json.dumps(rep, indent=2))

    r, r2 = pair_correlation(gammas)
    sel = r > 0.2
    err = float(np.max(np.abs(r2[sel] - montgomery_prediction(r[sel]))))
    print(f"pair correlation: max |empirical − Montgomery| = {err:.4f} for r > 0.2")

    cmp = compare_to_random_matrix(min(gammas.size, 10000))
    print(
        "zeta vs GUE matrix: D = {:.4f} (p = {:.3g});  "
        "zeta vs Poisson: D = {:.4f} (p = {:.3g})".format(
            cmp["ks2_zeta_vs_gue_matrix"]["statistic"],
            cmp["ks2_zeta_vs_gue_matrix"]["pvalue"],
            cmp["ks2_zeta_vs_poisson"]["statistic"],
            cmp["ks2_zeta_vs_poisson"]["pvalue"],
        )
    )


if __name__ == "__main__":  # pragma: no cover
    _demo()
