"""``localpos``, the place-local Toeplitz gate, and what it does *not* decide.

An attempt at ``docs/09`` §5.1's Requirement C ("structural positivity") at one
place at a time, run to its wall. The construction is real and closes exactly;
the honest verdict is in :func:`scope` and in ``docs/24``, it factors the
prime side of the explicit formula into a manifest norm, and that is provably
not enough to reach RH.

What is built
-------------

For a Dirichlet series ``f(s) = Σ aₙ n^{-s}`` with ``a₁ = 1``, write
``−f′/f = Σ bₙ Λ-style`` and set ``λ_m = b_{p^m}/log p`` at the place ``p``.
The **place-p kernel** is the Toeplitz form

    K_p^{(d)}(θ) = d + 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ),

and the object this module computes is the *normalization-free* threshold

    c_p := the least diagonal ``c`` for which every finite Toeplitz section
           with diagonal ``c`` and off-diagonals ``λ_m p^{−m/2}`` is positive
           semidefinite,

so that the place-``p`` Toeplitz form with diagonal ``d`` is PSD exactly when
``c_p ≤ d``. When the weighted sequence is absolutely summable this is the
cosine-series minimum ``c_p = − min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)``
(standard: a Toeplitz form with summable symbol is PSD iff the symbol is
nonnegative), and that is what :func:`threshold` evaluates. When the weighted
sequence grows (regime ``"divergent"``) the module's convention is
``c_p = +∞``. At ``|α_j| = √p`` the cosine series diverges but the least PSD
diagonal can still be finite: for ``ζ(s − ½)`` it is exactly ``1 = d``
(measured, every section up to N = 400), :func:`threshold` reports the
``"boundary"`` regime there, and :func:`gate` says INDETERMINATE rather than
a number. The regime is read from an envelope fit to block maxima of the
weighted terms over at least 96 terms, with an uncertainty interval built
from several variants of that fit (``DIAGNOSIS-335.md``): summable and
divergent both require the whole interval on one side of 1, so oscillating
weights from a conjugate pair of Satake parameters are read by their
envelope, and cases whose envelope rate the window cannot separate from 1
are reported as boundary rather than guessed. An earlier version read the
regime off two sampled terms, which a cosine zero in either sampled term
could throw to the wrong side in both directions. This one reading of
``c_p`` is used throughout. Nothing is chosen: ``d`` is the degree read off
the object's own gamma factors, and ``c_p`` is a minimum, not a fit.

For a genuine Euler factor with real coefficients (Satake parameters real or
in conjugate pairs) ``λ_m = Σ_j α_j^m``, and for ``|α_j| < √p`` the convergent
series sums to

    K_p^{(d)}(θ) = Σ_j (1 − |α_j|²/p) / |1 − α_j p^{−1/2} e^{iθ}|²,

each summand nonnegative. **Forward direction (derived):** if every
``|α_j| ≤ √p`` then ``c_p ≤ d``, because each parameter contributes a PSD
Toeplitz matrix with unit diagonal (a Poisson kernel's coefficients below
``√p``, a rank-one Gram matrix at ``√p``).

**Converse (not established by the closed form):** positivity of the
rational expression says nothing outside the convergence regime. At
``p = 2``, ``α = (3√2, 0, 0, 0)`` it is ``3 − 8/(10 − 6 cos θ) ≥ 1`` although
one parameter exceeds ``√p``; the defining series diverges there, and the
module does not use the rational expression: :func:`threshold` reports
``"divergent"`` and :func:`gate` returns FAIL (pinned by
``test_closed_form.py``). The converse for ``c_p`` as defined above rests on
a separate argument: a PSD section with diagonal ``c`` has ``|s_m| ≤ c`` (its
``2×2`` principal minors), while ``s_m = Σ_j (α_j/√p)^m`` is unbounded once
some ``|α_j| > √p`` (no cancellation among the parameters prevents it), so
``c_p = +∞``. That
argument is written down in ``CORRECTIONS.md`` ("Later correction") as an
unreviewed derivation; read the iff as forward-derived, converse unreviewed.
Either way the gate is not a test for "has an Euler product" (see
:func:`ramanujan_violator`).

Why the kernel is the thing
---------------------------

``K_p`` is not decoration. Writing ``Φ_p f = Σ_{m≥0} p^{−m/2} f(· − m log p)``
(the one-sided local shift-average), the prime side of the Riemann–Weil
explicit formula decomposes place by place as

    prime term = − Σ_p log p · (Q_p(f) − ‖f‖²),   Q_p(f) = (1 − 1/p)‖Φ_p f‖²,

measured against ``zeta.weil.explicit_formula_sides`` and agreeing to 22
digits. Each ``Q_p ≥ 0`` *by construction*, it is a norm, which is
Requirement C's norm identity, achieved locally.

And the wall, stated in the same breath: ``Q_p − ‖f‖²`` is **not** of definite
sign (measured: 52 of 60 places positive, 8 negative, for the autocorrelation
pair). The local norms do not assemble into a global one. Positivity of every
``Q_p`` is therefore compatible with either sign of ``W(h)``, and this
construction does not decide RH. Nor can ``c_p`` locate the critical line:
for ``ζ(s−δ)``, ``c_p ≤ d`` holds at every place for every ``δ ≤ ½``
(:func:`provenance_report`, ``docs/24`` §6), so ``δ = 0.1``, whose functional
equation is symmetric about ``Re s = 0.6``, passes. The reason that stood here
until 2026-10-21, that by ``docs/18`` §6 no coefficient functional can read
the position of the critical line, is false and mis-cited; the director run
rejected it (``docs/25``, C-SHIFT-01) and this paragraph had not caught up.

Provenance (``docs/09`` §5.1 Requirement A)
-------------------------------------------

Every quantity here is a function of ``{a_{p^k}}`` alone. No zeros, no
``ξ``-phases, no zero-counting functions enter any definition. That is
mechanically checkable and :func:`provenance_report` states it.

Honest scope
------------

Nothing here is evidence for RH, and a PASS is not a certificate: the
detector's blindness threshold is measured (``eps*`` in :func:`lesion_sweep`,
≈ 0.184 on the ζ→DH interpolation), so a PASS means "no violation above that
magnitude at the tested places". See :func:`scope`.
"""

from __future__ import annotations

import math
from functools import lru_cache
from typing import Callable, Iterable, Sequence

import numpy as np

__all__ = [
    "DEFAULT_PRIMES",
    "local_lambdas",
    "threshold",
    "kernel",
    "satake_kernel",
    "gate",
    "periodic_local",
    "satake_local",
    "epstein_local",
    "epstein_local_check",
    "lesion_sweep",
    "null_distribution",
    "reference_table",
    "provenance_report",
    "scope",
]

#: The places scanned by default. Small primes carry the signal: c_p → 0 like
#: 2d/√p, so a violation that is invisible at p = 2, 3 is invisible everywhere.
DEFAULT_PRIMES: tuple[int, ...] = (
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
)

#: Series truncation target. The tail is *bounded*, not hoped for: see the
#: ``tail`` return of :func:`threshold`.
DEFAULT_TOL: float = 1e-14


# ---------------------------------------------------------------------------
# local coefficient interfaces
# ---------------------------------------------------------------------------


#: how close the weighted-series envelope rate may sit to 1, in log units,
#: before the place in question can no longer be separated from the boundary:
#: the floor of the uncertainty interval in :func:`_envelope_estimate`
_RATIO_EPS = 1e-6

#: minimum number of weighted terms the regime envelope is read from. The
#: series truncation depth for ``c_p`` can be as small as 15 at p = 97, and a
#: window that short cannot separate envelope growth from a slowly varying
#: amplitude, so the regime reading extends the same lambda computation to at
#: least this many terms. The depth used for ``c_p`` itself does not move.
_REGIME_DEPTH = 96


def periodic_local(period: Sequence[float]) -> Callable[[int, int], float]:
    """``a_{p^k}`` for a sequence periodic mod ``q = len(period)``.

    ``period[r]`` is ``a_n`` for ``n ≡ r (mod q)``; index 0 is the ``q | n``
    slot. Exact by modular exponentiation, no coefficient array, so no
    ceiling on ``k`` (the p^k overflow that a truncated array imposes is the
    reason this indirection exists).
    """
    q = len(period)
    if q == 0:
        raise ValueError("period must be non-empty")
    return lambda p, k: float(period[pow(int(p), int(k), q)])


def satake_local(alphas: Sequence[complex]) -> Callable[[int, int], float]:
    """``a_{p^k} = h_k(α)``, the complete homogeneous symmetric polynomial,
    i.e. the genuine degree-``len(alphas)`` Euler factor ``Π (1 − α_j x)^{-1}``.

    Used for the reference PASS cases and for :func:`ramanujan_violator`.
    """
    a = tuple(complex(x) for x in alphas)

    def coeff(p: int, k: int) -> float:
        if k == 0:
            return 1.0
        # h_k by Newton-free expansion: coefficients of Π 1/(1-α_j x)
        series = np.zeros(k + 1, dtype=complex)
        series[0] = 1.0
        for al in a:
            acc = np.zeros(k + 1, dtype=complex)
            power = 1.0 + 0j
            for j in range(k + 1):
                acc[j:] += series[: k + 1 - j] * power
                power *= al
            series = acc
        return float(series[k].real)

    return coeff


def epstein_local(principal: bool = True, disc: int = -23) -> Callable[[int, int], float]:
    """``a_{p^k}`` for an Epstein zeta function of discriminant ``disc``.

    Specialised to ``disc = -23`` (class number 3, unit group ±1), the pair of
    rivals the zeta department already uses. ``principal=True`` gives the form
    ``x²+xy+6y²``; ``False`` gives ``2x²+xy+3y²``.

    Counted through ideal classes rather than by enumerating lattice points:
    ``zeta.epstein.epstein_representation_count`` is exact but enumerates, so it
    cannot reach the ``p^k`` with ``k ≈ 90`` that the ``p = 2`` truncation needs.
    The two agree on every ``p^k`` small enough for both, asserted in
    :func:`epstein_local_check`, which is the reason this shortcut is allowed.
    """
    if disc != -23:
        raise NotImplementedError(
            "only disc = -23 (h = 3) is implemented; other discriminants need their "
            "own class-group bookkeeping"
        )

    def kronecker(p: int) -> int:
        if p == 2:
            return 0 if disc % 2 == 0 else (1 if disc % 8 in (1, 7) else -1)
        a = disc % p
        if a == 0:
            return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1

    @lru_cache(maxsize=None)
    def represented_by_principal(p: int) -> bool:
        for y in range(0, int(math.isqrt(int(4 * p / abs(disc)))) + 2):
            for x in range(-int(math.isqrt(p)) - 2, int(math.isqrt(p)) + 3):
                if x * x + x * y + 6 * y * y == p:
                    return True
        return False

    def coeff(p: int, k: int) -> float:
        if k == 0:
            return 1.0
        chi = kronecker(p)
        if chi == -1:                      # inert: only even k, and (p)^{k/2} is principal
            n_ideals = 1 if k % 2 == 0 else 0
            return float(n_ideals if principal else 0)
        if chi == 0:                       # ramified: [P]^2 principal, h = 3 odd => [P] principal
            return float(1 if principal else 0)
        # split: P^i Pbar^{k-i}, class [P]^{2i-k}; ord([P]) is 1 or 3
        if represented_by_principal(p):
            return float((k + 1) if principal else 0)
        n_principal = sum(1 for i in range(k + 1) if (2 * i - k) % 3 == 0)
        return float(n_principal if principal else (k + 1 - n_principal) // 2)

    return coeff


def epstein_local_check(max_n: int = 5000) -> dict:
    """Cross-check :func:`epstein_local` against the laboratory's own counter.

    ``r_Q(n) = 2·#{ideals of norm n in the class}`` for disc −23 (units ±1), so
    the comparison is exact, not approximate. Returns the prime powers tested
    and any disagreement; an empty ``mismatches`` is the licence to use the
    class-group route at the depths the gate needs.
    """
    from zeta import epstein as _ep

    tested, mismatches = 0, []
    principal, nonprincipal = epstein_local(True), epstein_local(False)
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 59):
        for k in (1, 2, 3):
            n = p**k
            if n > max_n:
                continue
            tested += 1
            got = (2 * principal(p, k), 2 * nonprincipal(p, k))
            want = (
                float(_ep.epstein_representation_count(n, (1, 1, 6))),
                float(_ep.epstein_representation_count(n, (2, 1, 3))),
            )
            if got != want:
                mismatches.append({"n": n, "got": got, "want": want})
    return {"tested": tested, "mismatches": mismatches}


def local_lambdas(aloc: Callable[[int, int], float], p: int, M: int) -> np.ndarray:
    """``λ_0..λ_M`` at the place ``p`` from the log-derivative recursion.

    ``λ_m = m·a_{p^m} − Σ_{j<m} a_{p^j} λ_{m−j}``, with ``λ_0 = 1``. For a
    genuine Euler factor this returns the power sums ``Σ_j α_j^m`` (checked in
    :func:`satake_check`); for ζ it returns all ones.
    """
    a = [float(aloc(p, k)) for k in range(M + 1)]
    lam = np.zeros(M + 1)
    lam[0] = 1.0
    for m in range(1, M + 1):
        lam[m] = m * a[m] - sum(a[j] * lam[m - j] for j in range(1, m))
    return lam


# ---------------------------------------------------------------------------
# the statistic
# ---------------------------------------------------------------------------


def _depth(p: int, tol: float) -> int:
    return max(8, math.ceil(2 * math.log(1 / tol) / math.log(p)))


def _exp_capped(x: float) -> float:
    return float("inf") if x > 709.0 else math.exp(x)


def _block_maxima(
    a: np.ndarray, ms: np.ndarray, width: int
) -> tuple[np.ndarray, np.ndarray]:
    """Largest ``a`` in each contiguous block, at its actual index ``m``."""
    nblocks = max(2, len(a) // width)
    positions, values = [], []
    for idx in np.array_split(np.arange(len(a)), nblocks):
        seg = a[idx]
        j = int(np.argmax(seg))
        if seg[j] > 0 and math.isfinite(float(seg[j])):
            positions.append(float(ms[idx[j]]))
            values.append(float(seg[j]))
    return np.array(positions), np.array(values)


def _fit_line(xs: np.ndarray, ys: np.ndarray) -> tuple[float, float, np.ndarray]:
    """Least squares ``ys ~ intercept + slope * xs`` with its residuals."""
    design = np.vstack([np.ones_like(xs), xs]).T
    coef, *_ = np.linalg.lstsq(design, ys, rcond=None)
    intercept, slope = float(coef[0]), float(coef[1])
    return intercept, slope, ys - (intercept + slope * xs)


def _block_rms_slope(a: np.ndarray, ms: np.ndarray, width: int) -> float:
    """Envelope slope read from block root-mean-square values, for cross-check."""
    nblocks = max(2, len(a) // width)
    starts, logs = [], []
    for idx in np.array_split(np.arange(len(a)), nblocks):
        value = float(np.sqrt(np.mean(a[idx].astype(float) ** 2)))
        if value > 0 and math.isfinite(value):
            starts.append(float(ms[idx[0]]))
            logs.append(math.log(value))
    if len(starts) < 2:
        return float("nan")
    return _fit_line(np.array(starts), np.array(logs))[1]


def _envelope_estimate(
    weights: np.ndarray,
) -> tuple[float, float, float, float]:
    """``(rate, rate_lo, rate_hi, level)`` for the envelope of ``|weights|``.

    The regime question is the value of ``limsup |w_m|^(1/m)`` relative to
    1. Individual terms cannot answer it when the weights oscillate: for a
    conjugate pair ``w_m = 2 R^m cos(m phi)`` a sampled term can sit near a
    cosine zero whatever ``R`` does. Block maxima can: a block that spans
    a zero still contains terms near the envelope ``level * rate^m``, and a
    least squares line through their logs at their actual indices estimates
    ``log rate``. The interval, not the point estimate, carries the verdict.
    It covers several variants of the fit (three block widths, a block RMS
    slope and the two half-window slopes), widened by half the variant
    spread on each side and by a statistical term from the main fit, with a
    floor of ``_RATIO_EPS``. When the weights are steady every variant
    agrees to floating point accuracy and the interval collapses to that
    floor, which keeps the sharp single-parameter boundary resolution.
    When the window cannot separate a slowly varying amplitude from
    growth, the variants disagree, the interval widens past 1 and the
    caller reports the boundary regime. NaN components mean the finite
    window supplied cannot support a reading at all. See
    ``DIAGNOSIS-335.md`` for the measurements behind this design.
    """
    a = np.abs(np.asarray(weights, dtype=float))
    ms = np.arange(1, len(a) + 1, dtype=float)
    if len(a) < 8 or not np.any(a > 0):
        return 0.0, 0.0, 0.0, 0.0
    tail_a, tail_m = a[len(a) // 2 :], ms[len(a) // 2 :]
    if not np.any(tail_a > 0):
        return 0.0, 0.0, 0.0, 0.0
    width = int(min(12, max(4, len(a) // 12)))
    bm, bmax = _block_maxima(tail_a, tail_m, width)
    if len(bm) < 4:
        return float("nan"), float("nan"), float("nan"), float("nan")
    log_bmax = np.log(bmax)
    _, slope, resid = _fit_line(bm, log_bmax)
    n = len(bm)
    sxx = float(np.sum((bm - bm.mean()) ** 2))
    if n > 2 and sxx > 0:
        std_err = math.sqrt(float(np.sum(resid**2) / (n - 2)) / sxx)
    else:
        std_err = float("inf")
    pair_slopes = np.array(
        [
            (log_bmax[j] - log_bmax[i]) / (bm[j] - bm[i])
            for i in range(n)
            for j in range(i + 1, n)
        ]
    )
    pair_mad = (
        float(np.median(np.abs(pair_slopes - np.median(pair_slopes))))
        if pair_slopes.size
        else 0.0
    )
    variants = [slope]
    for variant_width in (4, 8, 16):
        if len(tail_a) >= 2 * variant_width:
            v_bm, v_bmax = _block_maxima(tail_a, tail_m, variant_width)
            if len(v_bm) >= 2:
                variants.append(_fit_line(v_bm, np.log(v_bmax))[1])
    rms_slope = _block_rms_slope(tail_a, tail_m, width)
    if rms_slope == rms_slope:
        variants.append(rms_slope)
    for part in (slice(0, n // 2), slice(n // 2, None)):
        if len(bm[part]) >= 2:
            variants.append(_fit_line(bm[part], log_bmax[part])[1])
    delta = max(
        _RATIO_EPS,
        3.0 * std_err if math.isfinite(std_err) else 0.0,
        2.0 * pair_mad,
    )
    spread = (max(variants) - min(variants)) / 2.0
    log_level = float(np.max(log_bmax - slope * bm))
    return (
        _exp_capped(slope),
        _exp_capped(min(variants) - spread - delta),
        _exp_capped(max(variants) + spread + delta),
        _exp_capped(log_level),
    )


def _legacy_ratio(weights: np.ndarray, depth: int) -> float:
    """The two-term ratio of the 2026-08-11 regime test.

    Kept only for coefficient callables that cannot be evaluated at the
    extended regime depth, so their previous behaviour is preserved
    exactly instead of failing where they used to return a reading.
    """
    w = np.abs(weights)
    nz = np.flatnonzero(w > 0)
    if nz.size < 2:
        return 0.0
    last, prev = nz[-1], nz[max(0, nz.size - 1 - max(1, depth // 10))]
    return float((w[last] / w[prev]) ** (1.0 / max(1, last - prev)))


def threshold(
    aloc: Callable[[int, int], float],
    p: int,
    *,
    tol: float = DEFAULT_TOL,
    ngrid: int = 4001,
) -> tuple[float, float]:
    """``(c_p, tail_bound)`` at the place ``p``.

    ``c_p = − min_θ 2 Σ_{m≥1} λ_m p^{−m/2} cos(mθ)``: the least diagonal for
    which the place-``p`` Toeplitz kernel is positive semidefinite. No
    normalization is chosen; compare it against the degree ``d``.

    The second entry is a truncation estimate,
    ``2·max_{m≤M}|λ_m|·p^{−(M+1)/2}/(1 − p^{−1/2})``. A verdict is only reported
    when the excess clears it by an order of magnitude (:func:`gate`).

    **It is an estimate, not a bound, and the difference is measured.** It
    maxes over the λ_m it has *computed*, while the discarded tail contains
    λ_m for m > M, larger whenever |λ_m| grows. For a_loc twisted by p^{mδ}
    with δ close to ½ the true tail behaves like ``2x^{M+1}/(1−x)`` with
    ``x = p^{δ−1/2} → 1``, which the formula above does not track: at
    ``p = 2, δ = 0.49`` the truncated ``c`` reads 15.99 against the true
    0.9965, an error of 15.0 against a reported "bound" of 2.52, violated
    sixfold (measured 2026-08-11). Both the PASS and the FAIL sides near
    ``x = 1`` inherit that, which is why :func:`gate` now reports a third
    verdict instead of resolving the doubt in either direction.

    The third entry is the regime of the weighted series, read from its
    envelope by :func:`_envelope_estimate` over at least ``_REGIME_DEPTH``
    terms. It must be ``"summable"``, with the whole uncertainty interval for
    the envelope rate below 1, for the truncation estimate to mean anything.
    The geometric part of the estimate in that regime is read off the fitted
    envelope at the truncation depth, which for steady weights is the same
    geometric term this function has reported since 2026-08-11. Until the
    repair for issue 335 the regime was read off two sampled terms, which a
    cosine zero in either term could throw to the wrong side of 1 for
    conjugate-pair weights, in both directions (``DIAGNOSIS-335.md``).
    """
    M = _depth(p, tol)
    regime_depth = max(M, _REGIME_DEPTH)
    extended = True
    try:
        lam_full = local_lambdas(aloc, p, regime_depth)
    except Exception:
        # A coefficient callable that cannot reach the extended depth keeps
        # its previous reading: the legacy two-term ratio at depth M.
        extended = False
        regime_depth = M
        lam_full = local_lambdas(aloc, p, M)
    lam = lam_full[: M + 1]
    weights = lam[1:] * p ** (-np.arange(1, M + 1) / 2.0)
    theta = np.linspace(0.0, np.pi, ngrid)
    series = 2 * np.sum(weights[:, None] * np.cos(np.outer(np.arange(1, M + 1), theta)), axis=0)
    tail = 2 * float(np.max(np.abs(lam))) * p ** (-(M + 1) / 2.0) / (1 - p ** -0.5)
    if not extended:
        ratio = _legacy_ratio(weights, M)
        if ratio < 1.0 - _RATIO_EPS:
            regime = "summable"
            w = np.abs(weights)
            nz = np.flatnonzero(w > 0)
            if nz.size:
                tail = max(tail, 2.0 * float(w[nz[-1]]) * ratio / (1.0 - ratio))
        elif ratio > 1.0 + _RATIO_EPS:
            regime = "divergent"
            tail = float("inf")
        else:
            regime = "boundary"
            tail = float("inf")
        return float(-series.min()), float(tail), regime
    # Read the envelope on the finite prefix of the extended weights. A
    # non-finite entry means the weighted terms overflowed double precision
    # inside the window, which at the primes this module scans is itself
    # growth past any finite diagonal, unless the finite prefix is still
    # long enough to carry its own envelope reading. NaN entries are not
    # read as growth: they leave the regime undecided.
    regime_weights = lam_full[1:] * p ** (-np.arange(1, regime_depth + 1) / 2.0)
    if np.any(np.isnan(regime_weights)):
        return float(-series.min()), float("inf"), "boundary"
    finite = np.isfinite(regime_weights)
    if not np.all(finite):
        cut = int(np.flatnonzero(~finite)[0])
        if cut < 24:
            return float(-series.min()), float("inf"), "divergent"
        regime_weights = regime_weights[:cut]
    rate, rate_lo, rate_hi, level = _envelope_estimate(regime_weights)
    if rate != rate:
        regime = "boundary"
        tail = float("inf")
    elif rate == 0.0:
        regime = "summable"
    elif rate_lo > 1.0:
        regime = "divergent"  # c_p is +infinity; any finite degree is violated
        tail = float("inf")
    elif rate_hi < 1.0:
        regime = "summable"
        tail = max(tail, 2.0 * level * rate ** (M + 1) / (1.0 - rate))
    else:
        # The interval straddles 1: on the bound to the resolution this
        # window supports, including slow amplitude patterns the window
        # cannot separate from a rate of exactly 1.
        regime = "boundary"
        tail = float("inf")
    return float(-series.min()), float(tail), regime


def kernel(
    aloc: Callable[[int, int], float],
    p: int,
    theta: float | np.ndarray,
    degree: int,
    *,
    tol: float = DEFAULT_TOL,
) -> np.ndarray:
    """``K_p^{(d)}(θ)`` itself, for plotting and for the closed-form check."""
    M = _depth(p, tol)
    lam = local_lambdas(aloc, p, M)
    th = np.atleast_1d(np.asarray(theta, dtype=float))
    weights = lam[1:] * p ** (-np.arange(1, M + 1) / 2.0)
    return degree + 2 * np.sum(weights[:, None] * np.cos(np.outer(np.arange(1, M + 1), th)), axis=0)


def satake_kernel(alphas: Sequence[complex], p: int, theta: float | np.ndarray) -> np.ndarray:
    """The closed form ``Σ_j (1 − |α_j|²/p)/|1 − α_j p^{−1/2}e^{iθ}|²``.

    This equals the kernel's Fourier series only when all ``|α_j| < √p``
    (with real or conjugate-paired parameters). An earlier version of this
    docstring said the expression is nonnegative for all ``θ`` exactly when
    every ``|α_j| ≤ √p``; that is false. With ``p = 2`` and
    ``α = (3√2, 0, 0, 0)`` it is everywhere at least 1, while the defining
    Fourier series diverges. :func:`gate` never evaluates this expression;
    it is used only by :func:`satake_check`.
    """
    th = np.atleast_1d(np.asarray(theta, dtype=float))
    out = np.zeros_like(th)
    for al in alphas:
        al = complex(al)
        out += (1 - abs(al) ** 2 / p) / np.abs(1 - al * p**-0.5 * np.exp(1j * th)) ** 2
    return out


def gate(
    aloc: Callable[[int, int], float],
    degree: int,
    *,
    primes: Iterable[int] = DEFAULT_PRIMES,
    tol: float = DEFAULT_TOL,
    margin: float = 10.0,
) -> dict:
    """Run the gate over the places. Returns verdict, witnesses, and margins.

    A place is a **witness** only when ``c_p > d + margin·tail``, the
    truncation estimate has to be cleared before a FAIL is spoken.

    **Three verdicts, not two (2026-08-11).** Until this revision the function
    had no way to say *cannot decide*, so "the truncation is out of control"
    was encoded as the favourable answer: at a shift δ ≥ 0.5 the local series
    diverges, ``max_c`` and the estimate blow up together, no place clears
    ``margin·tail``, and the caller read **PASS**: for an object whose true
    ``c_p`` is ``+∞``. The mirror-image failure is worse and was found only
    on a second pass: on ``δ ∈ [0.4877, 0.5]``, where every place genuinely
    satisfies the local bound, the truncated series overshoots and the gate
    returns **FAIL with named witness primes**. Both move with ``tol``, which
    is this repository's own signature of an artifact.

    ``INDETERMINATE`` is returned whenever any place falls in the
    ``"boundary"`` regime: its weighted series is not contracting on the
    evidence of the computed terms, which is the condition both failures
    share. That follows the discipline this repository applies elsewhere:
    the safe answer to "cannot decide" is a third value, never the pleasant
    one of the two.

    **Regime reading (repaired for issue 335).** From 2026-08-11 to this
    repair the regime was read off two weighted terms a decade apart. For
    a conjugate pair the weights ``2 R^m cos(m phi)`` oscillate, so that
    comparison could land on either side of 1 whatever the envelope did:
    ``α = 0.9·√2·e^{±0.2i}`` at ``p = 2`` was called divergent and FAILed
    although ``c_p ≈ 1.894 < 2``; ``α = 1.2·√7·e^{±0.4i}`` at ``p = 7``
    PASSed although ``c_p = +∞``; and 22 of the 60 unit-modulus control
    angles FAILed although every margin was at least 0.343. The regime is
    now read from an envelope fit over at least 96 weighted terms, and a
    place is called summable or divergent only when the whole uncertainty
    interval for its envelope rate lies on one side of 1
    (``DIAGNOSIS-335.md``). Near-boundary rates with slow amplitude
    patterns, which a finite window cannot separate from 1 by envelope
    methods, return INDETERMINATE instead of a guessed verdict. One
    limitation this repair does not remove: in the summable regime a place
    whose truncated ``c`` exceeds ``d`` by less than ``margin·tail`` is no
    witness, so the verdict can be PASS although that place was not
    resolved. For ``ζ(s−δ)`` at ``δ = 0.49``, ``p = 2``, the truncated
    ``c`` reads 15.99 against ``d = 1`` with a tail estimate of 149.9, and
    the PASS is right only because the true value, 0.9965, happens to lie
    below ``d``. ``test_closed_form.py`` pins that case as well as the
    corrected conjugate-pair verdicts.
    """
    primes = list(primes)
    cs, tails, oks = [], [], []
    for p in primes:
        c, t, regime = threshold(aloc, p, tol=tol)
        cs.append(c)
        tails.append(t)
        oks.append(regime)
    cs_a, tails_a = np.array(cs), np.array(tails)
    witnesses = [
        (int(p), float(c))
        for p, c, t in zip(primes, cs_a, tails_a)
        if c > degree + margin * t
    ]
    divergent = [int(p) for p, r in zip(primes, oks) if r == "divergent"]
    boundary = [int(p) for p, r in zip(primes, oks) if r == "boundary"]
    if divergent:  # the weighted local series does not converge: c_p = +infinity
        verdict = "FAIL"
        witnesses = sorted(
            set(witnesses) | {(int(p), float("inf")) for p in divergent}
        )
    elif boundary:
        verdict = "INDETERMINATE"
    else:
        verdict = "PASS" if not witnesses else "FAIL"
    return {
        "verdict": verdict,
        "divergent_places": divergent,
        "boundary_places": boundary,
        "degree": degree,
        "max_c": float(cs_a.max()),
        "excess": float(cs_a.max() - degree),
        "witnesses": witnesses,
        "c_by_prime": {int(p): float(c) for p, c in zip(primes, cs_a)},
        "max_tail": float(tails_a.max()),
    }


# ---------------------------------------------------------------------------
# controls, the reason this is a gate and not a decoration
# ---------------------------------------------------------------------------


def satake_check(alphas: Sequence[complex], p: int, theta: float = 1.1) -> dict:
    """Series vs. closed form at one point, valid within the convergence regime."""
    aloc = satake_local(alphas)
    return {
        "series": float(kernel(aloc, p, theta, len(alphas))[0]),
        "closed_form": float(satake_kernel(alphas, p, theta)[0]),
    }


def ramanujan_violator(alpha: float = 2.3, p: int = 5) -> dict:
    """A **genuine** Euler product the gate rejects, the honest boundary.

    ``α, 1/α`` with ``α`` large is a genuine degree-2 Euler factor (real
    coefficients) that violates the Ramanujan bound. The gate fails it at
    small ``p``. So the gate does *not* test "has an Euler product". What it
    reads is the local bound ``|α_j| ≤ √p``: the forward direction is
    derived, the converse is an unreviewed derivation (module docstring).
    Here ``α = 2.3 > √5`` puts the place in the ``"divergent"`` regime, so
    ``c_p = +∞`` by the module's convention; the ``c_p`` returned is a
    finite-depth truncation (65.24 at the default depth 41, 22.46 at depth 23,
    110.80 at depth 52), not the value. An earlier version of this docstring
    called the factor legitimate, with its functional equation intact, and the
    returned note said ``|alpha| > sqrt(p)`` "is allowed in the Selberg class".
    It is not: that class's Ramanujan axiom and, at ``p = 5``, its
    Euler-product bound ``θ < ½`` both exclude ``|α| > √5`` (``docs/09`` §3,
    axioms (4) and (5)). Nor does anything in this module construct or check a
    functional equation for it.
    """
    aloc = satake_local([alpha, 1 / alpha])
    c, tail, tail_ok = threshold(aloc, p)
    return {
        "alpha": alpha,
        "p": p,
        "c_p": c,
        "degree": 2,
        "verdict": (
            "INDETERMINATE"
            if tail_ok == "boundary"
            else ("PASS" if (tail_ok == "summable" and c <= 2 + 10 * tail) else "FAIL")
        ),
        "sqrt_p": math.sqrt(p),
        "note": (
            "genuine Euler factor; rejected because |alpha| > sqrt(p), so the weighted local "
            "series diverges and c_p = +inf (the c_p above is a truncation); the Selberg class "
            "excludes such a factor"
        ),
    }


def lesion_sweep(
    epsilons: Sequence[float] = (0.0, 0.01, 0.05, 0.1, 0.15, 0.2, 0.4, 0.7, 1.0),
    *,
    kappa: float | None = None,
    primes: Iterable[int] = (2, 3, 5, 7, 11, 13, 17, 19, 23),
) -> dict:
    """Plant a graded violation and find where the detector goes blind.

    Interpolates ζ → Davenport–Heilbronn coefficientwise. The returned
    ``eps_star`` is the smallest interpolation parameter the gate can see; a
    PASS means nothing below it. A detector whose blindness is unmeasured
    reports power it does not have (``harness/README.md``).
    """
    if kappa is None:  # the repo's own value; imported lazily to keep this module standalone
        from zeta import epstein

        kappa = float(epstein.kappa(dps=25))
    zeta_per = [0.0, 1.0, 1.0, 1.0, 1.0]
    dh_per = [0.0, 1.0, kappa, -kappa, -1.0]

    def blend(eps: float):
        return periodic_local([(1 - eps) * z + eps * d for z, d in zip(zeta_per, dh_per)])

    rows = []
    for eps in epsilons:
        res = gate(blend(eps), 1, primes=primes)
        rows.append({"eps": float(eps), "excess": res["excess"], "detected": res["verdict"] == "FAIL"})
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if gate(blend(mid), 1, primes=primes)["verdict"] == "FAIL":
            hi = mid
        else:
            lo = mid
    return {"rows": rows, "eps_star": float((lo + hi) / 2), "kappa": float(kappa)}


def null_distribution(
    n_samples: int = 400,
    seed: int = 20260810,
    *,
    primes: Iterable[int] = (2, 3, 5, 7, 11, 13, 17, 19, 23),
) -> dict:
    """What a *generic* non-factoring period-5 real sequence scores.

    A nonzero excess means nothing until the null is known. Reports the null
    band and Davenport–Heilbronn's percentile within it.
    """
    from zeta import epstein

    rng = np.random.default_rng(seed)
    scores = []
    for _ in range(n_samples):
        t = rng.normal(0, 1, 2)
        per = [0.0, 1.0, float(t[0]), float(t[1]), 0.0]
        scores.append(gate(periodic_local(per), 1, primes=primes)["excess"])
    scores_a = np.array(scores)
    kappa = float(epstein.kappa(dps=25))
    dh = gate(periodic_local([0.0, 1.0, kappa, -kappa, -1.0]), 1, primes=primes)["excess"]
    return {
        "median": float(np.median(scores_a)),
        "p05": float(np.percentile(scores_a, 5)),
        "p95": float(np.percentile(scores_a, 95)),
        "fraction_failing": float((scores_a > 0).mean()),
        "dh_excess": float(dh),
        "dh_percentile": float(100 * (scores_a < dh).mean()),
    }


# ---------------------------------------------------------------------------
# the two statements that keep this honest
# ---------------------------------------------------------------------------


def reference_table(primes: Iterable[int] = DEFAULT_PRIMES) -> list[dict]:
    """The department's reference claims, re-derived rather than remembered.

    Degrees are read off each object's own gamma factors, never chosen to make
    a verdict come out. Every row states the expected verdict; a row whose
    ``verdict`` and ``expected`` disagree is a failure of the gate, not of the
    subject, which is the calibration rule of ``harness/README.md``.
    """
    from zeta import epstein as _ep

    kappa = float(_ep.kappa(dps=25))
    cases = [
        ("zeta", periodic_local([1.0]), 1, "pi^{-s/2}Gamma(s/2)", "PASS"),
        ("L(chi quad mod 5)", periodic_local([0.0, 1.0, -1.0, -1.0, 1.0]), 1,
         "Gamma(s/2), even chi", "PASS"),
        ("degree-2 Euler factor (phi=0.9)",
         satake_local([complex(math.cos(0.9), math.sin(0.9)),
                       complex(math.cos(0.9), -math.sin(0.9))]), 2,
         "genuine degree-2 control", "PASS"),
        ("Davenport-Heilbronn", periodic_local([0.0, 1.0, kappa, -kappa, -1.0]), 1,
         "(pi/5)^{-(s+1)/2}Gamma((s+1)/2)", "FAIL"),
        ("DH-family t=0", periodic_local([0.0, 1.0, 0.0, 0.0, -1.0]), 1,
         "same gamma factor", "FAIL"),
        ("Epstein (1,1,6) principal", epstein_local(True), 2,
         "(2pi/sqrt23)^{-s}Gamma(s)", "FAIL"),
        ("Epstein (2,1,3) non-principal", epstein_local(False), 2,
         "(2pi/sqrt23)^{-s}Gamma(s)", "FAIL"),
    ]
    rows = []
    for name, aloc, degree, gamma, expected in cases:
        res = gate(aloc, degree, primes=primes)
        rows.append({
            "subject": name, "degree": degree, "gamma_factor": gamma,
            "max_c": res["max_c"], "excess": res["excess"],
            "verdict": res["verdict"], "expected": expected,
            "witnesses": res["witnesses"][:3],
            "agrees": res["verdict"] == expected,
        })
    return rows


def provenance_report() -> dict:
    """Requirement A, stated mechanically: what enters the definitions."""
    return {
        "inputs": "a_{p^k} only (local Dirichlet coefficients)",
        "zeros_used": False,
        "xi_phases_used": False,
        "zero_counting_used": False,
        "note": (
            "c_p is a functional of the coefficient sequence alone. It is NOT blind to a real "
            "shift, and the earlier note here said it was: for zeta(s-delta) the local parameter "
            "is alpha_p = p^delta, so c_p = 2x/(1+x) with x = p^(delta-1/2) for delta < 1/2. "
            "At delta = 1/2 the cosine series diverges but the least PSD diagonal is 1 = d "
            "(measured; gate() reports INDETERMINATE there), and for delta > 1/2 c_p = +infinity. "
            "So c_p <= d holds exactly when delta <= 1/2 under the least-PSD-diagonal reading "
            "(delta > 1/2 direction: unbounded power sums, see CORRECTIONS.md). What "
            "follows is weaker and is the honest statement: on |delta| < 1/2 the verdict does "
            "not move, so a PASS cannot locate the critical line; delta = 0.1 is a passing "
            "function whose zeros sit on Re s = 0.6. The threshold is the Selberg-class Euler "
            "product axiom's theta < 1/2 (Conrey-Ghosh 1992, remark 5) and, on the automorphic "
            "side, the Jacquet-Shalika bound |log_p |alpha_p|| < 1/2, which Sarnak states as "
            "sharp. The universal it replaces -- 'no coefficient functional can read the "
            "position of the critical line' -- is false: Titchmarsh 14.25(B)/(C) gives "
            "M(x) = O(x^(1/2+eps)) <=> RH, a criterion in the coefficients of 1/zeta alone. "
            "docs/18 §6, which the old note cited, says ORDINATE statistics, which is a "
            "different and correct claim."
        ),
        "blindness_radius_delta": 0.5,
    }


def scope() -> dict:
    """What a verdict from this module does and does not mean."""
    return {
        "is": (
            "a local coefficient criterion with c_p the least PSD Toeplitz diagonal: for real or "
            "conjugate-paired Satake parameters, |alpha_j| <= sqrt(p) implies c_p <= d (derived); "
            "the converse is not established by the closed form and rests on an unreviewed "
            "PSD-boundedness derivation (CORRECTIONS.md, 'Later correction'). On the bound "
            "|alpha_j| = sqrt(p), gate() reports INDETERMINATE: for steady weights (measured: "
            "zeta(s - 1/2); single real parameters +sqrt(2), -sqrt(3), +sqrt(97); the pair "
            "+-sqrt(5)) and, after the repair for issue 335, for conjugate pairs on the bound "
            "as well (measured: sqrt(2) e^(+-0.9i) and sqrt(2) e^(+-2.0i) at p = 2)."
        ),
        "is_not": [
            "evidence for RH (docs/08); nothing computed here could be",
            "a test for 'has an Euler product', see ramanujan_violator()",
            "a global positivity statement: Q_p - ||f||^2 is not of definite sign, so the "
            "local norms do not assemble into a global one",
            "a decision procedure: gate() measures c_p in floating point by truncation and "
            "reads the regime from an envelope fit to the weighted terms with an uncertainty "
            "interval; an envelope rate the computed window cannot separate from 1, including "
            "near-boundary conjugate pairs with slow amplitude patterns, returns "
            "INDETERMINATE rather than a verdict, and in the summable regime an excess the "
            "truncation estimate cannot resolve still reads as PASS (zeta(s - 0.49) at p = 2); "
            "both limitations are pinned in test_closed_form.py",
        ],
        "pass_means": (
            "no violation above the measured blindness threshold at the tested places; "
            "see lesion_sweep()['eps_star']"
        ),
        "requirement_C_status": (
            "achieved locally (Q_p = (1-1/p)||Phi_p f||^2, a norm at every place) and NOT "
            "globally, which is exactly where docs/09 §5.1 predicts an attempt bleeds"
        ),
    }
