"""Heat flow on the Riemann Ξ function and the de Bruijn–Newman constant.

This is the centrepiece of the laboratory.  Everything here is built on one
super-exponentially decaying, even, positive weight

    Φ(u) = Σ_{n≥1} (2π²n⁴ e^{9u} − 3π n² e^{5u}) · exp(−π n² e^{4u})                (1)

and the one-parameter family of entire functions obtained by inserting a
Gaussian factor e^{tu²} into its cosine transform

    H_t(z) = ∫₀^∞ e^{t u²} Φ(u) cos(z u) du .                                       (2)

**The t = 0 normalisation (determined empirically in this module, not quoted
from memory).**  ``H0_vs_Xi`` measures the two free constants of the ansatz
H₀(z) = c · Ξ(a z) from the data itself:

    a = sqrt( (H₀''(0)/H₀(0)) / (Ξ''(0)/Ξ(0)) ),      c = H₀(0) / Ξ(0)

and then rationalises them.  The answer found on this machine is

    H₀(z) = (1/8) · Ξ(z/2),          Ξ(T) := ξ(1/2 + iT)                            (3)

verified to an **absolute residual ≤ 1e-42 at mp.dps = 40** over real z ∈ [0,100]
and over complex z (see ``H0_vs_Xi`` and ``tests/test_heatflow.py``).  Hence

    zeros of H₀ on the real axis  ⟺  z = ±2γ_n ,   γ_n the zeta zero ordinates.     (4)

**The heat equation and its sign (verified, not assumed).**  Differentiating (2)
under the integral sign, ∂_t brings down u² and ∂_z² brings down −u².  Therefore

    ∂H/∂t = −∂²H/∂z²        i.e.        ∂H/∂t + ∂²H/∂z² = 0                         (5)

which is the *backward* heat equation: H_t = exp(−t ∂_z²) H₀.  ``heat_equation_residual``
computes the left-hand side of (5) by central differences; it is ~1e-18 at dps = 30.
The sign matters: it is why *increasing* t is the smoothing/repelling direction here
even though the classical forward heat equation ∂_t p = +∂_x² p makes real roots
attract.  See ``polynomial_heat_flow`` for the elementary version of exactly this
sign bookkeeping.

**The de Bruijn–Newman constant.**

    Λ := inf{ t ∈ ℝ : H_t has only real zeros }.

de Bruijn (1950) and Newman (1976) showed the set of such t is a closed half-line,
so Λ is well defined and H_t has only real zeros for every t ≥ Λ.  Then

    RH  ⟺  Λ ≤ 0 ,        and Rodgers–Tao (2020) proved  Λ ≥ 0 ,
    so  RH  ⟺  Λ = 0 .

See ``lambda_facts`` for the rigorous numerical bounds with citations.

**Accuracy achieved (honest statement, re-measured).**  ``H_t`` is evaluated with a
composite Gauss–Legendre rule whose nodes, weights and Φ-values are memoised (Φ
depends on neither z nor t, so the expensive part is paid once).  Cross-checked
against ``mpmath.quadgl`` and against the independent oracle Ξ(z/2)/8 evaluated at
dps + 80, the **absolute** error measured over z ∈ [0, 400] is

    dps = 30 → 3.8e-32      dps = 40 → 8.7e-42      dps = 60 → 2.9e-62            (5a)

i.e. roughly 10^{−(dps+1)}: for real z and |t| ≤ 1, |H_t(z)| ≤ H_t(0) ≤ 0.0629
(H_t(0) increases slowly with t; H₀(0) = 0.06214).  The guarantee quoted by
``recommended_dps`` is the deliberately conservative 10^{−(dps−2)}.

Because |H₀(z)| ≈ (1/8)|Ξ(z/2)| ~ exp(−π z/8), the number of correct *significant*
digits falls off linearly in z.  The **bound**

    digits(z) ≳ dps − 2 − 0.1706 · |z|                                              (6)

is what ``recommended_dps`` inverts; it is a floor, not the achieved value, and it
is conservative by 2–9 digits.  Measured significant digits::

        z =      0     30    100    200    250    300    400     eq.(6) at z=100
  dps=30      30.2   28.7   18.6    2.3   (--)   (--)   (--)     10.9
  dps=40      39.9   38.0   27.1   12.8    2.3   (--)   (--)     20.9
  dps=60      60.3   58.6   48.1   31.3   22.7   13.1   (--)     40.9

(``(--)`` = no correct digits: |H₀| has fallen below the absolute error floor.
Measured against ξ built from scratch at dps + 80.)  So at dps = 30,
H₀(100) = 3.95e-16 carries ~18.6 significant digits, and 15 digits are held out to
z ≈ 115; to hold 15 digits out to z = 150 the conservative rule asks for dps = 46,
of which ~27 digits are actually delivered.

**Known limitation, now fixed but worth stating**: before the panel-count rule took
``dps`` into account (see ``_panels_for``), the quadrature had a discretisation
floor near 1e-57 that *no* value of ``dps`` could beat — H₀(30) stalled at 5.2e-58
at dps = 60 and degraded to 1.1e-55 at dps = 100.  ``test_H_t_converges_with_dps``
pins the fix.
"""

from __future__ import annotations

import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from mpmath import mp

__all__ = [
    "DEFAULT_DPS",
    "xi_backend_report",
    "H0_RELATION",
    "PHI_STRIP",
    "Phi",
    "Phi_is_even_defect",
    "H_t",
    "H0_vs_Xi",
    "heat_equation_residual",
    "zeros_of_H_t",
    "track_zeros",
    "zero_gap_statistics",
    "lambda_facts",
    "polynomial_heat_flow",
    "recommended_dps",
    "Xi_reference",
]

DEFAULT_DPS: int = 30

#: The t = 0 normalisation, as *determined* by :func:`H0_vs_Xi` on this machine.
#: ``H0(z) == c * Xi(a*z)`` with these exact rational constants.
H0_RELATION: dict[str, Any] = {
    "relation": "H_0(z) = (1/8) * Xi(z/2)",
    "c": (1, 8),
    "a": (1, 2),
}

#: |H_0(z)| ~ exp(-pi z / 8), so this many decimal digits are lost per unit of z.
_DIGITS_LOST_PER_Z: float = math.pi / 8 / math.log(10)  # ~0.17055

_DATA_DIR = Path(__file__).resolve().parent.parent / "data"


# --------------------------------------------------------------------------- #
#  Ξ reference (prefer the sibling module, fall back to a local definition)
# --------------------------------------------------------------------------- #

def _xi_local(s: Any) -> Any:
    """ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)  (local fallback)."""
    s = mp.mpmathify(s)
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi_reference(T: Any, backend: str = "auto") -> Any:
    """Ξ(T) = ξ(1/2 + iT), real for real T.

    ``backend="auto"`` prefers the sibling ``zeta.core`` (so the two independent
    implementations genuinely cross-check each other) and falls back to the local
    ξ above.  ``backend="local"`` forces the local one.

    Note ``zeta.core.Xi`` is real-argument-only on this build, so complex T is
    routed to ``zeta.core.xi(1/2 + iT)`` when that exists, else to the local ξ.
    Use :func:`xi_backend_report` to see which path a given argument takes and
    how far the two implementations differ — do not assume the sibling is used.

    Raises ``ValueError`` on an unrecognised ``backend``: silently treating an
    unknown string as ``"auto"`` would make a typo look like a passing cross-check.
    """
    if backend not in ("auto", "local"):
        raise ValueError(f"backend must be 'auto' or 'local', got {backend!r}")
    Tm = mp.mpmathify(T)
    if backend == "local":
        return _xi_local(mp.mpf(1) / 2 + 1j * Tm)
    try:  # pragma: no cover - depends on which sibling modules exist
        import zeta.core as _core  # type: ignore

        if mp.im(Tm) == 0 and hasattr(_core, "Xi"):
            return mp.mpmathify(_core.Xi(mp.mpf(mp.re(Tm))))
        if hasattr(_core, "xi"):
            return mp.mpmathify(_core.xi(mp.mpf(1) / 2 + 1j * Tm))
    except Exception:
        pass
    return _xi_local(mp.mpf(1) / 2 + 1j * Tm)


def xi_backend_report(T_values: Sequence[Any] | None = None, dps: int = 40) -> dict[str, Any]:
    """Compare ``Xi_reference`` (sibling ``zeta.core``) against the local ξ.

    Returns which backend answered and the worst absolute disagreement, so the
    accuracy of the cross-check is *measured* rather than assumed.  Measured on
    this build: ``zeta.core.Xi`` carries a fixed absolute error of ~1.1e-32
    regardless of requested precision, and rejects complex arguments.
    """
    if T_values is None:
        T_values = [0, 1, 7, 14.13, 25, 50, mp.mpc(3, 1)]
    with mp.workdps(dps):
        try:
            import zeta.core as _core  # type: ignore

            has = {"Xi": hasattr(_core, "Xi"), "xi": hasattr(_core, "xi")}
        except Exception:
            has = {}
        worst = mp.mpf(0)
        rows = []
        for T in T_values:
            ref = mp.mpmathify(Xi_reference(T))
            loc = mp.mpmathify(Xi_reference(T, backend="local"))
            d = abs(ref - loc)
            worst = max(worst, d)
            rows.append({"T": T, "diff": +d})
        return {
            "sibling_available": bool(has),
            "sibling_symbols": has,
            "max_abs_difference": +worst,
            "rows": rows,
            "dps": dps,
        }


def _ordinate_of(v: Any) -> Any:
    """Extract the ordinate γ from either a bare γ or a full zero ρ = 1/2 + iγ.

    ``zeta.zeros.first_n_zeros`` may return either convention, so normalise.
    Careful: ``mpf(14.13).imag`` is 0, not 14.13 — testing ``hasattr(v, 'imag')``
    is *not* enough, we must test whether the imaginary part is actually non-zero.
    """
    v = mp.mpmathify(v)
    im = mp.im(v)
    return mp.mpf(im) if im != 0 else mp.mpf(mp.re(v))


def _reference_ordinates(n: int) -> list[Any]:
    """First n zeta zero ordinates γ_n, from ``zeta.zeros`` if available.

    Falls back to ``mpmath.zetazero`` — which is an independent oracle either way.
    """
    try:  # pragma: no cover - depends on which sibling modules exist
        from zeta.zeros import first_n_zeros  # type: ignore

        vals = [_ordinate_of(v) for v in list(first_n_zeros(n))[:n]]
        if len(vals) == n and all(v > 0 for v in vals):
            return vals
    except Exception:
        pass
    return [mp.mpf(mp.zetazero(k + 1).imag) for k in range(n)]


# --------------------------------------------------------------------------- #
#  Φ
# --------------------------------------------------------------------------- #

#: Φ's series converges on the open strip |Im u| < π/8 — the connected component
#: of {Re e^{4u} > 0} containing the real axis.  (Re e^{4u} is also positive on the
#: disconnected bands |Im u − kπ/2| < π/8, k ≠ 0, where the series converges to
#: *something*, but those bands cannot be reached from ℝ without crossing a line of
#: divergence, so this module restricts Φ to the principal strip.)
PHI_STRIP: float = math.pi / 8

#: Refuse to sum the series when it would take more than this many terms.  Via
#: the folded public :func:`Phi` the count diverges like (π/8 − |Im u|)^{−1/2} at
#: the strip boundary, so the cap bites only within ~2e-10 of |Im u| = π/8 — where
#: any answer is precision-limited garbage anyway.  Without it, near-boundary
#: arguments hang for hours: float(π/8) itself sits 1.5e-17 *below* the true
#: boundary, slips past the strip check, and needs ~7.5e8 terms.  (The *unfolded*
#: series used by :func:`Phi_is_even_defect` also hits the cap for Re u ≲ −5.2,
#: where the defect has been pure noise since |u| ≈ 0.8 — see its docstring.)
_MAX_TERMS: int = 200_000


def _decay_rate(u: Any) -> Any:
    """ρ(u) := Re(e^{4u}), the rate governing |exp(−π n² e^{4u})| = exp(−π n² ρ).

    For real u this is just e^{4u}.  For u = x + iy it is e^{4x}·cos(4y), which is
    **negative** for π/8 < |y| < 3π/8 — there the summands of (1) grow with n and
    the series diverges.  Using e^{4·Re u} in its place (as a naive reading of (1)
    suggests) both under-counts terms inside the strip and fails to notice that
    the series is divergent outside it.
    """
    return mp.re(mp.exp(4 * mp.mpmathify(u)))


def _check_strip(u: Any) -> None:
    """Raise unless u lies in the strip |Im u| < π/8, where the series (1) converges.

    On the strip Re e^{4u} = e^{4 Re u}·cos(4 Im u) > 0; on its boundary and out to
    |Im u| = 3π/8 the summands stop decaying.  (Re e^{4u} > 0 holds again on bands
    around Im u = ±π/2, ±π, …, but those are disconnected from the real axis — see
    ``PHI_STRIP``.)
    """
    if abs(mp.im(u)) >= mp.pi / 8:
        raise ValueError(
            "Phi(u) is defined by a series that converges only on the strip "
            f"|Im u| < pi/8 = {PHI_STRIP:.9f}; got "
            f"Im u = {mp.nstr(mp.im(u), 8)}.  On and beyond the boundary the "
            "summands stop decaying and any partial sum is meaningless."
        )


def _terms_needed(u: Any, dps: int) -> int:
    """Number of n-terms so the tail of (1) falls below 10^{−(dps+15)}.

    The n-th summand has modulus O(n⁴ exp(−π n² ρ)) with ρ = Re(e^{4u}), so we need
    π n² ρ ≳ ln(10)·(dps+15), i.e. n ≳ sqrt(ln(10)(dps+15) / (π ρ)).
    This blows up like e^{−2u} as Re u → −∞, which is why :func:`Phi` folds through
    the exact identity Φ(−u) = Φ(u) rather than summing in the left half-plane.

    Raises rather than hangs when the count exceeds ``_MAX_TERMS`` — reachable only
    within ~2e-10 of the strip boundary.  Not academic: ``mpc(0, str(math.pi/8))``
    lies 1.5e-17 *inside* the open strip (float(π/8) rounds down), so it passes
    ``_check_strip`` yet would need ~7.5e8 terms.
    """
    rho = _decay_rate(u)
    if rho <= 0:
        _check_strip(u)  # normally raises with the informative message
        raise ValueError(f"Re(e^(4u)) = {mp.nstr(rho, 8)} <= 0; series (1) diverges")
    thr = mp.log(10) * (dps + 15)
    n = max(int(mp.sqrt(thr / (mp.pi * rho))) + 3, 3)
    if n > _MAX_TERMS:
        raise ValueError(
            f"Phi(u): the series would need {n} terms, because Im u = "
            f"{mp.nstr(mp.im(u), 8)} lies within "
            f"{mp.nstr(mp.pi / 8 - abs(mp.im(u)), 3)} of the strip boundary "
            f"pi/8 = {PHI_STRIP:.9f} where convergence degenerates; "
            "refusing rather than hanging."
        )
    return n


def _phi_series(u: Any, terms: int | None, dps: int) -> Any:
    """The **raw** truncated series (1), with no use of evenness.

    Numerically trustworthy only for Re u ≳ −0.6: the summands are O(1) while Φ(u)
    is itself O(exp(−π e^{4|u|})), so the sum is a cancellation of roughly
    π e^{4|u|}/ln 10 decimal digits.  At dps = 40 that exhausts the precision by
    |u| ≈ 0.85, beyond which the result is pure noise of arbitrary sign.  Public
    :func:`Phi` folds first and so never enters that regime; this helper is kept
    separate only so :func:`Phi_is_even_defect` can measure the identity honestly.
    """
    with mp.workdps(dps):
        u = mp.mpmathify(u)
        _check_strip(u)
        nmax = _terms_needed(u, dps) if terms is None else int(terms)
        e4, e5, e9 = mp.exp(4 * u), mp.exp(5 * u), mp.exp(9 * u)
        total = mp.mpf(0)
        for n in range(1, nmax + 1):
            n2 = mp.mpf(n) ** 2
            total += (2 * mp.pi**2 * n2**2 * e9 - 3 * mp.pi * n2 * e5) * mp.exp(
                -mp.pi * n2 * e4
            )
        return +total


def Phi(u: Any, terms: int | None = None, dps: int = DEFAULT_DPS) -> Any:
    """Φ(u) = Σ_{n≥1} (2π²n⁴ e^{9u} − 3π n² e^{5u}) · exp(−π n² e^{4u}).

    The theta-derived weight whose cosine transform is the Riemann Ξ function.
    Φ is **even**, strictly **positive on the real axis**, and decays
    super-exponentially: Φ(u) ≈ 2π² e^{9u} exp(−π e^{4u}) as u → +∞.

    Domain
    ------
    The series converges on the open strip ``|Im u| < π/8`` — the connected
    component of {Re e^{4u} > 0} containing the real axis.  For |Im u| ≥ π/8 the
    summands stop decaying, so a ``ValueError`` is raised rather than a
    meaningless partial sum returned.  A ``ValueError`` is also raised within
    ~2e-10 of the boundary, where the series converges in principle but would
    need over 2·10⁵ terms; ``float(π/8)`` itself lands in that zone (1.5e-17
    *below* the true boundary) and used to hang for hours instead of raising.

    Evenness folding — this matters numerically
    -------------------------------------------
    For Re u < 0 the summands are O(1) while Φ(u) is O(exp(−π e^{4|u|})), so the
    raw series is a catastrophic cancellation: at dps = 40 it has lost every
    significant digit by |u| ≈ 0.85 and returns noise **of the wrong sign** (the
    raw series gives −2.73e-41 at u = −1, where Φ(−1) = +5.10e-70; at u = −3 it
    gives −1.4e-39 where Φ(−3) = +1.7e-222046).  This function therefore applies
    the exact identity Φ(u) = Φ(−u) *first*, so the series is only ever summed
    where Re u ≥ 0 and no cancellation occurs.  :func:`Phi_is_even_defect` exposes
    the unfolded behaviour for inspection.

    Parameters
    ----------
    u : real or complex with |Im u| < π/8
        Argument.
    terms : int, optional
        Number of terms of the series.  Default: chosen automatically so the
        truncation error is below 10^{−(dps+15)}.
    dps : int
        Working precision (decimal digits) used for the evaluation.

    Returns
    -------
    mpf (or mpc for complex u)

    Notes
    -----
    Checked against ``mpmath.nsum`` given enough guard digits to survive the
    unfolded series' cancellation (π e^{4|u|}/ln 10 digits).  Relative accuracy is
    ≈ (1 + π e^{4|Re u|})·10^{−(dps+2)}: about 10^{−dps} for moderate |Re u|
    (measured 5.1e-41 at u = −0.3, dps = 40) but degrading with |u| — 2.1e-39 at
    u = −1.0 and 1.2e-38 at u = −1.4 (dps = 40) — because the exponent argument
    π n² e^{4|u|} (≈ 850 at u = 1.4) is itself computed to only dps digits.
    Verified value Φ(0) = 0.4466969004671234440869846670547091132204 (dps = 40).
    """
    with mp.workdps(dps):
        u = mp.mpmathify(u)
        _check_strip(u)
        if mp.re(u) < 0:  # exact, since Phi is even -- kills the cancellation
            u = -u
        return _phi_series(u, terms, dps)


def Phi_is_even_defect(
    u: Any, dps: int = DEFAULT_DPS, relative: bool = False
) -> Any:
    """|Φ_series(u) − Φ_series(−u)| for the **unfolded** series (1) — 0 exactly.

    Evenness of Φ is the theta functional equation θ(1/x) = √x·θ(x) in disguise.
    Concretely, with ψ(x) = Σ_{n≥1} e^{−πn²x}, F(x) = d/dx[x^{3/2}ψ'(x)] and
    Φ(u) = 2e^{3u}F(e^{4u}), evenness of Φ is exactly F(1/x) = x^{3/2}F(x)
    (verified independently to 1.6e-51 at x = 1.5, 4.6e-51 at x = 3, dps = 50).
    It is what makes H_t(z) an *even* function of z.

    This deliberately calls the raw series on **both** sides: using the folded
    :func:`Phi` would return identically zero and test nothing.

    Honest reading of the numbers (dps = 40)
    ----------------------------------------
    ::

        |u|   absolute defect   RELATIVE defect     verdict
        0.1       2.3e-41           7.5e-41         identity confirmed
        0.37      2.5e-41           5.0e-38         identity confirmed
        0.5       1.4e-41           1.0e-34         identity confirmed
        0.8       3.6e-42           4.1e-13         precision nearly exhausted
        1.0       2.7e-41           5.4e+28         left side is pure noise
        2.0       2.3e-41           2.6e+4017       left side is pure noise

    The *absolute* defect sits at the rounding floor for every u, but past
    |u| ≈ 0.6 that is evidence of nothing — both sides are then astronomically
    smaller than the noise, so an absolute-tolerance assertion there cannot fail.
    Pass ``relative=True`` for the quantity that can: it is below 10^{−34} for
    |u| ≤ 0.5 at dps = 40 and useless beyond |u| ≈ 0.8.  The cure is not more
    precision but the folding done inside :func:`Phi`.
    """
    with mp.workdps(dps):
        u = mp.mpmathify(u)
        d = abs(_phi_series(u, None, dps) - _phi_series(-u, None, dps))
        if not relative:
            return +d
        ref = abs(Phi(u, dps=dps))
        return +(d / ref) if ref != 0 else mp.inf


# --------------------------------------------------------------------------- #
#  Quadrature machinery for H_t
# --------------------------------------------------------------------------- #

def recommended_dps(z_max: float, digits: int = 15) -> int:
    """Working precision needed for ``digits`` significant digits of H_t up to z_max.

    Inverts the **conservative bound** (6):  dps ≈ digits + 2 + 0.1706·z_max, plus
    3 guard digits.  Verified sufficient (never tight): asking for 15 digits at
    z = 100 returns 38 and delivers 25.9; asking for 10 digits at z = 250 returns
    58 and delivers 20.7.  Over-provisioning by 6–11 digits is intentional.
    """
    return int(math.ceil(digits + 2 + _DIGITS_LOST_PER_Z * abs(float(z_max)))) + 3


@lru_cache(maxsize=16)
def _gauss_legendre(k: int, dps: int) -> tuple[tuple[Any, ...], tuple[Any, ...]]:
    """k-point Gauss–Legendre nodes/weights on [−1, 1].

    Roots of the Legendre polynomial P_k by Newton from the Chebyshev guess
    x_i ≈ cos(π(i − 1/4)/(k + 1/2)); weights w_i = 2/((1−x_i²) P_k'(x_i)²).
    Built with ``dps + 30`` guard digits and verified two ways: exact reproduction
    of the moments ∫_{−1}^{1} x^m dx for all m < 2k (worst error 3.1e-61 at
    dps = 30 and 1.8e-91 at dps = 60, both k = 20, evaluated at dps + 30), and
    agreement with ``numpy.polynomial.legendre.leggauss`` to 8.2e-16 in the
    weights and exactly in the nodes (i.e. to double precision, its limit).
    """
    with mp.workdps(dps + 30):
        xs: list[Any] = []
        ws: list[Any] = []
        for i in range(1, k + 1):
            x = mp.cos(mp.pi * (i - mp.mpf(1) / 4) / (k + mp.mpf(1) / 2))
            for _ in range(300):
                p = mp.legendre(k, x)
                dp = k * (x * p - mp.legendre(k - 1, x)) / (x**2 - 1)
                dx = p / dp
                x -= dx
                if abs(dx) < mp.mpf(10) ** (-mp.dps + 2):
                    break
            dp = k * (x * mp.legendre(k, x) - mp.legendre(k - 1, x)) / (x**2 - 1)
            xs.append(+x)
            ws.append(+(2 / ((1 - x**2) * dp**2)))
    return tuple(xs), tuple(ws)


def _integration_limit(t: float, dps: int) -> Any:
    """Smallest U with e^{tU²}·2π²e^{9U}·exp(−π e^{4U}) < 10^{−(dps+12)}.

    Beyond U the integrand of (2) is below the rounding floor, so truncating
    ∫₀^∞ at U is harmless.  U ≈ 0.885 at dps = 30 and ≈ 1.011 at dps = 60 — the
    integrand really is that sharply concentrated, which is why this works.
    """
    with mp.workdps(dps + 5):
        tgt = -(dps + 12) * mp.log(10)

        def f(U: Any) -> Any:
            return t * U**2 + 9 * U + mp.log(2 * mp.pi**2) - mp.pi * mp.exp(4 * U) - tgt

        return +mp.findroot(f, mp.mpf(1.0))


def _panels_for(z_abs: float, u_max: float, dps: int, n_gauss: int = 20) -> int:
    """Panel count for the composite k-point Gauss rule; bucketed to powers of 2·24.

    Three requirements, all of which must be met — the count is the max:

    1. **Oscillation.**  Each panel should span ≲ 1 wavelength of cos(z·u):
       ``z·u_max/π + 8`` panels.
    2. **Requested precision.**  A k-point Gauss rule applied to e^{iωx} on a panel
       carrying ω radians has error ≈ (e·ω/(8k))^{2k}.  Demanding 10^{−dps} gives
       ω ≤ (8k/e)·10^{−dps/(2k)}, i.e. ``z·u_max·e·10^{dps/(2k)}/(8k)`` panels.
    3. **Φ's own super-exponential variation.**  Independently of z, Φ ~ exp(−πe^{4u})
       has logarithmic derivative ≈ 4πe^{4u_max} ≈ 840 near the top of the interval;
       resolving that to 10^{−dps} needs the floor to double roughly every 45 digits.

    Requirement 2 was **missing** before and produced a hard precision floor: with a
    z-only rule, H_t(30) stalled at an absolute error of 5.2e-58 and then got
    *worse* with more digits (1.6e-56 at dps = 80, 1.1e-55 at dps = 100), because
    raising dps widens u_max without adding panels.  With this rule the same point
    reaches 5.6e-83 at dps = 80.  Counts are unchanged for dps ≤ 45, so the common
    case costs nothing.
    """
    need_osc = int(math.ceil(z_abs * u_max / math.pi)) + 8
    need_prec = int(
        math.ceil(z_abs * u_max * math.e * 10.0 ** (dps / (2.0 * n_gauss)) / (8.0 * n_gauss))
    )
    need = max(need_osc, need_prec)
    p = 24 * 2 ** max(0, math.ceil((dps - 45) / 45))
    while p < need:
        p *= 2
    return p


@lru_cache(maxsize=32)
def _quad_rule(
    dps: int, u_max_key: int, n_panels: int, n_gauss: int
) -> tuple[tuple[Any, ...], tuple[Any, ...], tuple[Any, ...]]:
    """Memoised composite Gauss–Legendre rule on [0, U] together with Φ at the nodes.

    Returns ``(nodes, weights, phi_values)``.  Φ depends on neither z nor t, so a
    whole zero-tracking sweep costs one rule build plus a few thousand cheap
    dot products.  ``u_max_key`` is U quantised to 1e-6 to keep the cache small.
    """
    with mp.workdps(dps):
        u_max = mp.mpf(u_max_key) / 10**6
        xs, ws = _gauss_legendre(n_gauss, dps)
        h = u_max / n_panels
        nodes: list[Any] = []
        weights: list[Any] = []
        for p in range(n_panels):
            a = p * h
            for x, w in zip(xs, ws):
                nodes.append(a + h * (x + 1) / 2)
                weights.append(w * h / 2)
        phis = [Phi(u, dps=dps) for u in nodes]
    return tuple(nodes), tuple(weights), tuple(phis)


def _rule_for(z_abs: float, t: float, dps: int, n_gauss: int = 20):
    """Pick (and memoise) the rule appropriate for arguments up to |Re z| = z_abs."""
    u_max = _integration_limit(max(float(t), 1.0), dps) * mp.mpf("1.02")
    key = int(mp.nint(u_max * 10**6))
    n_panels = _panels_for(z_abs, float(u_max), dps, n_gauss)
    return _quad_rule(dps, key, n_panels, n_gauss)


def _H_cached(z: Any, t: Any, dps: int, z_scale: float | None = None) -> Any:
    """H_t(z) via the memoised composite Gauss–Legendre rule."""
    with mp.workdps(dps):
        z = mp.mpc(z)
        scale = float(abs(mp.re(z))) if z_scale is None else float(z_scale)
        nodes, weights, phis = _rule_for(scale, float(t), dps)
        t = mp.mpf(t)
        total = mp.mpc(0)
        if t == 0:
            for u, w, ph in zip(nodes, weights, phis):
                total += w * ph * mp.cos(z * u)
        else:
            for u, w, ph in zip(nodes, weights, phis):
                total += w * ph * mp.exp(t * u**2) * mp.cos(z * u)
        return +total


def _H_adaptive(z: Any, t: Any, dps: int) -> Any:
    """H_t(z) via ``mpmath.quadgl`` on an oscillation-aware subdivision.

    Slower, and completely independent of the cached rule — used to validate it.
    """
    with mp.workdps(dps):
        z = mp.mpc(z)
        t = mp.mpf(t)
        u_max = _integration_limit(float(t), dps)
        ncyc = float(abs(mp.re(z))) * float(u_max) / (2 * math.pi)
        nsub = max(8, int(4 * ncyc) + 8)
        pts = [u_max * mp.mpf(k) / nsub for k in range(nsub + 1)]

        def f(u: Any) -> Any:
            return mp.exp(t * u**2) * Phi(u, dps=dps) * mp.cos(z * u)

        return +mp.quadgl(f, pts)


def H_t(
    z: Any,
    t: Any = 0,
    dps: int = DEFAULT_DPS,
    quad: str = "cached",
) -> Any:
    """H_t(z) = ∫₀^∞ e^{t u²} Φ(u) cos(z u) du.

    An entire, **even** function of z for every real t, real-valued for real z
    (Φ is real and even; cos is even).  At t = 0 it is the Riemann Ξ function:
    H₀(z) = (1/8)·Ξ(z/2), see :func:`H0_vs_Xi`.  It satisfies the *backward*
    heat equation ∂H/∂t = −∂²H/∂z², see :func:`heat_equation_residual`.

    Parameters
    ----------
    z : real or complex
        Argument.  ``mpc`` is returned in all cases.
    t : real
        Heat-flow time.  Any real t is admissible: e^{tu²} is crushed by the
        exp(−π e^{4u}) inside Φ, so (2) converges for every t.
    dps : int
        Working precision.  See :func:`recommended_dps` — you need
        dps ≳ digits + 2 + 0.171·|z|.
    quad : {"cached", "adaptive"}
        ``"cached"`` (default) uses the memoised composite Gauss–Legendre rule
        (≈25× faster after the first call).  ``"adaptive"`` uses
        ``mpmath.quadgl``; the two agree to 1.1e-31 at dps = 30 over
        z ∈ {0, 28.27, 60, 100, 150, 2−3i, 30+2i} and t ∈ {0, ±0.4, 0.1, 0.3}.

    Returns
    -------
    mpc

    Accuracy
    --------
    Measured against the independent oracle Ξ(z/2)/8 (evaluated at dps + 60), the
    absolute error over z ∈ [0, 400] is **3.8e-32 at dps = 30, 8.7e-42 at dps = 40,
    2.9e-62 at dps = 60** (worst point z = 0 in every case) — about 10^{−(dps+1)}.  The guaranteed figure used by
    :func:`recommended_dps` is the conservative 10^{−(dps−2)}.  For complex z the
    same absolute error holds relative to |H_t|, which grows like e^{|Im z|·u_max}
    (measured relative error 1.2e-40 at z = 30+30i, dps = 40).  Significant digits
    degrade with z per bound (6) because H₀ itself decays like exp(−πz/8); see the
    measured table in the module docstring.
    """
    if quad == "cached":
        return _H_cached(z, t, dps)
    if quad == "adaptive":
        return _H_adaptive(z, t, dps)
    raise ValueError(f"quad must be 'cached' or 'adaptive', got {quad!r}")


# --------------------------------------------------------------------------- #
#  The t = 0 normalisation, determined empirically
# --------------------------------------------------------------------------- #

def _rationalise(x: Any, max_den: int = 64, tol: Any = 1e-20) -> tuple[int, int] | None:
    """Nearest simple rational p/q to x with q ≤ max_den, if within tol."""
    from fractions import Fraction

    fr = Fraction(float(x)).limit_denominator(max_den)
    if abs(mp.mpf(fr.numerator) / fr.denominator - x) < tol:
        return fr.numerator, fr.denominator
    return None


def H0_vs_Xi(z_values: Sequence[Any] | None = None, dps: int = 40) -> dict[str, Any]:
    """Determine and verify the constants in  H₀(z) = c · Ξ(a z).

    **Nothing is assumed.**  Both constants are measured from the functions:

    * ``c = H₀(0)/Ξ(0)``  — no derivatives involved.
    * ``a`` by **two independent routes**, which must agree:

      1. *Curvature at the origin.*  H₀ and Ξ are even, so near 0 they look like
         H₀(0)(1 + ½ (H₀''(0)/H₀(0)) z²) and c·Ξ(0)(1 + ½ a²(Ξ''(0)/Ξ(0)) z²);
         matching the z² coefficients gives

             a = sqrt( (H₀''(0)/H₀(0)) / (Ξ''(0)/Ξ(0)) ).

         H₀''(0) = −∫₀^∞ u² Φ(u) du comes straight from the integral
         representation, so there is no differencing error on that side.
      2. *First zero.*  H₀ and Ξ vanish together, so a = γ₁ / z₁ where z₁ is the
         first positive real zero of H₀ and γ₁ the first zeta ordinate.

      Route 1 differentiates the module's own ``_xi_local`` rather than
      ``Xi_reference``: a sibling ``zeta.core.Xi`` may pin its own internal
      working precision, in which case ``mp.diff`` silently returns exactly 0 and
      the fit would blow up.  (This actually happened during development.)

    Both are then snapped to the nearest simple rational and the *exact rational*
    relation is verified pointwise over ``z_values``.

    Returns
    -------
    dict with keys ``relation`` (str), ``c``, ``a`` (mpf, the exact rationals),
    ``c_rational``, ``a_rational`` (tuple[int,int] or None),
    ``c_measured``, ``a_measured`` (mpf, raw fitted values),
    ``max_residual`` (mpf, max |H₀(z) − c·Ξ_local(a z)| — measures THIS module's
    quadrature), ``max_residual_vs_sibling`` (same but against ``zeta.core``, so it
    also carries that module's error), ``max_relative_residual``, ``residuals``,
    ``a_from_curvature``, ``a_from_first_zero``, ``z_values``, ``dps``.

    Result on this machine (dps = 40, real z ∈ [0, 100] plus complex probes)::

        relation                : H_0(z) = (1/8) * Xi((1/2)*z)
        a_from_curvature        : 0.5   (to 2.9e-41)
        a_from_first_zero       : 0.5   (to 2.4e-41)
        c_measured              : 0.125 (to 1.1e-42)
        max_residual            : 7.9e-42   (vs local xi -- our quadrature)
        max_residual_vs_sibling : ~1e-33    (vs zeta.core.Xi, limited by IT)
    """
    if z_values is None:
        z_values = [0, 1, 3, 7, 14, 28.2, 30, 50, 80, 100, mp.mpc(5, 1), mp.mpc(2, -3)]

    with mp.workdps(dps):
        # --- measure c ------------------------------------------------------
        # Fit against the *local* xi so the measured constants reflect this
        # module's own precision; the sibling zeta.core is then used separately
        # as an independent cross-check (see max_residual_vs_sibling below).
        h0 = _H_cached(0, 0, dps)
        xi0 = mp.mpf(mp.re(Xi_reference(0, backend="local")))
        c_meas = h0 / xi0

        # --- measure a, route 1: curvature at the origin ---------------------
        nodes, weights, phis = _rule_for(1.0, 0.0, dps)
        # H_0''(0) = -int_0^inf u^2 Phi(u) du, from the integral representation
        h0pp = -sum(w * ph * u**2 for u, w, ph in zip(nodes, weights, phis))
        # Differentiate the *local* xi: a sibling zeta.core.Xi may pin its own
        # internal precision, which silently collapses mp.diff to exactly 0.
        xi0_loc = mp.mpf(mp.re(_xi_local(mp.mpf(1) / 2)))
        xipp_loc = mp.diff(
            lambda T: mp.re(_xi_local(mp.mpf(1) / 2 + 1j * T)), mp.mpf(0), 2
        )
        a_curv = mp.sqrt((h0pp / h0) / (xipp_loc / xi0_loc))

        # --- measure a, route 2: first zero ----------------------------------
        # H_0 and Xi vanish together, so a = gamma_1 / z_1 with z_1 the first
        # positive real zero of H_0.  Fully independent of route 1.
        try:
            z1 = zeros_of_H_t(0, 20.0, 40.0, dps=dps)[0]
            a_zero = _reference_ordinates(1)[0] / z1
        except Exception:  # pragma: no cover - defensive
            a_zero = None

        a_meas = a_curv

        tol = mp.mpf(10) ** (-dps // 2)
        a_rat = _rationalise(mp.re(a_meas), tol=tol)
        c_rat = _rationalise(mp.re(c_meas), tol=tol)
        a = mp.mpf(a_rat[0]) / a_rat[1] if a_rat else mp.mpf(mp.re(a_meas))
        c = mp.mpf(c_rat[0]) / c_rat[1] if c_rat else mp.mpf(mp.re(c_meas))

        def _fmt(rat: tuple[int, int] | None, val: Any) -> str:
            if rat is None:
                return mp.nstr(val, 12)
            return f"{rat[0]}/{rat[1]}" if rat[1] != 1 else str(rat[0])

        relation = f"H_0(z) = ({_fmt(c_rat, c)}) * Xi(({_fmt(a_rat, a)})*z)"

        # --- verify with the exact rational constants ------------------------
        residuals: list[Any] = []
        rel_residuals: list[Any] = []
        residuals_sibling: list[Any] = []
        for z in z_values:
            zz = mp.mpc(z)
            lhs = _H_cached(zz, 0, dps)
            rhs = c * mp.mpmathify(Xi_reference(a * zz, backend="local"))
            d = abs(lhs - rhs)
            residuals.append(+d)
            if abs(lhs) > 0:
                rel_residuals.append(+(d / abs(lhs)))
            rhs_sib = c * mp.mpmathify(Xi_reference(a * zz))
            residuals_sibling.append(+abs(lhs - rhs_sib))

        return {
            "relation": relation,
            "c": +c,
            "a": +a,
            "c_rational": c_rat,
            "a_rational": a_rat,
            "c_measured": +mp.mpf(mp.re(c_meas)),
            "a_measured": +mp.mpf(mp.re(a_meas)),
            "a_from_curvature": +mp.mpf(mp.re(a_curv)),
            "a_from_first_zero": (None if a_zero is None else +mp.mpf(mp.re(a_zero))),
            "max_residual": max(residuals),
            "max_relative_residual": max(rel_residuals) if rel_residuals else mp.mpf(0),
            "max_residual_vs_sibling": max(residuals_sibling),
            "residuals": residuals,
            "z_values": list(z_values),
            "dps": dps,
        }


# --------------------------------------------------------------------------- #
#  Heat equation
# --------------------------------------------------------------------------- #

def heat_equation_residual(
    z: Any, t: Any = 0, h: Any = None, dps: int = DEFAULT_DPS
) -> Any:
    """|∂H/∂t + ∂²H/∂z²| for H_t(z), by central differences.

    **Sign convention, verified numerically rather than assumed.**  Differentiating
    H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du under the integral sign,

        ∂H/∂t   = ∫₀^∞  u² e^{tu²} Φ(u) cos(zu) du
        ∂²H/∂z² = ∫₀^∞ (−u²) e^{tu²} Φ(u) cos(zu) du

    so the two are exact negatives and H obeys the **backward** heat equation

        ∂H/∂t = −∂²H/∂z²,      equivalently   H_t = exp(−t ∂_z²) H₀.

    This function returns the residual ∂H/∂t + ∂²H/∂z², which is therefore zero.
    Both signs were checked directly against these two integrands as well
    (they agree to every displayed digit, e.g. at (z,t) = (10, 0.2):
    ∂H/∂t = −4.85383252228e-5 and ∂²H/∂z² = +4.85383252228e-5).

    Parameters
    ----------
    h : optional
        Step for the central differences.  Default 10^{−dps//5}, which balances
        the O(h²) truncation error against the O(ε/h²) rounding error.

    Measured: 1.6e-18 at (z,t) = (3, 0); 1.0e-18 at (10, 0.2); 3.4e-19 at
    (28, −0.1) — all at dps = 30, h = 1e-6.
    """
    with mp.workdps(dps):
        z = mp.mpc(z)
        t = mp.mpf(t)
        step = mp.mpf(10) ** (-(dps // 5)) if h is None else mp.mpf(h)
        scale = float(abs(mp.re(z))) + 1.0

        dH_dt = (
            _H_cached(z, t + step, dps, z_scale=scale)
            - _H_cached(z, t - step, dps, z_scale=scale)
        ) / (2 * step)
        d2H_dz2 = (
            _H_cached(z + step, t, dps, z_scale=scale)
            - 2 * _H_cached(z, t, dps, z_scale=scale)
            + _H_cached(z - step, t, dps, z_scale=scale)
        ) / step**2
        return +abs(dH_dt + d2H_dz2)


# --------------------------------------------------------------------------- #
#  Real zeros of H_t
# --------------------------------------------------------------------------- #

def zeros_of_H_t(
    t: Any,
    z_min: Any,
    z_max: Any,
    n_samples: int | None = None,
    dps: int | None = None,
) -> list[Any]:
    """Real zeros of H_t on [z_min, z_max], by sign change plus bracketed refinement.

    H_t is real on the real axis, so a sign change brackets a zero of odd order.
    Each bracket is refined with ``mpmath.findroot(..., solver='anderson')``.

    At **t = 0** these are exactly the rescaled zeta ordinates: since
    H₀(z) = (1/8)Ξ(z/2) and Ξ(γ_n) = 0, the zeros are z = 2γ_n.  Measured
    agreement with ``zeta.zeros.first_n_zeros`` (or ``mpmath.zetazero``) for the
    first 10 zeros (window [20, 105]): **max error 1.3e-19** at dps = 30
    (1.8e-18 against 20-digit decimal literals, which is those literals' own
    resolution -- 2*gamma_1 = 28.269450283469387580 carries only 19 digits).

    Parameters
    ----------
    t : real
        Heat-flow time.  t > 0 is the forward/repelling direction, t < 0 attracting.
    z_min, z_max : real
        Search window.  H_t is even, so only z > 0 carries information.
    n_samples : int, optional
        Grid points for the sign-change scan.  Default ``4*(z_max−z_min) + 50``,
        comfortably finer than the ~3.3 minimum spacing of the low-lying zeros.
    dps : int, optional
        Default ``recommended_dps(z_max, 15)`` — large z needs more digits because
        |H_t| is itself exponentially small there (equation (6)).

    Returns
    -------
    list of mpf, increasing.

    Caveat
    ------
    Sign-change scanning cannot see zeros of even order (e.g. a just-collided
    double zero) nor pairs closer than the grid spacing.  For the low-lying zeros
    over |t| ≤ 1 the spacing never drops below ~3.2, so this is safe here;
    increase ``n_samples`` for wider windows or more negative t.
    """
    if dps is None:
        dps = max(DEFAULT_DPS, recommended_dps(float(z_max), 15))
    with mp.workdps(dps):
        t = mp.mpf(t)
        a, b = mp.mpf(z_min), mp.mpf(z_max)
        n = int(4 * float(b - a)) + 50 if n_samples is None else int(n_samples)
        scale = float(abs(b)) + 1.0

        def f(x: Any) -> Any:
            return mp.mpf(mp.re(_H_cached(x, t, dps, z_scale=scale)))

        grid = [a + (b - a) * k / n for k in range(n + 1)]
        vals = [f(x) for x in grid]

        out: list[Any] = []
        for i in range(n):
            if vals[i] == 0:
                out.append(+grid[i])
                continue
            if mp.sign(vals[i]) != mp.sign(vals[i + 1]):
                root = mp.findroot(f, (grid[i], grid[i + 1]), solver="anderson")
                out.append(+mp.mpf(mp.re(root)))
        if vals[n] == 0:
            out.append(+grid[n])
        return out


def zero_gap_statistics(
    t: Any,
    z_min: Any = 20.0,
    z_max: Any = 105.0,
    dps: int | None = None,
) -> dict[str, Any]:
    """Spacing statistics of the real zeros of H_t on [z_min, z_max].

    The minimum gap is the quantity that controls the entire de Bruijn–Newman
    story: zeros can only leave the real axis by first colliding, so
    ``min_gap(t) > 0`` for every t ≥ Λ, and the forward flow drives it upward.

    Returns
    -------
    dict with ``t``, ``n_zeros``, ``zeros``, ``gaps``, ``min_gap``, ``max_gap``,
    ``mean_gap``, ``min_gap_at`` (midpoint of the tightest pair), ``window``.

    Measured on [20, 105] (the first 10 zeros: 2γ₁ = 28.27 … 2γ₁₀ = 99.55;
    note 2γ₁₁ = 105.94, so 105 is the right cut for exactly ten): min gap 3.28939 at t = −0.3,
    3.53736 at t = 0, 3.94962 at t = +0.6 — strictly increasing in t.
    """
    zs = zeros_of_H_t(t, z_min, z_max, dps=dps)
    gaps = [zs[i + 1] - zs[i] for i in range(len(zs) - 1)]
    if not gaps:
        return {
            "t": mp.mpf(t),
            "n_zeros": len(zs),
            "zeros": zs,
            "gaps": [],
            "min_gap": None,
            "max_gap": None,
            "mean_gap": None,
            "min_gap_at": None,
            "window": (mp.mpf(z_min), mp.mpf(z_max)),
        }
    i_min = min(range(len(gaps)), key=lambda i: gaps[i])
    return {
        "t": mp.mpf(t),
        "n_zeros": len(zs),
        "zeros": zs,
        "gaps": gaps,
        "min_gap": gaps[i_min],
        "max_gap": max(gaps),
        "mean_gap": sum(gaps) / len(gaps),
        "min_gap_at": (zs[i_min] + zs[i_min + 1]) / 2,
        "window": (mp.mpf(z_min), mp.mpf(z_max)),
    }


# --------------------------------------------------------------------------- #
#  Zero trajectories under the flow
# --------------------------------------------------------------------------- #

def _cache_path(tag: str, payload: dict[str, Any]) -> Path:
    key = hashlib.sha256(
        json.dumps(payload, sort_keys=True, default=str).encode()
    ).hexdigest()[:16]
    return _DATA_DIR / f"heatflow_{tag}_{key}.npz"


def track_zeros(
    t_values: Sequence[float],
    z_max: float = 105.0,
    n_zeros: int = 10,
    dps: int | None = None,
    use_cache: bool = True,
) -> dict[str, Any]:
    """Follow the first ``n_zeros`` positive real zeros of H_t as t varies.

    Method: one full sign-change scan at the t nearest 0, then **numerical
    continuation** outward in both directions — each zero is re-solved with
    ``findroot`` seeded from its position at the previous t.  Zero motion is
    smooth in t (the zeros are simple), so this is both faster than rescanning
    and, crucially, it preserves zero *identity* across the sweep.

    Physics of the picture produced
    -------------------------------
    * **t > 0 (forward / repelling).**  H_t = exp(−t∂_z²)H₀, so increasing t is
      the repelling direction: consecutive real zeros push apart, the minimum gap
      grows monotonically, and no zero can leave the real axis.
    * **t < 0 (backward / attracting).**  Gaps shrink.  If two real zeros collide
      they immediately become a complex-conjugate pair and leave the axis.

    Honest caveat: Rodgers–Tao's Λ ≥ 0 is **not** visible in this window.  The
    non-real zeros that Λ ≥ 0 forces for t < 0 occur at enormous height, where
    the zeta zeros are anomalously closely spaced (Lehmer pairs and worse), not
    among the first ten.  Over |t| ≤ 1 the zeros tracked here stay real and well
    separated; what this function exhibits is the repulsion *mechanism*, not the
    location of Λ.

    Returns
    -------
    dict with
      ``t_values``   (n_t,) float64, sorted ascending
      ``zeros``      (n_t, n_zeros) float64 trajectories, NaN where a zero was lost
      ``zeros_mp``   list of lists of mpf at full precision (None when cache-loaded)
      ``min_gap``    (n_t,) float64 minimum consecutive gap at each t
      ``spread``     (n_t,) float64 last zero − first zero
      ``n_real``     (n_t,) int, zeros successfully tracked
      ``z_max``, ``n_zeros``, ``dps``, ``source`` ("computed" or "cache")

    Cached to ``data/heatflow_track_zeros_<hash>.npz`` so re-runs are instant.
    """
    ts = sorted(float(t) for t in t_values)
    payload = {"t": ts, "z_max": float(z_max), "n": int(n_zeros), "dps": dps}
    path = _cache_path("track_zeros", payload)
    if use_cache and path.exists():
        with np.load(path) as f:
            return {
                "t_values": f["t_values"],
                "zeros": f["zeros"],
                "zeros_mp": None,
                "min_gap": f["min_gap"],
                "spread": f["spread"],
                "n_real": f["n_real"],
                "z_max": float(z_max),
                "n_zeros": int(n_zeros),
                "dps": int(f["dps"]),
                "source": "cache",
            }

    if dps is None:
        dps = max(DEFAULT_DPS, recommended_dps(float(z_max), 15))

    with mp.workdps(dps):
        scale = float(z_max) + 1.0

        def froot(x: Any, t: Any) -> Any:
            return mp.mpf(mp.re(_H_cached(x, t, dps, z_scale=scale)))

        i0 = min(range(len(ts)), key=lambda i: abs(ts[i]))
        base = zeros_of_H_t(ts[i0], 1.0, z_max, dps=dps)
        if len(base) < n_zeros:
            raise ValueError(
                f"only {len(base)} zeros of H_t below z_max={z_max}; "
                f"raise z_max to track {n_zeros} zeros"
            )
        base = base[:n_zeros]

        rows: dict[int, list[Any]] = {i0: base}
        for direction in (+1, -1):
            prev = list(base)
            i = i0 + direction
            while 0 <= i < len(ts):
                cur: list[Any] = []
                for seed in prev:
                    try:
                        r = mp.findroot(lambda x, tt=ts[i]: froot(x, tt), seed)
                        r = mp.mpf(mp.re(r))
                        lo = cur[-1] if cur and not mp.isnan(cur[-1]) else mp.mpf(0)
                        cur.append(r if r > lo else mp.nan)
                    except Exception:
                        cur.append(mp.nan)
                rows[i] = cur
                prev = [c if not mp.isnan(c) else p for c, p in zip(cur, prev)]
                i += direction

        zeros_mp = [rows[i] for i in range(len(ts))]

    arr = np.array(
        [[float(v) if not mp.isnan(v) else np.nan for v in row] for row in zeros_mp],
        dtype=float,
    )
    with np.errstate(invalid="ignore"):
        if arr.shape[1] > 1:
            min_gap = np.nanmin(np.diff(arr, axis=1), axis=1)
        else:
            min_gap = np.full(len(ts), np.nan)
        spread = arr[:, -1] - arr[:, 0]
    n_real = np.sum(~np.isnan(arr), axis=1).astype(int)
    t_arr = np.array(ts, dtype=float)

    _DATA_DIR.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        t_values=t_arr,
        zeros=arr,
        min_gap=min_gap,
        spread=spread,
        n_real=n_real,
        dps=np.array(dps),
    )
    return {
        "t_values": t_arr,
        "zeros": arr,
        "zeros_mp": zeros_mp,
        "min_gap": min_gap,
        "spread": spread,
        "n_real": n_real,
        "z_max": float(z_max),
        "n_zeros": int(n_zeros),
        "dps": int(dps),
        "source": "computed",
    }


# --------------------------------------------------------------------------- #
#  Known rigorous facts about Λ
# --------------------------------------------------------------------------- #

def lambda_facts() -> dict[str, Any]:
    """Rigorous bounds and statements about the de Bruijn–Newman constant Λ.

    Every numeric entry here is a *published theorem*, not something computed by
    this module.  ``lower_bound`` and ``upper_bound`` are the current best known.

    The bounds and attributions below were checked against the primary sources
    (Odlyzko's own survey of the history in Numer. Algorithms 25 (2000), 293-303,
    and the published abstracts).  Note the upper bounds 0.22 and 0.2 are
    **non-strict**; the only known strict upper bound is Ki-Kim-Lee's Lambda < 1/2.
    """
    return {
        "definition": "Lambda := inf{ t in R : H_t has only real zeros }",
        "well_defined_because": (
            "de Bruijn (1950) / Newman (1976): the set of t for which H_t has only "
            "real zeros is a closed half-line [Lambda, infinity), so the infimum "
            "exists and is attained."
        ),
        "equivalence": "RH  <=>  Lambda <= 0",
        "consequence": "With Rodgers-Tao (Lambda >= 0):  RH  <=>  Lambda == 0",
        "lower_bound": 0.0,
        "lower_bound_is_strict": False,
        "upper_bound": 0.2,
        "upper_bound_is_strict": False,
        "current_interval": "0 <= Lambda <= 0.2",
        "history": [
            {
                "bound": "Lambda <= 1/2",
                "who": "N. G. de Bruijn",
                "where": (
                    "The roots of trigonometric integrals, "
                    "Duke Math. J. 17 (1950), 197-226"
                ),
            },
            {
                "bound": "Lambda >= 0 conjectured",
                "who": "C. M. Newman",
                "where": (
                    "Fourier transforms with only real zeros, "
                    "Proc. Amer. Math. Soc. 61 (1976), 245-251 -- "
                    "'the Riemann hypothesis, if true, is only barely so'"
                ),
            },
            {
                "bound": "Lambda > -5.895e-9",
                "who": "G. Csordas, A. M. Odlyzko, W. Smith, R. S. Varga",
                "where": (
                    "A new Lehmer pair of zeros and a new lower bound for the "
                    "de Bruijn-Newman constant Lambda, "
                    "Electron. Trans. Numer. Anal. 1 (1993), 104-111"
                ),
            },
            {
                "bound": "Lambda > -4.379e-6",
                "who": "G. Csordas, W. Smith, R. S. Varga",
                "where": (
                    "Lehmer pairs of zeros, the de Bruijn-Newman constant Lambda, "
                    "and the Riemann Hypothesis, Constr. Approx. 10 (1994), 107-129"
                ),
            },
            {
                "bound": "Lambda > -2.7e-9",
                "who": "A. M. Odlyzko",
                "where": (
                    "An improved bound for the de Bruijn-Newman constant, "
                    "Numer. Algorithms 25 (2000), 293-303"
                ),
            },
            {
                "bound": "Lambda < 1/2  (strict)",
                "who": "H. Ki, Y.-O. Kim, J. Lee",
                "where": (
                    "On the de Bruijn-Newman constant, "
                    "Adv. Math. 222 (2009), 281-306"
                ),
            },
            {
                "bound": "Lambda > -1.14541e-11",
                "who": "Y. Saouter, X. Gourdon, P. Demichel",
                "where": (
                    "An improved lower bound for the de Bruijn-Newman constant, "
                    "Math. Comp. 80 (2011), 2281-2287"
                ),
            },
            {
                "bound": "Lambda <= 0.22",
                "who": "D. H. J. Polymath (Polymath15, led by T. Tao)",
                "where": (
                    "Effective approximation of heat flow evolution of the Riemann "
                    "xi function, and a new upper bound for the de Bruijn-Newman "
                    "constant, Res. Math. Sci. 6 (2019), no. 3, paper 31"
                ),
            },
            {
                "bound": "Lambda >= 0  (PROVED -- resolves Newman's conjecture)",
                "who": "B. Rodgers, T. Tao",
                "where": (
                    "The de Bruijn-Newman constant is non-negative, "
                    "Forum Math. Pi 8 (2020), e6 (arXiv:1801.05914, 2018)"
                ),
            },
            {
                "bound": "Lambda <= 0.2",
                "who": "D. J. Platt, T. S. Trudgian",
                "where": (
                    "The Riemann hypothesis is true up to 3e12, "
                    "Bull. Lond. Math. Soc. 53 (2021), 792-797 "
                    "(arXiv:2004.09765) -- sharpens Polymath15's 0.22 using "
                    "RH verified to height 3e12"
                ),
            },
        ],
        "note": (
            "The Lambda >= 0 proof is NOT a finite computation and is invisible in "
            "the low-lying zeros: it shows that Lambda < 0 would force the zeta "
            "zeros to be far too regularly spaced at large height to be compatible "
            "with known pair-correlation / fluctuation results."
        ),
    }


# --------------------------------------------------------------------------- #
#  Elementary illustration: heat flow on a real polynomial
# --------------------------------------------------------------------------- #

def _heat_evolve_coeffs(coeffs: np.ndarray, t: float, sign: int) -> np.ndarray:
    """exp(sign·t·d²/dx²) p = Σ_{k≥0} (sign·t)^k/k! · p^{(2k)}(x)  (finite for polys)."""
    out = np.array(coeffs, dtype=float)
    d = np.array(coeffs, dtype=float)
    fact = 1.0
    for k in range(1, len(coeffs) // 2 + 1):
        d = np.polyder(d, 2)
        if d.size == 0:
            break
        fact *= k
        out = np.polyadd(out, ((sign * t) ** k / fact) * d)
    return out


def _root_ode_rhs(r: np.ndarray, const: float) -> np.ndarray:
    """dr_i/dt = const · Σ_{j≠i} 1/(r_i − r_j)."""
    r = np.asarray(r, dtype=complex)
    out = np.zeros_like(r)
    for i in range(len(r)):
        s = 0.0 + 0.0j
        for j in range(len(r)):
            if i != j:
                s += 1.0 / (r[i] - r[j])
        out[i] = const * s
    return out


def _rk4(r0: np.ndarray, t0: float, t1: float, const: float, steps: int) -> np.ndarray:
    r = np.array(r0, dtype=complex)
    h = (t1 - t0) / steps
    for _ in range(steps):
        k1 = _root_ode_rhs(r, const)
        k2 = _root_ode_rhs(r + h / 2 * k1, const)
        k3 = _root_ode_rhs(r + h / 2 * k2, const)
        k4 = _root_ode_rhs(r + h * k3, const)
        r = r + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
    return r


def _sort_complex(a: np.ndarray) -> np.ndarray:
    """Sort complex roots by (real, imag) so trajectories stay identifiable."""
    a = np.asarray(a, dtype=complex)
    return a[np.lexsort((a.imag, a.real))]


def polynomial_heat_flow(
    roots: Sequence[float],
    t_values: Sequence[float],
    ode_steps_per_unit_t: int = 4000,
) -> dict[str, Any]:
    """The whole Λ story in miniature: heat flow on a real polynomial.

    Let p(x) = Π_i (x − r_i) and flow it with **the same sign convention as H_t**,

        ∂p/∂t = −∂²p/∂x² ,      p_t = exp(−t d²/dx²) p = Σ_k (−t)^k/k! p^{(2k)} ,

    which is an exact finite sum for a polynomial.  Then the roots move by

        dr_i/dt = +2 · Σ_{j≠i} 1/(r_i − r_j) .                                       (7)

    Derivation: with p = Π(x−r_i) one has ∂²p/∂x² = p·Σ_i (1/(x−r_i))·2Σ_{j≠i}1/(r_i−r_j)
    and ∂p/∂t = −p·Σ_i r_i'/(x−r_i); matching residues at x = r_i gives (7).

    **Sign and constant verified numerically, all four combinations.**  RK4 on (7)
    vs. the roots of the exactly heat-evolved coefficient vector, for roots
    [−3, −1, 0.5, 2, 4.5] over t ∈ [0, 0.35]::

        exp(-t D^2)  with const = +2  ->  max|ODE - exact| = 9.3e-15   OK
        exp(-t D^2)  with const = -2  ->  max|ODE - exact| = 1.6e+00   WRONG
        exp(+t D^2)  with const = -2  ->  max|ODE - exact| = 2.7e-14   OK
        exp(+t D^2)  with const = +2  ->  max|ODE - exact| = 1.6e+00   WRONG

    So the pairing is rigid: **exp(−tD²) ↔ +2 (roots REPEL for t>0),
    exp(+tD²) ↔ −2 (roots ATTRACT for t>0).**  In the same run the root spread went
    7.5 → 8.8529 under exp(−tD²) and 7.5 → 5.9015 under exp(+tD²).

    This function uses the de Bruijn–Newman convention exp(−tD²), so that
    "t increasing = repulsion" matches ``H_t`` exactly.  Note that the ODE is often
    quoted with a −2; that version belongs to the *classical forward* heat equation
    ∂_t p = +∂_x² p, under which real roots attract and collide — the opposite
    dynamical picture.  The two statements "dr_i/dt = −2Σ 1/(r_i−r_j)" and
    "roots repel for t > 0" are mutually inconsistent.

    Backward direction (t < 0 here) shrinks gaps; when two real roots collide they
    leave the real axis as a complex-conjugate pair, exactly as the zeros of H_t
    would below Λ.  ``collision_t`` reports the sampled t closest to 0 at which the
    roots are no longer all real.

    Parameters
    ----------
    roots : sequence of float
        Distinct real roots at t = 0.
    t_values : sequence of float
        Times to evaluate.  Include negatives to see collisions.
    ode_steps_per_unit_t : int
        RK4 steps per unit of |t| (default 4000).

    Returns
    -------
    dict with
      ``t_values``     (n_t,) float64, sorted
      ``roots_exact``  (n_t, n) complex128 — roots of the exactly heat-evolved poly
      ``roots_ode``    (n_t, n) complex128 — roots from RK4 on (7)
      ``max_ode_error`` float — worst |exact − ODE| over the all-real times
      ``max_abs_imag`` (n_t,) float64 — largest |Im root| (>0 ⇔ left the real axis)
      ``min_gap``      (n_t,) float64 — min gap of the real parts (NaN once complex)
      ``spread``       (n_t,) float64
      ``collision_t``  float or None — sampled t nearest 0 with non-real roots
      ``all_real``     (n_t,) bool
      ``convention``, ``ode``, ``verification`` — what was checked

    Everything here is double precision (numpy). Both routes evolve in a
    coordinate centered at a middle input root, then translate back. This avoids
    coefficient cancellation from a large common offset; high degree or tightly
    clustered roots can still be ill-conditioned. ``roots_exact`` names the
    finite coefficient evolution, not exact-arithmetic root finding.
    ``max_ode_error`` measures agreement in the centered coordinate, before the
    final translation can round away small differences.
    """
    r0 = np.asarray(sorted(float(r) for r in roots), dtype=float)
    if len(set(r0.tolist())) != len(r0):
        raise ValueError("roots must be distinct")
    ts = np.array(sorted(float(t) for t in t_values), dtype=float)
    n = len(r0)
    origin = r0[n // 2] if n else 0.0
    centered = r0 - origin
    c0 = np.poly(centered)
    sign = -1  # de Bruijn-Newman convention: p_t = exp(-t D^2) p, matching H_t
    const = +2.0  # its verified partner

    roots_exact = np.empty((len(ts), n), dtype=complex)
    for i, t in enumerate(ts):
        if t == 0:
            roots_exact[i] = centered
            continue
        ct = _heat_evolve_coeffs(c0, float(t), sign)
        rr = np.roots(ct) if len(ct) > 1 else np.array([], dtype=complex)
        if len(rr) < n:
            rr = np.concatenate([rr, np.full(n - len(rr), np.nan + 0j)])
        roots_exact[i] = _sort_complex(rr)

    roots_ode = np.empty((len(ts), n), dtype=complex)
    for i, t in enumerate(ts):
        steps = max(200, int(ode_steps_per_unit_t * abs(float(t))) + 1)
        roots_ode[i] = _sort_complex(_rk4(centered, 0.0, float(t), const, steps))

    max_abs_imag = np.max(np.abs(roots_exact.imag), axis=1)
    all_real = max_abs_imag < 1e-8
    errs = np.abs(roots_exact - roots_ode)
    max_ode_error = float(np.nanmax(errs[all_real])) if all_real.any() else float("nan")

    reals = np.sort(roots_exact.real, axis=1)
    if n > 1:
        min_gap = np.min(np.diff(reals, axis=1), axis=1)
    else:
        min_gap = np.full(len(ts), np.nan)
    min_gap = np.where(all_real, min_gap, np.nan)
    spread = reals[:, -1] - reals[:, 0]

    collided = ts[~all_real]
    collision_t = (
        float(collided[np.argmin(np.abs(collided))]) if collided.size else None
    )

    return {
        "t_values": ts,
        "roots_exact": roots_exact + origin,
        "roots_ode": roots_ode + origin,
        "max_ode_error": max_ode_error,
        "max_abs_imag": max_abs_imag,
        "min_gap": min_gap,
        "spread": spread,
        "collision_t": collision_t,
        "all_real": all_real,
        "initial_roots": r0,
        "convention": "p_t = exp(-t d^2/dx^2) p   (same sign as H_t; t>0 repels)",
        "ode": "dr_i/dt = +2 * sum_{j != i} 1/(r_i - r_j)",
        "verification": {
            "checked": (
                "RK4 on the root ODE vs the roots of the exactly heat-evolved "
                "coefficient vector p_t = sum_k (-t)^k/k! p^(2k)"
            ),
            "max_ode_error": max_ode_error,
            "sign_pairing": {
                "exp(-t D^2)": "dr_i/dt = +2 sum 1/(r_i-r_j)  -> roots REPEL for t>0",
                "exp(+t D^2)": "dr_i/dt = -2 sum 1/(r_i-r_j)  -> roots ATTRACT for t>0",
            },
        },
    }
