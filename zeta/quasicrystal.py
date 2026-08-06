"""The zero measure as a crystalline (atomic) Fourier object — and the one
gate in this family that the Davenport–Heilbronn counterexample fails.

Guinand's summation formula says the zeros and the prime powers are a Fourier
pair.  Read as a statement about *measures*: the counting measure of the
ordinates, μ = Σ_γ δ_γ, has a Fourier transform that is **atomic**, with atoms
sitting exactly at u = log n and weights proportional to Λ(n)/√n.  That is the
defining shape of a Fourier quasicrystal (Kurasov–Sarnak 2020 build such
measures deliberately; ζ supplies one for free).

What this module measures, with a Gaussian-tapered window of width A:

    Z(u) = Σ_{γ>0} e^{−γ²/2A²} cos(γu)

* **The atom law.**  Z(log n) ≈ c·Λ(n)/√n with c = −A/(2√(2π)), a constant
  *derived* here from the Weil explicit formula for the test-function pair
  h(r) = e^{−r²/2A²}cos(ru), ĥ(x) = ½[ŵ(x−u) + ŵ(x+u)], ŵ(x) =
  (A/√(2π))e^{−A²x²/2}.  The derivation is checked, not trusted: measured/
  predicted runs 0.94–0.98 across taper widths spanning 2.5× (the shortfall is
  the finite zero list — the taper is only down to 0.04 at γ₁₀₀₀).
* **The Euler-product signature.**  ζ's Euler product forces Λ to vanish off
  the prime powers, so the transform must be *silent* at log 6, log 10,
  log 12, …  Measured with 1000 zeros: prime-power atoms have median |Z| =
  60.1, composite locations 2.2, ambient background 0.90 — a 26.8× separation.
  The zero measure sees the factorization.
* **The battery verdict, and it is the interesting one** (`docs/09` gate #3).
  Every other structural probe in this repository passes Davenport–Heilbronn
  as readily as ζ.  This one does not.  f_DH is a *sum* of two Dirichlet
  L-functions, not an Euler product, so its log-derivative −f′/f has
  coefficients spread over all integers: b₆ = +1.936, b₁₄ = −2.852,
  b₂₁ = +3.290 sit where ζ is exactly silent.  DH's zero measure is still
  crystalline — it just crystallises on a *different, non-multiplicative*
  atom set.

  The honest reading: this gate detects the **Euler product**, not RH.  DH
  was already known to lack one.  What the measurement adds is that the
  atomic structure of the zero measure is a strictly sharper invariant than
  the functional equation — it separates ζ from the standard counterexample,
  where positivity-flavoured probes do not.  That is a computational instance
  of the strengthened gate in `docs/09` §5.1: *factorization*, not
  positivity, is what carries the arithmetic.  It is not evidence for RH;
  possessing an Euler product is not known to imply RH — that implication is
  substantially the content of the Grand Riemann Hypothesis itself.

Everything here is *accurate*, not *certified* (float transform over an
mpmath-sourced zero list; see `zeta/rigor.py` for the reserved word).
"""

from __future__ import annotations

from typing import Any, Iterable, Sequence

import numpy as np

__all__ = [
    "zero_measure_transform",
    "predicted_atom_constant",
    "atom_table",
    "euler_signature_report",
    "dh_log_derivative_coefficients",
    "dh_dirichlet_defect",
    "crystallinity_battery",
]

# Integers used throughout as the two probe classes.
PRIME_POWERS = (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19)
COMPOSITES = (6, 10, 12, 14, 15, 18, 20, 21, 22, 24, 26, 28, 30)


def zero_measure_transform(ordinates: Sequence[float], A: float):
    """Return u ↦ Σ_{γ>0} e^{−γ²/2A²} cos(γu) for the given ordinates.

    The Gaussian taper is what makes the transform a function rather than a
    distribution; A controls the trade-off between atom sharpness (∼1/A) and
    truncation error from the finite zero list.  Callers should keep A well
    below the largest ordinate — see ``atom_table``'s measured ratios for how
    much the residual taper costs.
    """
    g = np.asarray(ordinates, dtype=float)
    w = np.exp(-0.5 * (g / float(A)) ** 2)

    def Z(u):
        u = np.atleast_1d(np.asarray(u, dtype=float))
        return (w[None, :] * np.cos(g[None, :] * u[:, None])).sum(axis=1)

    return Z


def predicted_atom_constant(A: float) -> float:
    """c = −A/(2√(2π)): the derived height of the log-n atom per unit Λ(n)/√n.

    From the explicit formula applied to h(r) = e^{−r²/2A²}cos(ru): the prime
    side contributes −Σ_n (Λ(n)/√n)·½[ŵ(log n − u) + ŵ(log n + u)] and ŵ
    peaks at (A/√(2π)); the ½ survives because the zero side counts ±γ.
    """
    return -float(A) / (2.0 * np.sqrt(2.0 * np.pi))


def atom_table(
    ordinates: Sequence[float],
    A: float,
    integers: Iterable[int] = PRIME_POWERS,
) -> dict[str, Any]:
    """Measured atom heights at log n against the derived prediction."""
    from .explicit import mangoldt

    Z = zero_measure_transform(ordinates, A)
    c = predicted_atom_constant(A)
    rows = []
    for n in integers:
        lam = mangoldt(n) / np.sqrt(n)
        z = float(Z(np.log(n))[0])
        rows.append(
            {
                "n": int(n),
                "lambda_over_sqrt_n": lam,
                "measured": z,
                "predicted": c * lam,
                "ratio": (z / (c * lam)) if lam else None,
            }
        )
    ratios = [r["ratio"] for r in rows if r["ratio"] is not None]
    return {
        "A": float(A),
        "predicted_constant": c,
        "rows": rows,
        "ratio_mean": float(np.mean(ratios)) if ratios else None,
        "ratio_spread": float(np.std(ratios)) if ratios else None,
    }


def _background(Z, rng_seed: int = 2, n_samples: int = 800) -> np.ndarray:
    """|Z| sampled away from every log n, n ≤ 80 — the non-atomic floor."""
    rng = np.random.default_rng(rng_seed)
    u = rng.uniform(0.6, 3.6, n_samples)
    keep = np.array(
        [min(abs(x - np.log(k)) for k in range(2, 80)) > 0.05 for x in u]
    )
    return np.abs(Z(u[keep]))


def euler_signature_report(
    ordinates: Sequence[float], A: float | None = None
) -> dict[str, Any]:
    """Quantify the silence at composite non-prime-powers.

    ``separation`` is median |Z| at prime powers divided by median |Z| at
    composites: large means the transform is reading the Euler product.
    """
    g = np.asarray(ordinates, dtype=float)
    if A is None:
        A = float(g.max()) / 3.0
    Z = zero_measure_transform(g, A)
    pp = np.abs(np.array([float(Z(np.log(n))[0]) for n in PRIME_POWERS]))
    comp = np.abs(np.array([float(Z(np.log(n))[0]) for n in COMPOSITES]))
    bg = _background(Z)
    return {
        "A": float(A),
        "n_ordinates": int(g.size),
        "prime_power_median": float(np.median(pp)),
        "composite_median": float(np.median(comp)),
        "background_median": float(np.median(bg)),
        "background_p99": float(np.percentile(bg, 99)),
        "separation": float(np.median(pp) / np.median(comp)),
        "composite_over_background": float(np.median(comp) / np.median(bg)),
    }


# ----------------------------------------------------------------------
# Davenport–Heilbronn: where its atoms actually are
# ----------------------------------------------------------------------

def dh_log_derivative_coefficients(n_max: int = 32, dps: int = 30) -> list[float]:
    """b_n with −f′/f(s) = Σ_{n≥1} b_n n^{−s}, for the DH function f.

    Derived by Dirichlet convolution from f's own coefficients: matching
    n^{−s} in Σ a_n log(n) n^{−s} = (Σ b_m m^{−s})(Σ a_k k^{−s}) gives
    a_n log n = Σ_{m|n} b_m a_{n/m}, solved upward from a₁ = 1.  Correctness
    is not assumed — :func:`dh_dirichlet_defect` evaluates both sides.

    Returns a list indexed 0..n_max (index 0 unused, set to 0.0).
    """
    from mpmath import mp

    from .epstein import dh_coefficient

    with mp.workdps(dps + 10):
        a = [mp.mpf(0)] * (n_max + 1)
        for n in range(1, n_max + 1):
            a[n] = mp.mpf(dh_coefficient(n))
        b = [mp.mpf(0)] * (n_max + 1)
        for n in range(1, n_max + 1):
            s = a[n] * mp.log(n)
            for m in range(1, n):
                if n % m == 0:
                    s -= b[m] * a[n // m]
            b[n] = s / a[1]
        return [float(x) for x in b]


def dh_dirichlet_defect(
    s: complex = 3.0, n_max: int = 400, n_ref: int = 3000, dps: int = 30
) -> float:
    """|Σ b_n n^{−s} − (−f′/f)(s)|, the cross-check on the recursion.

    The reference value is built by a route that shares no arithmetic with
    the convolution: f and f′ are each summed as their own Dirichlet series
    (f′(s) = −Σ a_n log(n) n^{−s}) and *divided*, where
    :func:`dh_log_derivative_coefficients` instead *convolves*.  Re(s) must
    be comfortably > 1 for both to converge absolutely.

    Trap, found the hard way and left documented rather than worked around:
    the obvious reference — ``mp.diff(lambda z: mp.log(dh_f(z)), s)`` —
    returns **exactly 0.0**.  ``dh_f`` rounds its result to a fixed working
    precision internally, so across ``mp.diff``'s tiny step the function is
    bit-for-bit constant and the derivative silently vanishes.  Using it as
    the reference reports a flat ~1.4e-3 "defect" at every ``n_max``, which
    is the whole value of −f′/f, not an error in the coefficients.  A defect
    that does not shrink with truncation is diagnostic of a broken
    reference, not a broken series.
    """
    from mpmath import mp

    from .epstein import dh_coefficient

    with mp.workdps(dps + 10):
        s = mp.mpf(s) if not isinstance(s, complex) else mp.mpc(s)
        a = [mp.mpf(0)] + [mp.mpf(dh_coefficient(n)) for n in range(1, n_ref + 1)]
        f_ref = mp.fsum(a[n] * mp.power(n, -s) for n in range(1, n_ref + 1))
        fp_ref = -mp.fsum(
            a[n] * mp.log(n) * mp.power(n, -s) for n in range(2, n_ref + 1)
        )
        reference = -fp_ref / f_ref

        b = dh_log_derivative_coefficients(n_max, dps=dps)
        series = mp.fsum(mp.mpf(b[n]) * mp.power(n, -s) for n in range(2, n_max + 1))
        return float(abs(series - reference))


def crystallinity_battery(
    n_zeta_zeros: int = 1000, dh_t_max: float = 120.0, n_coeff: int = 24
) -> dict[str, Any]:
    """The gate: does the atomic structure separate ζ from Davenport–Heilbronn?

    Returns the ζ Euler signature, the DH log-derivative coefficients at the
    composite locations where ζ is silent, and the verdict fields.  Unlike
    every other probe in this repository's battery, this one *does* separate
    them — see the module docstring for exactly how much that is worth.
    """
    from .explicit import first_zeros, mangoldt

    gam = first_zeros(n_zeta_zeros)
    zeta_sig = euler_signature_report(gam)

    b = dh_log_derivative_coefficients(max(n_coeff, max(COMPOSITES)))
    dh_composite = {n: b[n] for n in COMPOSITES if n < len(b)}
    zeta_composite = {n: mangoldt(n) for n in COMPOSITES}
    dh_loud = {n: v for n, v in dh_composite.items() if abs(v) > 0.5}

    return {
        "zeta_euler_signature": zeta_sig,
        "zeta_composite_mangoldt": zeta_composite,
        "dh_composite_log_derivative": dh_composite,
        "dh_composite_nonzero_count": len(dh_loud),
        "dh_loudest_composites": dict(
            sorted(dh_loud.items(), key=lambda kv: -abs(kv[1]))[:4]
        ),
        "separates": bool(
            zeta_sig["separation"] > 5.0 and len(dh_loud) >= 3
        ),
        "verdict": (
            "The atomic structure of the zero measure separates zeta from "
            "Davenport-Heilbronn: zeta is silent at composite non-prime-powers "
            "(Euler product => Lambda supported on prime powers) while DH's "
            "-f'/f is loud there. This detects the Euler product, NOT RH; an "
            "Euler product is not known to imply RH (that is substantially "
            "GRH itself). docs/09 gate #3, strengthened form (§5.1)."
        ),
    }
