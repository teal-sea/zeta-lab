"""Newman's Lee–Yang program, made computational, and its battery verdict.

Statistical mechanics has a theorem that puts zeros on a line.  Lee–Yang
(1952): for a ferromagnet, the zeros of the partition function in the complex
fugacity plane all lie on the unit circle.  Newman spent the 1970s asking
whether ζ could be brought into that framework, and the de Bruijn–Newman
constant is what came out (`zeta/heatflow.py`, `docs/05`).

The dictionary this module makes explicit.  Read Φ, the heat kernel density
of `zeta/heatflow.py`, as the **single-site spin measure** of a lattice
model.  Its moment generating function is the partition function, and the
free energy is

    f(h) = log ∫ Φ(u) e^{hu} du .

That integral is not an abstraction: it is ξ.  Measured here rather than
recalled, ``free_energy_normalization`` reports

    ∫ Φ(u) e^{hu} du = ¼ · ξ(½ + h/2)

(the ratio against the ``(1/8)Ξ(z/2)`` form of `heatflow.py` comes out at
exactly 2.0, stable across h: Φ is even and de Bruijn's H₀ integrates over
the half-line).  So **the free energy of the Φ spin model is log ξ on the
real axis**, and "Φ lies in the Lee–Yang class", its Fourier transform has
only real zeros, is precisely RH.  That is a restatement, not progress; its
value is that the *classical sufficient conditions* for membership become
things one can measure.

What is measured here:

* **GHS** (Griffiths–Hurst–Sherman): f‴(h) ≤ 0 for h > 0, the statement that
  magnetization is concave in the field.  In ξ coordinates with w = h/2 this
  is G‴(w) ≤ 0 for G(w) = log ξ(½+w).  Two independent routes agree to five
  digits: a finite-difference derivative of ξ itself (assumes nothing), and
  the RH-assuming Hadamard form G‴(w) = −4w Σ_γ (3γ²−w²)/(γ²+w²)³.
* **Log-concavity of Φ**: (log Φ)″ < 0 throughout, measured from −74.9 at
  u = 0 to −9.1×10³ at u = 1.3.  Φ is a positive, even, log-concave density.

**The verdict, and it is negative** (`docs/09` gate #3).  GHS holds for ζ
across the whole tested range, and it holds just as cleanly for the
Davenport–Heilbronn function, which violates RH.  Its completed form is real
and symmetric about ½, so the same free energy is defined, and its G‴ is
negative at every probe point (−1.02×10⁻² at w = 0.5 through −3.05×10⁻⁴ at
w = 40).  A ferromagnetic-inequality probe therefore distinguishes nothing:
whatever makes ζ's zeros real, GHS does not see it.  This is the expected
yield and it is recorded rather than buried.

Two traps met on the way, both left documented in
:func:`log_xi_third_derivative`: ``mp.diff`` silently returns ~0 on ``xi``
(internal rounding makes it bit-constant across the step), and the textbook
5-point stencil for a third derivative is easy to write with its sign
flipped, caught here only because the independent zero-sum route disagreed.

Everything here is *accurate*, not *certified* (see `zeta/rigor.py`).
"""

from __future__ import annotations

from typing import Any, Callable, Sequence

import numpy as np
from mpmath import mp

__all__ = [
    "free_energy_normalization",
    "log_xi_third_derivative",
    "ghs_defect",
    "ghs_zero_sum",
    "ghs_scan",
    "phi_log_concavity",
    "ghs_battery",
]

DEFAULT_PROBES = (0.5, 1.0, 2.0, 5.0, 10.0, 14.0, 20.0, 25.0, 30.0, 40.0)


def free_energy_normalization(
    h_values: Sequence[float] = (0.0, 0.5, 1.2), dps: int = 25
) -> dict[str, Any]:
    """Measure the constant c in ∫Φ(u)e^{hu}du = c·ξ(½+h/2).

    Derived, never remembered (house rule): the integral is evaluated by
    quadrature and divided by ξ.  The ratio must be the *same* at every h,
    that constancy is what makes it a normalization rather than a fit.
    """
    from .core import xi
    from .heatflow import Phi

    ratios = []
    with mp.workdps(dps):
        for h in h_values:
            h = mp.mpf(h)
            integral = mp.quad(lambda u: Phi(u) * mp.e ** (h * u), [-4, 0, 4])
            ratios.append(float(integral / xi(mp.mpf(0.5) + h / 2)))
    arr = np.array(ratios)
    return {
        "h_values": list(map(float, h_values)),
        "ratios": ratios,
        "constant": float(arr.mean()),
        "spread": float(arr.std()),
        "matches_quarter": bool(abs(arr.mean() - 0.25) < 1e-9 and arr.std() < 1e-9),
    }


def _d3_central(f: Callable, w: float, step: float, dps: int) -> float:
    """f‴(w) by the 5-point central stencil.

    [f(w+2s) − 2f(w+s) + 2f(w−s) − f(w−2s)] / (2s³).  The sign convention is
    pinned by :func:`ghs_zero_sum` in the tests; writing this stencil negated
    is a live hazard and the cross-check is the only thing that catches it.
    """
    with mp.workdps(dps):
        w = mp.mpf(w)
        s = mp.mpf(step)
        return float(
            (f(w + 2 * s) - 2 * f(w + s) + 2 * f(w - s) - f(w - 2 * s)) / (2 * s**3)
        )


def log_xi_third_derivative(
    w: float, source: str = "zeta", step: float = 0.05, dps: int = 40
) -> float:
    """G‴(w) for G(w) = log ξ(½+w), or the Davenport–Heilbronn analogue.

    Trap, documented rather than worked around: the obvious
    ``mp.diff(lambda x: mp.log(xi(0.5+x)), w, 3)`` returns ~1e-47, i.e.
    zero.  ``xi`` rounds to a fixed working precision internally, so across
    ``mp.diff``'s automatic step the function is bit-for-bit constant and the
    derivative silently vanishes.  Same failure as ``dh_f`` in
    `zeta/quasicrystal.py`.  A hand-rolled stencil with an explicit,
    calibrated step is required; ``step=0.05`` at ``dps=40`` reproduces the
    independent zero-sum route to five digits.
    """
    if source == "zeta":
        from .core import xi

        f = lambda x: mp.log(xi(mp.mpf(0.5) + x))
    elif source == "dh":
        from .epstein import completed_dh

        f = lambda x: mp.log(completed_dh(mp.mpf(0.5) + x))
    else:
        raise ValueError("source must be 'zeta' or 'dh'")
    return _d3_central(f, w, step, dps)


def ghs_defect(w: float, source: str = "zeta", **kw) -> float:
    """The GHS defect: G‴(w).  GHS is the assertion that this is ≤ 0.

    Returned as a signed measurement, not a boolean, a positive value at
    some w would be the interesting event, and rounding it to True/False
    would throw away the margin.
    """
    return log_xi_third_derivative(w, source=source, **kw)


def ghs_zero_sum(w: float, n_zeros: int = 2000) -> float:
    """G‴(w) = −4w Σ_γ (3γ²−w²)/(γ²+w²)³, the Hadamard route, assuming RH.

    Under RH the pairing ρ = ½±iγ gives ξ(½+w) = ξ(½)·∏_γ (1 + w²/γ²), and
    this is the third derivative of its log.  Independent of
    :func:`log_xi_third_derivative` in every step, which is what makes the
    agreement a check.  Truncating the product omits terms of sign −12w/γ⁴,
    so a truncated value is an *over*estimate (less negative), the bias runs
    against a false GHS pass.
    """
    from .explicit import first_zeros

    g = np.asarray(first_zeros(n_zeros), dtype=float)
    w = float(w)
    return float(-4.0 * w * np.sum((3.0 * g**2 - w * w) / (g**2 + w * w) ** 3))


def ghs_scan(
    probes: Sequence[float] = DEFAULT_PROBES, source: str = "zeta", **kw
) -> dict[str, Any]:
    """Evaluate the GHS defect across probe points and report any violation."""
    vals = [ghs_defect(w, source=source, **kw) for w in probes]
    violations = [(float(w), v) for w, v in zip(probes, vals) if v > 0]
    return {
        "source": source,
        "probes": list(map(float, probes)),
        "defects": vals,
        "max_defect": float(max(vals)),
        "violations": violations,
        "ghs_holds_on_probes": len(violations) == 0,
    }


def phi_log_concavity(
    u_values: Sequence[float] = (0.0, 0.2, 0.5, 0.8, 1.0, 1.3),
    step: float = 0.01,
    dps: int = 40,
) -> dict[str, Any]:
    """(log Φ)″ at the given points; negative everywhere means log-concave.

    Log-concavity is necessary for the comfortable end of Lee–Yang theory but
    nowhere near sufficient for real zeros of the transform, a Gaussian is
    log-concave and its transform has no zeros at all.  Reported because a
    *failure* here would have been the surprise.
    """
    from .heatflow import Phi

    out = []
    with mp.workdps(dps):
        s = mp.mpf(step)
        for u in u_values:
            u = mp.mpf(u)
            lp = lambda x: mp.log(Phi(x))
            out.append(float((lp(u + s) - 2 * lp(u) + lp(u - s)) / s**2))
    return {
        "u_values": list(map(float, u_values)),
        "second_derivatives": out,
        "log_concave": all(v < 0 for v in out),
        "max_value": float(max(out)),
    }


def ghs_battery(probes: Sequence[float] = DEFAULT_PROBES) -> dict[str, Any]:
    """Run GHS on ζ and on Davenport–Heilbronn: does the inequality separate them?

    The answer measured here is **no**, which is the point.  Recorded as a
    negative result per `docs/09` gate #3: a structural property shared with
    a function that violates RH cannot be what makes ζ's zeros real.
    """
    z = ghs_scan(probes, source="zeta")
    d = ghs_scan(probes, source="dh")
    cross = [
        {
            "w": float(w),
            "from_xi": ghs_defect(w, source="zeta"),
            "from_zeros": ghs_zero_sum(w),
        }
        for w in (1.0, 5.0, 20.0)
    ]
    for c in cross:
        c["relative_gap"] = abs(c["from_xi"] - c["from_zeros"]) / abs(c["from_zeros"])
    return {
        "zeta": z,
        "dh": d,
        "route_cross_check": cross,
        "max_route_gap": float(max(c["relative_gap"] for c in cross)),
        "separates": bool(z["ghs_holds_on_probes"] != d["ghs_holds_on_probes"]),
        "verdict": (
            "GHS holds for zeta AND for Davenport-Heilbronn across every probe "
            "point, so the ferromagnetic inequality distinguishes nothing "
            "(docs/09 gate #3). The Lee-Yang restatement of RH is exact -- the "
            "free energy of the Phi spin model is log xi -- but membership in "
            "the Lee-Yang class is RH itself, not a route to it."
        ),
    }
