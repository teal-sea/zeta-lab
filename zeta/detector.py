"""Detecting off-line zeros without solving for them, the position-sensitive gate.

Every probe in `docs/18` §1–2 failed for the same reason: it consumed only
*ordinates*.  ζ(s−δ) has the same ordinates as ζ while its zeros sit on a
different vertical line, so no ordinate statistic can locate the critical
line at all.  What is needed is a statistic that sees a zero's **real part**.

The Weil explicit formula is exactly that.  In the convention of
`zeta/weil.py`,

    Σ_ρ h(γ_ρ) = arch(h) + pole(h) − 2 Σ_n b_n n^{−1/2} g(log n),

with g(u) = (1/2π)∫h(r)e^{−iru}dr and **γ_ρ = (ρ − ½)/i**.  For a zero on
the line γ_ρ is real; for an off-line zero ρ = β+iγ it is
γ − i(β − ½), *complex*.  The right-hand side is built from the Dirichlet
coefficients and the gamma factor alone and therefore accounts for **all**
zeros.  So

    residue(c) := [arithmetic side] − [sum over ON-LINE zeros only]

is precisely the contribution of the zeros that are not on the line, and
neither input to it ever knows an off-line zero exists.

Measured, with a bump h centred at c (`detector_battery`):

* **ζ is silent.**  |residue| ≤ 6.5e-15 across probes at c = 20 … 120,
  float noise.  Its on-line zeros account for the entire explicit formula.
* **Davenport–Heilbronn spikes.**  Quiet (≤ 1e-9) at c = 40, 60, 75, 100,
  and at c = γ₀ = 85.699348 it reads **+4.096324360134**, against a
  predicted contribution from the known off-line quadruple
  {β+iγ₀, 1−β+iγ₀, and conjugates} of **+4.096324360134**, agreeing to
  **8.9e-15**.
* **The peak height measures how far off the line the zero is, but only if
  you already know where the peak is.**  The quadruple contributes
  ≈ 4·exp(a·(β−½)²), so inverting gives |β − ½| = 0.308517 against the true
  0.308517, to **1.3e-14** (`recover_distance_from_line`).  That 1.3e-14 is
  obtained by evaluating the residue *at* `OFFLINE_ZERO_IM`, i.e. at thirteen
  correct decimals of the answer, and the inversion `sqrt(log(r/4)/a)` is
  infinitely steep at r = 4: the whole signal lives in the fourth decimal of
  the residue.  Measured 2026-08-11: displacing the centre by 7e-4 costs seven
  orders (7.2e-7 error), and running the module's *own* pipeline end to end,
  `residue_scan` on the grid the tests use, then argmax, then invert, recovers
  0.0221 against the true 0.3085, a **92.8 % error**.  So: **detection is
  unconditional, quantification is conditional on an independently located
  ordinate.**  `recover_distance_from_line` says the same in its own docstring;
  the headline above used to say it only there.

The archimedean brackets are *derived*, not recalled.  For a completed
function Λ(s) = Λ_∞(s)f(s) the bracket is 2·Re(Λ_∞′/Λ_∞)(½+ir):

* ζ, with Λ_∞ = π^{−s/2}Γ(s/2):        Re ψ(¼ + ir/2) − log π
* DH, with Λ_∞ = (π/5)^{−(s+1)/2}Γ((s+1)/2):  Re ψ(¾ + ir/2) + log(5/π)

and the ζ row is checked against `zeta.weil`'s own convention by the
vanishing of the ζ residue, which is a three-way agreement between an
integral, a prime sum and a zero list that share no code.

**What this is not.**  It is not a proof of RH for ζ over any range, and it
is not *certified* (`zeta/rigor.py` owns that word, this is float/mpmath
without enclosures).  It is a finite-range consistency statement of the same
family as `verify_rh_up_to`, reached by a different route.

**The load-bearing caveat.**  The residue measures "zeros unaccounted for by
the supplied on-line list".  A *missing* on-line zero, sign-change hunting
can skip a close pair, produces residue indistinguishable from an off-line
zero.  The statistic therefore has to be paired with an independent count of
the on-line zeros; `online_list_is_complete` does that against
`zeta.epstein.zeros_on_line`, and a scan whose completeness has not been
checked reports nothing trustworthy.
"""

from __future__ import annotations

import json
import os
from typing import Any, Callable, Sequence

import numpy as np
from mpmath import mp

__all__ = [
    "DEFAULT_WIDTH",
    "bump_pair",
    "archimedean_bracket",
    "arithmetic_side",
    "online_zero_side",
    "offline_residue",
    "residue_scan",
    "recover_distance_from_line",
    "online_list_is_complete",
    "detector_battery",
]

# h(r) = exp(-a(r-c)^2) + exp(-a(r+c)^2).  a = 1/4 keeps h about two units
# wide in r while g stays narrow enough in u that the coefficient sum is
# exhausted well before n = 2000.  Both facts are checked in the tests.
DEFAULT_WIDTH = mp.mpf("0.25")
DEFAULT_N_MAX = 2000
DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data")


def bump_pair(c, a=DEFAULT_WIDTH) -> tuple[Callable, Callable]:
    """The even bump h centred at ±c, with its exact Fourier partner g.

    h(r) = e^{−a(r−c)²} + e^{−a(r+c)²};  under g(u) = (1/2π)∫h e^{−iru}dr
    the two shifted Gaussians combine into a single modulated one,

        g(u) = cos(cu)·e^{−u²/4a} / √(πa),

    which is `zeta.weil.gaussian_pair(a)`'s g at c = 0, doubled, the
    doubling being the second bump.  h accepts complex r, which is the whole
    point: off-line zeros are evaluated off the real axis.
    """
    c = mp.mpf(c)
    a = mp.mpf(a)

    def h(r):
        r = r if isinstance(r, mp.mpc) else mp.mpf(r)
        return mp.e ** (-a * (r - c) ** 2) + mp.e ** (-a * (r + c) ** 2)

    def g(u):
        u = mp.mpf(u)
        return mp.cos(c * u) * mp.e ** (-u * u / (4 * a)) / mp.sqrt(mp.pi * a)

    return h, g


def archimedean_bracket(r, source: str = "zeta"):
    """2·Re(Λ_∞′/Λ_∞)(½+ir), derived from each function's gamma factor."""
    if source == "zeta":
        return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, 1) * r / 2)) - mp.log(mp.pi)
    if source == "dh":
        return mp.re(mp.digamma(mp.mpf(3) / 4 + mp.mpc(0, 1) * r / 2)) + mp.log(
            5 / mp.pi
        )
    raise ValueError("source must be 'zeta' or 'dh'")


def _coefficients(source: str, n_max: int) -> list[float]:
    """b_n with −f′/f = Σ b_n n^{−s}: Λ(n) for ζ, the DH recursion for DH."""
    if source == "zeta":
        from .explicit import mangoldt

        return [0.0] + [0.0] + [mangoldt(n) for n in range(2, n_max + 1)]
    if source == "dh":
        from .epstein import kappa
        from .factorization import dh_family_coefficients, log_derivative_coefficients

        a = dh_family_coefficients(float(kappa(30)), n_max)
        return list(log_derivative_coefficients(a, n_max))
    raise ValueError("source must be 'zeta' or 'dh'")


def arithmetic_side(
    c, source: str = "zeta", a=DEFAULT_WIDTH, n_max: int = DEFAULT_N_MAX
) -> Any:
    """arch + pole − 2Σ b_n n^{−1/2} g(log n).  Uses no zeros whatsoever.

    ζ carries a pole at s = 1 contributing h(i/2) + h(−i/2); DH is entire and
    contributes none.  Sign trap, met the hard way: the prime term already
    carries its own −2, so it is *added* to the archimedean term, not
    subtracted, getting this backwards leaves ζ residues of order 1 that
    look like a real signal.
    """
    h, g = bump_pair(c, a)
    lo = max(mp.mpf(0), mp.mpf(c) - 25)
    arch = mp.quad(
        lambda r: h(r) * archimedean_bracket(r, source), [lo, mp.mpf(c), mp.mpf(c) + 25]
    ) / mp.pi

    b = _coefficients(source, n_max)
    prime = -2 * mp.fsum(
        mp.mpf(b[n]) / mp.sqrt(n) * g(mp.log(n))
        for n in range(2, n_max + 1)
        if b[n] != 0
    )
    pole = (
        h(mp.mpc(0, mp.mpf(1) / 2)) + h(mp.mpc(0, -mp.mpf(1) / 2))
        if source == "zeta"
        else mp.mpf(0)
    )
    return mp.re(arch + pole + prime)


def _online_ordinates(source: str) -> list:
    if source == "zeta":
        from .explicit import first_zeros

        return [mp.mpf(float(g)) for g in first_zeros(200)]
    path = os.path.join(DATA_DIR, "dh_zeros_online_T120.json")
    with open(path) as fh:
        return [mp.mpf(z) for z in json.load(fh)["zeros"]]


def online_zero_side(c, source: str = "zeta", a=DEFAULT_WIDTH) -> Any:
    """Σ over the ON-LINE ordinates of h(γ) + h(−γ)."""
    h, _ = bump_pair(c, a)
    return mp.re(mp.fsum(h(z) + h(-z) for z in _online_ordinates(source)))


def offline_residue(
    c, source: str = "zeta", a=DEFAULT_WIDTH, n_max: int = DEFAULT_N_MAX
) -> dict[str, Any]:
    """The statistic: what the on-line zeros fail to account for."""
    arith = arithmetic_side(c, source, a, n_max)
    zsum = online_zero_side(c, source, a)
    return {
        "c": float(c),
        "source": source,
        "arithmetic": float(arith),
        "online_zeros": float(zsum),
        "residue": float(arith - zsum),
    }


def residue_scan(
    c_values: Sequence[float], source: str = "zeta", a=DEFAULT_WIDTH
) -> dict[str, Any]:
    """Residue across a range of centres, the peak localizes an off-line zero."""
    rows = [offline_residue(c, source, a) for c in c_values]
    res = np.array([r["residue"] for r in rows])
    i = int(np.argmax(np.abs(res)))
    return {
        "source": source,
        "c_values": [float(x) for x in c_values],
        "residues": res.tolist(),
        "max_abs_residue": float(np.abs(res).max()),
        "argmax_c": float(rows[i]["c"]),
    }


def recover_distance_from_line(residue: float, a=DEFAULT_WIDTH) -> float:
    """|β − ½| from the peak height, inverting ≈ 4·exp(a(β−½)²).

    Assumes the peak is a single quadruple {β±iγ, 1−β±iγ} sitting at the
    scan centre, which is the configuration a symmetric functional equation
    forces.  Returns 0.0 for a residue at or below 4 (nothing off the line).
    """
    r = mp.mpf(residue)
    if r <= 4:
        return 0.0
    return float(mp.sqrt(mp.log(r / 4) / mp.mpf(a)))


def online_list_is_complete(
    t0: float, t1: float, dps: int = 15, method: str = "sign_changes"
) -> dict[str, Any]:
    """Cross-check the cached DH on-line ordinates against a second count.

    The residue cannot tell an off-line zero from an on-line zero the
    sign-change hunt missed, so this guard is not optional.

    **What the cheap route does and does not establish (measured 2026-08-11).**
    ``method="sign_changes"`` counts sign changes of Z_dh with
    ``zeta.epstein.zeros_on_line``: the *same technique on the same function*
    that produced the cached list, on a grid that is in fact **1.4×–1.8×
    coarser** (mean_spacing/20 ≈ 0.069–0.091 against the cache's 0.05).  A pair
    closer than either step is missed by both, identically.  So it is a
    grid-refinement check with **no power** against the failure mode the
    docstring used to claim it covered; ``independent`` in the returned dict
    says so, in data.

    ``method="strip"`` is the count that is genuinely independent of the
    technique: ``zeta.epstein.count_zeros_box`` applies the argument principle
    to the rectangle ``Re s ∈ [-0.5, 1.5]``, ``Im s ∈ (t0, t1]``, so it sees
    *every* zero in the strip, on the line or not.  The identity it checks is

        strip count = on-line count + 2·(number of off-line quadruple members)

    so with the off-line zeros known (``expected_offline``, default: the one
    quadruple at γ ≈ 85.699 that ``zeta.epstein`` locates) it decides
    completeness outright.  Measured on the cached list: deficit 0 at T = 40
    and T = 60, deficit exactly 2 at T = 90, the quadruple.  It costs ~25–115 s
    per window against ~1 s, which is why it is not the default.

    ``complete`` is the verdict of whichever route ran; ``independent`` is True
    only for ``"strip"``.
    """
    from .epstein import zeros_on_line

    cached = [z for z in _online_ordinates("dh") if t0 < float(z) <= t1]
    out: dict[str, Any] = {
        "window": (float(t0), float(t1)),
        "cached_count": len(cached),
        "method": method,
    }
    if method == "sign_changes":
        reference = int(zeros_on_line(t0, t1, dps=dps))
        out["reference_count"] = reference
        out["independent"] = False
        out["shares_blind_spot_with_the_cache"] = (
            "both are Z_dh sign-change scans; a pair closer than either grid "
            "step is invisible to both"
        )
        out["complete"] = bool(len(cached) == reference)
        return out
    if method == "strip":
        from .epstein import OFFLINE_ZERO_IM, count_zeros_box

        strip = int(count_zeros_box(complex(-0.5, t0), complex(1.5, t1), dps=dps))
        # each off-line quadruple contributes two members per (positive) window:
        # beta + i*gamma and 1 - beta + i*gamma
        expected_offline = 2 * sum(
            1 for g in (float(OFFLINE_ZERO_IM),) if t0 < g <= t1
        )
        out["strip_count"] = strip
        out["expected_offline_members"] = expected_offline
        out["deficit"] = strip - len(cached) - expected_offline
        out["independent"] = True
        out["complete"] = bool(out["deficit"] == 0)
        return out
    raise ValueError(f"unknown method {method!r} (use 'sign_changes' or 'strip')")


def detector_battery(a=DEFAULT_WIDTH) -> dict[str, Any]:
    """ζ silent, Davenport–Heilbronn spiking at its off-line zero.

    The one probe in this family that separates them *by zero position*
    rather than by arithmetic, see the module docstring for exactly what
    that does and does not establish.
    """
    from .epstein import OFFLINE_ZERO_IM, OFFLINE_ZERO_RE

    quiet = [20.0, 45.0, 60.0, 100.0]
    zeta_res = [abs(offline_residue(c, "zeta", a)["residue"]) for c in quiet]
    dh_quiet = [abs(offline_residue(c, "dh", a)["residue"]) for c in (40.0, 60.0, 100.0)]

    gamma0 = float(OFFLINE_ZERO_IM)
    beta0 = float(OFFLINE_ZERO_RE)
    peak = offline_residue(gamma0, "dh", a)

    h, _ = bump_pair(gamma0, a)
    quad = [
        mp.mpc(beta0, gamma0),
        mp.mpc(1 - beta0, gamma0),
        mp.mpc(beta0, -gamma0),
        mp.mpc(1 - beta0, -gamma0),
    ]
    predicted = float(
        mp.re(mp.fsum(h((rho - mp.mpf(1) / 2) / mp.mpc(0, 1)) for rho in quad))
    )
    recovered = recover_distance_from_line(peak["residue"], a)

    return {
        "zeta_max_abs_residue": float(max(zeta_res)),
        "dh_quiet_max_abs_residue": float(max(dh_quiet)),
        "dh_peak_c": gamma0,
        "dh_peak_residue": peak["residue"],
        "predicted_quadruple": predicted,
        "peak_match_error": abs(peak["residue"] - predicted),
        "recovered_distance": recovered,
        "true_distance": beta0 - 0.5,
        "recovery_error": abs(recovered - (beta0 - 0.5)),
        "separates": bool(max(zeta_res) < 1e-9 < peak["residue"]),
        "verdict": (
            "The Weil residue separates zeta from Davenport-Heilbronn by zero "
            "POSITION, not by arithmetic: zeta is silent to float noise while "
            "DH spikes at its off-line ordinate, matching the known quadruple "
            "and recovering |beta-1/2| from the peak height. Detects off-line "
            "zeros without solving for them. NOT a proof of RH over any range "
            "and NOT certified; and it cannot distinguish an off-line zero "
            "from a missing on-line one, so it requires online_list_is_complete."
        ),
    }
