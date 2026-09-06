"""The prime signal as additive synthesis, and the power its partials carry.

Put the explicit formula in log-time.  With u = log x, define

    S(u) = (ψ(e^u) − e^u) / e^{u/2} .

Riemann's formula says S is exactly what a synthesizer patch looks like:

    S(u) = − Σ_ρ e^{(ρ−½)u}/ρ + (small archimedean terms) ,

one partial per zero.  On RH every ρ − ½ is purely imaginary, so every
partial is a pure tone cos(γu + φ) with a *constant* envelope and amplitude
1/|ρ|.  A zero off the line at Re ρ = β > ½ is a partial whose envelope
swells like e^{(β−½)u}, a note that grows without bound.

That converts RH into a statement an audio engineer would recognise:

    **RH  ⟺  the prime patch has finite average power.**

Precisely, S has a Besicovitch B² mean square, and under RH its value is a
closed form:

    P = Σ_ρ 1/(ρ(1−ρ)) = 2 + γ_Euler − log(4π) = 0.0461914179…

so the primes play at a constant RMS of √P = 0.2149… .  This module measures
P three independent ways (`power_report`): a Λ-sieve on the prime side, a
sum over cached zero ordinates plus a density tail on the zero side, and the
closed form.  They agree, which is a check on the implementations and on
nothing else.

**The wall, stated plainly.**  This is a genuine equivalence, not a route to
a proof.  Proving finite mean power from the prime side means expanding S²
into Σ Λ(n)Λ(m) correlations, i.e. controlling the variance of primes in
short intervals, and by Goldston–Montgomery that control is *equivalent* to
the pair correlation of the zeros.  The audio framing reaches Montgomery's
program in three steps and then stops exactly where everything else does.
No agreement computed here is evidence for RH (Littlewood; `docs/08`); a
disagreement would indicate a bug.

Everything here is *accurate*, not *certified* (see `zeta/rigor.py`).
"""

from __future__ import annotations

import json
import os
from typing import Any

import numpy as np

__all__ = [
    "MEAN_POWER_CLOSED_FORM",
    "closed_form_power",
    "prime_signal",
    "mean_power_prime_side",
    "mean_power_zero_side",
    "power_report",
]

# 2 + γ_Euler − log(4π).  Value pinned in tests; recomputed, never hardcoded,
# by closed_form_power().
MEAN_POWER_CLOSED_FORM = 0.04619141793224202


def closed_form_power() -> float:
    """Σ_ρ 1/(ρ(1−ρ)) = 2 + γ_Euler − log 4π.

    The classical evaluation of the sum over *all* non-trivial zeros, from
    the Hadamard product for ξ; it does not assume RH (the sum pairs ρ with
    1−ρ regardless of where they sit).  What RH supplies is that this same
    number is the mean power of S, because only then is every partial's
    envelope constant.
    """
    return float(2.0 + np.euler_gamma - np.log(4.0 * np.pi))


def _mangoldt_array(N: int) -> np.ndarray:
    """Λ(n) for n ≤ N as a float array (index 0 unused)."""
    is_comp = np.zeros(N + 1, dtype=bool)
    for p in range(2, int(N**0.5) + 1):
        if not is_comp[p]:
            is_comp[p * p :: p] = True
    Lam = np.zeros(N + 1)
    for p in np.flatnonzero(~is_comp)[2:]:
        lp = np.log(float(p))
        q = int(p)
        while q <= N:
            Lam[q] = lp
            q *= int(p)
    return Lam


def prime_signal(N: int = 10**6, n_samples: int = 200_000, u_min: float = 2.0):
    """Sample S(u) = (ψ(e^u) − e^u)/e^{u/2} on a uniform log-time grid.

    Returns (u, S).  N caps the sieve, so u runs up to log N.
    """
    psi = np.cumsum(_mangoldt_array(N))
    u = np.linspace(u_min, np.log(N), n_samples)
    x = np.exp(u)
    idx = np.floor(x).astype(np.int64)
    return u, (psi[idx] - x) / np.sqrt(x)


def mean_power_prime_side(
    N: int = 10**6, n_samples: int = 200_000, u_start: float = 6.0
) -> dict[str, Any]:
    """Average of S(u)² over log-time, from the prime side only.

    The window starts at ``u_start`` rather than at the bottom: near x small
    the archimedean and trivial-zero terms dropped from the pure-tone picture
    are not yet negligible, and they bias the mean upward.  The reported
    convergence table makes that visible instead of hiding it.
    """
    u, S = prime_signal(N, n_samples, u_min=2.0)
    U = u[-1]

    def window(u0: float) -> float:
        m = u >= u0
        return float(np.trapezoid(S[m] ** 2, u[m]) / (u[m][-1] - u[m][0]))

    starts = [s for s in (2.0, 4.0, 6.0, 8.0) if s < U - 1.0]
    return {
        "N": int(N),
        "u_max": float(U),
        "convergence": {float(s): window(s) for s in starts},
        "mean_power": window(u_start),
        "rms": float(np.sqrt(window(u_start))),
        "u_start": float(u_start),
    }


def mean_power_zero_side(n_zeros: int = 1000) -> dict[str, Any]:
    """2·Σ_{γ>0} 1/(¼+γ²) over cached ordinates, plus a density tail estimate.

    The tail uses the Riemann–von Mangoldt density dN ≈ (1/2π)log(γ/2π)dγ:
    ∫_T^∞ 2/γ² dN = (log(T/2π) + 1)/(πT).  It is an estimate, not a bound,
    labelled as such in the returned dict.
    """
    from .explicit import first_zeros

    g = np.asarray(first_zeros(n_zeros), dtype=float)
    partial = float(np.sum(2.0 / (0.25 + g**2)))
    T = float(g[-1])
    tail = float((np.log(T / (2 * np.pi)) + 1.0) / (np.pi * T))
    return {
        "n_zeros": int(n_zeros),
        "gamma_max": T,
        "partial_sum": partial,
        "tail_estimate": tail,
        "tail_is_estimate_not_bound": True,
        "total": partial + tail,
    }


def power_report(
    N: int = 10**6, n_zeros: int = 1000, n_samples: int = 200_000
) -> dict[str, Any]:
    """All three routes to P, with their pairwise gaps.

    ``prime_gap`` is expected to be the largest by far: the prime-side
    average converges slowly (the window is only a few e-foldings wide) and
    approaches P from above.  See the module docstring for why agreement is
    not evidence of anything.
    """
    closed = closed_form_power()
    zero = mean_power_zero_side(n_zeros)
    prime = mean_power_prime_side(N, n_samples)
    return {
        "closed_form": closed,
        "zero_side": zero,
        "prime_side": prime,
        "rms_amplitude": float(np.sqrt(closed)),
        "zero_gap": abs(zero["total"] - closed),
        "prime_gap": abs(prime["mean_power"] - closed),
        "note": (
            "Agreement checks the implementations, not RH. Proving finiteness "
            "from the prime side is equivalent to pair-correlation control "
            "(Goldston-Montgomery), which is where every other route stops too."
        ),
    }
