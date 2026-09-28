"""Integer-relation probes on the zero ordinates, the ℚ-independence face.

It is conjectured (and used, e.g. throughout Rubinstein–Sarnak prime-race
theory under the name LI, "Linear Independence") that the positive ordinates
γ₁ < γ₂ < … of the non-trivial zeros are linearly independent over ℚ.  Not
even a single instance is proven: no one can rule out γ₂/γ₁ ∈ ℚ.  A relation,
if one existed, would be a spectacular structural fact, and several known
theorems (on Mertens-sum oscillation, on prime races) would lose their
standard proofs.

This module runs the PSLQ integer-relation algorithm on high-precision
batches of ordinates and reports **bounded exclusions**:

    "PSLQ at working precision d found no integer relation Σ aᵢγᵢ = 0 with
     max|aᵢ| ≤ B among the first n ordinates."

Honest-scope notes, per house rules:

* A terminated PSLQ run is a *bounded search*, not a proof of independence.
  The conjecture is not made more likely by any finite exclusion
  (`docs/08-why-it-is-hard.md`; Littlewood's warning applies to negatives
  too).
* A run that *found* a relation is, per the standing rule, a bug until the
  relation survives an independent recomputation of the ordinates at at
  least double the precision (``confirm_relation``).  PSLQ near its
  precision floor emits junk relations with huge coefficients; the
  ``floor_ratio`` field measures the margin.
* The search itself is validated by planting a known relation and requiring
  PSLQ to recover it exactly (``pslq_sanity``), following the repo pattern
  of calibrating an instrument before pointing it at the unknown.

Precision economics: detecting (or excluding) a relation with coefficients
up to B among n values needs roughly n·log₁₀B digits, plus guard.  The
``dps`` defaults are set from that count and asserted, not assumed.
"""

from __future__ import annotations

from typing import Any, Sequence

from mpmath import mp, mpf, pslq

from .zeros import first_n_zeros

__all__ = [
    "pslq_sanity",
    "zero_relation_search",
    "constants_relation_search",
    "confirm_relation",
]


def _needed_dps(n_values: int, max_coeff: int, guard: int = 40) -> int:
    """Digits needed for PSLQ to be meaningful: n·log10(B) plus guard.

    The guard is not cosmetic.  Over the coefficient box max|aᵢ| ≤ B a
    pigeonhole argument guarantees *accidental* combinations with
    |Σ aᵢγᵢ| as small as roughly scale·B^{−(n−1)}; if PSLQ's internal
    tolerance (≈ 10^−dps) is looser than that floor, it terminates on such
    an accident and reports a junk "relation", observed directly in this
    repo's first n=20 run: coefficients ~7·10⁵, residual 4.4·10⁻¹⁰⁴,
    unchanged on recomputation at dps 300, i.e. the pigeonhole floor for
    n=20, B=10⁶ on values of scale ~10².  Forty digits of guard puts the
    tolerance well below that floor, so an accident can no longer satisfy
    PSLQ and only an exact relation terminates the search early.
    """
    import math

    return int(math.ceil(n_values * math.log10(max_coeff))) + guard


def pslq_sanity(dps: int = 60) -> dict[str, Any]:
    """Validate the instrument: PSLQ must recover a planted relation exactly.

    Plants γ₃ = γ₁ + γ₂ − (γ₁ + γ₂ − γ₃) style relations directly:
    the vector (γ₁, γ₂, γ₁+γ₂, 2γ₁−3γ₂) admits the independent relations
    (1, 1, −1, 0) and (2, −3, 0, −1); PSLQ must return one of them (any
    integer combination of the two is also valid, the check verifies the
    returned vector annihilates the input to working precision and is not
    the zero vector).
    """
    with mp.workdps(dps):
        g = first_n_zeros(2, dps=dps)
        vec = [g[0], g[1], g[0] + g[1], 2 * g[0] - 3 * g[1]]
        rel = pslq(vec, maxcoeff=10**4, maxsteps=10**5)
        found = rel is not None
        if found:
            residual = abs(sum(a * v for a, v in zip(rel, vec)))
            nontrivial = any(a != 0 for a in rel)
        else:  # pragma: no cover - would indicate a broken mpmath
            residual = mp.inf
            nontrivial = False
        return {
            "found": found,
            "relation": list(rel) if found else None,
            "residual": float(residual),
            "nontrivial": bool(nontrivial),
            "passed": bool(found and nontrivial and residual < mpf(10) ** (-dps + 15)),
            "dps": dps,
        }


def zero_relation_search(
    n_zeros: int = 12,
    max_coeff: int = 10**6,
    dps: int | None = None,
    max_steps: int = 2 * 10**5,
) -> dict[str, Any]:
    """Search for an integer relation among the first ``n_zeros`` ordinates.

    Returns a dict with ``relation`` (None expected), the exclusion
    statement parameters, and ``floor_ratio`` = dps_used / dps_needed, a
    run with ratio < 1 is underpowered and says nothing; the function
    raises rather than emit such a result.
    """
    needed = _needed_dps(n_zeros, max_coeff)
    if dps is None:
        dps = needed
    if dps < needed:
        raise ValueError(
            f"dps={dps} is below the {needed} digits needed for "
            f"n={n_zeros}, max_coeff={max_coeff}; an underpowered PSLQ run "
            "excludes nothing"
        )
    with mp.workdps(dps):
        gammas = first_n_zeros(n_zeros, dps=dps)
        rel = pslq(gammas, maxcoeff=max_coeff, maxsteps=max_steps)
        if rel is None:
            status = "excluded"
            statement = (
                f"PSLQ at {dps} digits found no relation sum(a_i * gamma_i) = 0 "
                f"with max|a_i| <= {max_coeff} among the first {n_zeros} "
                "zero ordinates (bounded search, not a proof)"
            )
            residual = None
        else:
            residual = abs(sum(a * g for a, g in zip(rel, gammas)))
            # An exact relation leaves a residual at the rounding floor of the
            # ordinates themselves; anything materially above it is the
            # pigeonhole accident documented in _needed_dps.
            if residual < mpf(10) ** (-dps + 15):
                status = "candidate"
                statement = (
                    "RELATION CANDIDATE, treat as a bug until confirmed "
                    "at double precision (see confirm_relation)"
                )
            else:
                status = "inconclusive_floor_noise"
                statement = (
                    f"PSLQ terminated on a pigeonhole accident (residual "
                    f"{mp.nstr(residual, 3)} >> 10^{-dps + 15}); the search "
                    f"excludes nothing, rerun with dps >= {needed + 60}"
                )
        result: dict[str, Any] = {
            "n_zeros": n_zeros,
            "max_coeff": max_coeff,
            "dps": dps,
            "dps_needed": needed,
            "floor_ratio": round(dps / needed, 3),
            "max_steps": max_steps,
            "relation": list(rel) if rel is not None else None,
            "status": status,
            "excluded": status == "excluded",
            "statement": statement,
        }
        if residual is not None:
            result["residual"] = float(residual)
        return result


def constants_relation_search(
    n_zeros: int = 6,
    max_coeff: int = 10**4,
    dps: int | None = None,
    max_steps: int = 2 * 10**5,
) -> dict[str, Any]:
    """Search for relations linking ordinates to the classical constants.

    Vector: (γ₁, …, γ_n, π, log 2, log 3, γ_Euler, 1).  A hit would tie a
    zero ordinate to the classical constant ring, nothing of the sort is
    known or expected.  Same exclusion semantics as
    :func:`zero_relation_search`.
    """
    n_values = n_zeros + 5
    needed = _needed_dps(n_values, max_coeff)
    if dps is None:
        dps = needed
    if dps < needed:
        raise ValueError(f"dps={dps} below required {needed}")
    with mp.workdps(dps):
        gammas = first_n_zeros(n_zeros, dps=dps)
        consts = [+mp.pi, mp.log(2), mp.log(3), +mp.euler, mp.mpf(1)]
        vec = list(gammas) + consts
        rel = pslq(vec, maxcoeff=max_coeff, maxsteps=max_steps)
        if rel is None:
            status = "excluded"
        elif abs(sum(a * v for a, v in zip(rel, vec))) < mpf(10) ** (-dps + 15):
            status = "candidate"
        else:
            status = "inconclusive_floor_noise"
        return {
            "n_zeros": n_zeros,
            "constants": ["pi", "log2", "log3", "euler", "1"],
            "max_coeff": max_coeff,
            "dps": dps,
            "dps_needed": needed,
            "relation": list(rel) if rel is not None else None,
            "status": status,
            "excluded": status == "excluded",
        }


def confirm_relation(
    relation: Sequence[int], n_zeros: int, dps: int
) -> dict[str, Any]:
    """Recompute the ordinates from scratch at ``dps`` and test a candidate.

    The bar: |Σ aᵢγᵢ| must stay below 10^(−dps+15) at the *higher* precision.
    A candidate that fails here was PSLQ noise, which is the expected
    outcome for any candidate this module ever produces.
    """
    if len(relation) != n_zeros:
        raise ValueError("relation length must equal n_zeros")
    with mp.workdps(dps):
        gammas = [mp.im(mp.zetazero(k)) for k in range(1, n_zeros + 1)]
        residual = abs(sum(a * g for a, g in zip(relation, gammas)))
        tol = mpf(10) ** (-dps + 15)
        return {
            "residual": float(residual),
            "tolerance": float(tol),
            "confirmed": bool(residual < tol),
            "dps": dps,
        }
