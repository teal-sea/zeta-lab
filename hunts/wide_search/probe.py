"""Shared instruments for the `wide_search` hunt.

Nothing in here decides anything. These are the four standing controls
(`hunts/README.md`) in reusable form, so that a candidate that survives triage
is measured the same way every time and the measurement is recorded rather
than remembered.

The one non-obvious instrument is :func:`precision_response`. The laboratory's
standing rule — earned three times in a single day, per `ROADMAP.md` — is that
*an artifact does not respond to added precision; a real quantity does*. Its
converse signature matters just as much: a discrepancy that refuses to move
under **every** convergence knob points at a mis-bound constant rather than at
a real effect. So the helper reports the whole ladder, not a verdict.

Run from the repo root with `.venv/bin/python`.
"""

from __future__ import annotations

import math
from typing import Any, Callable, Sequence

from mpmath import mp


# --------------------------------------------------------------------------
# control 4 — precision response
# --------------------------------------------------------------------------


def precision_response(
    compute: Callable[[int], Any],
    dps_ladder: Sequence[int] = (15, 25, 40, 60),
) -> dict[str, Any]:
    """Run ``compute(dps)`` up a precision ladder and report the movement.

    ``compute`` receives a working precision in decimal digits and must return
    a real number (anything ``mpmath.mpf`` accepts). It is called inside an
    ``mp.workdps`` context, so it may use global mpmath precision freely; the
    caller's precision is restored on exit.

    The returned dict carries the ladder, the successive absolute and relative
    movements, and ``settled_digits`` — the number of leading decimal digits
    that stopped moving between the last two rungs. No verdict is returned:
    what counts as "settled" depends on what the quantity is being used for,
    and a helper that decided that for the caller would be deciding the
    result.
    """
    values: list[Any] = []
    used: list[int] = []
    for dps in dps_ladder:
        with mp.workdps(dps):
            values.append(mp.mpf(compute(dps)))
        used.append(dps)

    moves: list[float] = []
    rel_moves: list[float] = []
    for a, b in zip(values, values[1:]):
        with mp.workdps(max(used) + 10):
            d = abs(b - a)
            moves.append(float(d))
            rel_moves.append(float(d / abs(b)) if b != 0 else float("inf"))

    settled = 0
    if rel_moves:
        last = rel_moves[-1]
        if last == 0:
            settled = used[-1]
        elif math.isfinite(last) and last > 0:
            settled = max(0, int(-math.log10(last)))

    return {
        "dps_ladder": list(used),
        "values": [mp.nstr(v, 25) for v in values],
        "abs_moves": moves,
        "rel_moves": rel_moves,
        "settled_digits": settled,
        "note": (
            "An artifact does not respond to added precision; a real quantity "
            "does. A value that refuses to move under every knob may instead "
            "be a mis-bound constant."
        ),
    }


# --------------------------------------------------------------------------
# control 1 — rival
# --------------------------------------------------------------------------


def rival_check(claim_fn: Callable[[dict], Any], dps: int = 30) -> dict[str, Any]:
    """Run a structural claim through `zeta.epstein.battery`.

    ``claim_fn`` receives a zeta-like interface dict and returns truthy/falsy.
    A claim that also fires on Davenport-Heilbronn or on either discriminant
    -23 Epstein form distinguishes nothing, however interesting it looks on
    zeta alone.

    The trap this cannot detect is recorded in `hunts/README.md`: if the claim
    was *designed* against this rival set, a pass measures the laboratory's own
    admission criterion rather than the subject.
    """
    from zeta.epstein import battery

    out = dict(battery(claim_fn, dps=dps))
    out["trap"] = (
        "if the test set is the rival set, this measured the admission "
        "criterion, not the subject"
    )
    return out


# --------------------------------------------------------------------------
# control 2/3 — surrogate and lesion
# --------------------------------------------------------------------------


def null_band(
    statistic: Callable[[Sequence[float]], float],
    draw: Callable[[int], Sequence[float]],
    n_draws: int = 300,
    seed: int = 0,
) -> dict[str, Any]:
    """Where does the observed statistic sit inside a matched null?

    ``draw(i)`` returns one surrogate input; ``statistic`` reduces an input to
    a number. Returns the null's quantiles so a claim of "unusual" acquires a
    denominator. `ROADMAP.md` records the calibration that makes this
    non-optional: against a null of random non-factoring sequences,
    Davenport-Heilbronn sits at the **27th percentile** — typical, not exotic.
    """
    import numpy as np

    rng = np.random.default_rng(seed)
    _ = rng  # draw() owns its own randomness; seed is recorded for the log
    vals = np.array([float(statistic(draw(i))) for i in range(n_draws)])
    qs = [1, 5, 25, 50, 75, 95, 99]
    return {
        "n_draws": n_draws,
        "seed": seed,
        "mean": float(vals.mean()),
        "std": float(vals.std(ddof=1)) if n_draws > 1 else float("nan"),
        "quantiles": {q: float(np.percentile(vals, q)) for q in qs},
        "min": float(vals.min()),
        "max": float(vals.max()),
    }


def percentile_of(value: float, null: dict[str, Any]) -> float:
    """Rough percentile of ``value`` inside a :func:`null_band` summary."""
    qs = sorted(null["quantiles"].items())
    if value <= qs[0][1]:
        return float(qs[0][0])
    for (q0, v0), (q1, v1) in zip(qs, qs[1:]):
        if v0 <= value <= v1:
            if v1 == v0:
                return float(q1)
            return float(q0 + (q1 - q0) * (value - v0) / (v1 - v0))
    return float(qs[-1][0])


__all__ = [
    "precision_response",
    "rival_check",
    "null_band",
    "percentile_of",
]
