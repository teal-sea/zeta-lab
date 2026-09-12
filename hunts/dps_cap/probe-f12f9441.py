"""What the ``min(dps, 20)`` cap in ``zeta/epstein.py`` costs.

``epstein_interface`` clamps precision on two of its entries: ``min(dps, 20)``
on ``count_zeros_box`` and ``min(dps, 15)`` on ``zeros_on_line``.  This probe
measures one number that clamp has to survive, at a point high enough up the
strip that ``Gamma(s)`` has decayed far below the absolute error a 20-digit
evaluation can carry:

    abs(epstein_completed(0.8 + 85.7i, (2, 1, 3), dps=D))

The headline is that number at ``D = 20`` and ``D = 60``.  The rest of the
sweep is there so the two headline rows can be read against a scale: ``D = 80``
is the convergence control for ``D = 60``, and the intermediate rows locate the
precision below which the routine returns no correct digit at all.

Run: ``.venv/bin/python hunts/dps_cap/probe.py`` (~18 s measured, no network).
Writes ``results.json`` beside this file.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from mpmath import mp

from zeta.epstein import epstein_completed

FORM = (2, 1, 3)
POINT = ("0.8", "85.7")

#: The two the mission asks for.
HEADLINE = (20, 60)
#: The scale they are read against; the last entry is the convergence control.
SWEEP = (20, 30, 40, 50, 60, 80)


def measure(dps: int) -> dict:
    """``abs(epstein_completed(0.8 + 85.7i, FORM, dps=dps))``, with timing.

    The point is parsed at the precision it will be evaluated at, so every row
    is the same complex number to every digit that row carries.  ``abs`` is
    taken inside a ``workdps`` wider than the value, because taking it at the
    ambient 15 digits would silently truncate the result to 15 and make a
    convergence comparison read far better than it is.
    """

    with mp.workdps(dps):
        s = mp.mpc(POINT[0], POINT[1])
        s_repr = mp.nstr(s, min(dps, 25))
    start = time.perf_counter()
    value = epstein_completed(s, FORM, dps=dps)
    elapsed = time.perf_counter() - start
    with mp.workdps(dps + 5):
        magnitude = abs(value)
        return {
            "dps": dps,
            "s": s_repr,
            "abs": mp.nstr(magnitude, dps),
            "abs_float": float(magnitude),
            "log10_abs": float(mp.log10(magnitude)) if magnitude != 0 else None,
            "exactly_zero": bool(value == 0),
            "re": mp.nstr(mp.re(value), min(dps, 25)),
            "im": mp.nstr(mp.im(value), min(dps, 25)),
            "seconds": round(elapsed, 3),
        }


def archimedean_envelope() -> dict:
    """``abs((sqrt(d)/pi)^s Gamma(s))`` at the same point, ``d = ac - b^2/4``.

    The size oracle, and the only number here that does not come from the
    lattice sum under test: the docstring of ``epstein_completed`` defines
    ``Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s)``, so dividing a claimed
    magnitude by this envelope reports what ``abs(zeta_Q(s))`` that claim
    implies.  ``zeta_Q`` is a Dirichlet series continued into the strip and
    grows polynomially in ``t``, so an implied value of order 1 is ordinary and
    one of order ``1e25`` is not a value the function takes.
    """

    a, b, c = FORM
    with mp.workdps(50):
        s = mp.mpc(POINT[0], POINT[1])
        d = mp.mpf(a) * c - mp.mpf(b) ** 2 / 4
        env = abs((mp.sqrt(d) / mp.pi) ** s) * abs(mp.gamma(s))
        return {"d": mp.nstr(d, 10), "envelope": mp.nstr(env, 12), "envelope_float": float(env)}


def parse_sensitivity() -> dict:
    """The same point, written three ways, evaluated at D = 20 and D = 60.

    ``mp.mpc('0.8', '85.7')`` is a different bit pattern at every parse
    precision, and all of them denote the same complex number to well past any
    digit that matters.  A converged evaluation must therefore return the same
    magnitude for all of them.  A floor-level artefact need not, and this is
    the sharpest available test of which one the capped path is returning.
    """

    out = {}
    for label, parse_dps in (("parsed_dps_15", 15), ("parsed_dps_20", 20), ("parsed_dps_60", 60)):
        with mp.workdps(parse_dps):
            s = mp.mpc(POINT[0], POINT[1])
        row = {}
        for eval_dps in HEADLINE:
            value = epstein_completed(s, FORM, dps=eval_dps)
            with mp.workdps(eval_dps + 5):
                row[str(eval_dps)] = float(abs(value))
        out[label] = row
    # Python floats, the way a caller who did not think about it would write it.
    s = mp.mpc(0.8, 85.7)
    row = {}
    for eval_dps in HEADLINE:
        value = epstein_completed(s, FORM, dps=eval_dps)
        with mp.workdps(eval_dps + 5):
            row[str(eval_dps)] = float(abs(value))
    out["python_floats"] = row

    spreads = {}
    for eval_dps in HEADLINE:
        magnitudes = [row[str(eval_dps)] for row in out.values()]
        spreads["spread_at_dps_{0}".format(eval_dps)] = max(magnitudes) / min(magnitudes)
    out.update(spreads)
    return out


def main() -> dict:
    rows = {d: measure(d) for d in SWEEP}
    for row in rows.values():
        flag = "  <- exactly zero" if row["exactly_zero"] else ""
        print("dps={0:3d}  abs = {1:<26} ({2} s){3}".format(
            row["dps"], mp.nstr(mp.mpf(row["abs_float"]), 12), row["seconds"], flag
        ))

    low, high = (rows[d] for d in HEADLINE)
    # How far the capped answer is from the converged one, as a plain factor.
    ratio = low["abs_float"] / high["abs_float"]
    # How many digits of the D=60 answer survive the jump to D=80.
    with mp.workdps(90):
        ref = mp.mpf(rows[80]["abs"])
        rel = abs(mp.mpf(high["abs"]) - ref) / ref
        correct_digits = float(-mp.log10(rel))

    env = archimedean_envelope()
    parse = parse_sensitivity()
    implied = {
        str(row["dps"]): row["abs_float"] / env["envelope_float"]
        for row in rows.values()
        if not row["exactly_zero"]
    }

    out = {
        "form": list(FORM),
        "point": "0.8 + 85.7i",
        "headline": {str(d): rows[d] for d in HEADLINE},
        "sweep": [rows[d] for d in SWEEP],
        "ratio_dps20_over_dps60": ratio,
        "dps60_correct_digits_vs_dps80": correct_digits,
        "archimedean_envelope": env,
        "implied_abs_zeta_Q": implied,
        "parse_sensitivity": parse,
    }
    Path(__file__).with_name("results.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8"
    )
    print("ratio (dps=20)/(dps=60) = {0:.6e}".format(ratio))
    print("dps=60 agrees with dps=80 to {0:.1f} significant digits".format(correct_digits))
    print("archimedean envelope = {0}".format(env["envelope"]))
    for dps_key, value in sorted(implied.items(), key=lambda kv: int(kv[0])):
        print("  dps={0:>2}  implies abs(zeta_Q) = {1:.6e}".format(dps_key, value))
    print("same point written four ways:")
    for label in ("parsed_dps_15", "parsed_dps_20", "parsed_dps_60", "python_floats"):
        row = parse[label]
        print("  {0:<14}  dps=20 -> {1:.6e}   dps=60 -> {2:.6e}".format(
            label, row["20"], row["60"]
        ))
    print("  spread at dps=20: {0:.1f}x    spread at dps=60: {1:.3g}x".format(
        parse["spread_at_dps_20"], parse["spread_at_dps_60"]
    ))
    return out


if __name__ == "__main__":
    main()
