"""Where up the strip does the capped precision stop returning digits?

`probe.py` answers the mission's question at one point. This script answers the
one follow-up needed to judge a claim already on the record: the thread from run
`d9ae5359` (`GATE5-P6-B`) states that the capped rival interface "cannot count
Epstein zeros above roughly t = 25". That number decides which earlier verdicts
are suspect, so it is worth a measurement rather than an estimate.

Method: walk `s = 0.8 + it` up the strip, evaluate at the cap (dps = 20) and at
dps = 60, and report the relative disagreement. Where it is ~1e-16 the capped
path is fine; where it reaches 1 the capped path has stopped tracking the
function.

Run: ``.venv/bin/python hunts/dps_cap/crossover.py`` (~1 min, no network).
Writes ``crossover.json`` beside this file.
"""

from __future__ import annotations

import json
from pathlib import Path

from mpmath import mp

from zeta.epstein import epstein_completed

FORM = (2, 1, 3)
SIGMA = "0.8"
HEIGHTS = ("5", "10", "20", "25", "30", "35", "40", "45", "50", "60", "85.7")
CAPPED, REFERENCE = 20, 60


def row(t_text: str) -> dict:
    # Parse at the reference precision so both evaluations get the same point;
    # probe.py shows the capped answer otherwise depends on the parse.
    with mp.workdps(REFERENCE):
        s = mp.mpc(SIGMA, t_text)
    capped = epstein_completed(s, FORM, dps=CAPPED)
    reference = epstein_completed(s, FORM, dps=REFERENCE)
    with mp.workdps(REFERENCE + 5):
        ref_abs = abs(reference)
        # Relative error of the whole complex value, so a wrong phase counts:
        # count_zeros_box consumes the argument, not the magnitude.
        rel = abs(capped - reference) / ref_abs if ref_abs != 0 else None
        return {
            "t": t_text,
            "abs_reference": float(ref_abs),
            "abs_capped": float(abs(capped)),
            "relative_error": float(rel) if rel is not None else None,
        }


def main() -> dict:
    rows = [row(t) for t in HEIGHTS]
    usable = [r for r in rows if r["relative_error"] is not None and r["relative_error"] < 1e-6]
    lost = [r for r in rows if r["relative_error"] is not None and r["relative_error"] > 0.5]
    out = {
        "sigma": SIGMA,
        "form": list(FORM),
        "capped_dps": CAPPED,
        "reference_dps": REFERENCE,
        "rows": rows,
        "highest_t_still_accurate_to_1e6": usable[-1]["t"] if usable else None,
        "lowest_t_fully_lost": lost[0]["t"] if lost else None,
    }
    Path(__file__).with_name("crossover.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8"
    )
    print("  t      abs(Lambda_Q)      relative error of the dps=20 value")
    for r in rows:
        print("  {0:<6} {1:.6e}      {2:.3e}".format(
            r["t"], r["abs_reference"], r["relative_error"]
        ))
    print("highest t still accurate to 1e-6 : {0}".format(out["highest_t_still_accurate_to_1e6"]))
    print("lowest t fully lost (rel > 0.5)  : {0}".format(out["lowest_t_fully_lost"]))
    return out


if __name__ == "__main__":
    main()
