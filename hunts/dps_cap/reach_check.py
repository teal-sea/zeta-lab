"""Does the cap cost a wrong answer, or a refusal?  UNRESOLVED — see below.

``count_zeros_box`` requires the accumulated winding to land within 1e-6 of an
integer and raises ``ArithmeticError`` otherwise, so a noise-valued contour
should be refused rather than miscounted.  This runs the capped interface path
over a box at the height measured in ``measure.py``, and optionally the same
box at the precision the caller asked for.

**Outcome of the runs attempted: neither returned.** The uncapped comparison
was stopped after 30 minutes and the capped path after 25.  That is a timing
observation and nothing more: this file answers neither question, and no
conclusion about the winding guard should be drawn from it.  A plausible cause
is ``_edge_variation`` subdividing without converging when the contour samples
carry no correct digits, but that is a hypothesis this run did not test.  It
is left here as a starting point, not as evidence.
"""

import json

from mpmath import mp

from zeta.epstein import count_zeros_box, epstein_completed, epstein_interface

FORM = (2, 1, 3)
BOX = (-1, 84, 2, 88)


def attempt(dps: int, capped: bool) -> dict:
    """Count the box either through the interface (capped) or uncapped."""
    with mp.workdps(dps + 10):
        s0, s1 = mp.mpc(BOX[0], BOX[1]), mp.mpc(BOX[2], BOX[3])
    try:
        if capped:
            n = epstein_interface(FORM, dps)["count_zeros_box"](s0, s1)
        else:
            n = count_zeros_box(
                s0, s1, dps=dps, fn=lambda z: epstein_completed(z, FORM, dps=dps)
            )
        return {"dps": dps, "capped": capped, "result": n, "error": None}
    except Exception as exc:  # the guard firing is the interesting outcome
        return {
            "dps": dps,
            "capped": capped,
            "result": None,
            "error": f"{type(exc).__name__}: {exc}",
        }


if __name__ == "__main__":
    # Only the capped path is run by default.  The uncapped comparison is the
    # same contour with every sample at dps=60 and it did not finish in 30
    # minutes, so it is opt-in rather than pretended to be cheap.
    import sys

    attempts = [attempt(60, capped=True)]
    if "--uncapped" in sys.argv:
        attempts.append(attempt(60, capped=False))
    out = {
        "box": {"re": [BOX[0], BOX[2]], "im": [BOX[1], BOX[3]]},
        "form": list(FORM),
        "attempts": attempts,
        "uncapped_run": "--uncapped" in sys.argv,
    }
    print(json.dumps(out, indent=2))
    with open("hunts/dps_cap/reach.json", "w") as handle:
        json.dump(out, handle, indent=2)
        handle.write("\n")
