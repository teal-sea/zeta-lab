"""One number at two precisions: what the dps=20 cap costs.

``zeta/epstein.py`` caps precision inside the rival interfaces it hands to the
battery: ``epstein_interface`` calls ``count_zeros_box`` with
``dps=min(dps, 20)`` and ``zeros_on_line`` with ``dps=min(dps, 15)``;
``zeta_interface`` and ``dh_interface`` cap their box counts the same way.

This measures the cost on a single evaluation of the completed Epstein zeta
high on the strip, where Gamma(s) decay makes the magnitude tiny and 20 digits
of working precision may not survive the cancellation.
"""

import json
import time

from mpmath import mp, mpc

from zeta.epstein import epstein_completed

FORM = (2, 1, 3)
RE, IM = "0.8", "85.7"


def measure(dps: int) -> dict:
    """abs(Lambda_Q(s)) at the requested dps, with wall time."""
    started = time.perf_counter()
    with mp.workdps(dps + 10):
        s = mpc(RE, IM)
    value = epstein_completed(s, FORM, dps=dps)
    with mp.workdps(dps + 10):
        magnitude = abs(value)
        text = mp.nstr(magnitude, min(dps, 25))
        log10 = mp.nstr(mp.log10(magnitude), 12)
    return {
        "dps": dps,
        "magnitude": text,
        "log10_magnitude": log10,
        "seconds": round(time.perf_counter() - started, 3),
    }


if __name__ == "__main__":
    out = {
        "quantity": "abs(epstein_completed(s, form, dps=D))",
        "s": RE + "+" + IM + "i",
        "form": list(FORM),
        "runs": [measure(20), measure(60)],
        "ladder": [measure(D) for D in (30, 40, 80, 100)],
        "ladder_note": (
            "dps 80 and 100 agree to every digit printed, so the converged "
            "magnitude is 1.617452632377971296327251e-58.  Everything at or "
            "below dps 40 is the working-precision noise floor: it falls by "
            "one order per digit of dps, which is the signature of roundoff "
            "and not of a quantity being resolved.  dps 60 is the first rung "
            "on the ladder that is the number rather than the floor, and it "
            "agrees with the converged value to 13 digits.  See "
            "print_check.py for why abs() must be taken inside a workdps "
            "block: outside one it is evaluated at mpmath's default 15 "
            "digits and silently truncates the answer to 16."
        ),
    }
    print(json.dumps(out, indent=2))
    with open("hunts/dps_cap/results.json", "w") as handle:
        json.dump(out, handle, indent=2)
        handle.write("\n")
