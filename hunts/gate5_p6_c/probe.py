"""Gate-5 property 6, run against the four battery functions on the four
preregistered boxes of ``MISSION.md``.

Property 6 as stated in ``docs/09`` gate #3:

    in a box strictly off the critical line, the completed function has no
    zeros

The box is a free parameter of that sentence, so this probe holds the
sigma-band fixed and varies only the height window: if the verdict flips
between two windows of the same band, the property as stated has no truth
value.

Every parameter here is the one committed in ``MISSION.md`` before any
winding number was computed. Nothing is nudged after the fact: a box whose
winding residual fails the integrality guard is recorded as ``undetermined``.

Run from the repository root::

    .venv/bin/python hunts/gate5_p6_c/probe.py

Results stream to ``hunts/gate5_p6_c/results.json`` after every count, so a
run stopped by the clock still leaves everything it managed to establish.
"""

from __future__ import annotations

import json
import pathlib
import sys
import time

from mpmath import mp

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))

from zeta.core import xi
from zeta.epstein import count_zeros_box, dh_f, epstein_completed

OUT = pathlib.Path(__file__).resolve().parent / "results.json"

DPS = 20

# ---------------------------------------------------------------------------
# a documented deviation from MISSION.md, forced by a measured defect
# ---------------------------------------------------------------------------
#
# MISSION.md fixed dps = 20 for every count.  That is adequate for xi and for
# f, and it is NOT adequate for Lambda_Q above t ~ 30.  Measured here, at
# sigma = 0.8, form (2,1,3), by comparing dps = 20 against dps = 40 and 80:
#
#     t = 5    |Lambda_Q| = 9.53053e-4     dps 20 agrees with dps 80 to 6 s.f.
#     t = 14   |Lambda_Q| = 2.06288e-9     dps 20 agrees with dps 80 to 6 s.f.
#     t = 44   |Lambda_Q| = 1.02595e-29    dps 20 vs dps 80 = 1.0261e-29
#                                          -> 4 correct digits, and the
#                                             argument differs in the 3rd
#
# The cause is structural, not a tuning accident.  epstein_completed forms
# ``first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s``, whose last two terms
# are O(1/t), while the answer decays like |Gamma(s)| ~ exp(-pi t / 2).  So
# roughly ``pi t / (2 ln 10) = 0.6822 t`` digits cancel.  At dps = 20 the
# *phase* of Lambda_Q is noise for t above ~ 30, and count_zeros_box's
# adaptive bisection then recurses to its depth limit on every segment: the
# first attempt at this probe ran dps = 20 at t = 85.7 and did not return.
#
# The rule below is a function of the box alone.  It was written from the
# table above, which is a measurement of *cost and accuracy*, before any
# Epstein winding number had been computed.
GUARD_PER_UNIT_HEIGHT = 0.6822


def dps_for(fn_key, box):
    if not fn_key.startswith("epstein"):
        return DPS
    import math

    return DPS + int(math.ceil(GUARD_PER_UNIT_HEIGHT * max(abs(v) for v in box["t"])))

# ---------------------------------------------------------------------------
# the preregistered boxes (MISSION.md, committed before any count)
# ---------------------------------------------------------------------------

BOXES = [
    {
        "id": "B1",
        "sigma": (0.7, 0.9),
        "t": (85.5, 85.9),
        "blind": False,
        "why": "band A at the height of the pinned Davenport-Heilbronn "
               "off-critical-line zero 0.808517 + 85.699348i (Spira 1994); "
               "declared non-blind, present to realise the 'a rival fails' "
               "pole of the well-posedness question",
    },
    {
        "id": "B2",
        "sigma": (0.7, 0.9),
        "t": (10.0, 14.0),
        "blind": True,
        "why": "band A, blind low window; cheapest boundary in the design",
    },
    {
        "id": "B3",
        "sigma": (0.7, 0.9),
        "t": (40.0, 44.0),
        "blind": True,
        "why": "band A, blind middling window; checks whether B2 is typical",
    },
    {
        "id": "B4",
        "sigma": (1.05, 1.55),
        "t": (10.0, 14.0),
        "blind": True,
        "why": "band B, strictly right of sigma = 1 and clear of the Lambda_Q "
               "pole at s = 1; zeta is zero-free here as a theorem",
    },
]

# ---------------------------------------------------------------------------
# the four functions, counted through the same routine the battery uses
# ---------------------------------------------------------------------------


def _zeta_fn(z):
    return xi(z, dps=DPS)


def _dh_fn(z):
    # what dh_interface counts: f itself.  In sigma > 0 the completion factor
    # (pi/5)^{-(s+1)/2} Gamma((s+1)/2) is zero-free and pole-free, so the
    # zeros of F and of f coincide there (MISSION.md).
    return dh_f(z, dps=DPS)


def _epstein_fn(form):
    def make(dps, _f=form):
        return lambda z: epstein_completed(z, _f, dps=dps)

    return make


FUNCTIONS = [
    ("riemann_zeta", "xi", lambda d: _zeta_fn),
    ("davenport_heilbronn", "f (= F in sigma > 0)", lambda d: _dh_fn),
    ("epstein_2_1_3", "Lambda_Q, form (2,1,3)", _epstein_fn((2, 1, 3))),
    ("epstein_1_1_6", "Lambda_Q, form (1,1,6)", _epstein_fn((1, 1, 6))),
]

# Boxes the Epstein arm is not attempted on, and why.  Declared here rather
# than discovered later: the guarded precision the rule above demands makes
# each Lambda_Q evaluation cost roughly linearly more, and B1 and B3 sit high
# enough that the two forms together do not fit the run's budget.
EPSTEIN_SKIP = {
    "B1": "needs dps ~ 79 (0.6822 * 85.9 digits of cancellation) at ~9 s per "
          "evaluation; ~24 boundary evaluations per form before adaptive "
          "refinement, so ~7 minutes per form, ~15 minutes for both",
    "B3": "needs dps ~ 50 at ~3.5 s per evaluation; ~124 boundary evaluations "
          "per form, so ~7 minutes per form, ~15 minutes for both",
}


def counted(fn):
    """Wrap fn so the probe can report what each count actually cost."""
    state = {"n": 0}

    def wrapped(z):
        state["n"] += 1
        return fn(z)

    return wrapped, state


def run_one(fn, box, dps):
    """One argument-principle count.  Returns a record, never raises."""
    (s0_re, s1_re), (t0, t1) = box["sigma"], box["t"]
    wrapped, state = counted(fn)
    started = time.time()
    with mp.workdps(dps):
        s0 = mp.mpc(mp.mpf(repr(s0_re)), mp.mpf(repr(t0)))
        s1 = mp.mpc(mp.mpf(repr(s1_re)), mp.mpf(repr(t1)))
    try:
        n = count_zeros_box(s0, s1, dps=dps, fn=wrapped)
        record = {"zeros": n, "satisfies_property_6": n == 0}
    except ArithmeticError as exc:
        record = {"zeros": None, "satisfies_property_6": None,
                  "undetermined": str(exc)}
    record["dps"] = dps
    record["evaluations"] = state["n"]
    record["seconds"] = round(time.time() - started, 2)
    return record


def verdict_for(box_counts):
    """The verdict rule fixed in MISSION.md, applied to one box."""
    z = box_counts.get("riemann_zeta", {}).get("zeros")
    rivals = {k: v for k, v in box_counts.items()
              if k != "riemann_zeta" and "skipped" not in v}
    if z is None or any(v.get("zeros") is None for v in rivals.values()):
        return "incomplete"
    if z != 0:
        return "box-invalidated (zeta itself has a zero in it)"
    if not rivals:
        return "incomplete"
    shared = sorted(k for k, v in rivals.items() if v["zeros"] == 0)
    partial = len(rivals) < len(FUNCTIONS) - 1
    if shared:
        # one rival sharing the property already settles the box: gate #3 asks
        # the structure be ungrantable to *every* rival.
        return "VACUOUS"
    return "DISTINGUISHES (partial: not all rivals run)" if partial \
        else "DISTINGUISHES"


def main():
    results = {
        "hunt": "gate5_p6_c",
        "property": "in a box strictly off the critical line, the completed "
                    "function has no zeros (docs/09 gate #3, property 6)",
        "dps": DPS,
        "route": "argument principle, zeta.epstein.count_zeros_box, default "
                 "forced subdivision step",
        "preregistered": "hunts/gate5_p6_c/MISSION.md, committed before any "
                         "winding number was computed",
        "boxes": {b["id"]: {"sigma": list(b["sigma"]), "t": list(b["t"]),
                            "blind": b["blind"], "why": b["why"]}
                  for b in BOXES},
        "counts": {b["id"]: {} for b in BOXES},
        "verdict_per_box": {},
        "complete": False,
        "precision_rule": "dps = 20 for xi and f; for Lambda_Q, 20 + ceil(0.6822 * t_max) to carry the exp(-pi t / 2) cancellation in epstein_completed (see probe.py)",
    }

    def flush():
        for b in BOXES:
            results["verdict_per_box"][b["id"]] = verdict_for(
                results["counts"][b["id"]]
            )
        OUT.write_text(json.dumps(results, indent=2) + "\n")

    flush()
    # cheap functions across every box first, so a run cut short by the clock
    # still carries a complete picture for the two that finish quickly.
    for name, what, make in FUNCTIONS:
        for box in BOXES:
            if name.startswith("epstein") and box["id"] in EPSTEIN_SKIP:
                rec = {"zeros": None, "satisfies_property_6": None,
                       "skipped": EPSTEIN_SKIP[box["id"]]}
            else:
                dps = dps_for(name, box)
                rec = run_one(make(dps), box, dps)
            rec["counted_on"] = what
            results["counts"][box["id"]][name] = rec
            print(f"{box['id']:>3} {name:<22} {rec}", flush=True)
            flush()

    results["complete"] = all(
        len(results["counts"][b["id"]]) == len(FUNCTIONS) for b in BOXES
    )
    flush()
    print("verdicts:", results["verdict_per_box"], flush=True)


if __name__ == "__main__":
    main()
