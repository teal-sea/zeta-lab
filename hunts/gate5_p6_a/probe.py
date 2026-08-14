#!/usr/bin/env python3
"""Hunt #13 (gate5_p6_a): settle gate #3 battery property 6.

    "in a box strictly off the critical line, the completed function has
     no zeros"

The boxes, the precision and the counting route were fixed in `MISSION.md`
and committed before this file existed. Run end to end with:

    .venv/bin/python hunts/gate5_p6_a/probe.py

It writes `results.json` next to itself, incrementally, so that a cell that
runs out of its wall-clock allowance costs one recorded gap rather than the
whole run.

Everything here is a float-grade measurement (`AGENTS.md`, rung 1): one
route, no enclosures. It is called one.
"""

from __future__ import annotations

import json
import signal
import sys
import time
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from mpmath import mp  # noqa: E402

from zeta.core import xi  # noqa: E402
from zeta.epstein import (  # noqa: E402
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    completed_dh,
    count_zeros_box,
    epstein_completed,
)

OUT = Path(__file__).resolve().parent / "results.json"

# --- preregistered parameters (MISSION.md, committed first) ----------------

DPS = 20
CAP_SECONDS = 420.0
MAX_STEP_HALVINGS = 3
MAX_NUDGES = 2
NUDGE = 0.005

BOXES = {
    "A": {
        "sigma": (0.70, 0.92),
        "t": (85.55, 85.85),
        "why": (
            "contains the pinned Davenport-Heilbronn off-line zero; the box "
            "most favourable to a DISTINGUISHES verdict"
        ),
    },
    "B": {
        "sigma": (0.70, 0.92),
        "t": (70.10, 70.40),
        "why": "same shape, unrelated ordinate; measures box dependence",
    },
    "C": {
        "sigma": (1.02, 1.60),
        "t": (0.50, 50.50),
        "why": (
            "the half plane where zeta's completed function is zero-free as a "
            "theorem; exploratory, run only if affordable"
        ),
    },
}

# The completed function of each of the four battery members, uniformly.
# Note: `zeta.epstein.dh_interface` wires its own `count_zeros_box` to the
# *uncompleted* f, while the zeta and Epstein interfaces use the completed
# form. In every box used here the gamma factor of `completed_dh` is finite
# and non-vanishing, so the two agree; using `completed_dh` keeps the four
# columns literally the same claim.
FUNCTIONS = {
    "riemann_zeta": lambda z: xi(z, dps=DPS),
    "davenport_heilbronn": lambda z: completed_dh(z, dps=DPS),
    "epstein_2_1_3": lambda z: epstein_completed(z, (2, 1, 3), dps=DPS),
    "epstein_1_1_6": lambda z: epstein_completed(z, (1, 1, 6), dps=DPS),
}


class Timeout(Exception):
    pass


def _alarm(signum, frame):  # pragma: no cover - signal path
    raise Timeout()


def _default_step(t_hi: float):
    """The routine's own default step, recomputed so it can be halved."""
    with mp.workdps(DPS):
        tmax = max(abs(t_hi), mp.mpf(10))
        return mp.mpf(1) / (2 * mp.log(5 * tmax / (2 * mp.pi)))


def count(name, sigma, t_lo, t_hi, cap=CAP_SECONDS):
    """One cell of the table, with the preregistered retry and nudge policy."""
    fn = FUNCTIONS[name]
    record = {
        "function": name,
        "sigma": list(sigma),
        "t": [t_lo, t_hi],
        "dps": DPS,
        "retries": [],
    }
    base = _default_step(t_hi)
    started = time.time()
    signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, cap)
    try:
        for nudge in range(MAX_NUDGES + 1):
            lo, hi = t_lo + nudge * NUDGE, t_hi + nudge * NUDGE
            for halving in range(MAX_STEP_HALVINGS + 1):
                step = base / (2**halving)
                try:
                    n = count_zeros_box(
                        mp.mpc(sigma[0], lo),
                        mp.mpc(sigma[1], hi),
                        dps=DPS,
                        fn=fn,
                        step=step,
                    )
                except Timeout:
                    raise
                except ArithmeticError as exc:
                    record["retries"].append(
                        {
                            "nudge": nudge,
                            "halving": halving,
                            "error": str(exc)[:200],
                        }
                    )
                    continue
                record.update(
                    {
                        "count": int(n),
                        "status": "ok",
                        "nudges_used": nudge,
                        "step_halvings_used": halving,
                        "t_actual": [lo, hi],
                        "seconds": round(time.time() - started, 2),
                    }
                )
                return record
        record.update(
            {
                "status": "undecided",
                "count": None,
                "seconds": round(time.time() - started, 2),
            }
        )
        return record
    except Timeout:
        record.update(
            {
                "status": "timeout",
                "count": None,
                "seconds": round(time.time() - started, 2),
            }
        )
        return record
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


def confirm() -> int:
    """`probe.py --confirm`: re-run the one cell the verdict rests on at a
    finer step, and record whether the count moves.

    A winding number near zero is what you get from "no zeros" and also from
    "this contour was under-resolved and happened to close". `count_zeros_box`
    already refuses a residual above 1e-6, which is the primary guard; halving
    the forced-subdivision length is the secondary one. Halving was the retry
    policy preregistered in `MISSION.md`; running it here on a cell that did
    not error is an added robustness check, and it is labelled as one.
    """
    results = json.loads(OUT.read_text())
    box = BOXES["A"]
    base = _default_step(box["t"][1])
    block = {
        "cell": "box A / epstein_2_1_3",
        "why": "the surviving rival; the whole verdict rests on this count",
        "runs": [],
    }
    for halvings in (1, 2):
        t0 = time.time()
        signal.signal(signal.SIGALRM, _alarm)
        signal.setitimer(signal.ITIMER_REAL, CAP_SECONDS)
        try:
            n = count_zeros_box(
                mp.mpc(box["sigma"][0], box["t"][0]),
                mp.mpc(box["sigma"][1], box["t"][1]),
                dps=DPS,
                fn=FUNCTIONS["epstein_2_1_3"],
                step=base / (2**halvings),
            )
            block["runs"].append(
                {
                    "step_halvings": halvings,
                    "count": int(n),
                    "seconds": round(time.time() - t0, 2),
                }
            )
        except Timeout:
            block["runs"].append(
                {
                    "step_halvings": halvings,
                    "count": None,
                    "status": "timeout",
                    "seconds": round(time.time() - t0, 2),
                }
            )
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
        print(block["runs"][-1], flush=True)
    counts = {r["count"] for r in block["runs"] if r["count"] is not None}
    block["stable"] = counts == {0}
    results.setdefault("robustness", []).append(block)
    OUT.write_text(json.dumps(results, indent=2) + "\n")
    return 0


def main() -> int:
    results = {
        "hunt": "gate5_p6_a",
        "hunt_number": 13,
        "property": (
            "in a box strictly off the critical line, the completed function "
            "has no zeros"
        ),
        "grade": "measured (rung 1: one route, float grade)",
        "dps": DPS,
        "cap_seconds": CAP_SECONDS,
        "boxes": BOXES,
        "pinned_dh_offline_zero": {
            "re": str(OFFLINE_ZERO_RE),
            "im": str(OFFLINE_ZERO_IM),
        },
        "controls": {},
        "cells": [],
        "cost_probe": {},
    }

    def save():
        OUT.write_text(json.dumps(results, indent=2) + "\n")

    # --- control 1: a straddling box with a known answer ------------------
    print("control 1: xi over sigma [0.20,0.80], t [13.60,14.60] ...", flush=True)
    c1 = count("riemann_zeta", (0.20, 0.80), 13.60, 14.60)
    c1["expected"] = 1
    c1["passed"] = c1.get("count") == 1
    results["controls"]["straddling_box_xi_gamma1"] = c1
    print("   ->", c1.get("status"), c1.get("count"), f"{c1['seconds']}s", flush=True)
    save()

    # --- boxes A and B, all four functions --------------------------------
    for label in ("A", "B"):
        box = BOXES[label]
        for name in FUNCTIONS:
            print(f"box {label} / {name} ...", flush=True)
            cell = count(name, box["sigma"], box["t"][0], box["t"][1])
            cell["box"] = label
            results["cells"].append(cell)
            print(
                "   ->",
                cell.get("status"),
                cell.get("count"),
                f"{cell['seconds']}s",
                flush=True,
            )
            save()

    # --- control 2: the Davenport-Heilbronn cell of box A is known ---------
    dh_a = next(
        c for c in results["cells"]
        if c["box"] == "A" and c["function"] == "davenport_heilbronn"
    )
    results["controls"]["dh_box_A_contains_pinned_zero"] = {
        "expected": ">= 1",
        "observed": dh_a.get("count"),
        "passed": isinstance(dh_a.get("count"), int) and dh_a["count"] >= 1,
    }
    save()

    # --- cost probe, then box C if it fits --------------------------------
    probe_point = mp.mpc(1.3, 25.0)
    for name, fn in FUNCTIONS.items():
        t0 = time.time()
        try:
            signal.signal(signal.SIGALRM, _alarm)
            signal.setitimer(signal.ITIMER_REAL, 60.0)
            fn(probe_point)
            per_sample = time.time() - t0
        except Timeout:
            per_sample = float("inf")
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
        results["cost_probe"][name] = round(per_sample, 4)
    box_c = BOXES["C"]
    step_c = float(_default_step(box_c["t"][1]))
    perimeter = 2 * (box_c["sigma"][1] - box_c["sigma"][0]) + 2 * (
        box_c["t"][1] - box_c["t"][0]
    )
    forced = perimeter / step_c
    results["cost_probe"]["box_C_forced_segments"] = round(forced, 1)
    results["cost_probe"]["box_C_projected_seconds"] = {
        n: round(results["cost_probe"][n] * forced * 4, 1) for n in FUNCTIONS
    }
    save()
    affordable = all(
        results["cost_probe"]["box_C_projected_seconds"][n] < CAP_SECONDS
        for n in FUNCTIONS
    )
    results["cost_probe"]["box_C_attempted"] = affordable
    print("cost probe:", results["cost_probe"], flush=True)
    save()

    if affordable:
        for name in FUNCTIONS:
            print(f"box C / {name} ...", flush=True)
            cell = count(name, box_c["sigma"], box_c["t"][0], box_c["t"][1])
            cell["box"] = "C"
            results["cells"].append(cell)
            print(
                "   ->",
                cell.get("status"),
                cell.get("count"),
                f"{cell['seconds']}s",
                flush=True,
            )
            save()

    # --- verdicts ---------------------------------------------------------
    results["verdicts"] = {}
    for label in ("A", "B", "C"):
        cells = {c["function"]: c for c in results["cells"] if c["box"] == label}
        if not cells:
            continue
        rivals = [n for n in cells if n != "riemann_zeta"]
        survivors = [n for n in rivals if cells[n].get("count") == 0]
        zeta_free = cells.get("riemann_zeta", {}).get("count") == 0
        if zeta_free and survivors:
            # `battery`'s own rule: a structure the claim shares with ANY rival
            # cannot be load bearing. One survivor settles the box, and an
            # unfinished cell elsewhere cannot unsettle it.
            verdict = "VACUOUS"
        elif any(c.get("status") != "ok" for c in cells.values()):
            verdict = "not-settled"
        elif zeta_free:
            verdict = "DISTINGUISHES"
        else:
            verdict = "VACUOUS"
        results["verdicts"][label] = {
            "verdict": verdict,
            "counts": {n: c.get("count") for n, c in cells.items()},
            "survivors": [
                n for n, c in cells.items()
                if n != "riemann_zeta" and c.get("count") == 0
            ],
        }
    save()
    print(json.dumps(results["verdicts"], indent=2))
    return 0


if __name__ == "__main__":
    if "--confirm" in sys.argv:
        raise SystemExit(confirm())
    raise SystemExit(main())
