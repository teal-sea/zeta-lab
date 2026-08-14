"""Gate-5 property 6, run exactly as ``MISSION.md`` preregistered it.

    in a box strictly off the critical line, the completed function has
    no zeros

Counts zeros of zeta (via xi), the Davenport-Heilbronn function and the two
discriminant -23 Epstein zetas in the preregistered boxes, and reads
``zeta.epstein.battery``'s own verdict rule off the counts.

Run from the repo root::

    .venv/bin/python hunts/gate5_p6_b/probe.py

Writes ``hunts/gate5_p6_b/results.json`` next to this file.  Every cell
carries its own status, so an undecided cell is visible in the output rather
than absent from it.

Nothing here is evidence for or against RH (``docs/08``).  It measures what
separates zeta from RH-violating look-alikes, and nothing more.
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

import mpmath
from mpmath import mp

from zeta.core import xi
from zeta.epstein import (
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    count_zeros_box,
    dh_f,
    epstein_completed,
)

# ---------------------------------------------------------------------------
# the preregistered parameters (MISSION.md, sections 2-4)
# ---------------------------------------------------------------------------

#: (name, sigma_lo, sigma_hi, t_lo, t_hi).  Strictly off the critical line,
#: clear of t = 0 and of the Epstein pole at s = 1.
BOXES = [
    ("A", 0.70, 0.92, 1.5, 11.5),
    ("B", 0.70, 0.92, 85.2, 86.2),
    ("C", 1.05, 1.60, 1.5, 11.5),
]

#: Digits the completed Epstein function loses to the Gamma(s) decay in its
#: Mellin-split representation, per unit height: pi / (2 ln 10).
EPSTEIN_LOSS_PER_T = math.pi / (2 * math.log(10))

CELL_CAP_SECONDS = 8 * 60
GLOBAL_CAP_SECONDS = 20 * 60
ADEQUACY_EXTRA_DPS = 15
ADEQUACY_TOL = 1e-6
NUDGE = 0.005


def _dps_for(function_name: str, t_max: float) -> int:
    """The preregistered working precision (MISSION.md section 3)."""
    if function_name.startswith("epstein"):
        return 20 + int(math.ceil(EPSTEIN_LOSS_PER_T * t_max))
    return 20


def _evaluator(function_name: str, dps: int):
    """The counted object for each function (MISSION.md section 1)."""
    if function_name == "riemann_zeta":
        return lambda z, _d=dps: xi(z, dps=_d)
    if function_name == "davenport_heilbronn":
        return lambda z, _d=dps: dh_f(z, dps=_d)
    form = tuple(int(part) for part in function_name.split("_")[1:])
    return lambda z, _f=form, _d=dps: epstein_completed(z, _f, dps=_d)


class _Memo:
    """Memoized contour evaluator.

    ``_arg_variation`` re-evaluates both endpoints of every segment, so a
    cache on the sample point roughly halves the evaluation count.  It changes
    no mathematics: the integrands are deterministic functions of s.
    """

    def __init__(self, fn):
        self._fn = fn
        self._cache: dict = {}
        self.calls = 0

    def __call__(self, z):
        key = (str(mp.re(z)), str(mp.im(z)))
        if key not in self._cache:
            self.calls += 1
            self._cache[key] = self._fn(z)
        return self._cache[key]

    @property
    def distinct(self) -> int:
        return len(self._cache)


def _forced_segments(box, dps: int) -> int:
    """The forced pre-subdivision count ``count_zeros_box`` will use."""
    _, s_lo, s_hi, t_lo, t_hi = box
    with mp.workdps(dps):
        t_max = max(abs(t_lo), abs(t_hi), 10.0)
        step = mp.mpf(1) / (2 * mp.log(5 * t_max / (2 * mp.pi)))
        width = mp.mpf(s_hi) - mp.mpf(s_lo)
        height = mp.mpf(t_hi) - mp.mpf(t_lo)
        per_edge = [width, height, width, height]
        return int(sum(max(1, int(mp.ceil(edge / step))) for edge in per_edge))


def _adequacy(function_name: str, box, dps: int) -> dict:
    """MISSION.md section 3: the same corner at dps and dps + 15."""
    _, _, s_hi, _, t_hi = box
    corner = mpmath.mpc(s_hi, t_hi)
    lo = _evaluator(function_name, dps)(corner)
    hi = _evaluator(function_name, dps + ADEQUACY_EXTRA_DPS)(corner)
    scale = max(abs(lo), abs(hi))
    rel = float(abs(lo - hi) / scale) if scale > 0 else 0.0
    return {
        "corner": f"{s_hi}+{t_hi}i",
        "value_at_dps": mpmath.nstr(lo, 8),
        "value_at_dps_plus_15": mpmath.nstr(hi, 8),
        "relative_difference": rel,
        "passed": rel < ADEQUACY_TOL,
    }


def _count(function_name: str, box, dps: int, budget_left: float) -> dict:
    """One cell: the zero count of one function in one box, with its status."""
    name, s_lo, s_hi, t_lo, t_hi = box
    cell = {
        "function": function_name,
        "box": name,
        "sigma": [s_lo, s_hi],
        "t": [t_lo, t_hi],
        "dps": dps,
    }

    t0 = time.time()
    cell["adequacy"] = _adequacy(function_name, box, dps)
    per_eval = (time.time() - t0) / 2.0
    cell["seconds_per_evaluation"] = per_eval
    if not cell["adequacy"]["passed"]:
        cell["status"] = "NOT-DECIDED-PRECISION"
        return cell

    segments = _forced_segments(box, dps)
    projected = per_eval * segments * 2
    cell["forced_segments"] = segments
    cell["projected_seconds"] = projected
    if projected > CELL_CAP_SECONDS or projected > budget_left:
        # MISSION.md section 4: predicted-infeasible cells are not run.
        cell["status"] = "NOT-DECIDED-BY-COST"
        cell["cost_arithmetic"] = (
            f"{per_eval:.2f} s/eval x {segments} forced segments x 2 "
            f"= {projected:.0f} s, against a {CELL_CAP_SECONDS} s cell cap "
            f"and {budget_left:.0f} s of global budget"
        )
        return cell

    lo, hi = complex(s_lo, t_lo), complex(s_hi, t_hi)
    for attempt in (0, 1):
        memo = _Memo(_evaluator(function_name, dps))
        started = time.time()
        try:
            cell["zeros"] = count_zeros_box(lo, hi, dps=dps, fn=memo)
            cell["status"] = "DECIDED"
        except ArithmeticError as exc:
            cell.setdefault("contour_errors", []).append(str(exc))
            if attempt == 0:
                # MISSION.md section 5: one nudge, by the fixed rule.
                hi = complex(s_hi + NUDGE, t_hi + NUDGE)
                cell["nudged_to"] = [hi.real, hi.imag]
                continue
            cell["status"] = "NOT-DECIDED-CONTOUR"
        cell["seconds"] = time.time() - started
        cell["distinct_evaluations"] = memo.distinct
        return cell
    return cell


def _verdict(box_name: str, cells: dict) -> dict:
    """MISSION.md section 6: battery's own rule, reproduced unchanged."""
    rivals = [n for n in cells if n != "riemann_zeta"]
    claim = {n: (c.get("zeros") == 0 if c["status"] == "DECIDED" else None)
             for n, c in cells.items()}
    undecided = sorted(n for n, v in claim.items() if v is None)
    zeta_holds = claim.get("riemann_zeta")
    shared = sorted(n for n in rivals if claim[n] is True)

    if zeta_holds is None:
        verdict = "NOT-DECIDED"
    elif zeta_holds is False:
        verdict = "FALSE-OF-ZETA"
    elif shared:
        verdict = "VACUOUS"
    elif undecided:
        verdict = "NOT-DECIDED"
    else:
        verdict = "DISTINGUISHES"

    return {
        "box": box_name,
        "claim_holds": claim,
        "shared_with": shared,
        "undecided": undecided,
        "verdict": verdict,
    }


def main() -> int:
    started = time.time()
    functions = [
        "riemann_zeta",
        "davenport_heilbronn",
        "epstein_2_1_3",
        "epstein_1_1_6",
    ]
    # MISSION.md section 4 fixes the execution order.
    order = [
        ("A", functions),
        ("B", ["riemann_zeta", "davenport_heilbronn"]),
        ("B", ["epstein_2_1_3", "epstein_1_1_6"]),
        ("C", functions),
    ]
    boxes = {b[0]: b for b in BOXES}

    cells: dict = {name: {} for name in boxes}
    for box_name, group in order:
        box = boxes[box_name]
        for function_name in group:
            if function_name in cells[box_name]:
                continue
            left = GLOBAL_CAP_SECONDS - (time.time() - started)
            if left <= 0:
                cells[box_name][function_name] = {
                    "function": function_name,
                    "box": box_name,
                    "status": "NOT-DECIDED-BY-BUDGET",
                }
                continue
            dps = _dps_for(function_name, box[4])
            cell = _count(function_name, box, dps, left)
            cells[box_name][function_name] = cell
            print(
                f"[{time.time() - started:7.1f}s] box {box_name} "
                f"{function_name:20s} dps={dps:3d} "
                f"{cell['status']:24s} zeros={cell.get('zeros')}",
                flush=True,
            )

    verdicts = {name: _verdict(name, cells[name]) for name in boxes if cells[name]}
    decided = {n: v for n, v in verdicts.items()
               if v["verdict"] in {"VACUOUS", "DISTINGUISHES", "FALSE-OF-ZETA"}}
    distinct = sorted({v["verdict"] for v in decided.values()})

    if not decided:
        overall = "NOT-SETTLED"
    elif len(distinct) == 1:
        overall = distinct[0]
    else:
        overall = "NOT-WELL-POSED"

    out = {
        "hunt": "gate5_p6_b",
        "run_id": "d9ae5359-933a-4a85-a0e7-28c04e36bc26",
        "property": (
            "in a box strictly off the critical line, the completed function "
            "has no zeros"
        ),
        "preregistered_in": "hunts/gate5_p6_b/MISSION.md",
        "boxes": {b[0]: {"sigma": [b[1], b[2]], "t": [b[3], b[4]]} for b in BOXES},
        "davenport_heilbronn_offline_zero": {
            "re": str(OFFLINE_ZERO_RE),
            "im": str(OFFLINE_ZERO_IM),
            "inside_box_B": True,
        },
        "cells": cells,
        "verdicts": verdicts,
        "overall": overall,
        "wall_clock_seconds": time.time() - started,
        "scope": (
            "Nothing here is evidence for or against RH (docs/08). A hunt is a "
            "probe, not a result. Grade: measured."
        ),
    }
    path = Path(__file__).resolve().parent / "results.json"
    path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(f"\noverall: {overall}")
    for name in sorted(verdicts):
        v = verdicts[name]
        print(f"  box {name}: {v['verdict']:16s} shared_with={v['shared_with']} "
              f"undecided={v['undecided']}")
    print(f"wrote {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
