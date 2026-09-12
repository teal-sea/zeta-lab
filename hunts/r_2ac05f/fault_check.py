"""Fault injection: a control that cannot fail is not a control.

Two plants, run against the probe's own machinery:

1. Force the x^1 coefficient of Qhat_kappa to g instead of kappa*g, i.e.
   plant exactly the defect this adjudication attributes to the published
   table.  The Farmer-Gonek kappa = 1 control still passes (it is blind to
   the plant by construction, since kappa*g = g there), while C_{2,2} moves
   to the published -4.  This is the demonstration that the kappa = 1 row,
   the only externally anchored control either hunt ran, has zero power
   against the defect.

2. Corrupt the pairing denominator by one factorial step.  The Farmer-Gonek
   control goes red.  That is the demonstration that it has power against
   the thing it *is* calibrating.

Run: .venv/bin/python hunts/r_2ac05f/fault_check.py
"""

from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import permutations
from math import factorial
from pathlib import Path

import probe as _p  # noqa: E402  (run from this directory, or see __main__)


def main() -> dict:
    n = 11
    fg = _p.farmer_gonek_row(n)

    baseline_control = _p.form_factor(1, n) == fg
    c_kappa_2 = {k: str(_p.form_factor(k, 2)[2]) for k in (1, 2, 3, 4, 5)}

    # --- plant 1: drop the multiplicity ------------------------------------
    original_qhat = _p.qhat

    def multiplicity_dropped(kappa: int, order: int):
        q = list(original_qhat(kappa, order))
        if kappa >= 2 and len(q) > 1:
            q[1] = _p.G
        return q

    _p.qhat = multiplicity_dropped
    _p._PAIR_CACHE.clear()
    plant1_control = _p.form_factor(1, n) == fg
    plant1_c22 = str(_p.form_factor(2, 2)[2])
    _p.qhat = original_qhat
    _p._PAIR_CACHE.clear()

    # --- plant 2: corrupt the pairing --------------------------------------
    original_pair = _p.pair_words

    def off_by_one(left, right):
        if len(left) != len(right):
            return F(0)
        r = len(left)
        denom = factorial(2 * r + sum(left) + sum(right))  # was ... - 1
        total = 0
        for sigma in permutations(right):
            prod = 1
            for b, d in zip(left, sigma):
                prod *= factorial(b + d + 1)
            total += prod
        return F(total, denom)

    _p.pair_words = off_by_one
    _p._PAIR_CACHE.clear()
    plant2_control = _p.form_factor(1, n) == fg
    _p.pair_words = original_pair
    _p._PAIR_CACHE.clear()

    report = {
        "baseline_farmer_gonek_control_passes": baseline_control,
        "C_kappa_2_for_kappa_1_to_5": c_kappa_2,
        "plant_1_multiplicity_dropped": {
            "farmer_gonek_control_still_passes": plant1_control,
            "C_2_2_becomes": plant1_c22,
            "reading": "the kappa=1 control is blind to this defect; the "
                       "planted value is the published one",
        },
        "plant_2_pairing_off_by_one": {
            "farmer_gonek_control_still_passes": plant2_control,
            "reading": "the kappa=1 control does have power against the "
                       "ingredient it calibrates",
        },
    }
    print(json.dumps(report, indent=2))
    Path(__file__).with_name("fault_check.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    return report


if __name__ == "__main__":
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    main()
