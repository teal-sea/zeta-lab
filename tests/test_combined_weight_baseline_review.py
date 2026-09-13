"""The combined-weight baseline review's numbers are pinned, and its checker still agrees.

``hunts/prime_pair_error/frontier/2026-09-06/certificate_route_test/BASELINE_REVIEW.md`` is
an independent review of the package's final combined-weight repair (M = 15, R = 100000,
mask 210, corrections at 17, 19, 23, 29, 31). Its checker, ``review/baseline_check.py``,
imports nothing from the package and writes ``review/baseline_check.json``.

Same habit as ``tests/test_factorial_pilot_archive.py``: a number stated in a document is
re-derived here, cheaply, so the document cannot drift from the record. Three things.

1. The checker's recorded run says every check passed, and reports the quantities the
   review states.
2. The recorded final coefficients re-verify from scratch with the checker's own functions:
   balanced, mass 2641/3, lifted prefix at least one on every cell of [1, R), the leading
   constant enclosed around the recorded value with kappa(D) > 0.
3. The review labels the material as it must: it survives, it is not a prime-counting
   record, and it bears on nothing about RH.

The full checker (about 25 s) is not rerun here; this is the fast tier.
"""

from __future__ import annotations

import importlib.util
import json
import os
from fractions import Fraction

import mpmath as mp

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PKG = os.path.join(
    REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06", "certificate_route_test"
)
REVIEW = os.path.join(PKG, "BASELINE_REVIEW.md")
CHECKER = os.path.join(PKG, "review", "baseline_check.py")
RECORDED_RUN = os.path.join(PKG, "review", "baseline_check.json")

STATED_C_PREFIX = "1.04866366379322062823"
STATED_MASS = Fraction(2641, 3)
STATED_TAIL = 15
STATED_REPAIRS = 537
STATED_NEGATIVE_CELLS = 705


def _checker():
    spec = importlib.util.spec_from_file_location("baseline_check", CHECKER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_the_recorded_checker_run_passed_and_states_the_reviewed_quantities():
    run = json.loads(open(RECORDED_RUN, encoding="utf-8").read())
    assert run["all_ok"] is True
    assert all(v.get("ok", True) for v in run["checks"].values())
    got = run["reproduced"]
    assert got["C"].startswith(STATED_C_PREFIX)
    assert Fraction(got["finite_coefficient_mass"]) == STATED_MASS
    assert got["tail_coefficient"] == STATED_TAIL
    assert got["repairs"] == STATED_REPAIRS
    assert got["negative_seed_cells_below_R"] == STATED_NEGATIVE_CELLS


def test_the_recorded_final_seed_reverifies_from_scratch():
    bc = _checker()
    rec = json.loads(open(os.path.join(PKG, "aggregate_results.json"), encoding="utf-8").read())
    inp = json.loads(open(os.path.join(PKG, "inputs.json"), encoding="utf-8").read())
    final = bc.coeffs(rec["new_coefficients"])
    star = bc.coeffs(inp["repair_coefficients"])
    assert bc.balanced(final) and bc.balanced(star)
    assert bc.mass(final) == STATED_MASS == Fraction(rec["new_final_mass"])
    assert bc.common_den(final) == 3

    lifted = bc.prefix(bc.lifted_increments(final, bc.R, 3))
    assert min(lifted[1:]) >= 3, "a cell of [1, R) has lifted weight below one"
    seed = bc.floor_sum_table(final, bc.R, 3)
    assert sum(1 for x in seed[1:] if x < 0) == STATED_NEGATIVE_CELLS

    C = bc.C_iv(final, STATED_TAIL, star)
    recorded = mp.mpf(rec["new_final_C"])
    assert bc.lo(C) <= recorded <= bc.hi(C)
    assert bc.hi(C) - bc.lo(C) < mp.mpf(10) ** -40
    assert bc.lo(bc.kappa_iv(final)) > 0
    assert bc.lo(C) > 1, "the leading constant is above one; nothing here is an RH-scale bound"


def test_the_review_labels_the_material_honestly():
    text = open(REVIEW, encoding="utf-8").read()
    assert "**Survives.**" in text
    assert "nothing here is a prime-counting record" in text.lower()
    assert "bears on rh" in text.lower()
    assert "external verification is pending" in text.lower()
    assert "certified" not in text.lower()
