"""Pins for the numbers NOTES.md quotes from ccm_arithmetic/data/ (no recomputation).

Each test reads the committed JSON and fails if a regenerated file moved a
quoted number.  The recomputing tests are in test_ccm_arithmetic.py.
Nothing here writes into the tree.
Run: .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/ccm_arithmetic/test_ccm_arithmetic_data.py
"""

from __future__ import annotations

import json
import os
from fractions import Fraction

from flint import arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")


def _cells(kind):
    with open(os.path.join(DATA, f"measure_{kind}.json")) as fh:
        return json.load(fh)["cells"]


def _ball(s):
    ctx.prec = 200
    return arb(s)


def _c(r):
    return float(Fraction(r["c"]))


def test_zeta_grid_structure():
    z = _cells("zeta")
    assert len(z) == 30
    for r in z.values():
        assert _ball(r["lambdas"][0]) > 0
        assert float(r["lambda_mid"][1]) / float(r["lambda_mid"][0]) >= 1.6e6
        assert float(r["proj_residual"][4]) <= 8.3e-11
        assert float(r["misfit0"]) <= 6.95e-3
        assert r["sturm_extra_zeros"] == [0, 1, 2]
        assert float(r["capture_m2"]["bound_dist"]) >= 2.8e4
        assert float(r["capture_m2"]["actual_dist"]) <= 6.6e-4
        if r["N"] >= 64 and _c(r) >= 13:
            assert r["zeros"]["n_matched_1e-8"] == r["zeros"]["n_Xi"]
            assert float(r["zeros"]["max_dev"]) <= 7.8e-16
    assert min(float(r["proj_residual"][4]) for r in z.values()) < 7e-27
    assert z["50:128"]["zeros"]["n_Xi"] == 29
    assert float(z["50:128"]["compact"]["0.45"]["rel"]) < 7.3e-2
    assert float(z["60:128"]["capture_m2"]["mu"]) < 1.3e-169


def test_zeta_compact_error_at_fixed_band_turns_back():
    z = _cells("zeta")
    row = sorted((r for r in z.values() if r["N"] == 32), key=_c)
    errs = [float(r["compact"]["0"]["abs"]) for r in row]
    i = errs.index(min(errs))
    assert row[i]["c"] == "19" and 7.0e-3 < errs[i] < 7.2e-3
    assert errs[-1] > 9.0e-2


def test_dh_crossing_capture_and_gap_zero():
    d = _cells("dh")
    assert _ball(d["61/2:64"]["lambdas"][0]) > 0
    assert _ball(d["31:64"]["lambdas"][0]).upper() < 0
    assert float(d["31:64"]["misfit0"]) < 1.2e-4
    assert float(d["33:64"]["misfit0"]) > 0.999
    for key, r in d.items():
        if 29 <= _c(r) <= 33 and r["N"] in (64, 128) and key != "30:64":
            v1 = [float(x) for x in r["dh_gap_zeros_v1_v2"][0]]
            assert len(v1) == 1 and 85.729 < v1[0] < 85.735
    assert [round(float(x), 3) for x in d["30:64"]["dh_gap_zeros_v1_v2"][0]] == [85.096, 85.761]


def test_epstein_and_dedekind():
    e = _cells("epstein")
    for key in ("19:64", "25:64", "27:64", "28:64", "29:64"):
        assert _ball(e[key]["lambdas"][0]) > 0
        assert 0.08 < float(e[key]["misfit0"]) < 0.11
    assert _ball(e["59/2:64"]["lambdas"][0]).upper() < 0
    assert float(e["59/2:64"]["misfit0"]) > 0.98
    dd = _cells("dedekind")
    assert len(dd) == 26
    assert all(_ball(r["lambdas"][0]) > 0 for r in dd.values())
    assert max(float(r["misfit0"]) for r in dd.values()) < 0.041


def test_wa_threshold_and_dial():
    w = _cells("wa")
    assert float(w["2:32"]["misfit0"]) < 0.19 and float(w["3:32"]["misfit0"]) > 0.998
    with open(os.path.join(DATA, "wa_threshold.json")) as fh:
        t = json.load(fh)["bisection"]
    assert (t["32"]["positive_at"], t["32"]["negative_at"]) == ("39161/16384", "19581/8192")
    assert (t["64"]["positive_at"], t["64"]["negative_at"]) == ("39143/16384", "4893/2048")
    assert all(step[2] for n in ("32", "64") for step in t[n]["steps"])  # conclusive pivots
    with open(os.path.join(DATA, "wa_dial.json")) as fh:
        dial = json.load(fh)
    assert dial["a0_equals_2Qzeta_maxdev"] < 4e-180
    lo = [dial["dial"][a]["c_float"][0] for a in ("1/4", "1/8", "1/16", "1/32", "1/64")]
    steps = [b - a for a, b in zip(lo, lo[1:])]
    assert all(0.13 < s < 0.19 for s in steps)
    assert all(h[2] for a in dial["dial"].values() for h in a["hist"])


def test_rigidity_scales():
    for name, pos, gap in (("rigidity_13_32_2.json", 4.18e-49, 6.555e-45), ("rigidity_31_64_2.json", 1.515e-103, 8.556e-99)):
        with open(os.path.join(DATA, name)) as fh:
            d = json.load(fh)
        assert abs(float(_ball(d["eps_positivity_scale"]).mid()) / pos - 1) < 1e-3
        assert abs(float(_ball(d["eps_gap_scale"]).mid()) / gap - 1) < 1e-3
