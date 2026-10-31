"""Pins for the v6 census landing sweep (``census_sweep.py``, NOTES.md section 7).

What is checked, each against something that can fail:

1. The numpy transcription equals ``probe.ode_null_control`` on identical
   inputs, at a high pair with neighbouring off-line pairs in its window.
2. Pairs 1 to 5 built from the census receipts reproduce this hunt's own
   ``results.json`` null-control landings (built from sign-scanned zeros).
3. The committed ``census_sweep.jsonl`` is complete (ids 1..1268, finite) and
   recomputes bit for bit; every pair lands before its isolated y0^2/2.
4. The numbers NOTES.md section 7 quotes: the census-wide latest landing,
   the runner-up, and the deep-ten comparison with the predictions file.
5. Lesion: dropping one on-line zero from a window moves the landing by far
   more than the tolerances above, so check 2 is not vacuous.
6. Agreement with ``hunts/lambda_dh_exact``, which landed the same model on
   windows it built itself (40 pairs below height 19,960).

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/flow_repair/test_census_sweep.py
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import pytest

from hunts.flow_repair import census_sweep as cs
from hunts.flow_repair import probe as fr

HERE = Path(__file__).resolve().parent
ROWS = {r["n"]: r for r in map(json.loads, (HERE / "census_sweep.jsonl").read_text().splitlines())}
PRED = json.loads((HERE / "deep_predictions_v1.json").read_text())


def test_numpy_port_equals_probe_ode_null_control():
    g, y0, reals, others = cs.window_config(1081)  # height 17363, 5 neighbouring pairs
    assert len(others) >= 3
    t_end = 1.25 * 0.5 * y0 * y0
    ref = fr.ode_null_control({"gamma": g, "y0": y0}, reals, others, t_end, n_steps=120,
                              window=cs.W, rho_tail=1.0 / fr.mean_gap(g))
    ts, sl = cs.ode_np(g, y0, reals, others, t_end, n_steps=120)
    assert ts == pytest.approx(ref["tstar_ode"], rel=1e-13)
    assert sl == pytest.approx(ref["slope0_ode"], rel=1e-13)


def test_receipt_windows_reproduce_results_json():
    repo = json.loads((HERE / "results.json").read_text())["ode_null"]
    for k in range(1, 6):
        r = ROWS[k]
        assert r["n_reals"] == repo[f"pair{k}"]["n_line_zeros"]
        assert r["tstar_ode"] == pytest.approx(repo[f"pair{k}"]["tstar_ode"], rel=1e-7)


def test_committed_sweep_is_complete_and_recomputes():
    assert sorted(ROWS) == list(range(1, 1269))
    assert all(math.isfinite(r["tstar_ode"]) for r in ROWS.values())
    assert all(r["tstar_ode"] < r["isolated_y0sq_half"] for r in ROWS.values())
    assert [n for n, r in ROWS.items() if r["edge"]] == [1266, 1267, 1268]
    for n in (5, 107):
        assert cs.land(n) == ROWS[n]


def test_notes_numbers():
    core = sorted((r for r in ROWS.values() if not r["edge"]), key=lambda r: -r["tstar_ode"])
    assert core[0]["n"] == 5 and core[0]["tstar_ode"] == pytest.approx(0.05766566, abs=5e-9)
    assert core[1]["n"] == 107 and core[1]["tstar_ode"] == pytest.approx(0.05586457, abs=5e-9)
    assert hashlib.sha256((HERE / "deep_predictions_v1.json").read_bytes()).hexdigest() == (
        "2616116f766a413c26deb64fb516b2f31bc110a735750a83c33ba923524d0082")
    deep = [r["n"] for r in ROWS.values() if r["y0"] > 0.37]
    assert sorted(deep) == sorted(p["n_v6"] for p in PRED["predictions"])
    over, inside = [], 0
    for p in PRED["predictions"]:
        t = ROWS[p["n_v6"]]["tstar_ode"]
        lo, hi = p["parameter_bootstrap_95"]
        inside += lo <= t <= hi
        over.append(100 * (p["predicted_t"] / t - 1))
    assert inside == 0 and min(over) > 0
    assert sum(over) / len(over) == pytest.approx(9.51, abs=0.005)
    assert max(over) == pytest.approx(29.96, abs=0.005)


def test_agrees_with_lambda_dh_exact_censuses():
    """hunts/lambda_dh_exact landed the same model on windows it built itself
    (sign-scanned line zeros, located off-line zeros, closed strip counts)."""
    root = HERE.parent / "lambda_dh_exact"
    theirs = json.loads((root / "census_1e4.json").read_text())["rows"]
    theirs += [x for x in json.loads((root / "census_runs/full_r2/census_1e5.json").read_text())["rows"]
               if x.get("landing_ode") and x["gamma"] < cs.CENSUS_TOP - cs.W]
    assert len(theirs) >= 40
    for x in theirs:
        r = min(ROWS.values(), key=lambda r: abs(r["gamma"] - x["gamma"]))
        assert abs(r["gamma"] - x["gamma"]) < 1e-4
        assert r["tstar_ode"] == pytest.approx(x["landing_ode"], rel=1e-5)
    # NOTES.md section 7: all ten predicted pairs had ODE landings in the tree before this sweep
    for p in PRED["predictions"]:
        assert min(abs(x["gamma"] - p["height"]) for x in theirs) < 1e-4


def test_lesion_missing_online_zero_is_visible():
    g, y0, reals, others = cs.window_config(5)
    i = min(range(len(reals)), key=lambda j: abs(reals[j] - g))
    t_end = 1.25 * 0.5 * y0 * y0
    full, _ = cs.ode_np(g, y0, reals, others, t_end)
    cut, _ = cs.ode_np(g, y0, reals[:i] + reals[i + 1:], others, t_end)
    assert full is not None and cut is not None
    assert abs(cut / full - 1) > 1e-4  # >1000x the 1e-7 tolerance of the reproduction check
