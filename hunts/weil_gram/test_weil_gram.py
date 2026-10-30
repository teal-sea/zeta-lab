"""Pins for weil_gram's records (added at landing, 2026-10-30)."""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name: str) -> dict:
    return json.loads((HERE / name).read_text())


def test_each_results_file_was_computed_at_its_own_dps() -> None:
    """The first results_dps90.json was computed at dps 50: run_base took its
    default dps from DPS when it was defined, and main() never passed it."""
    for dps in (50, 90):
        for name, r in _load(f"results_dps{dps}.json").items():
            assert r["dps"] == dps, (dps, name)


def test_main_passes_its_precision_to_run_base(monkeypatch) -> None:
    import gram

    seen = []

    def fake_run_base(name, sigmas, cache, dps=None):
        seen.append(dps)
        return {"lambda_min": 1.0, "lambda_min_from_zeros": 1.0, "at_floor": False,
                "worst_entry_rel_diff": 0.0, "n_uncovered": 0, "n_entries": 1,
                "largest_uncovered_scale": 0.0}

    monkeypatch.setattr(gram, "run_base", fake_run_base)
    monkeypatch.setattr(gram.sys, "argv", ["gram.py", "77"])
    monkeypatch.setattr(gram.json, "dump", lambda *a, **k: None)
    monkeypatch.setattr(gram, "open", lambda *a, **k: open("/dev/null", "w"), raising=False)
    gram.main()
    assert seen and all(d == 77 for d in seen)


def test_dps_50_and_90_agree_on_every_eigenvalue() -> None:
    a, b = _load("results_dps50.json"), _load("results_dps90.json")
    for name in ("broad", "plus1", "plus2"):
        for x, y in zip(a[name]["lambda"], b[name]["lambda"]):
            assert abs(x - y) <= 1e-12 * abs(x), (name, x, y)


def test_the_refinement_descent_is_the_recorded_one() -> None:
    rows = {r["k"]: r for r in _load("refine_dps50.json")}
    assert abs(rows[2]["lambda_min"] / 2.404e-3 - 1) < 1e-3
    assert abs(rows[6]["lambda_min"] / 5.029e-22 - 1) < 1e-3
    lam = [rows[k]["lambda_min"] for k in range(2, 7)]
    assert all(x > y for x, y in zip(lam, lam[1:]))
