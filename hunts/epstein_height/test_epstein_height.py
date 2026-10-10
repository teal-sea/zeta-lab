"""Pins for the numbers `epstein_height`'s `RESULTS.md`, `AUDIT.md` and `docs/41` state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/epstein_height

Written 2026-10-10, when the hunt was landed on main as #129. Until then nothing
pinned these numbers: the scripts wrote artifacts, and the audit's own scripts
lived in a scratchpad that is not in the tree.

**Which routine.** The surface, the laws and the audit's counterexample were all
measured on `zeta.epstein.epstein_zeta` as it was before #291 (2026-10-09, "Fixes
#217"), which added a height lift of `ceil(EPSTEIN_DIGITS_PER_UNIT_HEIGHT * |t|)`
working digits. Setting that constant to zero restores the old routine exactly
(`epstein_completed` itself is unchanged), and it is the same planted fault
`tests/test_epstein_zeta_height.py` uses. So the reproductions below zero it, and
separate tests record what the current routine returns at the same cells.

Nothing writes into the tree: the scripts whose output is compared here run with
their artifact directory redirected to a temporary one.

Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import json
import math
import shutil
from pathlib import Path

import mpmath
import pytest
from mpmath import mp

import zeta.epstein as ep
from hunts.epstein_height import guard as G
from hunts.epstein_height import guard2 as G2
from hunts.epstein_height import law as LAW
from hunts.epstein_height import law2 as LAW2
from hunts.epstein_height import probe as P

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ART = HERE / "artifacts"
DOOR = ROOT / "docs" / "41-the-module-that-missed-the-guard.md"


@pytest.fixture(autouse=True)
def _restore_mpmath_precision():
    saved = mp.prec
    yield
    mp.prec = saved


@pytest.fixture
def pre_291(monkeypatch):
    """`epstein_zeta` without #291's height lift, i.e. the routine this hunt measured."""
    monkeypatch.setattr(ep, "EPSTEIN_DIGITS_PER_UNIT_HEIGHT", 0.0)


def _json(name: str):
    return json.loads((ART / name).read_text(encoding="utf-8"))


def _cell(rows, form, t, dps):
    hits = [r for r in rows if r["form"] == list(form) and r["t"] == t and r["dps"] == dps]
    assert len(hits) == 1, (form, t, dps, len(hits))
    return hits[0]


def _close(a, b, rel: float = 1e-9) -> bool:
    """JSON trees equal: ints, strings and None exactly, floats to ``rel``."""
    if isinstance(a, dict):
        return isinstance(b, dict) and a.keys() == b.keys() and all(_close(a[k], b[k], rel) for k in a)
    if isinstance(a, list):
        return isinstance(b, list) and len(a) == len(b) and all(_close(x, y, rel) for x, y in zip(a, b))
    if isinstance(a, float) and isinstance(b, (int, float)):
        return math.isclose(a, b, rel_tol=rel, abs_tol=1e-12)
    return a == b


def _digits(rel) -> float:
    rel = float(rel)
    return -math.log10(rel) if 0 < rel < 1 else 0.0


# --- the surface, against the routine as it was --------------------------------


@pytest.mark.parametrize("form, t, dps", [((1, 1, 4), 60.0, 20), ((1, 1, 4), 60.0, 15)])
def test_surface_cells_reproduce_against_the_pre_291_routine(pre_291, form, t, dps):
    """AUDIT.md attack 15 re-ran four cells bit for bit; two of them, live."""
    live = P.surface(form, [t], [dps])[0]
    stored = _cell(_json("surface.json"), form, t, dps)
    assert live["relative_error"] == pytest.approx(stored["relative_error"], rel=1e-9)
    assert live["oracle_abs"] == pytest.approx(stored["oracle_abs"], rel=1e-12)


@pytest.mark.slow
@pytest.mark.parametrize("form, t, dps", [((1, 1, 4), 120.0, 15), ((2, 1, 3), 100.0, 30)])
def test_the_headline_cells_reproduce_against_the_pre_291_routine(pre_291, form, t, dps):
    live = P.surface(form, [t], [dps])[0]
    stored = _cell(_json("surface.json"), form, t, dps)
    assert live["relative_error"] == pytest.approx(stored["relative_error"], rel=1e-9)


def test_the_current_routine_delivers_at_the_cells_that_failed():
    """What changed since: #291's lift. Measured 2026-10-10, not by this hunt."""
    for form, t in (((1, 1, 4), 60.0), ((2, 1, 3), 60.0)):
        row = P.surface(form, [t], [15])[0]
        assert row["correct_digits"] > 14, row


def test_the_surface_table_on_the_page():
    rows = _json("surface.json")
    assert len(rows) == 158
    table = {
        40: (15.6, 16.1, 16.1, 16.1, 16.1),
        60: (3.1, 8.2, 16.1, 16.1, 16.1),
        80: (0.0, 0.0, 5.1, 16.3, 16.3),
        120: (0.0, 0.0, 0.0, 0.0, 16.5),
        160: (0.0, 0.0, 0.0, 0.0, 2.4),
    }
    for t, digits in table.items():
        got = tuple(round(_cell(rows, (1, 1, 4), float(t), d)["correct_digits"], 1)
                    for d in (15, 20, 30, 50, 80))
        assert got == digits, t
    assert f"{_cell(rows, (1, 1, 4), 120.0, 15)['relative_error']:.1e}" == "2.3e+36"
    assert round(_cell(rows, (1, 1, 4), 80.0, 15)["relative_error"], 1) == 1.0
    # the audit's attack 15 values, bit for bit with the artifact
    for form, t, dps, rel in (((1, 1, 4), 60.0, 20, "5.762935e-09"),
                              ((2, 1, 3), 100.0, 30, "7.480392e+09"),
                              ((1, 0, 1), 80.0, 50, "2.307774e-18"),
                              ((1, 1, 4), 120.0, 15, "2.346323e+36")):
        assert f"{_cell(rows, form, t, dps)['relative_error']:.6e}" == rel
    for page in (HERE / "RESULTS.md", DOOR):
        text = page.read_text(encoding="utf-8")
        assert "| 60 | **3.1** | 8.2 | 16.1 | 16.1 | 16.1 |" in text
        assert "| 120 | **0** | **0** | **0** | **0** | 16.5 |" in text


def test_the_surface_is_the_grid_plus_the_boundary_cells():
    """AUDIT.md attack 14: 120 grid cells, 40 per form, merged with 38 of the 42
    boundary cells (the other 4 repeat a grid cell)."""
    rows, boundary = _json("surface.json"), _json("boundary.json")
    key = lambda r: (tuple(r["form"]), r["t"], r["dps"])  # noqa: E731
    grid = [r for r in rows if r["dps"] in (15, 20, 30, 50, 80)
            and r["t"] in (10, 20, 40, 60, 80, 100, 120, 160)]
    assert len(grid) == 120
    assert sorted(sum(1 for r in grid if tuple(r["form"]) == f)
                  for f in ((1, 1, 4), (2, 1, 3), (1, 0, 1))) == [40, 40, 40]
    assert len(boundary) == 42
    assert {key(r) for r in rows} == {key(r) for r in grid} | {key(r) for r in boundary}
    assert sum(key(r) in {key(g) for g in grid} for r in boundary) == 4


def test_smoke_rows_are_surface_rows():
    """smoke.json has no manifest; its rows are the probe's, cell for cell."""
    rows = _json("surface.json")
    for r in _json("smoke.json"):
        s = _cell(rows, tuple(r["form"]), r["t"], r["dps"])
        assert (r["relative_error"], r["oracle_abs"]) == (s["relative_error"], s["oracle_abs"])


def test_the_ceiling_is_float64_in_the_comparison():
    law = _json("law.json")
    assert round(law["oracle_floor"], 1) == 17.6
    assert all(r["correct_digits"] < 17.7 for r in _json("surface.json"))


# --- the two laws -----------------------------------------------------------------


def test_law_scripts_reproduce_their_artifacts(tmp_path, monkeypatch):
    shutil.copy(ART / "surface.json", tmp_path / "surface.json")
    monkeypatch.setattr(LAW, "ART", tmp_path)
    monkeypatch.setattr(LAW2, "ART", tmp_path)
    LAW.main()
    LAW2.main()
    LAW2.centred()
    for name in ("law.json", "law2.json"):
        live = json.loads((tmp_path / name).read_text(encoding="utf-8"))
        stored = _json(name)
        assert _close(live, stored), name


def test_first_model_residual_and_its_split_by_form():
    law = _json("law.json")
    assert law["n_testing_cells"] == 49
    assert (round(law["residual_mean"], 2), round(law["residual_rms"], 2)) == (0.13, 0.86)
    by = {}
    for r in law["rows"]:
        if 0.5 < r["correct_digits"] < r["oracle_ceiling_here"] - 0.5:
            by.setdefault(tuple(r["form"]), []).append(r["residual"])
    means = {f: round(sum(v) / len(v), 2) for f, v in by.items()}
    # RESULTS.md section 4 says +0.93 / +0.85 / -0.75: not reproduced (note there).
    assert means == {(1, 0, 1): 0.91, (1, 1, 4): 0.83, (2, 1, 3): -0.68}
    # the audit's own selection (attack 9): 1 < correct digits < 14
    by = {}
    for r in law["rows"]:
        if 1 < r["correct_digits"] < 14:
            by.setdefault(tuple(r["form"]), []).append(r["residual"])
    audit = {f: round(sum(v) / len(v), 3) for f, v in by.items()}
    assert audit == {(1, 1, 4): 0.848, (2, 1, 3): -0.667, (1, 0, 1): 1.156}
    assert round(audit[(1, 0, 1)] - audit[(2, 1, 3)], 2) == 1.82
    flat = [x for v in by.values() for x in v]
    assert len(flat) == 46
    # attack 9: the gaps between forms track the gaps in log10|zeta_Q|
    sel = [r for r in law["rows"] if 1 < r["correct_digits"] < 14]
    zq = {f: sum(math.log10(r["oracle_abs"]) for r in sel if tuple(r["form"]) == f)
          / sum(1 for r in sel if tuple(r["form"]) == f) for f in by}
    assert round(audit[(1, 1, 4)] - audit[(2, 1, 3)], 3) == 1.515
    assert round(zq[(1, 1, 4)] - zq[(2, 1, 3)], 3) == 1.498      # stated 1.551
    assert round(audit[(1, 0, 1)] - audit[(1, 1, 4)], 3) == 0.308
    assert round(zq[(1, 0, 1)] - zq[(1, 1, 4)], 3) == 0.299      # stated 0.313
    assert round(math.sqrt(sum(x * x for x in flat) / len(flat)), 3) == 0.917


def test_derived_law_numbers():
    law2 = _json("law2.json")
    per = {k: round(v["mean"], 2) for k, v in law2["per_form"].items()}
    assert per == {"(1, 1, 4)": 1.09, "(2, 1, 3)": 1.07, "(1, 0, 1)": 0.93}
    assert round(max(v["mean"] for v in law2["per_form"].values())
                 - min(v["mean"] for v in law2["per_form"].values()), 2) == 0.15
    assert round(law2["fitted_constant"], 3) == 1.068
    assert round(law2["rms_about_fitted_constant"], 3) == 0.357


def test_the_offset_is_mpmaths_decimal_to_binary_rounding():
    """AUDIT.md attack 6 and 12: 0.87 to 1.15 digits, and +1.086 -> +0.086."""
    extra = [mpmath.libmp.dps_to_prec(d + 20) * math.log10(2) - (d + 20)
             for d in sorted({r["dps"] for r in _json("surface.json")})]
    # RESULTS.md and AUDIT.md say 0.87 to 1.15; over every dps in the artifacts it
    # is 0.86 (dps 27, a boundary cell) to 1.15, and 0.87 to 1.15 over the grid's five.
    assert (round(min(extra), 2), round(max(extra), 2)) == (0.86, 1.15)
    grid = [mpmath.libmp.dps_to_prec(d + 20) * math.log10(2) - (d + 20) for d in (15, 20, 30, 50, 80)]
    assert (round(min(grid), 2), round(max(grid), 2)) == (0.87, 1.15)
    sel = [r for r in _json("law2.json")["rows"] if 1 < r["correct_digits"] < 14]
    before = [r["correct_digits"] - (r["dps"] + 20 - r["digits_lost_exact"]) for r in sel]
    after = [r["correct_digits"] - (mpmath.libmp.dps_to_prec(r["dps"] + 20) * math.log10(2)
                                    - r["digits_lost_exact"]) for r in sel]
    assert round(sum(before) / len(before), 2) == 1.09
    assert round(sum(after) / len(after), 2) == 0.09
    assert round(math.sqrt(sum(x * x for x in after) / len(after)), 3) == 0.357
    # "substituting the exact largest term for 1/t moves the mean by 0.002": 0.0008
    move = [0.5 * math.log10(1 + r["sigma"] ** 2 / r["t"] ** 2) for r in sel]
    assert round(sum(move) / len(move), 4) == 0.0008
    assert max(move) < 0.0035


# --- the guard, and the call the audit found ----------------------------------------


def test_the_audits_counterexample(pre_291):
    form, s = (2, 1, 3), mp.mpc(8, 80)
    assert round(G.digits_lost(8.0, 80.0), 2) == 39.90
    assert G.required_dps(8.0, 80.0, 4) == 24
    with mp.workdps(60):
        truth, _ = P.direct_lattice(s, form, 20000)
        zq = float(abs(truth))
    exact = LAW2.digits_lost_exact(8.0, 80.0, zq)
    assert round(exact, 2) == 44.07
    assert round(exact - G.digits_lost(8.0, 80.0), 2) == 4.17
    v = G.guarded_epstein_zeta(s, form, dps=24, want_digits=4)   # allowed
    with mp.workdps(60):
        got = _digits(abs(mp.mpc(v) - truth) / abs(truth))
    assert round(got, 2) == 0.59
    with pytest.raises(G2.PrecisionTooLow):
        G2.guarded_epstein_zeta(s, form, dps=24, want_digits=4)
    assert G2.required_dps((2, 1, 3), 8.0, 80.0, 4) > G2.required_dps((1, 1, 4), 8.0, 80.0, 4)


def test_the_same_call_on_the_current_routine():
    """What changed since: the lift alone puts this call above its 4 digits."""
    form, s = (2, 1, 3), mp.mpc(8, 80)
    with mp.workdps(60):
        truth, _ = P.direct_lattice(s, form, 20000)
        got = _digits(abs(mp.mpc(ep.epstein_zeta(s, form, dps=24)) - truth) / abs(truth))
    assert got > 4


def test_guard2_contract_artifact():
    rows = _json("guard2_contract.json")
    scored = [r for r in rows if r["delivered"] is not None]
    assert (len(rows), len(scored)) == (15, 12)
    assert all(r["delivered"] and r["correct_digits"] >= r["want"] for r in scored)
    excluded = [r for r in rows if r["delivered"] is None]
    assert {r["sigma"] for r in excluded} == {2.5}
    assert all(r["oracle_digits"] < r["want"] + 1 for r in excluded)
    assert (G2.MODEL_MARGIN, G2.STRIP_MARGIN) == (1.0, 3.0)
    at5 = [r["oracle_digits"] for r in rows if r["sigma"] == 5.0]
    at25 = [r["oracle_digits"] for r in rows if r["sigma"] == 2.5]
    assert (round(min(at5), 1), round(max(at5), 1)) == (15.7, 17.2)
    assert (round(min(at25), 1), round(max(at25), 1)) == (5.7, 6.3)


def test_the_other_allowed_calls_that_were_short(pre_291):
    """AUDIT.md attack 16: (2,1,3) at sigma 8, the first guard allows both."""
    for t, want, dps, delivered in ((100.0, 4, 37, 1.16), (60.0, 10, 18, 7.53)):
        s = mp.mpc(8, t)
        assert G.required_dps(8.0, t, want) == dps
        with mp.workdps(80):
            truth, _ = P.direct_lattice(s, (2, 1, 3), 20000)
        v = G.guarded_epstein_zeta(s, (2, 1, 3), dps=dps, want_digits=want)
        with mp.workdps(80):
            assert round(_digits(abs(mp.mpc(v) - truth) / abs(truth)), 2) == delivered


def test_the_working_precision_at_the_cancelling_step(monkeypatch):
    """AUDIT.md attack 5: a caller's dps arrives as dps + 20 (before #291), and
    as dps + 20 + ceil(0.6822 t) now."""
    seen = []
    real = mp.gammainc

    def spy(*a, **k):
        seen.append(mp.dps)
        return real(*a, **k)

    monkeypatch.setattr(mp, "gammainc", spy)
    for lift, expect in ((0.0, {15: 35, 30: 50, 80: 100}), (None, {15: 42, 30: 57})):
        if lift is not None:
            monkeypatch.setattr(ep, "EPSTEIN_DIGITS_PER_UNIT_HEIGHT", lift)
        else:
            monkeypatch.undo()
            monkeypatch.setattr(mp, "gammainc", spy)
        for dps, want in expect.items():
            seen.clear()
            ep.epstein_zeta(mp.mpc(5, 10), (1, 1, 4), dps=dps)
            assert set(seen) == {want}, (lift, dps, set(seen))


def test_stirling_against_mpmath():
    """AUDIT.md attack 7: the Gamma half of the first law is not where it fails."""
    worst_far = 0.0
    for sigma in (0.5, 2.5, 3.0, 5.0, 8.0):
        for t in (10.0, 40.0, 100.0, 160.0):
            with mp.workdps(30):
                exact = -float(mp.log10(abs(mp.gamma(mp.mpc(sigma, t)))))
            diff = exact - LAW.digits_lost(sigma, t)
            if sigma == 0.5:
                assert abs(diff) < 5e-6
            if t >= 100:
                worst_far = max(worst_far, abs(diff))
    assert round(worst_far, 3) == 0.003
    with mp.workdps(30):
        d = -float(mp.log10(abs(mp.gamma(mp.mpc(8, 10))))) - LAW.digits_lost(8.0, 10.0)
    assert round(d, 2) == -0.26


def test_the_first_contract_run_was_short_by_three_tenths(pre_291, monkeypatch):
    """RESULTS.md section 5: without the +1.0 margin, (2,1,3) at 2.5 + 60i."""
    monkeypatch.setattr(G2, "MODEL_MARGIN", 0.0)
    s = mp.mpc(2.5, 60)
    dps = G2.required_dps((2, 1, 3), 2.5, 60.0, 8)
    v = ep.epstein_zeta(s, (2, 1, 3), dps=dps)
    truth, oracle_digits = G2._truth(s, (2, 1, 3))
    with mp.workdps(60):
        got = _digits(abs(mp.mpc(v) - truth) / abs(truth))
    assert dps == 26
    assert round(8 - got, 1) == 0.3
    assert round(oracle_digits, 1) == 5.7


@pytest.mark.slow
def test_the_oracle_truncation_against_qmax_400000():
    """AUDIT.md attack 3 and RESULTS.md section 2, one cell of the nine re-run."""
    s = mp.mpc(5, 100)
    with mp.workdps(60 + 69):
        a, bound = P.direct_lattice(s, (1, 1, 4), 20000)
        b, _ = P.direct_lattice(s, (1, 1, 4), 400000)
        actual = float(abs(a - b))
    assert f"{actual:.2e}" == "9.94e-20" and f"{bound:.3e}" == "1.267e-17"
    assert round(bound / actual) == 127
    assert round(-math.log10(actual / float(abs(b))), 2) == 19.30


@pytest.mark.slow
def test_the_critical_line_attack(pre_291):
    """AUDIT.md attack 11 and 12, re-run: +4.66 for the first law, +1.35 derived."""
    rows = []
    for t in (40.0, 60.0, 80.0, 100.0):
        for margin in (4, 8):
            dps = LAW.required_dps(0.5, t, margin)
            s = mp.mpc(0.5, t)
            with mp.workdps(60 + int(0.7 * t)):
                beta = mp.power(4, -s) * (mp.zeta(s, mp.mpf(1) / 4) - mp.zeta(s, mp.mpf(3) / 4))
                truth = 4 * mp.zeta(s) * beta
            got = ep.epstein_zeta(s, (1, 0, 1), dps=dps)
            with mp.workdps(80):
                cd = _digits(abs(mp.mpc(got) - truth) / abs(truth))
            prec = mpmath.libmp.dps_to_prec(dps + 20) * math.log10(2)
            rows.append((cd - (dps + 20 - LAW.digits_lost(0.5, t)),
                         cd - (prec - LAW2.digits_lost_exact(0.5, t, float(abs(truth))))))
    law = [a for a, _ in rows]
    assert round(sum(law) / len(law), 2) == 4.66
    assert (round(min(law), 2), round(max(law), 2)) == (4.06, 5.36)
    assert round(sum(b for _, b in rows) / len(rows), 2) == 1.35


# --- what dps_cap left open -----------------------------------------------------------


def test_why_it_hangs_arithmetic():
    rows = {r["dps"]: r for r in _json("why_it_hangs.json")}
    lo, hi = rows[15], rows[100]
    assert (lo["accepted"], lo["n_segments"], hi["accepted"]) == (7, 24, 24)
    step = 1 / (2 * math.log(5 * 120 / (2 * math.pi)))
    assert lo["step"] == pytest.approx(step)
    assert round(lo["p_accept"], 3) == 0.292 and round(lo["branching_factor"], 3) == 1.417
    assert f"{lo['expected_evaluations_per_segment']:.1e}" == "6.4e+06"
    assert round(lo["branching_factor"] ** 45 * 2 / 86400) == 148
    assert hi["expected_evaluations_per_segment"] == 1.0


def test_from_log_refuses_rather_than_overwrites(tmp_path, monkeypatch):
    """surface.log is not in the tree (it never was committed); the rebuild
    cannot run, and it must not touch surface.json trying."""
    from hunts.epstein_height import from_log
    shutil.copy(ART / "surface.json", tmp_path / "surface.json")
    before = (tmp_path / "surface.json").read_bytes()
    monkeypatch.setattr(from_log, "ART", tmp_path)
    with pytest.raises(FileNotFoundError):
        from_log.main()
    assert (tmp_path / "surface.json").read_bytes() == before
    assert not (ART / "surface.log").exists()


# --- planted faults --------------------------------------------------------------------


def test_planted_fault_a_form_blind_bound_is_what_rung_b_catches(monkeypatch):
    monkeypatch.setattr(G2, "zeta_q_lower", lambda form, sigma, qmax=20000: (1.0, "series"))
    assert G2.required_dps((2, 1, 3), 8.0, 80.0, 4) == G2.required_dps((1, 1, 4), 8.0, 80.0, 4)


def test_planted_fault_the_surface_check_needs_the_old_routine():
    """Without zeroing the lift the stored 3.1-digit cell does not come back."""
    live = P.surface((1, 1, 4), [60.0], [15])[0]
    stored = _cell(_json("surface.json"), (1, 1, 4), 60.0, 15)
    assert live["relative_error"] < stored["relative_error"] * 1e-6


def test_planted_fault_the_first_guard_stops_firing_without_its_constant(monkeypatch):
    import law as toplevel_law  # the module guard.py reads, via its own sys.path entry
    monkeypatch.setattr(toplevel_law, "LEAD", 0.0)
    assert G.required_dps(5.0, 120.0, 10) == 15
