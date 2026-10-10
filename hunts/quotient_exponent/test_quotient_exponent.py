"""Pins for the numbers `quotient_exponent`'s `RESULTS.md`, `RUNS.md` and `docs/42` state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/quotient_exponent

Written 2026-10-10, when the hunt was landed on main as #130. Until then nothing
pinned these numbers: the scripts wrote artifacts, the model comparison of
section 4 existed only in the audit's scratchpad, and the factorial-form table of
section 2 had no script in the tree. Here the cheap solves are re-run live (the
three small diagonal cutoffs, the factorial form at those three, the `N = 10^3`
staircase, the plateau anatomy at three sizes, the free-support programme at
`N = 10^3` with its exact check), the model comparison is recomputed from the
sweep artifacts, and the expensive rows (`10^6` to `10^7`) are read from the
artifacts, which the 2026-10-10 re-run in `RUNS.md` reproduced.

Nothing writes into the tree: the scripts whose whole output is compared run with
their artifact directory redirected to a temporary one.

Every value here is a floating LP value (HiGHS through scipy) and is graded
measured. Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
from mpmath import mp

HERE = Path(__file__).resolve().parent
# staircase.py, closed_form.py and free_support.py import their sibling `lp` as a
# top-level module, as they do when run as scripts.
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from hunts.quotient_exponent import fit as FIT  # noqa: E402
from hunts.quotient_exponent import lp as LP  # noqa: E402

ROOT = HERE.parents[1]
ART = HERE / "artifacts"
SOURCE = ROOT / "hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier"


@pytest.fixture(autouse=True)
def _restore_mpmath_precision():
    """closed_form.py sets mp.dps = 40 at import; put it back after every test."""
    saved = mp.prec
    yield
    mp.prec = saved


def _json(name: str):
    return json.loads((ART / name).read_text(encoding="utf-8"))


def _diagonal() -> dict:
    rows = _json("lp_small.json") + _json("lp_large.json")
    return {r["N"]: r for r in rows}


def _inside():
    rows = [r for r in FIT.load() if r["excess"] > 0]
    return [r for r in rows if math.log(r["y"]) / math.log(r["N"]) <= 0.5 + 1e-9]


def _lsq(cols, target):
    A = np.vstack(cols).T
    sol, *_ = np.linalg.lstsq(A, target, rcond=None)
    resid = target - A @ sol
    return sol, float(np.sqrt((resid ** 2).mean()))


# --- section 2 and 3: the diagonal ----------------------------------------------


@pytest.mark.parametrize("N", [1000, 10000, 100000])
def test_small_diagonal_cutoffs_reproduce_live(N):
    live = LP.solve(N, math.isqrt(N), verbose=False)
    stored = _diagonal()[N]
    assert live["excess"] == pytest.approx(stored["excess"], rel=1e-12)
    assert live["cells"] == stored["cells"]
    assert live["n_binding_cells"] == stored["n_binding_cells"]
    assert live["identity"]["factorial_telescope_max_rel_defect"] < 1e-15


def test_the_published_values_agree_to_14_and_15_digits():
    text = (SOURCE / "DUAL_WITNESS.md").read_text(encoding="utf-8")
    d = _diagonal()
    for N, pinned, digits in ((1000, "41.28216944295939183072", 14),
                              (10000, "226.83268961232150239965", 15)):
        assert pinned in text
        mine = repr(d[N]["excess"]).replace(".", "")
        theirs = pinned.replace(".", "")
        same = next(i for i, (a, b) in enumerate(zip(mine, theirs)) if a != b)
        assert same == digits, (N, same)


def test_the_identity_table_including_the_two_new_cutoffs():
    d = _diagonal()
    # RESULTS.md section 2 prints 0 for the 3 x 10^6 sum: the artifact says 1.6e-16
    # (not reproduced as printed; the note is in place).
    table = {1000: (1.1e-16, 2.1e-16), 10000: (0.0, 3.2e-16), 100000: (1.5e-16, 4.9e-16),
             1000000: (0.0, 8.3e-16), 3000000: (1.6e-16, 2.3e-15), 10000000: (0.0, 2.4e-15)}
    for N, (sumw, tele) in table.items():
        ident = d[N]["identity"]
        assert float(f"{ident['sum_w_rel_defect']:.1e}") == sumw, N
        assert float(f"{ident['factorial_telescope_max_rel_defect']:.1e}") == tele, N


@pytest.mark.parametrize("N, stated", [(1000, 41.28216944295832), (10000, 226.83268961231443),
                                       (100000, 1035.2339342959604)])
def test_the_factorial_form_returns_the_same_optimum(N, stated):
    """RESULTS.md section 2 table: no script for it was in the tree; this is one."""
    from scipy.optimize import linprog
    y = math.isqrt(N)
    psi = LP.von_mangoldt_prefix(N)
    cells = LP.quotient_cells(N)
    A = (cells[:, None] // np.arange(1, y + 1)[None, :]).astype(np.float64)
    cost = np.array([math.lgamma(N // j + 1) for j in range(1, y + 1)])
    res = linprog(cost, A_ub=-A, b_ub=-np.ones(len(cells)), bounds=[(None, None)] * y,
                  method="highs")
    factorial = res.fun - psi[N]
    assert abs(factorial - _diagonal()[N]["excess"]) / _diagonal()[N]["excess"] < 1e-12
    assert factorial == pytest.approx(stated, rel=1e-11)


def test_the_diagonal_table():
    d = _diagonal()
    rows = [(1000, 31, 61, 41.282169, 0.2321), (10000, 100, 198, 226.832690, 0.2268),
            (100000, 316, 630, 1035.233934, 0.1841), (1000000, 1000, 1998, 6414.832164, 0.2029),
            (3000000, 1732, 3462, 14477.154080, 0.2008), (10000000, 3162, 6322, 30297.736768, 0.1704)]
    for N, y, cells, excess, ratio in rows:
        r = d[N]
        assert (r["y"], r["cells"]) == (y, cells)
        assert round(r["excess"], 6) == excess
        assert round(r["excess"] / N ** 0.75, 4) == ratio
    local = [math.log(d[b]["excess"] / d[a]["excess"]) / math.log(b / a)
             for a, b in ((1000, 10000), (10000, 100000), (100000, 1000000),
                          (1000000, 3000000), (3000000, 10000000))]
    assert [round(x, 4) for x in local] == [0.7399, 0.6593, 0.7921, 0.7409, 0.6134]
    # "0.2, which is 15% too large at the 10^7 diagonal point"
    assert round(100 * (0.2 - d[10000000]["excess"] / 10000000 ** 0.75) / 0.2) == 15


def test_binding_counts_and_the_ratio_door_1_explains():
    d = _diagonal()
    binding = [d[N]["n_binding_cells"] for N in sorted(d)]
    assert binding == [31, 103, 321, 1011, 1746, 3193]
    assert [round(d[N]["n_binding_cells"] / d[N]["y"], 3) for N in sorted(d)] == [
        1.0, 1.03, 1.016, 1.011, 1.008, 1.01]
    frac = [d[N]["n_binding_cells"] / d[N]["cells"] for N in sorted(d)]
    assert (round(min(frac), 3), round(max(frac), 3)) == (0.504, 0.52)


# --- section 4: the grid and the comparison ----------------------------------------


def test_the_grid_table():
    rows = {(r["N"], r["y"]): r for r in FIT.load()}
    table = {
        10000: (0.5244, 0.4563, 0.3538, 0.3152, 0.2268),
        100000: (0.5076, 0.4206, 0.4017, 0.2922, 0.1840),
        1000000: (0.4577, 0.4397, 0.3714, 0.3293, 0.2029),
    }
    for N, vals in table.items():
        got = []
        for a in (0.30, 0.35, 0.40, 0.45, 0.50):
            y = int(math.isqrt(N)) if a == 0.50 else max(2, int(round(N ** a)))
            r = rows[(N, y)]
            got.append(round(r["excess"] * math.sqrt(y) / N, 4))
        assert tuple(got) == vals, N
    ten7 = [round(rows[(10000000, y)]["excess"] * math.sqrt(y) / 10 ** 7, 4) for y in (631, 1413, 3162)]
    assert ten7 == [0.3662, 0.346, 0.1704]


def test_the_twenty_rows_and_the_surviving_lower_bound():
    inside = _inside()
    assert len(inside) == 20
    c = min(r["excess"] * math.sqrt(r["y"]) / r["N"] for r in inside)
    assert round(c, 4) == 0.1704
    falls = {}
    for r in inside:
        falls.setdefault(r["N"], []).append(r["excess"] * math.sqrt(r["y"]) / r["N"])
    ratios = [max(v) / min(v) for v in falls.values() if len(v) >= 3]
    # "falls by a factor of 2.1 to 2.8 as y grows"
    assert (round(min(ratios), 2), round(max(ratios), 2)) == (2.15, 2.76)


def test_the_model_comparison():
    inside = _inside()
    logE = np.array([math.log(r["excess"]) for r in inside])
    logN = np.array([math.log(r["N"]) for r in inside])
    logy = np.array([math.log(r["y"]) for r in inside])
    alpha = logy / logN
    one = np.ones(len(inside))
    free, rms_free = _lsq([one, logN, -logy], logE)
    _, rms_conj = _lsq([one], logE - logN + 0.5 * logy)
    _, rms_conj_alpha = _lsq([one, alpha], logE - logN + 0.5 * logy)
    _, rms_conj_alpha_N = _lsq([one, alpha, logN], logE - logN + 0.5 * logy)
    four, rms_four = _lsq([one, logN, -logy, alpha], logE)
    assert [round(x, 4) for x in (rms_free, rms_conj, rms_conj_alpha, rms_conj_alpha_N, rms_four)] == [
        0.1258, 0.3435, 0.1198, 0.1187, 0.1173]
    assert (round(free[1], 3), round(free[2], 3)) == (1.159, 0.874)
    assert (round(four[1], 3), round(four[2], 3)) == (1.042, 0.609)
    stored = _json("fit.json")["inside_alpha_half"]
    assert (stored["n"], round(stored["resid_rms_in_log"], 4)) == (20, 0.1258)


def test_fit_script_reproduces_its_artifacts(tmp_path, monkeypatch):
    for name in ("sweep.json", "sweep_1e6.json", "sweep_1e7_partial.json",
                 "lp_small.json", "lp_large.json"):
        (tmp_path / name).write_bytes((ART / name).read_bytes())
    monkeypatch.setattr(FIT, "ART", tmp_path)
    FIT.main()
    FIT.compare()
    for name in ("fit.json", "fit_comparison.json"):
        live = json.loads((tmp_path / name).read_text(encoding="utf-8"))
        stored = _json(name)

        def close(a, b):
            if isinstance(a, dict):
                return a.keys() == b.keys() and all(close(a[k], b[k]) for k in a)
            if isinstance(a, float):
                return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-12)
            return a == b

        assert close(live, stored), name


# --- sections 5 and 6: the staircase and the threshold -------------------------------


def test_the_staircase_at_1000_reproduces(tmp_path, monkeypatch):
    from hunts.quotient_exponent import staircase as ST
    monkeypatch.setattr(ST, "ART", tmp_path)
    monkeypatch.setattr(sys, "argv", ["staircase.py", "--N", "1000"])
    ST.main()
    live = json.loads((tmp_path / "staircase_N1000.json").read_text(encoding="utf-8"))
    stored = _json("staircase_N1000.json")
    assert [p["excess"] for p in live["plateaus"]] == pytest.approx(
        [p["excess"] for p in stored["plateaus"]], rel=1e-9, abs=1e-12)
    assert (live["y_star"], live["n_distinct_values"], len(live["curve"])) == (63, 33, 76)
    plateaus = {(p["y_from"], p["y_to"]): round(p["excess"], 6) for p in live["plateaus"]}
    assert plateaus[(42, 47)] == 10.34657 and plateaus[(48, 50)] == 10.283916
    assert plateaus[(51, 55)] == 10.2471 and plateaus[(56, 62)] == 2.426015
    assert plateaus[(63, 77)] == 0.0
    assert round(10.2471 / 2.426015, 1) == 4.2


def test_the_staircase_at_10000():
    st = _json("staircase_N10000.json")
    assert (st["y_star"], st["cells"], st["n_distinct_values"]) == (173, 198, 128)
    p = st["last_positive_plateau"]
    assert (p["y_from"], p["y_to"], p["length"], round(p["excess"], 6)) == (157, 172, 16, 9.406483)


def test_the_threshold_rows():
    rows = {r["N"]: r for r in _json("threshold.json")}
    table = {1000: (63, 61, 1.033, 0.5998), 10000: (173, 198, 0.874, 0.5595),
             100000: (589, 630, 0.935, 0.5540), 1000000: (1938, 1998, 0.970, 0.5479)}
    for N, (ystar, cells, ratio, alpha) in table.items():
        r = rows[N]
        assert (r["y_star"], r["cells"]) == (ystar, cells)
        assert round(r["y_star_over_cells"], 3) == ratio
        assert round(r["y_star_alpha"], 4) == alpha
    alphas = [rows[N]["y_star_alpha"] for N in sorted(rows)]
    assert alphas == sorted(alphas, reverse=True)
    # RUNS.md says the N = 10^6 value 123.83310675500282 "has no run behind it in
    # this tree". threshold.json is that run (RUNS.md, 2026-10-10 note).
    assert rows[1000000]["last_positive"] == pytest.approx(
        {"y": 1937, "excess": 123.83310675500282, "excess_direct": 123.83310675567783,
         "min_e_direct": -2.7284841053187847e-10}, rel=1e-12)
    log = (ART / "threshold.log").read_text(encoding="utf-8")
    for y in (1812, 1921, 1934, 1937):
        assert f"N=1000000 y=  {y} excess=1.238331e+02 -> positive" in log


def test_cells_with_prime_mass():
    for N, cells, hot in ((1000, 61, 40), (10000, 198, 99), (100000, 630, 275)):
        psi = LP.von_mangoldt_prefix(N)
        q = LP.quotient_cells(N)
        w = LP.cell_weights(N, q, psi)
        assert (len(q), int((w > 1e-12).sum())) == (cells, hot)


def test_equality_alone_is_satisfiable_far_below_y_star():
    """AUDIT.md attack 12: W = 1 on the prime-mass cells alone is consistent at
    y = 44, 104 and 391, against y* = 63, 173 and 589 (float rank, by least squares)."""
    for N, first in ((1000, 44), (10000, 104), (100000, 391)):
        psi = LP.von_mangoldt_prefix(N)
        q = LP.quotient_cells(N)
        hot = LP.cell_weights(N, q, psi) > 1e-12
        def consistent(y):
            A = (q[hot][:, None] // np.arange(1, y + 1)[None, :]).astype(np.float64)
            c, *_ = np.linalg.lstsq(A, np.ones(int(hot.sum())), rcond=None)
            return float(np.abs(A @ c - 1).max()) < 1e-8
        assert consistent(first) and not consistent(first - 1)


# --- section 6a and 6b ------------------------------------------------------------------


def test_free_support_at_1000_live_and_exact():
    from hunts.quotient_exponent import free_support as FS
    r = FS.zero_excess_min_mass(1000)
    assert (r["support_used"], r["max_j_used"], round(r["l1_mass"], 1)) == (35, 201, 45.5)
    assert FS.exact_check(r)["exact_zero_excess"]


def test_free_support_rows_on_the_page():
    rows = {r["N"]: r for r in _json("free_support.json")}
    table = {1000: (35, 201, 45.5), 10000: (109, 1251, 114.7), 100000: (285, 14286, 389.1)}
    for N, (used, maxj, mass) in table.items():
        r = rows[N]
        assert (r["support_used"], r["max_j_used"], round(r["l1_mass"], 1)) == (used, maxj, mass)
    assert rows[1000]["exact"]["exact_zero_excess"]
    assert "exact" not in rows[10000] and "exact" not in rows[100000]
    assert (float(f"{rows[10000]['min_slack_float']:.0e}"),
            float(f"{rows[100000]['min_slack_float']:.0e}")) == (-8e-13, -6e-12)
    assert [round(math.log(rows[N]["max_j_used"]) / math.log(N), 2) for N in (1000, 10000, 100000)] == [
        0.77, 0.77, 0.83]
    assert round(math.log(rows[100000]["l1_mass"]) / math.log(100000), 2) == 0.52


@pytest.mark.parametrize("N, y, expr, p, num, den", [
    (1000, 59, "(7/2) * log(2)", 2, 7, 2),
    (10000, 165, "3 * log(23)", 23, 3, 1),
    (100000, 563, "6 * log(113)", 113, 6, 1),
])
def test_the_plateau_value_is_one_cell_times_one_logarithm(N, y, expr, p, num, den):
    from hunts.quotient_exponent import closed_form as CF
    r = CF.anatomy(N, y)
    assert r["cells_with_excess_and_weight"] == 1
    assert r["closed_form"]["expression"] == expr
    assert r["carrier"]["excess_as_fraction"] == [num, den]
    with mp.workdps(30):
        assert abs(r["excess"] - float(mp.mpf(num) / den * mp.log(p))) < 1e-12 * r["excess"]


def test_closed_form_artifact():
    cf = _json("closed_form.json")
    assert cf["1000"]["plateau"]["y"] == list(range(56, 63))
    assert cf["10000"]["plateau"]["y"] == list(range(157, 173))
    assert cf["100000"]["plateau"]["y"] == list(range(545, 581))
    carriers = {k: {a["carrier"]["cell"] for a in v["anatomy"]} for k, v in cf.items() if k != "1000000"}
    assert carriers == {"1000": {31}, "10000": {434}, "100000": {884}}
    excess_cells = {k: sorted(a["cells_with_excess"] for a in v["anatomy"]) for k, v in cf.items()}
    assert (min(excess_cells["1000"]), max(excess_cells["1000"])) == (14, 15)
    assert (min(excess_cells["10000"]), max(excess_cells["10000"])) == (52, 57)
    assert (min(excess_cells["100000"]), max(excess_cells["100000"])) == (167, 181)
    big = cf["1000000"]["anatomy"][0]
    assert (big["y"], big["excess"], big["cells_with_excess"], big["cells_with_excess_and_weight"]) == (
        1995, 0.0, 497, 0)


def test_the_1e5_plateau_is_wider_than_the_scan_window():
    """closed_form.py scanned y = 545..580 and the plateau filled the window; the
    same value holds at y = 588 (threshold.json), so "width 36" is the window."""
    thr = {r["N"]: r for r in _json("threshold.json")}[100000]["last_positive"]
    assert thr["y"] == 588
    assert thr["excess"] == pytest.approx(_json("closed_form.json")["100000"]["plateau"]["value"], rel=1e-12)


def test_the_1e5_plateau_runs_from_538_to_588():
    values = {y: LP.solve(100000, y, verbose=False)["excess"] for y in (537, 538, 588, 589)}
    plateau = _json("closed_form.json")["100000"]["plateau"]["value"]
    assert round(values[537], 2) == 87.28
    assert values[538] == pytest.approx(plateau, rel=1e-12)
    assert values[588] == pytest.approx(plateau, rel=1e-12)
    assert values[589] == 0.0


@pytest.mark.parametrize("N, ys, carrier, low, high", [
    (1000, range(56, 63), 31, 14, 15),
    (10000, range(157, 173), 434, 50, 57),
    pytest.param(100000, range(538, 589), 884, 165, 182, marks=pytest.mark.slow),
])
def test_exactly_one_weighted_cell_at_every_support_of_the_plateau(N, ys, carrier, low, high):
    from hunts.quotient_exponent import closed_form as CF
    counts = []
    for y in ys:
        r = CF.anatomy(N, y)
        assert r["cells_with_excess_and_weight"] == 1, y
        assert r["carrier"]["cell"] == carrier, y
        assert len(r["carrier"]["prime_powers_in_range"]) == 1, y
        counts.append(r["cells_with_excess"])
    assert (min(counts), max(counts)) == (low, high)


@pytest.mark.parametrize("N, y", [(1000, 63), (10000, 173), (100000, 589)])
def test_zero_excess_at_y_star_has_an_exact_rational_witness(N, y):
    """AUDIT.md attack 3, by another route: the minimum-mass vertex of the
    zero-excess programme, rounded, checked in exact arithmetic on every cell."""
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    psi = LP.von_mangoldt_prefix(N)
    cells = LP.quotient_cells(N)
    hot = LP.cell_weights(N, cells, psi) > 1e-12
    A = (cells[:, None] // np.arange(1, y + 1)[None, :]).astype(np.float64)
    res = linprog(np.ones(2 * y), A_eq=csr_matrix(np.hstack([A[hot], -A[hot]])),
                  b_eq=np.ones(int(hot.sum())),
                  A_ub=-csr_matrix(np.hstack([A[~hot], -A[~hot]])), b_ub=-np.ones(int((~hot).sum())),
                  bounds=[(0, None)] * (2 * y), method="highs")
    assert res.success
    x = res.x[:y] - res.x[y:]
    for D in (1, 2, 4, 12, 60, 2520, 27720):
        c = [Fraction(v).limit_denominator(D) for v in x]
        support = [(j + 1, cj) for j, cj in enumerate(c) if cj != 0]
        W = [sum(cj * (int(q) // j) for j, cj in support) for q in cells]
        if all(Wq >= 1 for Wq in W) and all(Wq == 1 for Wq, h in zip(W, hot) if h):
            break
    else:
        pytest.fail(f"no exact witness at N={N}, y={y}")


def test_the_fitted_exponents_turn_sign_at_alpha_0_425():
    free = _json("fit.json")["inside_alpha_half"]
    slope, cut = free["a"] - 1, 0.5 - free["b"]
    assert (round(slope, 3), round(cut, 3)) == (0.159, -0.374)
    assert round(-slope / cut, 3) == 0.425


def test_audit_attacks_8_13_and_15():
    """The fitted exponents get the sign of the N-trend wrong at three alpha
    slices (8); the within-N slope drifts (13); the diagonal design is nearly
    rank-deficient (15)."""
    inside = _inside()
    slices = {}
    for r in inside:
        a = round(math.log(r["y"]) / math.log(r["N"]) * 20) / 20
        slices.setdefault(a, []).append(
            (math.log(r["N"]), math.log(r["excess"] * math.sqrt(r["y"]) / r["N"])))
    measured = {a: round(float(np.polyfit([p[0] for p in v], [p[1] for p in v], 1)[0]), 3)
                for a, v in slices.items()}
    for a, m, f in ((0.30, -0.030, 0.047), (0.35, -0.008, 0.028), (0.45, 0.017, -0.009)):
        assert measured[a] == m
        assert round(0.159 - 0.374 * a, 3) == f
    for N, b in ((10000, 0.946), (100000, 0.917), (1000000, 0.777)):
        pts = [(math.log(r["y"]), math.log(r["excess"])) for r in inside if r["N"] == N]
        assert round(-float(np.polyfit([p[0] for p in pts], [p[1] for p in pts], 1)[0]), 3) == b
    diag = [r for r in inside if abs(math.log(r["y"]) / math.log(r["N"]) - 0.5) < 0.01]
    sv = np.linalg.svd(np.array([[1.0, math.log(r["N"]), -math.log(r["y"])] for r in diag]),
                       compute_uv=False)
    assert [float(f"{v:.3g}") for v in sv] == [34.3, 0.632, 0.0112]
    # attack 14: the dense block at N = 10^8 is 1.6 GB by its own formula
    assert 2 * math.isqrt(10 ** 8) * 10 ** 4 * 8 == 1.6e9


def test_the_pages_state_these_numbers():
    results = (HERE / "RESULTS.md").read_text(encoding="utf-8")
    door = (ROOT / "docs" / "42-a-law-read-off-a-diagonal.md").read_text(encoding="utf-8")
    for s in ("30297.736768", "0.1704 N^{3/4}", "63, 173, 589, 1938", "0.5998, 0.5595, 0.5540, 0.5479",
              "| 10^7 | 3162 | 6322 | 30297.736768 | 0.1704 | 0.6134 |",
              "| **conjectured `(1, 1/2)`, `log C` linear in `alpha`** | **2** | **0.1198** |",
              "`(7/2) log 2` | `2.42601513195980858`", "`3 log 23` | `9.40648264778744907`",
              "`6 log 113` | `28.3643269122740434`",
              "| 10^3 | 31 | **35** | 201 | 45.5 | 63 |"):
        assert s in results, s
    for s in ("`a = 1.042`, `b = 0.609`", "`E >= 0.1704 N/sqrt(y)`", "`alpha > 0.425`",
              "factor of 2.1 to 2.8", "`(1.159, 0.874)`", "`2.7e-14`"):
        assert s in door, s


# --- planted faults -------------------------------------------------------------------


def test_planted_fault_an_off_by_one_cell_weight_breaks_the_identity(monkeypatch):
    real = LP.cell_weights

    def shifted(N, cells, psi):
        return real(N, cells + 1, psi)

    monkeypatch.setattr(LP, "cell_weights", shifted)
    r = LP.solve(1000, 31, verbose=False)
    assert r["identity"]["sum_w_rel_defect"] > 1e-3


def test_planted_fault_a_conjecture_given_no_moving_constant_loses():
    """The comparison the audit corrected, as a check that it can go either way."""
    inside = _inside()
    logE = np.array([math.log(r["excess"]) for r in inside])
    logN = np.array([math.log(r["N"]) for r in inside])
    logy = np.array([math.log(r["y"]) for r in inside])
    _, rms_free = _lsq([np.ones(len(inside)), logN, -logy], logE)
    _, rms_conj = _lsq([np.ones(len(inside))], logE - logN + 0.5 * logy)
    assert rms_conj > 2.5 * rms_free


def test_planted_fault_a_rational_off_by_one_part_in_a_billion_is_caught():
    from hunts.quotient_exponent import free_support as FS
    r = FS.zero_excess_min_mass(1000)
    bad = dict(r)
    bad["coefficients"] = list(r["coefficients"])
    bad["coefficients"][0] -= 1e-9
    assert not FS.exact_check(bad)["exact_zero_excess"]
    assert Fraction(1, 2) == Fraction(0.5)
