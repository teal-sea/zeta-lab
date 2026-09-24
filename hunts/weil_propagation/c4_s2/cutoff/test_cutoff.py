"""Pins every number stated in cutoff/RESULTS.md.

Run from the worktree root:
PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 \
    hunts/weil_propagation/c4_s2/cutoff
"""

from __future__ import annotations

import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import pytest
import sympy as sp
from mpmath import mp

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import cutoff as C  # noqa: E402

JSON_PATH = HERE / "cutoff_cells.json"

# Measured eigenvalue counts of the shift form H on the shared basis at
# dps 40 (cutoff_cells.json); RESULTS.md s5 table.  (c, N): (n_above_quarter,
# n_below_minus_quarter).
COUNTS = {
    (2.2, 8): (2, 2),
    (2.2, 16): (3, 4),
    (2.2, 32): (7, 8),
    (2.5, 8): (4, 4),
    (2.5, 16): (8, 8),
    (2.5, 32): (15, 16),
    (2.9, 8): (5, 6),
    (2.9, 16): (11, 12),
    (2.9, 32): (23, 22),
}


# --- s1: local facts at p = 2, exact ---------------------------------------


@pytest.mark.parametrize("K", [3, 5])
def test_two_adic_local_facts_exact(K):
    f = C.two_adic_facts(K)
    assert f["fourier_unitary"]
    assert f["closed_time_is_projection"] and f["closed_freq_is_projection"]
    # theory s7.3 item 2 says these are the same projection: they are not
    assert f["closed_time_equals_freq"] is False
    assert f["closed_time_freq_commute"] is True
    assert f["closed_product_rank"] == 1
    assert f["closed_product_range_is_1_Z2"]
    assert f["closed_joint_kernel_dim"] == 0
    assert f["open_time_freq_commute"] is False
    assert f["open_joint_kernel_dim"] == 1
    assert f["open_joint_kernel_is_sigma2"]
    assert f["sigma2_fourier_fixed"]
    assert f["sigma2_norm_sq"] == "3/4"


# --- s1: Gamma_S-invariance, exact ------------------------------------------


def test_product_ball_not_gamma_invariant_module_ball_is():
    lam = Fraction(1)
    x = (Fraction(3, 4), 0)
    x2 = C.act(*x, 1)
    assert C.in_product_ball(*x, lam) and not C.in_product_ball(*x2, lam)
    assert C.module(*x) == C.module(*x2) == Fraction(3, 4)
    for n in range(-5, 6):
        y = C.act(*x, n)
        assert C.in_module_ball(*y, lam)


@pytest.mark.parametrize(
    "pt, count",
    [
        ((Fraction(3, 4), 0), 1),
        ((Fraction(1, 10), 3), 7),
        ((Fraction(7, 3), -2), 0),
        ((Fraction(5, 1), 4), 2),
        ((Fraction(1, 1000), -1), 9),
    ],
)
def test_gamma_sum_of_product_ball_is_log_of_module(pt, count):
    lam = Fraction(1)
    assert C.orbit_count_product_ball(*pt, lam) == count
    assert C.orbit_count_formula(*pt, lam) == count
    # saturation of the product ball is the module ball
    assert (count > 0) == C.in_module_ball(*pt, lam)


# --- s2: eta_S and theta_S, two routes --------------------------------------


# Relative deviation between the two routes, measured at dps 30 (JSON):
# s: (eta, theta).  The quadrature of the oscillatory Mellin integral is what
# limits both; tolerances are 100x the measured value.
ROUTE_DEV = {
    0.0: (2.7e-22, 6.9e-32),
    1.3: (3.7e-21, 1.9e-31),
    5.7: (1.7e-17, 1.6e-31),
    14.1347: (1.5e-11, 2.3e-15),
}


@pytest.mark.parametrize("s", [0.0, 5.7])
def test_eta_theta_mellin_two_routes(s):
    (row,) = C.eta_theta_check(s_list=(s,), dps=30)
    eta_tol, theta_tol = (100 * x for x in ROUTE_DEV[s])
    assert row["eta_rel_dev"] < eta_tol
    assert row["theta_rel_dev"] < theta_tol
    # theta / eta is the positive multiplier m(s) = |1 - 2^(-1/2-is)|^2
    r = row["ratio_theta_over_eta"]
    assert abs(r.imag) < eta_tol
    assert abs(r.real - row["m_of_s"]) < eta_tol * 10


def test_multiplier_range_and_kappa():
    with mp.workdps(30):
        lo = C.m_of_s(0)
        hi = C.m_of_s(mp.pi / mp.log(2))
        assert abs(lo - (mp.mpf(3) / 2 - mp.sqrt(2))) < mp.mpf(10) ** -28
        assert abs(hi - (mp.mpf(3) / 2 + mp.sqrt(2))) < mp.mpf(10) ** -28
        grid = [C.m_of_s(mp.mpf(k) / 50) for k in range(0, 1000)]
        assert min(grid) >= lo - mp.mpf(10) ** -28
        assert max(grid) <= hi + mp.mpf(10) ** -28
        assert abs(lo - mp.mpf("0.0857864376269049512")) < mp.mpf(10) ** -18
        assert abs(hi - mp.mpf("2.9142135623730950488")) < mp.mpf(10) ** -18
    k = C.kappa_exact()
    assert sp.simplify(k - (17 + 12 * sp.sqrt(2))) == 0
    assert abs(float(k) - 33.970562748477) < 1e-9


# --- s4: comparison lemma, finite-dimensional sanity check -----------------


def test_comparison_lemma_in_finite_dimensions():
    r = C.comparison_lemma_trials(trials=400)
    assert r["ratio_min"] >= 1 / r["kappa"]
    assert r["ratio_max"] <= r["kappa"]


# --- s5: the atom form on the shared basis ---------------------------------


@pytest.mark.parametrize("c", C.CELLS_C)
def test_atom_matrix_two_routes(c):
    # closed form against weil_trunc/galerkin.py's prime block; measured 8.6e-41 at dps 40
    assert C.two_route_atom_dev(c, 8, dps=40) < 1e-37


@pytest.mark.parametrize("c", C.CELLS_C)
@pytest.mark.parametrize("N", [8, 16])
def test_shift_form_counts_live(c, N):
    r = C.shift_form_spectrum(c, N, dps=40)
    assert (r["n_above_quarter"], r["n_below_minus_quarter"]) == COUNTS[(c, N)]
    assert 0.49 < r["max_eig"] <= 0.5 + 1e-30
    assert -0.5 - 1e-30 <= r["min_eig"] < -0.49


@pytest.mark.parametrize("c", C.CELLS_C)
def test_shift_form_counts_stable_in_dps(c):
    # the counts are integers; recomputing at dps 25 must not move them
    r = C.shift_form_spectrum(c, 16, dps=25)
    assert (r["n_above_quarter"], r["n_below_minus_quarter"]) == COUNTS[(c, 16)]


def test_shift_form_counts_json_all_cells():
    data = json.loads(JSON_PATH.read_text())
    rows = {(r["c"], r["N"]): r for r in data["shift_form_cells"]}
    assert set(rows) == set(COUNTS)
    for key, (up, dn) in COUNTS.items():
        r = rows[key]
        assert r["dps"] == 40
        assert (r["n_above_quarter"], r["n_below_minus_quarter"]) == (up, dn)
        # counts track (2N+1)(l - log 2)/l to within 1
        assert abs(up - r["collar_fraction_times_dim"]) <= 1.0
    # growth in N at every c
    for c in C.CELLS_C:
        assert COUNTS[(c, 8)][0] < COUNTS[(c, 16)][0] < COUNTS[(c, 32)][0]


@pytest.mark.parametrize("c", C.CELLS_C)
def test_shift_form_counts_live_N32(c):
    r = C.shift_form_spectrum(c, 32, dps=40)
    assert (r["n_above_quarter"], r["n_below_minus_quarter"]) == COUNTS[(c, 32)]


def test_json_matches_live_small_parts():
    data = json.loads(JSON_PATH.read_text())
    assert data["kappa_exact"] == str(C.kappa_exact())
    assert data["two_adic_facts"] == C.two_adic_facts(5)
    for row in data["eta_theta_check"]:
        eta_tol, theta_tol = (1.5 * x for x in ROUTE_DEV[row["s"]])
        assert row["eta_rel_dev"] < eta_tol
        assert row["theta_rel_dev"] < theta_tol
    for v in data["atom_two_route_dev"].values():
        assert v < 1e-37
    assert math.isclose(data["comparison_lemma_trials"]["kappa"], 33.97056274847714, rel_tol=1e-12)
