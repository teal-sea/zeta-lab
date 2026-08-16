"""Controls for `k2_closure` (the k=2 tau-table)."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from k2_closure import (  # noqa: E402
    BUDGET0, P, TABLE_RECORD, cell_eval, far_total, planted_cap_fault,
    reproduce_k1_section7, zone_trade,
)


# -- reproduction: the module must re-derive the k=1 arithmetic -------------

def test_reproduces_k1_section7_window_total_to_all_printed_digits():
    rep = reproduce_k1_section7()
    assert abs(rep["windows"] - 8.1383160e-2) < 5e-10


def test_far_rows_are_conservative_relative_to_section7():
    rep = reproduce_k1_section7()
    assert rep["far"] >= rep["published_far"]


# -- the trade --------------------------------------------------------------

def test_integer_trade_matches_bruteforce():
    for cap, q in ((0.0185, 39 / 10000), (0.0226, 3 / 1000), (2e-4, 1 / 25000)):
        brute = max(cap * m - q * m * (m - 1) for m in range(0, 200))
        assert abs(P(cap, q) - brute) < 1e-15


def test_zone_trade_upper_bounds_single_zone_P():
    """One zone must reduce exactly to P(cap, q_within)."""
    got = zone_trade([0.02], [(12.3, 12.55)])
    import numpy as np
    q = None  # recompute the within-zone floor as the module does
    from k2_closure import _kpair
    q = float(_kpair(np.array([0.25]))[0]) / 200
    assert abs(got - P(0.02, q)) < 1e-12


# -- the table: binding cells stay positive, controls have power ------------

def test_binding_cells_positive_both_cap_modes():
    for ta in (6.32, 12.84, 63.40, 126.04):
        m_signed, _, _, _ = cell_eval(ta, ta + 0.02, signed=True)
        m_unsigned, _, _, _ = cell_eval(ta, ta + 0.02, signed=False)
        assert m_signed > 0, (ta, m_signed)
        assert m_unsigned > 0, (ta, m_unsigned)
        assert m_signed >= m_unsigned - 1e-12  # signed caps never worse


def test_planted_cap_fault_fires_at_1p02():
    rows = dict(planted_cap_fault())
    assert rows[1.0] > 0 and rows[1.02] < 0


def test_far_total_is_small_and_tau_monotone_structure():
    assert 0 < far_total(0.0) < 0.02
    assert far_total(70.0) > far_total(0.0)  # inner side switches on


def test_tail_closed_form_region_margin():
    """tau > 114.2: near <= 2x k=1 rows; verify a representative cell."""
    m, near, c1, kp4 = cell_eval(120.0, 120.02, signed=False)
    assert m > 0.05, m
    assert c1 < 5e-4
