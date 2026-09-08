"""Pins for DUAL_WITNESS.md: the exact dual witness for T*(31, 1000).

The witness is a basis S of Q_N; the redistributed measure nu = sum_q m_q
(A_S^T)^{-1} A[q,:] has exact rational per-prime coefficients, its moment
identities are checked as exact equalities, its signs by interval
arithmetic, and its gain equals the tight primal certificate's excess.  The
value pinned here is T*(31, 1000) - psi(1000) = 41.2821694429593918...,
which also equals the rational primal upper bound of PR #203 (41.28216944).
"""
from __future__ import annotations

import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HUNT = Path(__file__).resolve().parents[1] / "hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier"


def _load(name: str):
    if str(HUNT) not in sys.path:
        sys.path.insert(0, str(HUNT))
    spec = importlib.util.spec_from_file_location(name, HUNT / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def witness_1000_31():
    dw = _load("dual_witness")
    return dw.witness(1000, 31, dps=60, verbose=False)


def test_exact_witness_at_1000_31(witness_1000_31):
    w = witness_1000_31
    assert w["n_cells"] == 61 and w["n_primes"] == 168
    assert w["basis_is_support"] and len(w["basis_cells"]) == 31
    assert w["moment_identities_exact"]
    assert w["nu_all_nonnegative_by_enclosure"] and w["nu_min_lower_endpoint"] > 1e-3
    assert w["primal_tight_certificate_feasible_on_Q"]
    g_lo, g_hi = float(w["gain_interval"][0]), float(w["gain_interval"][1])
    assert 41.2821694429 < g_lo <= g_hi < 41.2821694430
    assert w["gain_width"] < 1e-50
    # the floating LP objective agrees to solver tolerance, and Codex's
    # rational primal (an upper bound) is not below the exact value
    assert abs(w["lp_gain_float"] - g_lo) < 1e-6
    assert 41.28216944 <= g_hi + 5e-9
    # the emptied cells and their gains (denominator 74 = basis determinant)
    assert w["emptied_cells"] == [7, 11, 13, 14, 18, 20, 23, 31, 32, 34, 52, 62, 111, 125, 142, 200, 250, 333]
    assert all(Fraction(g).denominator in (37, 74) for g in w["emptied_cells_gain_per_unit"].values())
    assert Fraction(w["emptied_cells_gain_per_unit"][200]) == Fraction(141, 74)


def test_exchange_construction_at_1000_31():
    # Construction B (DUAL_WITNESS.md Section 6): greedy prefix-mediated
    # exchanges give an exactly verified witness; three steps already beat
    # every one-sided prefix family, and the two-sided z_q LP reproduces the
    # exact optimum (Lemma 6).
    fm = _load("fake_mass_witness")
    out = fm.construction_a(1000, 31, verbose=False, greedy_steps=3)
    assert out["Q_plus"] == 29 and out["Q_minus_with_mass"] == 0
    assert abs(out["additions_rationalized_gain_float"] - 4 * 0.6931471805599453) < 1e-5
    assert out["additions_rationalized_feasible"] and out["additions_moments_exact"]
    assert all(c["t_max"] == 0.0 and c["binding_s"] == 17 for c in out["constant_parameter"])
    assert out["greedy_moments_exact"] and out["greedy_feasible_by_enclosure"]
    assert len(out["greedy"]) == 3
    assert out["greedy"][0]["a"] == 32 and out["greedy"][0]["b"] == 166
    assert out["greedy_total_gain_float"] > 15.0
    assert abs(out["two_sided_lp_gain_float"] - 41.2821694) < 1e-5


def test_prefix_family_certifies_nothing_at_1000_31():
    pw = _load("prefix_witness")
    out = pw.prefix_family(1000, 31, verbose=False)
    assert out["closed_form_rates_verified_exactly"]
    assert not out["full_transfer_feasible"]
    assert out["positive_gain_cells"] == {}
    assert abs(out["theta_lp_gain_float"]) < 1e-9
    assert out["rationalized_feasible_by_enclosure"] and out["rationalized_moment_identities_exact"]
    assert out["rough_spike_T_gain"] == 0.0
