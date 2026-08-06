"""Tests for zeta.factorization — Gate 4 as a decision statistic.

Every literal was measured in this environment before being asserted.

    zeta, L quadratic mod 3/4/5   D ~ 1e-32   (Euler product)
    DH real-part combination      D = 0.825
    Davenport-Heilbronn           D = 0.979   (27th pct of the null)
    null median 1.329, 5-95% band 0.534 - 4.313

The calibration direction matters more than the DH number: a statistic that
failed to return zero for the quadratic characters would be measuring
something other than factorization, so those rows are the real test.
"""

from __future__ import annotations

import numpy as np
import pytest

from zeta.factorization import (
    DEFAULT_N_MAX,
    KAPPA_REF,
    ZERO_THRESHOLD,
    euler_product_panel,
    factorization_defect,
    factorization_report,
    log_derivative_coefficients,
    null_distribution,
    periodic_coefficients,
)


def test_euler_products_score_exactly_zero():
    """The calibration: completely multiplicative coefficients must give 0."""
    panel = euler_product_panel()
    for name, row in panel.items():
        if row["has_euler_product"]:
            assert row["defect"] < ZERO_THRESHOLD, name


def test_non_euler_products_score_order_one():
    panel = euler_product_panel()
    dh = panel["Davenport-Heilbronn"]
    assert dh["defect"] == pytest.approx(0.979, abs=5e-3)
    assert panel["DH real-part combination (c=1/2)"]["defect"] == pytest.approx(
        0.825, abs=5e-3
    )


def test_every_panel_verdict_is_correct():
    panel = euler_product_panel()
    assert all(row["verdict_correct"] for row in panel.values())


def test_zeta_coefficients_reproduce_mangoldt():
    """For a_n = 1 the recursion must return b_n = Lambda(n) exactly."""
    from zeta.explicit import mangoldt

    b = log_derivative_coefficients(periodic_coefficients([1.0]))
    for n in range(2, 40):
        assert b[n] == pytest.approx(mangoldt(n), abs=1e-12)


def test_float_recursion_agrees_with_mpmath_route():
    """Cross-check against the independent mpmath implementation on DH."""
    from zeta.quasicrystal import dh_log_derivative_coefficients

    a = periodic_coefficients([1, KAPPA_REF, -KAPPA_REF, -1, 0], 32)
    b_float = log_derivative_coefficients(a, 32)
    b_mp = dh_log_derivative_coefficients(32)
    for n in range(2, 33):
        assert b_float[n] == pytest.approx(b_mp[n], abs=1e-9)


def test_defect_is_scale_invariant():
    """D must not change when f is multiplied by a constant... which it
    cannot be, since a_1 is normalized to 1 -- but scaling the *character*
    slot must move it, so this pins that D is not trivially constant."""
    d1 = factorization_defect(periodic_coefficients([1, 0.5, -0.5, -1, 0]))
    d2 = factorization_defect(periodic_coefficients([1, 0.1, -0.1, -1, 0]))
    assert d1 != pytest.approx(d2, rel=1e-3)


def test_null_distribution_brackets_dh():
    null = null_distribution(n_samples=200, seed=7)
    assert null["p05"] < 0.979 < null["p95"]
    assert null["median"] > 0.5


def test_report_places_dh_as_typical():
    r = factorization_report(n_samples=200)
    assert r["all_verdicts_correct"]
    assert r["dh_is_typical"] is True
    assert 5.0 < r["dh_percentile_in_null"] < 95.0
    assert "NOT RH" in r["verdict"]


def test_a1_must_be_normalized():
    with pytest.raises(ValueError):
        log_derivative_coefficients(np.zeros(DEFAULT_N_MAX + 1))
