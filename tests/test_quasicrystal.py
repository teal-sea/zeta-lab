"""Tests for zeta.quasicrystal — atomic structure of the zero measure.

Every literal was measured in this environment before being asserted.

The story in test order:

1. The atom constant c = −A/(2√(2π)) is *derived* from the explicit formula
   and lands within a few percent of measurement across taper widths
   (measured ratio 0.94–0.98; the shortfall is the finite zero list).
2. Atom heights follow Λ(n)/√n with ~3% spread.
3. The Euler-product signature: with 1000 zeros, prime-power atoms have
   median |Z| = 60.1 against 2.2 at composite non-prime-powers and 0.90
   ambient background — 26.8× separation.
4. The DH log-derivative recursion is validated against an independent
   series-ratio route, with the defect *shrinking* under truncation
   (2.3e-6 at n_max=200 → 7.1e-10 at 1600).  A flat defect would mean the
   reference is broken — which is exactly what mp.diff on dh_f produces,
   pinned here as a regression so no one reintroduces it.
5. The battery verdict: this gate separates ζ from Davenport–Heilbronn.
   b₆, b₁₄, b₂₁, b₂₆ are all loud where ζ is exactly silent.
"""

from __future__ import annotations

import numpy as np
import pytest

from zeta.explicit import first_zeros
from zeta.quasicrystal import (
    COMPOSITES,
    PRIME_POWERS,
    atom_table,
    crystallinity_battery,
    dh_dirichlet_defect,
    dh_log_derivative_coefficients,
    euler_signature_report,
    predicted_atom_constant,
    zero_measure_transform,
)


@pytest.fixture(scope="module")
def gammas():
    return first_zeros(1000)


def test_predicted_constant_matches_measurement(gammas):
    tab = atom_table(gammas, gammas[-1] / 3.0)
    assert 0.93 < tab["ratio_mean"] < 1.0      # measured 0.9609
    assert tab["ratio_spread"] < 0.06          # measured 0.0295


def test_atom_constant_scales_with_taper(gammas):
    """c ∝ A is a derivation, not a fit: halving A must halve the atoms."""
    A1 = gammas[-1] / 3.0
    A2 = A1 / 2.0
    assert predicted_atom_constant(A2) == pytest.approx(
        predicted_atom_constant(A1) / 2.0
    )
    r1 = atom_table(gammas, A1)["ratio_mean"]
    r2 = atom_table(gammas, A2)["ratio_mean"]
    # both routes track the prediction, so the ratios stay near each other
    assert abs(r1 - r2) < 0.06


def test_euler_product_signature(gammas):
    rep = euler_signature_report(gammas)
    assert rep["separation"] > 10.0            # measured 26.8
    assert rep["prime_power_median"] > 40.0    # measured 60.1
    # composites are quiet in absolute terms — within a few x of background
    assert rep["composite_over_background"] < 5.0


def test_background_is_flat_and_small(gammas):
    Z = zero_measure_transform(gammas, gammas[-1] / 3.0)
    # a prime-power atom towers over the largest background excursion
    atom = abs(float(Z(np.log(2))[0]))
    assert atom > 30.0
    rep = euler_signature_report(gammas)
    assert rep["background_p99"] < atom / 10.0


def test_dh_recursion_validated_by_independent_route():
    """Defect must SHRINK with truncation — that is what makes it a check."""
    d200 = dh_dirichlet_defect(3.0, 200)
    d800 = dh_dirichlet_defect(3.0, 800)
    assert d200 < 1e-4
    assert d800 < d200 / 10.0


def test_mp_diff_on_dh_f_is_the_documented_trap():
    """Regression: the obvious reference silently returns exactly zero."""
    from mpmath import mp

    from zeta.epstein import dh_f

    with mp.workdps(30):
        bad = mp.diff(lambda z: mp.log(dh_f(z, dps=30)), mp.mpf(3))
    assert bad == 0  # dh_f is bit-constant across mp.diff's step


def test_dh_coefficients_loud_where_zeta_is_silent():
    from zeta.explicit import mangoldt

    b = dh_log_derivative_coefficients(32)
    loud = [n for n in COMPOSITES if n < len(b) and abs(b[n]) > 0.5]
    assert len(loud) >= 3
    for n in loud:
        assert mangoldt(n) == 0.0   # zeta is exactly silent here
    # the specific loudest ones, pinned
    assert b[6] == pytest.approx(1.936, abs=2e-3)
    assert b[14] == pytest.approx(-2.852, abs=2e-3)
    assert b[21] == pytest.approx(3.290, abs=2e-3)


def test_prime_powers_and_composites_are_disjoint_classes():
    from zeta.explicit import mangoldt

    assert all(mangoldt(n) > 0 for n in PRIME_POWERS)
    assert all(mangoldt(n) == 0.0 for n in COMPOSITES)


@pytest.mark.slow
def test_battery_separates_zeta_from_dh():
    r = crystallinity_battery()
    assert r["separates"] is True
    assert r["zeta_euler_signature"]["separation"] > 10.0
    assert r["dh_composite_nonzero_count"] >= 3
    assert "NOT RH" in r["verdict"]
