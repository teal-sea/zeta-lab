"""Controls for level 2: projective gap consistency and anti-duplication.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_gap_consistency.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gap_consistency import (  # noqa: E402
    Kernel,
    cap_scan,
    collapse_saturation,
    cross_aggregate,
    decoy_cap,
    dh_rival_two_gap,
    duplication_cheat,
    float_vs_mpmath_defect,
    local_density,
    majorant_control,
    online_cross_mass,
    robust_family_exclusion,
    theta_floor_comparison,
    theta_floor_level2,
)


def test_float_mirror_agrees_with_the_mpmath_closed_form() -> None:
    """The bulk-scan implementation must be the same function."""
    assert float_vs_mpmath_defect() < 1e-5


def test_correlation_is_one_only_at_zero_gap() -> None:
    kernel = Kernel()
    assert abs(kernel.omega(0.0) - 1.0) < 1e-12
    for gap in (0.05 * k for k in range(1, 400)):
        assert abs(kernel.omega(gap)) < 1.0


def test_high_correlation_buys_only_a_small_gap() -> None:
    """LAW G's one-gap marginal, the inverse direction the family needs."""
    kernel = Kernel()
    previous = 0.0
    for level in (0.5, 0.9, 0.99):
        gap = kernel.max_gap_for_correlation(level)
        assert gap > 0
        assert kernel.omega(gap) >= level - 1e-9
        # a stricter correlation demand must buy a strictly smaller gap
        if previous:
            assert gap < previous
        previous = gap


def test_two_gap_word_is_not_freely_declarable() -> None:
    """Independent (multiplicative) outer correlations are refuted."""
    kernel = Kernel()
    assert kernel.two_gap_residual(0.7, 1.3) > 0.1
    # and the true value is the kernel at the summed gap, by construction
    assert abs(kernel.omega(0.7 + 1.3) - kernel.omega(2.0)) < 1e-12


def test_majorants_really_majorise() -> None:
    rec = majorant_control(samples=200)
    assert rec["worst_real_slack"] >= 0
    assert rec["worst_depth_slack"] >= 0


def test_caps_are_never_exceeded_by_real_configurations() -> None:
    rec = cap_scan(trials=15, seed=4)
    assert rec["worst_online_excess"] < 0
    assert rec["worst_cross_excess"] < 0


def test_the_cap_scan_has_power() -> None:
    """A cap planted 4x too small must be violated: the scan is not vacuous."""
    violations, trials = decoy_cap(trials=8, seed=9)
    assert violations >= trials - 1


def test_family_cross_mass_is_attained_only_by_collapse() -> None:
    """max_i R_i -> n-1 as the gaps go to zero, and falls away fast."""
    rows = collapse_saturation(n=50)
    spacing_zero = rows[0]
    assert abs(spacing_zero[1] - 49.0) < 1e-9
    # monotone decay as the configuration spreads
    masses = [row[1] for row in rows]
    assert masses[0] > masses[1] > masses[2] > masses[3]
    assert masses[-1] < 10.0


def test_cross_mass_does_not_grow_with_n_at_fixed_density() -> None:
    """The heart of level 2: n-independence where level 1 was n-extensive."""
    kernel = Kernel()
    masses = []
    for n in (20, 80, 240):
        xs = [j / 3.0 for j in range(n)]  # fixed local density
        mass, _ = cross_aggregate(kernel, xs, gap0=xs[n // 2], depth=0.3)
        masses.append(mass)
    assert max(masses) < 2 * min(masses) + 1.0
    assert max(masses) < 40.0


def test_duplication_cheat_is_rejected_past_the_crossover() -> None:
    rows = duplication_cheat(n_values=(10, 160), depth=0.3, nu=3)
    small, large = rows
    assert not small["rejected_by_level2"]  # honest: below the crossover
    assert large["rejected_by_level2"]
    assert large["margin"] > 0
    assert 10 < small["crossover_n"] < 160


def test_robust_family_exclusion_bounds_the_size() -> None:
    """Declaration-free: it bounds the quantity, so perturbations do not help."""
    kernel = Kernel()
    for nu in (3, 8):
        cap = kernel.kappa(nu)
        rec = robust_family_exclusion(10, nu=nu)
        assert rec["excluded"]
        assert rec["max_labels_allowed"] == cap + 1
        # every member large enough to defeat theta is excluded
        big = robust_family_exclusion(50, nu=nu)
        assert big["excluded"]
        assert big["excess_factor"] > 10


def test_local_density_counts_what_it_claims() -> None:
    assert local_density([0.0, 0.5, 0.9, 3.0]) == 3
    assert local_density([0.0, 2.0, 4.0]) == 1
    assert local_density([1.0] * 7) == 7


def test_theta_floor_is_positive_and_beats_level_one_at_large_bandwidth() -> None:
    assert theta_floor_level2(3) > 0
    rows = theta_floor_comparison(L_values=(8, 24, 32))
    assert all(row["level2"] > 0 for row in rows)
    # level 1 decays exponentially in L, level 2 polynomially: the ratio grows
    ratios = [row["level2"] / row["level1"] for row in rows]
    assert ratios[0] < ratios[1] < ratios[2]
    assert ratios[-1] > 100


def test_online_cross_mass_matches_its_own_definition() -> None:
    kernel = Kernel()
    xs = [0.0, 0.4, 1.1]
    worst, total = online_cross_mass(kernel, xs)
    expected_row0 = kernel.omega(-0.4) ** 2 + kernel.omega(-1.1) ** 2
    assert abs(total - sum(
        kernel.omega(a - b) ** 2 for a in xs for b in xs if a != b
    )) < 1e-12
    assert worst >= expected_row0 - 1e-12


def test_laws_hold_at_the_davenport_heilbronn_depth() -> None:
    rec = dh_rival_two_gap()
    assert abs(rec["depth"] - 0.30851718245663738) < 1e-12
    assert rec["depth_inflation"] > 1.0
    assert rec["cross_cap_at_dh_depth"] > 0
