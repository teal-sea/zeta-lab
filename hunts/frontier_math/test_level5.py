"""Controls for level 5: the enclosure pass and the multi-pair energy.

Run from the repo root:

    .venv/bin/python -m pytest -q -o addopts='' \
        hunts/frontier_math/test_level5.py
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from counting_bound import CountingBound  # noqa: E402
from enclosure_pass import EnclosedBound, f_lo, f_up  # noqa: E402
from pair_energy import PairEnergy, law_l_check  # noqa: E402

EB = EnclosedBound()
CB = CountingBound()
PE = PairEnergy()


# -- gate 1: the enclosure pass ----------------------------------------------


def test_ball_kernel_agrees_with_the_float_kernel() -> None:
    from flint import acb, arb

    for g, y in ((0.75, 0.3), (7.3, 0.45), (0.1, 0.002)):
        v = EB.phi2_acb(acb(arb(g), arb(y)))
        f = CB.phi2(complex(g, y))
        assert abs(float(v.real.mid()) - f.real) < 1e-9
        assert abs(float(v.imag.mid()) - f.imag) < 1e-9
        assert float(v.real.rad()) < 1e-15


def test_directed_endpoints_bracket_the_midpoint() -> None:
    from flint import arb

    x = arb("1.5", "1e-20")
    assert f_lo(x) < 1.5 < f_up(x)


def test_aL_is_exact_and_matches_float() -> None:
    assert abs(float(EB.aL_ball().mid()) - CB.aL) < 1e-9
    assert float(EB.aL_ball().rad()) < 1e-30


def test_hardened_quantities_are_on_the_safe_side() -> None:
    """Hardened slack below float slack; hardened sups above float f+."""
    for y in (0.1, 0.3, 0.45):
        assert EB.slack(y) <= CB.slack(y) + 1e-12
        assert EB.K_delta(0.3) <= CB.K_delta(0.3) + 1e-12
    # hardened sups majorise the true damage (coarser grid, bigger inflation)
    y = 0.3
    sups = EB.fine_sups(y, y * 1.001)
    from theta_recovery import Recovery

    rec = Recovery()
    g = -EB.fine_g_max + 1e-9
    while g < EB.fine_g_max:
        f_true = 2 * max(0.0, -rec.W(g, y))
        i = min(int((g + EB.fine_g_max) / EB.fine_step), len(sups) - 1)
        assert sups[i] >= f_true - 1e-9
        g += 0.0317


def test_hardened_scan_secures_a_positive_theta_on_probe_cells() -> None:
    """Representative depth cells: hardened cap <= hardened slack at theta 0.1."""
    for y in (0.05, 0.25, 0.45):
        y2 = y * 1.01
        sups = EB.fine_sups(y, y2)
        cap = min(
            EB.lambda_bar_from_sups(0.1, sups, y2, d) for d in EB.delta_choices
        )
        assert cap <= EB.slack(y), (y, cap, EB.slack(y))


# -- gate 2: LAW L and the multi-pair energy ----------------------------------


def test_law_l_is_exact() -> None:
    assert law_l_check(PE) < 1e-12


def test_difference_layer_is_nonnegative() -> None:
    for k in range(1, 200):
        assert PE.W(0.08 * k, 0.0) >= -1e-9


def test_shallow_shallow_negativity_is_depth_scaled() -> None:
    """|T|_- at equal shallow depths is inside the (1+m0) sigma^2(2y) envelope."""
    for y in (0.02, 0.05, 0.1):
        worst = min(PE.T(0.05 * k, y, y) for k in range(1, 320))
        envelope = -(1.2138) * PE.sigma_sq(2 * y)
        assert worst >= envelope - 1e-9
        assert worst < 0  # the negativity is real, just scaled


def test_split_weights_vanish_for_the_shallow_participant() -> None:
    w_shallow, w_deep = PE.split_weights(0.01, 0.45)
    assert w_shallow < 0.02
    assert abs(w_shallow + w_deep - 1) < 1e-12


def test_energy_decomposition_matches_brute_force() -> None:
    """LAW K + LAW L reassemble the off-line Frobenius energy."""
    pairs = [(0.0, 0.3), (0.9, 0.2), (2.2, 0.45)]
    rec = PE.total_energy(pairs)
    brute = 0.0
    for i, (t1, y1) in enumerate(pairs):
        for j, (t2, y2) in enumerate(pairs):
            if i == j:
                s2 = PE.sigma_sq(y1)
                brute += 4 + 8 * s2 + 8 * s2 * s2  # LAW K self term
            else:
                brute += PE.rec.pair_pair(t1 - t2, y1, y2)
    assert abs(brute - (rec["baseline"] + rec["slack_total"] + rec["cross_total"])) < 1e-9


def test_eta_below_one_at_unit_pair_density() -> None:
    table = PE.eta_table(nu_values=(1.0,))
    assert 0 < table[1.0] < 1


def test_pairwise_charging_fails_at_dense_packing() -> None:
    """The named level-6 kill control: eta blows past 1 at nu_p = 2."""
    table = PE.eta_table(nu_values=(2.0,), y_grid=(0.25, 0.35, 0.45))
    assert table[2.0] > 1


def test_collective_energy_survives_where_pairwise_charging_fails() -> None:
    """Scheme failure, not mathematics failure: total energy stays positive."""
    for nu_p in (1.0, 2.0):
        for name, row in PE.collective_battery(nu_p).items():
            assert row["survives"], (nu_p, name)
            assert row["cross_over_slack"] > -1


def test_assembly_overdraw_is_positive_and_quantified() -> None:
    """OUTCOME B: the combined per-pair budget overdraws at every depth."""
    caps = {0.05: 0.90, 0.25: 0.92, 0.45: 0.85}
    rows = PE.assembly_audit(
        lambda y: caps[min(caps, key=lambda k: abs(k - y))], nu_p=1.0
    )
    overdraws = [row["overdraw"] for row in rows.values()]
    assert all(o > 0 for o in overdraws)
    assert max(overdraws) < 0.5  # the deficit is bounded, not catastrophic
