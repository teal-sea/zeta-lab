"""Controls for the level-7 v-cell joint cap and the reconnect reading.

Run:  .venv/bin/python -m pytest -q -o addopts='' \
          hunts/frontier_math/test_v_certificate.py     (~4 min)
"""

from __future__ import annotations

import cmath
import math
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from v_certificate import VCertificate, chain_dp, greedy_joint_profit  # noqa: E402

PINCH = [(k / 1.5, 0.49) for k in range(15)]


@pytest.fixture(scope="module")
def vc():
    return VCertificate()


@pytest.fixture(scope="module")
def pinch_verdict(vc):
    return vc.verdict(PINCH, 0.02)


def test_law_n_floor_holds_on_random_windowed_configs():
    rng = random.Random(11)
    for _ in range(300):
        S = rng.uniform(3, 40)
        n = rng.randint(1, 50)
        xs = [rng.uniform(0.0, S) for _ in range(n)]
        v = rng.uniform(0.0, math.pi / S)
        F = abs(sum(cmath.exp(1j * x * v) for x in xs))
        assert F >= n * math.cos(v * S / 2) - 1e-9


def test_safe_cell_cross_is_nonnegative():
    rng = random.Random(13)
    for _ in range(300):
        S = rng.uniform(3, 40)
        xs = [rng.uniform(0.0, S) for _ in range(rng.randint(1, 25))]
        prs = [(rng.uniform(0.0, S), rng.uniform(0.01, 0.49))
               for _ in range(rng.randint(1, 12))]
        v = rng.uniform(0.0, math.pi / (2 * S))
        F_on = sum(cmath.exp(1j * x * v) for x in xs)
        F_p = sum(cmath.exp(1j * t * v) * 2 * math.cosh(y * v)
                  for t, y in prs)
        assert 2 * (F_on * F_p.conjugate()).real >= -1e-9


def test_chain_dp_reduces_to_per_cell_bound_when_uncoupled():
    cells = [0.5, 1.2, 0.0, 2.0]
    cK1 = 0.4
    # cK2 = 0: independent cells, exact optimum per cell: max_n nF - cK1 n(n-1)
    def per_cell(F):
        best = 0.0
        for n in range(30):
            best = max(best, n * F - cK1 * n * (n - 1))
        return best
    assert abs(chain_dp(cells, cK1, 0.0) - sum(per_cell(F) for F in cells)) < 1e-12


def test_law_m_mean_is_taper_free(vc):
    exact = 2 * vc.fb.law_m_exact()
    for v1 in (0.6, 1.4):
        tot, g, h = 0.0, -300.0, 0.05
        while g < 300.0:
            tot += vc.W_I(g, 0.3, v1) * h
            g += h
        assert abs(tot - exact) < 5e-3


def test_pinch_budget_matches_level6b(pinch_verdict):
    # slack 511.26, T -470.16 at the level-6b pinch (nu_p=1.5, y=0.49)
    assert abs(pinch_verdict["slack_total"] - 511.26) < 0.5
    assert abs(pinch_verdict["t_signed"] - (-470.16)) < 0.5


def test_joint_cap_closes_the_pinch(pinch_verdict):
    assert pinch_verdict["closes"], pinch_verdict


def test_joint_cap_dominates_greedy_joint_adversary(vc, pinch_verdict):
    greedy = greedy_joint_profit(vc, PINCH, 0.02)
    assert greedy <= pinch_verdict["j_cap"] + 1e-9


def test_direct_route_closes_the_former_seam():
    """The corrected joint-field DP closes nu_p in [1.1, 1.4] deep,
    where both the v-route and the separable accounting fail."""
    vc = VCertificate()
    for nu in (1.2, 1.3):
        pairs = [(k / nu, 0.49) for k in range(int(10 * nu))]
        rec = vc.verdict(pairs, 0.02)
        assert rec["closes"], (nu, rec["margin"])
        assert rec["detail"]["route"] == "direct"


def test_per_pair_clipping_is_the_recorded_near_miss():
    """Positive part must be of the JOINT field: clipping per pair
    discards the coincident-pair shielding and inflates the field by an
    order of magnitude at the seam (the separable accounting's ghost)."""
    vc = VCertificate()
    pe = vc.pe
    pairs = [(k / 1.3, 0.49) for k in range(13)]
    g = 4.65
    joint = max(0.0, sum(-2 * pe.W(g - t, y) for t, y in pairs))
    per_pair = sum(max(0.0, -2 * pe.W(g - t, y)) for t, y in pairs)
    assert joint == 0.0
    assert per_pair > 4.0


def test_extended_greedy_stays_inside_the_seam_budget():
    """The seam kill control: even the extended adversary (wider range,
    denser packing) extracts far less than the budget where both bounds
    fail — the hole is bound looseness, not adversary strength."""
    vc = VCertificate()
    pairs = [(k / 1.3, 0.49) for k in range(13)]
    pe = vc.pe
    budget = sum(pe.slack(y) for _, y in pairs)
    t_signed = 0.0
    for i, (t1, y1) in enumerate(pairs):
        for j in range(i + 1, len(pairs)):
            t2, y2 = pairs[j]
            t_signed += 2 * pe.T(t1 - t2, y1, y2)
    budget += t_signed
    profit = greedy_joint_profit(vc, pairs, 0.02, kmax=60,
                                 halfext=6.0, minsp=0.0625)
    assert profit < budget / 3, (profit, budget)


def test_theta_one_makes_the_cap_infinite(vc):
    assert not math.isfinite(vc.joint_cap(PINCH, theta=1.0))


def test_leak_term_shrinks_with_kappa(vc):
    # LAW N economics: a wider window (larger S) weakens the floor
    k_narrow = vc.kappa00(12.0, 1.4)
    k_wide = vc.kappa00(30.0, 1.4)
    assert k_narrow > k_wide > 0


def test_reconnect_controls():
    from reconnect import (  # noqa: E402
        CG_FLOOR, H_PINNED, HardenedGTable, first_reading,
    )
    from cg_transplant import CG_EDGES, CG_NU, bucket_floor  # noqa: E402

    table = HardenedGTable(n=150001)
    fl = bucket_floor(CG_NU, *CG_EDGES, table=table)
    # one-sided must not exceed the printed sampled value
    assert 0 < fl <= CG_FLOOR + 1e-12
    reading = first_reading(verbose=False)
    assert reading["lesion"] < 1e-9
    assert reading["candidate"] == pytest.approx(
        H_PINNED + 2 * reading["theta_full"] * reading["floor_one_sided"]
    )
    # the ladder's top two rungs agree (resolution-stable floor)
    vals = list(reading["ladder"].values())
    assert abs(vals[-1] - vals[-2]) < 1e-9


def test_hardened_direct_phi2_prime_and_field():
    """The arb pass's Phi2' ball must match a finite difference, and the
    hardened joint-field cells must majorise the float field tightly."""
    import dataclasses

    from flint import acb, arb

    from gap_consistency import _phi2_hat_f
    from hardened_direct import EnclosedDirect

    ed = EnclosedDirect()
    z0 = 0.7 + 0.49j
    fd = (_phi2_hat_f(z0 + 1e-6, 8.0, 1.0)
          - _phi2_hat_f(z0 - 1e-6, 8.0, 1.0)) / 2e-6
    _, pp = ed.phi2_pair_acb(acb(arb(0.7), arb(0.49)))
    assert abs(float(pp.real.mid()) - fd.real) < 1e-5
    assert abs(float(pp.imag.mid()) - fd.imag) < 1e-5
    assert float(pp.real.rad()) < 1e-12

    pe = VCertificate().pe
    pairs = [(k / 1.3, 0.49) for k in range(5)]
    cells = ed.field_cells(pairs, -2.0, 2.0)
    for i, cell_up in enumerate(cells):
        g = -2.0 + (i + 0.5) * ed.fine
        f_float = max(0.0, sum(-2 * pe.W(g - t, y) for t, y in pairs))
        assert cell_up >= f_float - 1e-9
    assert max(cells) < max(
        max(0.0, sum(-2 * pe.W(-2.0 + (i + 0.5) * ed.fine - t, y)
                     for t, y in pairs))
        for i in range(len(cells))
    ) + 0.2  # tight, not blanket


def test_hardened_direct_closes_a_former_hole_config():
    """One hardened end-to-end verdict (coarser fine grid for speed:
    coarser cells only enlarge the remainder, so the run stays one-sided)."""
    import dataclasses

    from hardened_direct import EnclosedDirect

    ed = dataclasses.replace(EnclosedDirect(), fine=0.02)
    pairs = [(k / 0.75, 0.49) for k in range(7)]
    rec = ed.verdict(pairs, 0.02)
    assert rec["closes"], rec


def test_eta_bracket_is_conservative():
    from full_ladder_scan import eta_for_cell  # noqa: E402
    etas = {0.01: 0.0, 0.05: 0.28, 0.15: 0.30}
    # a cell inside [0.01, 0.05] must read the 0.05 eta, not the 0.01 one
    assert eta_for_cell(etas, 0.02, 0.03) == 0.28
    # a cell spanning past 0.05 must pick up the deeper bracket
    assert eta_for_cell(etas, 0.04, 0.06) == 0.30
