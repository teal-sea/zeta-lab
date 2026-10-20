"""Pins for the 2026-10-19 correction to jensen_clock's Davenport-Heilbronn weight.

`omega_dh` used to drop every theta term below an absolute floor 10^-(dps+8), so
the weight was exactly 0 once e^(-pi x/5) fell below it (hunt #135,
`hunts/jensen_wedge/DH_GATE.md` section 1). It now stops at a relative cutoff.
These tests check the fixed weight against a cutoff-free sum at dps 75, where the
floor mattered, and put the original floor back as a planted fault that must fail
the same checks. The slow tests re-measure, with both cutoffs, the stage
`precision` tables, a flowed table and stage validate's two-quadrature figure (the
one published number the floor set); the last test pins the re-run of stage
`precision` to the digits published before the fix.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/jensen_clock
"""

from __future__ import annotations

import json

import pytest
from mpmath import mp

from hunts.jensen_clock import probe as jc

#: hunt #135's working precision (dps 60 + 15 guard), where DH_GATE.md measured
#: the floor: at dps 75 it cuts at u = 2.859
DPS = 75
M = 400


def omega_ref(x, kap):
    """omega with no stopping rule: the first 30 theta terms. For x >= 1 the
    n = 31 term is below e^(-600) of the leading one."""
    a_pat = (mp.mpf(1), kap, -kap, mp.mpf(-1), mp.mpf(0))
    return mp.fsum(n * a_pat[(n - 1) % 5] * mp.exp(-mp.pi * n * n * x / 5)
                   for n in range(1, 31))


def log_gamma(nodes, m, dps):
    """log gamma(m) = log(m!/(2m)! * sum w u^(2m)): gammas_from_nodes at one index."""
    with mp.workdps(dps):
        return (mp.loggamma(m + 1) - mp.loggamma(2 * m + 1)
                + mp.log(mp.fsum(w * u ** (2 * m) for u, w in nodes)))


@pytest.fixture(scope="module")
def nodes75():
    return {
        "fixed": jc.dh_nodes(DPS),
        "ref": jc.dh_nodes(DPS, omega=omega_ref),
        "floor": jc.dh_nodes(DPS, omega=jc.omega_dh_absolute_floor),
    }


def test_weight_keeps_its_relative_accuracy_past_the_old_floor():
    kap = jc.kappa(DPS)
    with mp.workdps(DPS):
        for u in ("0", "0.5", "2", "2.85", "2.87", "3.62", "4.2"):
            x = mp.exp(2 * mp.mpf(u))
            a, b = jc.omega_dh(x, kap), omega_ref(x, kap)
            assert a > 0, u
            assert abs(a / b - 1) < mp.mpf(10) ** -(DPS - 3), u


def test_the_original_floor_zeroes_the_weight_from_u_2_859():
    """The defect as recorded: the first term passes the floor while
    e^(-pi x/5) >= 10^-(dps+8)."""
    kap = jc.kappa(DPS)
    with mp.workdps(DPS):
        u_cut = mp.log(5 * (DPS + 8) * mp.log(10) / mp.pi) / 2
        assert abs(u_cut - mp.mpf("2.859")) < mp.mpf("5e-4")
        below = jc.omega_dh_absolute_floor(mp.exp(2 * (u_cut - mp.mpf("0.01"))), kap)
        above = jc.omega_dh_absolute_floor(mp.exp(2 * (u_cut + mp.mpf("0.01"))), kap)
        assert below > 0 and above == 0
        assert jc.omega_dh(mp.exp(2 * (u_cut + mp.mpf("0.01"))), kap) > 0


def test_no_default_node_has_zero_weight_at_dps_75(nodes75):
    zeros = {k: sum(1 for _, w in v if w == 0) for k, v in nodes75.items()}
    assert len(nodes75["fixed"]) == 3072
    assert zeros["fixed"] == 0 and zeros["ref"] == 0
    assert zeros["floor"] == 1001  # DH_GATE.md section 1


def test_log_gamma_400_at_dps_75_matches_the_cutoff_free_weight(nodes75):
    """Fails on the original floor: it puts log gamma(400) off by -1.7e-4
    (DH_GATE.md section 1), against a bound of 1e-65 for the fixed weight."""
    bound = mp.mpf(10) ** -65
    ref = log_gamma(nodes75["ref"], M, DPS)
    with mp.workdps(DPS):
        d_fixed = log_gamma(nodes75["fixed"], M, DPS) - ref
        d_floor = log_gamma(nodes75["floor"], M, DPS) - ref
        assert abs(d_fixed) < bound
        # the planted fault: the same check, the original floor, red by 60 orders
        assert abs(d_floor) > 10 ** 60 * bound
        assert abs(d_floor / mp.mpf("-1.7e-4") - 1) < mp.mpf("0.03")


#: DH tables, (dps, jmax, U, segs, gldeg, flow time t), with log10 of the measured
#: max relative difference, original floor against the fix, over j <= jmax (always
#: at j = jmax). The first four are stage `precision`'s; DH_GATE.md checked none of
#: the dps-110 and dps-160 ones. The last two are the default dps-130 table
#: flowed to t = 0.05, above every positive flow time the flowed stages use, and
#: to t = -0.31, where stage shift's E'' re-lifts (DH_GATE.md measured it at t = 0:
#: 1.6e-39).
FLOOR_TABLES = {
    (110, 280, "4.2", 16, 7, "0"): -32.15,
    (130, 320, "4.2", 16, 7, "0"): -39.94,
    (160, 360, "4.5", 20, 7, "0"): -54.77,
    (130, 320, "3.9", 13, 8, "0"): -39.85,
    (130, 328, "4.2", 16, 7, "0.05"): -38.73,
    (130, 328, "4.2", 16, 7, "-0.31"): -39.15,
}


@pytest.mark.slow
@pytest.mark.parametrize("cfg", sorted(FLOOR_TABLES))
def test_jensen_clock_tables_are_untouched_by_the_floor(cfg):
    dps, jmax, U, segs, gldeg, t = cfg
    fixed = jc.gammas_from_nodes(
        jc.dh_nodes(dps, U=U, segs=segs, gldeg=gldeg), jmax, dps, t=t)
    floor = jc.gammas_from_nodes(
        jc.dh_nodes(dps, U=U, segs=segs, gldeg=gldeg, omega=jc.omega_dh_absolute_floor),
        jmax, dps, t=t)
    with mp.workdps(dps):
        worst = max(abs(a / b - 1) for a, b in zip(floor, fixed))
        assert abs(mp.log10(worst) - FLOOR_TABLES[cfg]) < 0.05


@pytest.mark.slow
def test_validate_quadrature_agreement_was_the_floor():
    """Stage validate's two-quadrature check on the DH table (dps 130, j <= 320)
    published 2.63e-41. That figure is the floor: with it put back the check
    reproduces 2.63e-41; with the fix the two node sets agree at working
    precision (3.96e-130 measured)."""
    def agreement(omega):
        G = jc.gammas_from_nodes(jc.dh_nodes(jc.DPS, omega=omega), jc.JMAX_DEFAULT, jc.DPS)
        G2 = jc.gammas_from_nodes(
            jc.dh_nodes(jc.DPS, U="3.9", segs=13, gldeg=8, omega=omega),
            jc.JMAX_DEFAULT, jc.DPS)
        with mp.workdps(jc.DPS):
            return max(abs(a - b) / abs(a) for a, b in zip(G, G2) if a != 0)

    with mp.workdps(jc.DPS):
        assert agreement(jc.omega_dh) < mp.mpf(10) ** -125
        assert abs(mp.log10(agreement(jc.omega_dh_absolute_floor)) + mp.mpf("40.580")) < 0.01


#: stage `precision` as published before the fix (dps, U) -> (root Im at
#: d = 30000, d*), and its spread; the committed results.json is the re-run
PUBLISHED_PRECISION = {
    (110, "4.2"): ("28.479462237892980213", "20786.973402454"),
    (130, "4.2"): ("28.482325358286664218", "20785.132775918"),
    (160, "4.5"): ("28.482325358286664218", "20785.132775918"),
    (130, "3.9"): ("28.482325358286664218", "20785.132775918"),
}


def test_precision_stage_rerun_reproduces_the_published_digits():
    rec = json.loads(open(jc.RESULTS).read())["precision"]
    assert rec["dstar_max_rel_spread"] == "8.86e-5"
    got = {(r["dps"], r["U"]): (r["root_im_at_d30000"], r["dstar"]) for r in rec["runs"]}
    assert got == PUBLISHED_PRECISION
    assert rec["omega_dh_cutoff"] == "relative"


def test_flowed_stages_rerun_identical():
    """The three stages PR #315 left unrun (additivity, shift with its
    shift_ladder, additivity2), re-run on GitHub Actions with both fixes and
    compared field by field with results.json (RESULTS.md, "Correction")."""
    path = jc.os.path.join(jc.HERE, "rerun_2026-10-19.json")
    with open(path, encoding="utf-8") as fh:
        rec = json.load(fh)
    assert rec["omega_dh_cutoff"] == "relative"
    assert sorted(rec["stages"]) == ["additivity", "additivity2", "shift", "shift_ladder"]
    assert rec["totals"] == {"stages": 4, "fields_compared": 71, "identical": 71,
                             "changed": 0, "missing": 0, "added": 0}
