"""Pins for the 2026-10-19 correction to flow_repair's Davenport-Heilbronn weight.

`omega_dh` used to drop every theta term below an absolute floor 10^-(dps+8), so
the weight was exactly 0 once e^(-pi x/5) fell below it, the defect hunt #135's
gate found in `hunts/jensen_clock` (`hunts/jensen_wedge/DH_GATE.md` section 1).
It now stops at a relative cutoff. These tests check the fixed weight against a
cutoff-free sum where the floor bites (past the cut at the pair-1 flow's
precision, and in a high moment at dps 75) and put the original floor back as a
planted fault that must fail the same checks. They also pin what NOTES.md's
correction says about this hunt: every flow rule it built stops short of the old
cut, and the one published number that moved, the Phi evenness defect, is
rounding at dps 50 under either cutoff.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/flow_repair
"""

from __future__ import annotations

import json
import os
from types import SimpleNamespace

from mpmath import mp

from hunts.flow_repair import probe as fr
from zeta.epstein import kappa

#: the pair-1 flow's working precision (site dps 54) plus DHFlow's 10 guard
#: digits, the ambient precision at which its weight is evaluated
P_PAIR1 = 64

#: every DHFlow precision a published flow_repair stage used: validate (40),
#: precision (44, 54, 70; 54 is also pair1 and lesions), survey pairs 2 to 9
STAGE_DPS = (40, 44, 54, 70, 63, 81, 85, 107, 134, 137, 150, 165)


def omega_ref(x, kap):
    """omega with no stopping rule: the first 30 theta terms. For x >= 1 the
    n = 31 term is below e^(-600) of the leading one."""
    a_pat = (mp.mpf(1), kap, -kap, mp.mpf(-1), mp.mpf(0))
    return mp.fsum(n * a_pat[(n - 1) % 5] * mp.exp(-mp.pi * n * n * x / 5)
                   for n in range(1, 31))


def u_cut(P):
    """Where the original floor zeroes the weight at ambient precision P:
    e^(-pi x/5) = 10^-(P+8) with x = e^(2u)."""
    return mp.log(5 * (P + 8) * mp.log(10) / mp.pi) / 2


def test_weight_keeps_its_relative_accuracy_past_the_old_floor():
    """Green with the fix; the same check on the original floor fails at
    every u past the cut, where it returns exactly 0."""
    with mp.workdps(P_PAIR1):
        kap = kappa(P_PAIR1)
        cut = u_cut(P_PAIR1)
        assert abs(cut - mp.mpf("2.7877")) < mp.mpf("1e-4")
        past = 0
        for u in ("0", "0.5", "2", "2.78", "2.79", "2.9", "3.3", "4.2"):
            x = mp.exp(2 * mp.mpf(u))
            ref = omega_ref(x, kap)
            fixed = fr.omega_dh(x, kap)
            assert fixed > 0, u
            assert abs(fixed / ref - 1) < mp.mpf(10) ** -(P_PAIR1 - 3), u
            floor = fr.omega_dh_absolute_floor(x, kap)
            if mp.mpf(u) > cut:
                past += 1
                assert floor == 0, u  # the planted fault: red by 100%
            else:
                assert abs(floor / ref - 1) < mp.mpf(10) ** -(P_PAIR1 - 30), u
        assert past == 4


def test_the_original_floor_zeroes_the_weight_from_the_cut():
    """The defect as recorded: the first term passes the floor while
    e^(-pi x/5) >= 10^-(P+8)."""
    with mp.workdps(P_PAIR1):
        kap = kappa(P_PAIR1)
        cut = u_cut(P_PAIR1)
        below = fr.omega_dh_absolute_floor(mp.exp(2 * (cut - mp.mpf("0.001"))), kap)
        above = fr.omega_dh_absolute_floor(mp.exp(2 * (cut + mp.mpf("0.001"))), kap)
        assert below > 0 and above == 0
        assert fr.omega_dh(mp.exp(2 * (cut + mp.mpf("0.001"))), kap) > 0


def test_a_high_moment_of_the_weight_where_the_floor_bites():
    """log of int_0^4.2 u^800 Phi_DH(u) du at dps 75, hunt #135's parameter
    (its log gamma(400) is this up to an exact constant). The original floor
    puts it off by about 1.7e-4 (DH_GATE.md section 1); the fix agrees with
    the cutoff-free weight below 1e-60."""
    dps, m, U, panels = 75, 400, mp.mpf("4.2"), 16
    xs, ws = fr._gauss_legendre(24, dps)
    with mp.workdps(dps):
        kap = kappa(dps)
        nodes = []
        for p in range(panels):
            a, h = U * p / panels, U / panels
            nodes += [(a + h * (x + 1) / 2, w * h / 2) for x, w in zip(xs, ws)]

        def log_moment(omega):
            return mp.log(mp.fsum(w * u ** (2 * m) * fr.phi_dh_raw(u, kap, omega)
                                  for u, w in nodes))

        ref = log_moment(omega_ref)
        d_fixed = log_moment(fr.omega_dh) - ref
        d_floor = log_moment(fr.omega_dh_absolute_floor) - ref
        assert abs(d_fixed) < mp.mpf(10) ** -60
        assert -mp.mpf("2.0e-4") < d_floor < -mp.mpf("1.4e-4")


def test_every_published_flow_rule_stops_short_of_the_old_cut():
    """Why flow_repair's flow numbers could not lose a node to the floor:
    DHFlow truncates at 10^-(dps+12) of its design box (t <= 0.12,
    |Im z| <= 1.6) and evaluates the weight at dps + 10, whose floor is
    10^-(dps+18). The rule ends 0.0125 (dps 40) to 0.0013 (dps 165) short of
    the cut, closing as dps grows."""
    margins = []
    for dps in STAGE_DPS:
        with mp.workdps(dps + 10):
            rule = SimpleNamespace(dps=dps, t_max=0.12, imz_max=1.6)
            U = fr.DHFlow._integration_limit(rule)
            margins.append((dps, float(u_cut(dps + 10) - U)))
    assert all(m > 0.001 for _, m in margins), margins
    by_dps = dict(margins)
    assert abs(by_dps[40] - 0.01254) < 2e-5 and abs(by_dps[165] - 0.00128) < 2e-5
    # and the pair-1 rule itself: no node is zeroed by the original floor
    flow = fr.DHFlow(54, z_scale=87.7, omega=fr.omega_dh_absolute_floor)
    assert flow.n_nodes == 1300 and all(p != 0 for p in flow.phis)


def test_the_evenness_defect_is_rounding_under_either_cutoff():
    """Stage validate's Phi evenness defect (NOTES.md section 0: <= 4.2e-51 at
    dps 50) re-runs as <= 7.1e-51 with the fix. Both are rounding: at every
    probe, each side of the check is within 4 units of 2^-169 of a 120-digit
    reference, under both cutoffs."""
    with mp.workdps(120):
        kap_ref = kappa(120)
    worst = {}
    with mp.workdps(50):
        kap = kappa(mp.dps)
        unit = mp.mpf(2) ** -mp.prec
        for name, omega in (("fixed", fr.omega_dh), ("floor", fr.omega_dh_absolute_floor)):
            worst[name] = mp.mpf(0)
            for uv in ("0.1", "0.2", "0.35", "0.5"):
                u = mp.mpf(uv)
                lhs, rhs = fr.phi_dh_raw(u, kap, omega), fr.phi_dh_raw(-u, kap, omega)
                with mp.workdps(120):
                    ref = fr.phi_dh_raw(u, kap_ref, omega_ref)
                    assert abs(lhs / ref - 1) < 4 * unit, (name, uv)
                    assert abs(rhs / ref - 1) < 4 * unit, (name, uv)
                worst[name] = max(worst[name], abs(lhs - rhs) / abs(lhs))
        assert mp.nstr(worst["floor"], 3) == "4.15e-51"  # results.json, as published
        assert mp.nstr(worst["fixed"], 3) == "7.05e-51"


def test_the_rerun_record_matches_the_correction():
    """NOTES.md's correction quotes the re-run report; this keeps them equal."""
    path = os.path.join(fr.HERE, "rerun_2026-10-19.json")
    with open(path, encoding="utf-8") as fh:
        rec = json.load(fh)
    assert rec["omega_dh_cutoff"] == "relative"
    changed = {c["path"] for s in rec["stages"].values() for c in s["changed"]}
    assert changed == {
        f"validate.phi_evenness_defect.{i}.{k}" for i in (0, 2, 3) for k in ("abs", "rel")
    }
    assert all(not s["missing"] for s in rec["stages"].values())
