"""Pins for the circularity challenge of de_branges (hunt #150).

From ``circ_dbr.py``, which shares no code with ``dbr_common.py``. The census of
the page is the script's (about 15 minutes); here the zero itself, its windings,
the calibration, Conrey and Li's numbers and the zero trap. Writes nothing.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import circ_dbr as cd  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)


def test_own_chowla_selberg_matches_zeta_epstein_and_planted_prefactor_fails():
    from zeta import epstein as E

    with mp.workdps(30):
        for s in (mp.mpf(3), mp.mpc("0.7", "5")):
            assert abs(cd.epstein_cs(s) - E.epstein_zeta(s, cd.FORM, dps=30)) < mp.mpf(10) ** -20
        # planted fault: the prefactor 2^(s + 3/2) is off by a factor 2 and is seen
        bad = cd.epstein_cs(mp.mpf(3), pre_power="1.5")
        assert abs(bad - E.epstein_zeta(mp.mpf(3), cd.FORM, dps=30)) > mp.mpf(10) ** -8


def test_direct_lattice_sum_calibration():
    with mp.workdps(20):
        d = cd.direct_sum(4, 60)
        assert abs(cd.epstein_cs(4) - d) < mp.mpf(10) ** -6


def test_second_offline_zero_by_own_route():
    with mp.workdps(40):
        r = cd.newton_root(cd.BUILDER_ROOT, dps=40)
        assert abs(r - mp.mpc(*cd.BUILDER_ROOT)) < mp.mpf(10) ** -12
        assert abs(mp.re(r) - mp.mpf("0.7979971571787")) < mp.mpf(10) ** -12
        assert abs(cd.epstein_cs(r)) < mp.mpf(10) ** -25
        assert abs(cd.epstein_cs(r + mp.mpf("0.01"))) > mp.mpf("0.01")


def test_three_further_offline_zeros_by_two_routes():
    from zeta import epstein as E

    with mp.workdps(30):
        for re_, im_ in cd.NEW_ZEROS:
            r = mp.findroot(cd.epstein_cs, mp.mpc(re_, im_), tol=mp.mpf(10) ** -22)
            assert abs(r - mp.mpc(re_, im_)) < mp.mpf(10) ** -15
            assert mp.re(r) > mp.mpf("0.6")
            assert abs(cd.epstein_cs(r)) < mp.mpf(10) ** -20
            # second route: zeta.epstein, at its own precision floor
            assert abs(E.epstein_zeta(r, cd.FORM, dps=30)) < mp.mpf(10) ** -15
            assert abs(E.epstein_zeta(r + mp.mpf("0.01"), cd.FORM, dps=30)) > mp.mpf("0.01")


def test_builder_grid_points_miss_the_failure_at_33_65():
    with mp.workdps(30):
        h, y = mp.mpf(1) / 20, mp.mpf(1) / 20
        assert cd.defect_own(h, mp.mpf("33.650100582527335"), y) > mp.mpf("0.4")
        assert cd.defect_own(h, mp.mpf("33.5"), y) < 0
        assert cd.defect_own(h, mp.mpf("34.0"), y) < 0


def test_winding_one_around_the_zero_and_zero_beside_it():
    with mp.workdps(25):
        r = mp.mpc(*cd.BUILDER_ROOT)
        w = cd.winding(cd.epstein_cs, r, "0.02", steps_per_side=12)
        assert w["winding"] == 1 and w["max_increment"] < mp.pi / 4
        w0 = cd.winding(cd.epstein_cs, r + mp.mpf("0.1"), "0.02", steps_per_side=12)
        assert w0["winding"] == 0


def test_conrey_li_numbers_by_own_xi():
    rho, n1, n2 = cd.conrey_li_numbers(dps=40)
    with mp.workdps(40):
        assert abs(n1 / mp.mpf("-5.389100507182945e-69") - 1) < mp.mpf(10) ** -12
        assert abs(n2 - mp.mpf("-0.000131957")) < mp.mpf(10) ** -9


def test_builder_defect_reads_no_zero():
    import dbr_common as D

    with cd.zero_trap() as log:
        for kind in ("zeta", "dh"):
            v = D.defect_mp(kind, mp.mpf(1) / 4, mp.mpf(20), mp.mpf(1) / 5, dps=20)
            assert v < 0
    assert log == []
    with cd.zero_trap() as log:
        try:
            mp.zetazero(1)
        except RuntimeError:
            pass
    assert log == ["zetazero"]


def test_lexical_rules_and_manifest():
    for path in sorted(HERE.iterdir()):
        if path.suffix in {".py", ".md"}:
            text = path.read_text(encoding="utf-8")
            assert _RESERVED not in text.lower(), path.name
            assert _EM_DASH not in text, path.name
    sys.path.insert(0, str(ROOT / "tests"))
    try:
        import test_huntspec as hs
    finally:
        sys.path.remove(str(ROOT / "tests"))
    text = (HERE / "CHALLENGE_circularity.md").read_text(encoding="utf-8")
    blocks = re.findall(r"```runmanifest\n(.*?)```", text, re.DOTALL)
    assert blocks
    for block in blocks:
        assert hs.validate_runmanifest(hs.parse_huntspec(block)) == ()
