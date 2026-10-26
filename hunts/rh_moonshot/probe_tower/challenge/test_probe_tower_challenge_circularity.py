"""Pins for the circularity challenge of probe_tower (hunt #150).

Every number quoted in CHALLENGE_circularity.md is asserted here, from
``circ_probe.py``, which shares no code with ``tower_template.py``. Writes nothing.
"""
from __future__ import annotations

import re
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import circ_probe as cq  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)

WALLS = {  # k: (dual-only, floor delta0 -> 0, floor delta0 = 1/50)
    2: (Fr(0), Fr(3, 5), Fr(39, 64)),
    3: (Fr(1, 3), Fr(11, 15), Fr(71, 96)),
    4: (Fr(1, 2), Fr(4, 5), Fr(103, 128)),
    5: (Fr(3, 5), Fr(21, 25), Fr(27, 32)),
    6: (Fr(2, 3), Fr(13, 15), Fr(167, 192)),
    7: (Fr(5, 7), Fr(31, 35), Fr(199, 224)),
    8: (Fr(3, 4), Fr(9, 10), Fr(231, 256)),
    12: (Fr(5, 6), Fr(14, 15), Fr(359, 384)),
    100: (Fr(49, 50), Fr(124, 125), Fr(127, 128)),
}


def test_sigma0_closed_form_and_paper_value():
    sig, gap, at6 = cq.sigma0_symbolic()
    assert gap == 0
    assert at6 == sp.Rational(7, 8)


def test_walls_by_vertex_enumeration():
    for k, (dual, f0, f1) in WALLS.items():
        assert cq.sigma0_from_m(k, cq.lp_min_m(k, None, floor=False)[0]) == dual
        m0, x0 = cq.lp_min_m(k, Fr(0), floor=True)
        assert cq.sigma0_from_m(k, m0) == f0
        assert x0 == (Fr(1, 5), Fr(4, 5), Fr(0))
        assert cq.sigma0_from_m(k, cq.lp_min_m(k, Fr(1, 50), floor=True)[0]) == f1


def test_floor_wall_increasing_and_above_half():
    vals = [cq.sigma0_from_m(k, cq.lp_min_m(k, Fr(0), True)[0]) for k in range(2, 41)]
    assert all(b > a for a, b in zip(vals, vals[1:]))
    assert min(vals) == Fr(3, 5)


def test_dual_identity_and_planted_multiplier_fault():
    assert cq.dual_identity_residual() == 0
    assert cq.dual_identity_residual(y1_scale=sp.Rational(101, 100)) != 0


def test_dh_correction_at_offline_zero_by_hurwitz_route():
    with mp.workdps(30):
        r = cq.dh_correction_at_zero()
        assert r["absDH"] < mp.mpf(10) ** -30
        assert abs(r["absL1"] - mp.mpf("0.70219735")) < mp.mpf(10) ** -7
        assert abs(r["absL1"] - r["absL2"]) < mp.mpf(10) ** -20
        assert abs(r["absR"] - mp.mpf("0.77831832")) < mp.mpf(10) ** -7
        assert abs(r["absHminus1"] - 1) < mp.mpf(10) ** -20
        assert r["closed_gap"] < mp.mpf(10) ** -30


def test_shifted_zeta_passes_the_euler_step_with_H_equal_one():
    with mp.workdps(20):
        for delta in (mp.mpf(1) / 4, mp.mpf(1) / 10):
            S = cq.squarefree_moebius_sum(lambda n: mp.mpf(n) ** delta, 3, 20000)
            assert abs(S - 1 / mp.zeta(3 - delta)) < mp.mpf(10) ** -7


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
