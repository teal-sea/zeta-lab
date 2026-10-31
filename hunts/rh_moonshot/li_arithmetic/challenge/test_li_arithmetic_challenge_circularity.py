"""Pins for the circularity challenge of li_arithmetic (hunt #150).

Numbers quoted in CHALLENGE_circularity.md, from ``circ_li.py``, which shares no
code with ``li_arith_*.py``. The X = 10^8 scan of the page is the script's
(about 5 minutes); here the same routine runs at X = 10^6. Writes nothing.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import circ_li as cl  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)

_PP = None


def _pp():
    global _PP
    if _PP is None:
        _PP = cl.prime_powers(10**6)
    return _PP


def test_artifact_P_is_margin_minus_xi_side_lambda():
    art = json.loads(cl.ART.read_text())
    split = json.loads((cl.ART.parent / "split_zeta.json").read_text())
    for n in (1, 7, 100, 5000):
        lam = float(split["lambda"][n - 1])
        assert abs(art["P_exact"][n - 1] - (art["margin_M"][n - 1] - lam)) < 1e-9


def test_prime_side_reproduces_P_at_1e6():
    rows = cl.compare(ns=(1, 2, 5, 10, 20, 30, 60), Xs=(10**6,), pp=_pp())
    for n, r in rows.items():
        assert abs(r["1000000"] - r["P_artifact"]) < 1e-2, n
    assert abs(rows[1]["1000000"] - rows[1]["P_artifact"]) < 1e-4


def test_planted_fault_wrong_antiderivative_is_seen():
    m, lam = _pp()
    art = json.loads(cl.ART.read_text())
    bad = cl.prime_integral(2, 10**6, m, lam, alpha=3)
    assert abs(bad - art["P_exact"][1]) > 1.0
    # n = 1 cannot see it: L_0 = 1 for every alpha
    assert abs(cl.prime_integral(1, 10**6, m, lam, alpha=3) - art["P_exact"][0]) < 1e-4


def test_shifted_xi_has_positive_li_coefficients():
    with mp.workdps(30):
        lam0 = cl.shifted_li("0", n_max=6, nodes=128, dps=30)
        assert abs(lam0[0] - mp.mpf("0.0230957089661210338")) < mp.mpf(10) ** -15
        lamd = cl.shifted_li("0.25", n_max=10, nodes=128, dps=30)
        assert all(x > 0 for x in lamd)
        assert abs(lamd[0] - mp.mpf("0.0115513351955")) < mp.mpf(10) ** -12


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
