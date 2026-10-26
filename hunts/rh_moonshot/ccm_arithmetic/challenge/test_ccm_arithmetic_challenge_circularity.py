"""Pins for the circularity challenge of ccm_arithmetic (hunt #150).

Numbers quoted in CHALLENGE_circularity.md, from ``circ_ccm.py``, which reads the
builder's committed data and recomputes no matrix. Writes nothing.
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

import circ_ccm as cc  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)


def test_lambda1_nonincreasing_in_band_for_every_window():
    for kind, n_windows in (("zeta", 10), ("dedekind", 13), ("dh", 14)):
        rep = cc.interlacing_report(kind)
        assert len(rep) == n_windows, kind
        assert all(r["nonincreasing"] for r in rep.values()), kind


def test_zeta_band_drop_has_no_measured_limit():
    rep = cc.interlacing_report("zeta")
    assert all(r["all_positive"] for r in rep.values())
    assert abs(rep["60"]["orders_dropped"] - mp.mpf("112.25")) < mp.mpf("0.01")
    assert rep["13"]["orders_dropped"] > 9
    # still falling at the largest band: no limit in N is measured
    row = cc.lambda1_by_window("zeta")["60"]
    assert row[128] < row[64] * mp.mpf(10) ** -60


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
