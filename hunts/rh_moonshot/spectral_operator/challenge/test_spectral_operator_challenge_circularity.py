"""Pins for the circularity challenge of spectral_operator (hunt #150).

Run-time provenance of the builder's definition path, a planted control, and
the spectrum by mpmath's eigensolver; from ``circ_spo.py``. Writes nothing.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest
from mpmath import mp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
for _p in (str(HERE), str(ROOT)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import circ_spo as cs  # noqa: E402

_RESERVED = "cert" + "ified"
_EM_DASH = chr(0x2014)


@pytest.mark.parametrize("kind", ["zeta", "dh"])
def test_definition_path_reads_no_zero_at_run_time(kind):
    r = cs.provenance_report(kind, 13, 12)
    assert r["hits"] == []
    assert r["zero_files"] == []
    assert "wp_common.GAMMA_OFF" in r["poisoned"]


def test_every_zero_like_literal_on_the_path_is_text_or_poisoned():
    hits, names = cs.scan_once()
    assert ("wp_common", "GAMMA_OFF") in names and ("ccm_common", "EPSTEIN_OFF") in names
    for modname, lineno, _, _ in hits:
        kind = cs.hit_kind(modname, lineno)
        assert kind in ("docstring", "comment", "assignment"), (modname, lineno, kind)
        if kind == "assignment":
            assert any(m == modname for m, _ in names), (modname, lineno)


def test_planted_literal_is_found():
    import tempfile

    d = tempfile.mkdtemp()
    f = Path(d) / "tainted.py"
    f.write_text("SECRET = 14.1347251417\n", encoding="utf-8")
    hits = cs.literal_scan(n_zeros=3, files=[("tainted", str(f))])
    assert hits and hits[0][3] == "gamma_1"


def test_planted_control_is_caught():
    hits = cs.planted_control()
    assert ("call", "mpmath.zetazero") in hits


def test_traps_are_removed_afterwards():
    import zeta.core as ZC
    import wp_common as WP

    with cs.traps():
        pass
    assert isinstance(WP.GAMMA_OFF, str)
    assert callable(ZC.xi) and ZC.xi.__module__ == "zeta.core"
    with mp.workdps(15):
        assert abs(mp.im(mp.zetazero(1)) - cs.GAMMA_1) < 1e-10


def test_spectrum_by_mpmath_is_real_and_starts_at_gamma_1():
    r = cs.provenance_report("zeta", 13, 16)
    spec = cs.spectrum_mpmath(r["cell"])
    with mp.workdps(60):
        assert max(abs(mp.im(z)) for z in spec) < mp.mpf(10) ** -30
        pos = sorted(mp.re(z) for z in spec if mp.re(z) > 1)
        assert abs(pos[0] - cs.GAMMA_1) < mp.mpf(10) ** -12


def test_dh_spectrum_is_real_too():
    r = cs.provenance_report("dh", 13, 16)
    spec = cs.spectrum_mpmath(r["cell"])
    with mp.workdps(60):
        assert max(abs(mp.im(z)) for z in spec) < mp.mpf(10) ** -30


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
