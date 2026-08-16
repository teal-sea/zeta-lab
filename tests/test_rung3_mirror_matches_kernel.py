"""The Python ball mirror must agree with the Lean kernel BIT FOR BIT.

This is not a tolerance check and cannot be one.  `scripts/60_rung3_generate.py`
emits, per term, a literal equality that the kernel closes by evaluation: the
mirror computes the box, the certificate asserts the Lean expression *equals*
that literal, and the kernel checks it.  A mirror one ulp away from the kernel
does not produce a slightly worse certificate, it produces one that does not
compile at all — and the failure would surface only after the compute run had
been launched.

The fixture is byte-pinned output from `#eval` on
`ZetaLean.ComplexBall.dirichletTermBallB`.  Three real divergences were caught
by exactly this comparison when it was first run, all silent under any
tolerance:

1. Lean's `expCrB` did not coarsen the base `expSmallB`; the mirror did.
2. The mirror's rational square root ran at 96 bits; `absUpper p` uses `p`.
3. The mirror's re-centring displacement used a square root; `recentre` uses
   the L1 bound `|dre| + |dim|`.

If this test fails, do not adjust the fixture to match the mirror.  Decide which
side is authoritative — the kernel is, since it is what checks the certificate —
and fix the other.
"""
from __future__ import annotations

import importlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

ball = importlib.import_module("63_rung3_ball_mirror")
FIX = json.loads((ROOT / "tests" / "fixtures" /
                  "rung3_ball_term_kernel.json").read_text())
CFG = FIX["config"]
PT = FIX["point"]


def _point() -> "ball.C":
    return ball.C(F(PT["cre"]), F(PT["cim"]), F(PT["rad"]))


@pytest.mark.parametrize("m", sorted(FIX["terms"], key=int))
def test_mirror_term_box_is_bit_identical_to_the_kernel(m):
    want = FIX["terms"][m]
    mi = int(m)
    got = ball.dirichletTermBox2(CFG["nLog"], CFG["nExp"], CFG["p"],
                                 mi.bit_length(), CFG["kE"], mi, _point())
    assert got.cre == F(want["cre"]), f"m={m} centre.re"
    assert got.cim == F(want["cim"]), f"m={m} centre.im"
    assert got.rad == F(want["rad"]), f"m={m} radius"


def test_the_comparison_has_power():
    """A tolerance-based check would pass on all three divergences this test was
    written to catch, so confirm the check is exact and not approximate."""
    m = sorted(FIX["terms"], key=int)[0]
    mi = int(m)
    got = ball.dirichletTermBox2(CFG["nLog"], CFG["nExp"], CFG["p"],
                                 mi.bit_length(), CFG["kE"], mi, _point())
    one_ulp = F(1, 2 ** CFG["p"])
    assert got.rad + one_ulp != F(FIX["terms"][m]["rad"])
    assert abs(float(got.rad + one_ulp) - float(F(FIX["terms"][m]["rad"]))) < 1e-15


def test_the_pinned_config_is_the_one_the_plan_uses():
    """The fixture is only evidence about the configuration it was taken at."""
    assert (CFG["nLog"], CFG["nExp"], CFG["p"], CFG["kE"]) == (32, 20, 64, 10)
