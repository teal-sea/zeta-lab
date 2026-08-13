"""The leaf mirror reproduces `Leaves.lean` integer for integer.

This is the control whose absence let a broken table survive.

`o9_leaf.py` computed its transcendental leaves with Arb at 300 bits and a
4-ulp outward pad. `BandCert/Leaves.lean` builds them from truncated Taylor
series with `hornerI`, widens by one ulp, and for arguments outside `[-1,1]`
reduces modulo a `2^-64` enclosure of `2π` and doubles twice. Nobody ever
compared the two, so the Python model was narrower than the kernel, and the
table it certified was refuted by `decide +kernel` on 7 of 9 chunks
(`O9-2D-STATUS.md` §0).

The lesson recorded there is the general one: **a generator with no round-trip
against the thing it claims to mirror can only ever confirm itself.** So this
file runs the mirror and Lean side by side and requires the integers to be
equal — not close, equal. Fixed-point interval arithmetic has no rounding
slack to hide in, which is exactly what makes the check decisive.

The Lean half is marked slow: it elaborates `BandCert.Leaves`, which is a real
build. The pure-Python half runs in the fast tier and pins the structural
properties that do not need Lean.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
FM = REPO_ROOT / "hunts" / "frontier_math"
sys.path.insert(0, str(FM))

pytest.importorskip("flint", reason="o9_leaf imports python-flint at module scope")

from o9_leaf import Iv, ofQ  # noqa: E402
from o9_leaves_kernel import (  # noqa: E402
    PI2iv, SQ2, hornerI, kernel_leaves, shcSmall, sinCosIv, sinCosSmall,
    sinhCoshSmall, sinL,
)

SO = 1 << 64

#: The sampled arguments, in the order the Lean control file evaluates them.
SMALL = [F(1, 4), F(1, 2), F(1, 1), F(-3, 4)]
REDUCED = [F(28, 10), F(97, 8), F(30, 1), F(60, 1)]


# ---------------------------------------------------------------------------
# 1. Structural properties, no Lean required
# ---------------------------------------------------------------------------

def test_every_leaf_encloses_its_true_value() -> None:
    """The mirror is an enclosure, whatever else it is."""
    import mpmath as mp

    with mp.workdps(60):
        for q in SMALL:
            s, c = sinCosSmall(ofQ(q.numerator, q.denominator))
            assert s.lo / SO <= float(mp.sin(mp.mpf(q.numerator) / q.denominator)) <= s.hi / SO
            assert c.lo / SO <= float(mp.cos(mp.mpf(q.numerator) / q.denominator)) <= c.hi / SO
            sh, ch = sinhCoshSmall(ofQ(q.numerator, q.denominator))
            assert sh.lo / SO <= float(mp.sinh(mp.mpf(q.numerator) / q.denominator)) <= sh.hi / SO
            assert ch.lo / SO <= float(mp.cosh(mp.mpf(q.numerator) / q.denominator)) <= ch.hi / SO
        for q in REDUCED:
            s, c = sinCosIv(ofQ(q.numerator, q.denominator))
            v = mp.mpf(q.numerator) / q.denominator
            assert s.lo / SO <= float(mp.sin(v)) <= s.hi / SO
            assert c.lo / SO <= float(mp.cos(v)) <= c.hi / SO


def test_the_mirror_is_wider_than_the_arb_model_it_replaces() -> None:
    """The whole point: Lean's leaves are wider, and the old model hid that.

    If this ever fails, the mirror has drifted back toward the Arb model and
    the tables it produces stop predicting kernel outcomes.
    """
    from o9_leaf import leaves as arb_leaves

    lo, hi, y = F(61, 10), F(62, 10), F(1, 2)
    k = kernel_leaves(lo, hi, y)
    a = arb_leaves(lo, hi, y)
    wider = [key for key in ("sinX2", "cosX2")
             if (k[key].hi - k[key].lo) > (a[key].hi - a[key].lo)]
    assert wider, (
        "the kernel mirror is no wider than the Arb model on any trig leaf — "
        "that was the defect, so this test failing means it is back"
    )


def test_sq2_and_pi_are_the_pinned_integers_not_recomputed() -> None:
    """These are copied from `Leaves.lean`; recomputing them is the bug."""
    assert (SQ2.lo, SQ2.hi) == (26087635650665564424, 26087635650665564425)
    assert PI2iv.lo == 8 * 14488038916154245652
    assert PI2iv.hi == 8 * 14488038916154245716


def test_shc_small_is_the_expression_sinh_cosh_small_already_evaluates() -> None:
    """`O9-2D-STATUS.md` §3: the removable branch needs no new arithmetic."""
    a = ofQ(1, 3)
    assert shcSmall(a) == hornerI(
        [(1, 1), (1, 6), (1, 120), (1, 5040), (1, 362880), (1, 39916800),
         (1, 6227020800), (1, 1307674368000), (1, 355687428096000),
         (1, 121645100408832000), (1, 51090942171709440000)], a.sqr()).widen(1)


def test_horner_on_the_empty_list_is_zero() -> None:
    assert hornerI([], ofQ(1, 2)) == Iv(0, 0)


# ---------------------------------------------------------------------------
# 2. The round-trip against Lean — the control that was missing
# ---------------------------------------------------------------------------

_PKG = FM / "zeta23ext"
_CONTROL = _PKG / "Zeta23Ext" / "EForm3" / "O9RoundTrip.lean"


def _lean_available() -> bool:
    return (
        shutil.which("lake") is not None
        or (Path.home() / ".elan" / "bin" / "lake").is_file()
    ) and (_PKG / ".lake" / "packages" / "mathlib").exists()


@pytest.mark.slow
@pytest.mark.skipif(not _lean_available(), reason="needs elan + a built Mathlib")
def test_the_leaves_match_lean_integer_for_integer() -> None:
    env = dict(os.environ)
    env["PATH"] = f"{Path.home()}/.elan/bin:{env.get('PATH', '')}"
    out = subprocess.run(
        ["lake", "build", "Zeta23Ext.EForm3.O9RoundTrip"],
        cwd=_PKG, capture_output=True, text=True, env=env, timeout=3600, check=False,
    )
    # Parse line by line rather than with a greedy regex: lake interleaves
    # progress lines ("[8699/8699] Built …") that carry integers of their own,
    # and a regex running to end-of-string swallows the one after the last
    # #eval. A block starts at its `O9RoundTrip.lean:NN:0:` line and continues
    # while the following lines are indented.
    start = re.compile(r"O9RoundTrip\.lean:(\d+):0: (.*)$")
    found: list[tuple[int, list[str]]] = []
    for line in (out.stdout + out.stderr).splitlines():
        m = start.search(line)
        if m:
            found.append((int(m.group(1)), [m.group(2)]))
        elif found and line[:1] == " ":
            found[-1][1].append(line)
    blocks = [" ".join(parts) for _, parts in sorted(found, key=lambda t: t[0])]
    assert blocks, f"no #eval output; lake said:\n{blob[-2000:]}"

    expected: list[list[int]] = []
    for q in SMALL:
        s, c = sinCosSmall(ofQ(q.numerator, q.denominator))
        expected.append([s.lo, s.hi, c.lo, c.hi])
    for q in SMALL:
        s, c = sinhCoshSmall(ofQ(q.numerator, q.denominator))
        expected.append([s.lo, s.hi, c.lo, c.hi])
    for q in REDUCED:
        s, c = sinCosIv(ofQ(q.numerator, q.denominator))
        expected.append([s.lo, s.hi, c.lo, c.hi])
    expected.append([SQ2.lo, SQ2.hi])
    expected.append([PI2iv.lo, PI2iv.hi])

    assert len(blocks) == len(expected), (
        f"{len(blocks)} #eval blocks against {len(expected)} expected — "
        "O9RoundTrip.lean and this test have drifted apart"
    )
    for i, (block, want) in enumerate(zip(blocks, expected)):
        got = [int(x) for x in re.findall(r"-?\d+", block)]
        assert got == want, (
            f"leaf {i} diverges from the kernel:\n  lean = {got}\n  py   = {want}\n"
            "The mirror is not the kernel's arithmetic; no table it produces "
            "predicts a kernel outcome."
        )
