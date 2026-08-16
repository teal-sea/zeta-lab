"""Controls for `o9_leaf` — the O9 table in the kernel's own arithmetic."""

from __future__ import annotations

import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from o9_leaf import (  # noqa: E402
    CAPS, NAMED_GAPS, N_CELLS_KERNEL, SO, TRUE_SUPPORT, WINDOWS, Iv,
    _seed_segments, build, cell_verdict, damage_iv, emit_lean, ofInt, ofQ,
    validate,
)

_LEAN = (Path(__file__).resolve().parent / "zeta23ext" / "Zeta23Ext"
         / "EForm3")


# -- the fixed-point layer mirrors Iv.lean ----------------------------------

def test_flo_fhi_are_floor_and_ceiling():
    """Lean's Int `/` is ediv; for SO > 0 that is floor, including negatives."""
    from o9_leaf import fhi, flo
    for p in (-3 * SO - 1, -SO, -1, 0, 1, SO, 5 * SO + 7):
        assert flo(p) <= p / SO <= fhi(p)
        assert fhi(p) - flo(p) <= 1


def test_ofQ_encloses_the_rational():
    a = ofQ(1, 3)
    assert a.lo / SO <= 1 / 3 <= a.hi / SO
    assert a.hi - a.lo <= 1


def test_ofInt_is_exact():
    assert ofInt(7) == Iv(7 * SO, 7 * SO)


def test_arithmetic_is_sound_on_random_intervals():
    """add/sub/mul/sqr must enclose the true result.

    Compared in exact `Fraction`s: the intervals are 1 ulp of `2^-64` wide,
    which is finer than float can represent for operands of size ~3, so a
    float comparison here fails spuriously.
    """
    import random
    rng = random.Random(5)
    for _ in range(200):
        alo = rng.randint(-3 * SO, 3 * SO)
        a = Iv(alo, alo + rng.randint(0, SO))
        blo = rng.randint(-3 * SO, 3 * SO)
        b = Iv(blo, blo + rng.randint(0, SO))
        for x in (F(a.lo, SO), F(a.hi, SO)):
            for y in (F(b.lo, SO), F(b.hi, SO)):
                s_ = a.add(b)
                assert F(s_.lo, SO) <= x + y <= F(s_.hi, SO)
                d = a.sub(b)
                assert F(d.lo, SO) <= x - y <= F(d.hi, SO)
                m = a.mul(b)
                assert F(m.lo, SO) <= x * y <= F(m.hi, SO)
            q = a.sqr()
            assert F(q.lo, SO) <= x * x <= F(q.hi, SO)


# -- the damage enclosure ---------------------------------------------------

@pytest.mark.parametrize("s", ["6.517", "6.0653", "12.7", "25.2", "59.9",
                               "5.7"])
def test_damage_enclosure_contains_the_arb_reference(s):
    """The load-bearing check: the fixed-point interval is sound."""
    from flint import acb, arb, ctx
    ctx.prec = 200
    sq2 = arb(2).sqrt()

    def ref(y, sv):
        z = acb(arb(y), arb(sv))
        zp, zm = z + acb(0, 1) * acb(sq2), z - acb(0, 1) * acb(sq2)
        g = (zp / 2).sinh() / zp + (zm / 2).sinh() / zm
        return float((-((g * g).real)).mid())

    lo = F(s)
    hi = lo + F(1, 1000)
    d = damage_iv(lo, hi)
    assert d is not None
    a, b = d.as_floats()
    assert a <= ref(0.5, float(lo) + 0.0005) <= b


def test_damage_is_negative_below_the_first_window():
    """On a NARROW cell below the first window the enclosure decides.

    A wide cell there does not, and must not be expected to: over
    `[28/5, 6]` the enclosure is `[-0.0331, +0.00885]`, which straddles
    zero. That is the whole reason the walk subdivides, and the build
    discharges the region in cells (0 undecided).
    """
    narrow = damage_iv(F(59, 10), F(591, 100), F(1, 2))
    assert narrow is not None and narrow.hi < 0
    wide = damage_iv(F(28, 5), F(6), F(1, 2))
    assert wide is not None and wide.hi > 0        # undecidable while wide


# -- the table --------------------------------------------------------------

def test_seed_segments_cut_at_every_window_endpoint():
    """Bisection alone never lands on an endpoint; without this the walk
    never terminates on straddling cells."""
    segs = _seed_segments()
    pts = {a for a, _ in segs} | {b for _, b in segs}
    for wl, wh in WINDOWS:
        assert wl in pts and wh in pts
    assert len(segs) == 2 * len(WINDOWS) + 1


@pytest.fixture(scope="module")
def table():
    return build()


def test_every_cell_decides(table):
    v = validate(table)
    assert v["all_decided"], v
    assert v["undecided"] == 0


def test_table_size_is_recorded_and_reproduces(table):
    """476 on the kernel's leaves -- not Arb's 196, and not the Arb-model 344."""
    v = validate(table)
    assert v["cells"] == 476
    assert v["max_depth"] == 22


def test_margins_are_far_above_the_leaf_caveat_threshold(table):
    """The prediction is only safe if no cell passes by a few ulp."""
    v = validate(table)
    assert v["min_margin_ulp"] > 10 ** 6
    assert v["min_margin_abs"] > 1e-12


def test_cells_tile_the_interval_without_gaps(table):
    cells = table["cells"]
    assert cells[0]["lo"] == F(28, 5)
    assert cells[-1]["hi"] == F(60)
    for a, b in zip(cells, cells[1:]):
        assert a["hi"] == b["lo"]


def test_every_in_window_cell_carries_its_window_cap(table):
    for c in table["cells"]:
        inside = [k for k, (wl, wh) in enumerate(WINDOWS)
                  if wl <= c["lo"] and c["hi"] <= wh]
        if inside:
            expect = -((-(CAPS[inside[0]] * F(1, 4) * SO)).__floor__())
            assert c["target"] == expect
        else:
            assert c["target"] == 0


# -- emission ---------------------------------------------------------------

def test_emitted_lean_files_exist_and_are_consistent(table):
    r = emit_lean(table=table)
    data = Path(r["data"]).read_text()
    check = Path(r["check"]).read_text()
    assert data.count("⟨") == r["cells"] + 0
    assert "decide +kernel" in check
    assert check.count("theorem o9_chunk") == r["chunks"]
    assert "import Zeta23Ext.BandCert.Phi" in data


def test_the_package_stays_sorry_free():
    """O9Damage records its obligation in prose rather than as a `sorry`.

    zeta23ext has been sorry-free throughout; the first placeholder would
    cost more than the lemma is worth.
    """
    import re
    for f in _LEAN.parent.rglob("*.lean"):
        src = f.read_text()
        assert not re.search(r":=\s*(by\s+)?sorry\b", src), f
        assert not re.search(r"\bsorry\s*$", src, re.M), f


def test_s4_windows_strictly_contain_the_true_support():
    """The dependency that makes the complement decidable.

    `o9_scoping.py` shows that with the windows taken as the exact damage
    support, "no damage outside" is an equality at every endpoint and the
    complement does not close (404 leaves, depth wall). This table closes
    only because S4's `I_k` are decimal-rounded OUTWARD past the support.
    Tightening those endpoints would break this table.
    """
    for (wl, wh), (tl, th) in zip(WINDOWS, TRUE_SUPPORT):
        assert wl < tl, (wl, tl)
        assert th < wh, (th, wh)
        assert tl - wl < F(1, 1000)
        assert wh - th < F(1, 1000)


def test_kernel_count_disagrees_with_the_arb_grade_count():
    """196 is Arb-grade, 344 was the Arb model; the kernel's leaves need 476."""
    from window_table import N_CELLS as ARB_GRADE
    assert ARB_GRADE == 196
    assert N_CELLS_KERNEL == 476
    assert N_CELLS_KERNEL > ARB_GRADE


def test_o9_is_staged_but_not_wired_into_the_package():
    """Deliberate: the files are uncompiled here, so importing them from
    `Zeta23Ext.lean` would risk the other session's build."""
    root = _LEAN.parent.parent / "Zeta23Ext.lean"
    src = root.read_text()
    assert "import Zeta23Ext.EForm3.Main" in src          # the wired ones
    for orphan in ("O9Data", "O9Check", "O9Damage"):
        assert orphan not in src, orphan
    for f in ("O9Data.lean", "O9Check.lean", "O9Damage.lean"):
        assert (_LEAN / f).exists(), f


def test_named_gaps_are_honest():
    joined = " ".join(NAMED_GAPS)
    assert "NOT kernel-checked" in joined
    assert "LEAF CAVEAT" in joined
    assert "OUTWARD" in joined          # L4b, the widening dependency
    assert "RH" in joined
