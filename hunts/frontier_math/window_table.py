"""ROAD A, task 1: the per-window damage table, sized and generated.

The `k = 1` retention chain's one substantial formalisation obligation is
a leaf table deciding, on every cell of `s in [28/5, 60]` at `y = 1/2`,
either `D <= 0` or `D <= cap_k` for the window the cell belongs to.
`arm_identification.py` shows the enclosure machinery already exists
(`BandCert.Phi.phiC_mem`, since `ghat(z) = Phi2(-i z)`); what was missing
was the table's size.  Measured with Arb balls at 128 bits it is
**196 cells**.

**That is not the Lean cost.**  `o9_leaf.py` re-measures the same table in
the arithmetic the kernel actually runs, fixed point at `2^-64`, mirrored
from `Iv.lean`, and gets **344 cells**.  Arb at 128 bits is tighter than
fixed point at `2^-64`, so cells Arb decides need splitting again there;
the `196` below understates the real obligation by 43%.  It is kept as
what it is: an Arb-grade sizing, useful for the roadmap comparison in
`ROADMAP-OPTIONS.md`, superseded by `o9_leaf` for anything that will be
compiled.

## Two sizing attempts failed first, and the failures are the method

1. Requiring `D <= 0` on cells that straddle a window edge is
   **unprovable by enclosure**, `D` is exactly `0` there, so no ball
   ever has a nonpositive upper bound.  6.36e6 cells, 99.995% undecided.
2. Capping a bracket by ONE wide ball suffers the dependency problem: at
   half-width `0.6` the enclosure is `2.73e-02` against a true peak of
   `4.40e-03`, a **6x** blow-up, and the resulting cap sum `3.54e-02`
   already exceeds the budget `3.375e-02`.

Both are fixed by the same two changes: locate the true window edges and
put the brackets strictly *outside* them (so `D < 0` with margin
off-bracket, hence decidable), and compute each cap by **adaptive
subdivision inside** the bracket rather than one wide evaluation.

## The table

At `y = 1/2`, `s in [5.6, 60]`, computed with Arb balls at 128 bits:

* **9 windows**, widths `0.960975 .. 0.986001`, minimum gap between them
  `5.182969`; the first begins at `6.065319` (EForm3's `no_damage` gives
  the coarser `28/5`).
* **9 brackets**, each the window padded by `0.25` and rounded outward to
  `1e-3`, leaving a smallest inter-bracket gap of `4.683`.
* **143 in-bracket cells** carrying the nine caps, `4.483880e-03` down
  to `4.715629e-05`; caps sum to `6.595448e-03` one-sided,
  `1.319090e-02` both sides, against `Shq/2 = 3.375420e-02`: a ratio of
  `0.3908`.
* **53 off-bracket cells** over 10 segments, all discharging `D <= 0`,
  **0 undecided**.

`196` total, against the `62 .. 248` of `BandCert`'s existing tables, so
this is an ordinary instance of a pattern the package already carries,
not a new scale of problem.

The depth reduction is separate and cheaper: `D(y,s)/y^2 <= 4 D(1/2,s)`
showed 0 violations over 400 `s`-points x 6 depths, and closes with margin
`2.39x` because the budget coefficient `Shq(y)/2 / y^2` *increases* in
`y`, so its floor is `0.13087` at `y -> 0` against a requirement of
`5.487e-02`.  With that lemma the table is one-dimensional, which is why
it is `196` cells and not a two-dimensional sweep.

## What this is not

The cells are computed here in Arb, not in Lean; nothing in this module is
kernel-checked, and the table is a *specification* for the Lean leaf file,
not the leaf file.  The depth-reduction lemma is measured, not proved.
`k >= 2` is untouched.  Nothing here is evidence about RH.

Run ``.venv/bin/python hunts/frontier_math/window_table.py`` (~40 s).
"""

from __future__ import annotations

import json
from pathlib import Path

__all__ = [
    "TABLE", "N_CELLS", "N_IN_BRACKET", "N_OFF_BRACKET", "N_WINDOWS", "SHQ_HALF", "windows", "brackets",
    "cap_by_subdivision", "count_offbracket", "build", "NAMED_GAPS", "report",
]

#: `Shq(1/2)/2`, the budget the caps are measured against.
SHQ_HALF = 0.0337542039303139753
#: Arb-grade cell count (143 in-bracket + 53 off-bracket).  NOT the Lean
#: cost: `o9_leaf.N_CELLS_KERNEL` is 476 on the kernel's own leaves.
N_CELLS = 196
N_IN_BRACKET = 143
N_OFF_BRACKET = 53
N_WINDOWS = 9

_DATA = Path(__file__).resolve().parent / "data_window_table.json"


def _flint():
    from flint import arb, acb, ctx
    ctx.prec = 128
    return arb, acb


def _ghat(acb, arb, z):
    s2 = arb(2).sqrt()
    zp = z + acb(0, 1) * acb(s2)
    zm = z - acb(0, 1) * acb(s2)
    return (zp / 2).sinh() / zp + (zm / 2).sinh() / zm


def _dmg(arb, acb, y, s):
    g = _ghat(acb, arb, acb(y, s))
    return -((g * g).real)


def _box(arb, lo, hi):
    return arb((lo + hi) / 2.0, (hi - lo) / 2.0)


def windows(y: float = 0.5, s_lo: float = 5.6, s_hi: float = 60.0,
            step: float = 0.002) -> list:
    """The true intervals where `D > 0`, by sign change plus bisection."""
    arb, acb = _flint()

    def d(s):
        return float(_dmg(arb, acb, arb(y), arb(s)).mid())

    out, s, prev, lo = [], s_lo, d(s_lo), None
    while s < s_hi:
        s2 = s + step
        cur = d(s2)
        if prev <= 0 < cur:
            a, b = s, s2
            for _ in range(60):
                m = (a + b) / 2
                if d(m) <= 0:
                    a = m
                else:
                    b = m
            lo = b
        elif prev > 0 >= cur and lo is not None:
            a, b = s, s2
            for _ in range(60):
                m = (a + b) / 2
                if d(m) > 0:
                    a = m
                else:
                    b = m
            out.append((lo, a))
            lo = None
        s, prev = s2, cur
    return out


def brackets(wins, pad: float = 0.25, places: int = 3) -> list:
    """Windows padded outward to rational endpoints."""
    f = 10 ** places
    import math
    return [(math.floor((l - pad) * f) / f, math.ceil((h + pad) * f) / f)
            for l, h in wins]


def cap_by_subdivision(lo: float, hi: float, y: float = 0.5,
                       tol_rel: float = 0.02, max_depth: int = 22):
    """Tight upper bound for `D` on `[lo, hi]`, by adaptive subdivision.

    The cells ARE the proof of the cap, this is what the Lean leaf does.
    Returns `(cap, cells)`.
    """
    arb, acb = _flint()
    target = max(float(_dmg(arb, acb, arb(y),
                            arb(lo + (hi - lo) * i / 64)).mid())
                 for i in range(65))
    thresh = target * (1 + tol_rel)
    best, cells, stack = -1e18, 0, [(lo, hi, 0)]
    while stack:
        a, b, d = stack.pop()
        u = float(_dmg(arb, acb, arb(y), _box(arb, a, b)).upper())
        if u <= thresh or d >= max_depth:
            cells += 1
            best = max(best, u)
            continue
        m = (a + b) / 2
        stack.append((a, m, d + 1))
        stack.append((m, b, d + 1))
    return max(best, thresh), cells


def count_offbracket(brs, y: float = 0.5, s_lo: float = 5.6,
                     s_hi: float = 60.0, max_depth: int = 30):
    """Cells needed to discharge `D <= 0` outside every bracket."""
    arb, acb = _flint()
    segs, prev = [], s_lo
    for lo, hi in brs:
        if lo > prev:
            segs.append((prev, lo))
        prev = hi
    if prev < s_hi:
        segs.append((prev, s_hi))
    cells = undec = 0
    for a0, b0 in segs:
        stack = [(a0, b0, 0)]
        while stack:
            a, b, d = stack.pop()
            u = float(_dmg(arb, acb, arb(y), _box(arb, a, b)).upper())
            if u <= 0.0:
                cells += 1
                continue
            if d >= max_depth:
                cells += 1
                undec += 1
                continue
            m = (a + b) / 2
            stack.append((a, m, d + 1))
            stack.append((m, b, d + 1))
    return {"cells": cells, "undecided": undec, "segments": len(segs)}


def build(y: float = 0.5) -> dict:
    """Generate the whole table.  Cached to `data_window_table.json`."""
    wins = windows(y)
    brs = brackets(wins)
    caps, in_cells = [], 0
    for lo, hi in brs:
        c, n = cap_by_subdivision(lo, hi, y)
        caps.append(c)
        in_cells += n
    off = count_offbracket(brs, y)
    return {
        "y": y,
        "windows": [{"lo": l, "hi": h, "width": h - l} for l, h in wins],
        "brackets": [{"lo": l, "hi": h, "cap": c}
                     for (l, h), c in zip(brs, caps)],
        "min_gap_between_windows": min(wins[i + 1][0] - wins[i][1]
                                       for i in range(len(wins) - 1)),
        "min_gap_between_brackets": min(brs[i + 1][0] - brs[i][1]
                                        for i in range(len(brs) - 1)),
        "cap_sum_one_side": sum(caps),
        "cap_sum_both_sides": 2 * sum(caps),
        "shq_half": SHQ_HALF,
        "in_bracket_cells": in_cells,
        "off_bracket": off,
        "total_cells": in_cells + off["cells"],
    }


def TABLE() -> dict:
    """The cached table, generating it on first use."""
    if _DATA.exists():
        return json.loads(_DATA.read_text())
    t = build()
    _DATA.write_text(json.dumps(t, indent=1, sort_keys=True))
    return t


NAMED_GAPS = (
    "T1 the cells are computed in Arb here, NOT in Lean; nothing in this "
    "module is kernel-checked and the table is a specification for the "
    "leaf file, not the leaf file.",
    "T2 the depth reduction D(y,s)/y^2 <= 4 D(1/2,s) is measured on a "
    "grid (400 s-points x 6 depths), not proved; without it the table is "
    "two-dimensional and much larger.",
    "T3 the tail past s = 60 is not in this table; it is charged to "
    "EForm3's kernel-checked Wt majorant (Qim_far_sq).",
    "T4 cap_by_subdivision stops at a relative tolerance of 2%, so the "
    "caps are deliberately loose; the budget has room for that and the "
    "looseness is one-sided.",
    "T5 this is an ARB-grade sizing. In the kernel's fixed-point "
    "arithmetic the same table is 344 cells (`o9_leaf.py`), 43% larger; "
    "use that number for anything that will be compiled.",
    "T6 k >= 2 is untouched and nothing here is evidence about RH.",
)


def report() -> dict:
    t = TABLE()
    print(f"= the window table at y = {t['y']} =")
    print(f"  {len(t['windows'])} windows; widths "
          f"{min(w['width'] for w in t['windows']):.6f} .. "
          f"{max(w['width'] for w in t['windows']):.6f}")
    print(f"  first window begins at {t['windows'][0]['lo']:.6f} "
          f"(EForm3's no_damage gives the coarser 28/5 = 5.6)")
    print(f"  min gap between windows  {t['min_gap_between_windows']:.6f}")
    print(f"  min gap between brackets {t['min_gap_between_brackets']:.6f}")
    print("  brackets and caps:")
    for i, b in enumerate(t["brackets"]):
        print(f"    B{i+1}: [{b['lo']:.3f}, {b['hi']:.3f}]  cap "
              f"{b['cap']:.6e}")
    print(f"  cap sum: {t['cap_sum_one_side']:.6e} one side, "
          f"{t['cap_sum_both_sides']:.6e} both")
    print(f"  vs Shq/2 = {t['shq_half']:.6e}  -> ratio "
          f"{t['cap_sum_both_sides']/t['shq_half']:.4f}")
    print(f"= size =")
    print(f"  in-bracket cells  {t['in_bracket_cells']}")
    print(f"  off-bracket cells {t['off_bracket']['cells']} over "
          f"{t['off_bracket']['segments']} segments, "
          f"{t['off_bracket']['undecided']} undecided")
    print(f"  TOTAL {t['total_cells']} cells  "
          f"(BandCert's existing tables: 62-248)")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return t


if __name__ == "__main__":
    report()
