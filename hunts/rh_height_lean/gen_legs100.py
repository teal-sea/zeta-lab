"""Emit the top-leg files of `RHHeight100` (hunt #137, height 100).

Run from the repository root:

    .venv/bin/python hunts/rh_height_lean/gen_legs100.py          # write the three files
    .venv/bin/python hunts/rh_height_lean/gen_legs100.py --check  # compare, write nothing

The files are `lean/RHHeight100/LegsTop100A.lean` and `LegsTop100B.lean` (the leg
`[1/2, 2] + 100i`) and `lean/RHHeight100/LegsArg100.lean` (the point `1/2 + 100i`). The
bottom leg `[1/2, 2] + 3i` and the point `1/2 + 3i` are the height-50 files, reused as they
stand. Everything else is `gen_legs.py`: the same term boxes, the same segment slack and
point box, the same refusal to write a file whose inequalities do not hold with `MARGIN`,
and its renderers. Two things differ. At height 100 the exp-tower argument `|s log m|`
passes 256, so the range reduction uses `kE = 10` (hunt #133 used 8). And the partition
below was found by a greedy search over the dyadic grid of step 1/64 (`search_top100.py`,
scratch, not part of the proof): from each left end, the largest right end whose slack
exceeds `MARGIN`, choosing `N` by reach per prime tower. The point box at `1/2 + 100i`
needs `N = 68` before its imaginary part is pinned below zero: `Im zeta(1/2 + 100i)` is
only about `-0.0204` (measured, mpmath).
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LEAN_DIR = HERE / "lean" / "RHHeight100"

_spec = importlib.util.spec_from_file_location("gen_legs", HERE / "gen_legs.py")
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
G.KE = 10

TOP = (F(100), [(F(1, 2), F(39, 64), 24), (F(39, 64), F(47, 64), 20), (F(47, 64), F(57, 64), 20),
                (F(57, 64), F(71, 64), 20), (F(71, 64), F(91, 64), 18), (F(91, 64), F(63, 32), 16),
                (F(63, 32), F(2), 10)])
POINT = ("Arg100", F(1, 2), F(100), 68, F(-1, 5))


def build(M) -> dict:
    y = TOP[0]
    top = [G.segment(M, a, b, y, N) for a, b, N in TOP[1]]
    assert top[0]["a"] == F(1, 2) and top[-1]["b"] == 2
    for d0, d1 in zip(top, top[1:]):
        assert d0["b"] == d1["a"], "the segments must tile [1/2, 2]"
    for d in top:
        if not d["slack"] > G.MARGIN:
            raise SystemExit(f"REFUSED: slack {float(d['slack'])} at [{d['a']}, {d['b']}]")
    tag, x, yy, N, lo = POINT
    p = G.point(M, x, yy, N, lo)
    if not (p["ok"] and p["margin"] > G.MARGIN):
        raise SystemExit(f"REFUSED: the point box at {x} + {yy} i does not hold with the margin")
    pts = G.render_points([(tag, p)]).replace(
        "Boxes for zeta at 1/2 + 3i and 1/2 + 52i, and the arguments there",
        "The box for zeta at 1/2 + 100i, and the argument there")
    fix = lambda t: t.replace("`hunts/rh_height_lean/gen_legs.py`", "`hunts/rh_height_lean/gen_legs100.py`")
    pts = fix(pts)
    return {
        "LegsTop100A": (fix(G.render_legs("Re zeta > 0 on [1/2, 57/64] + 100i", y, top[:3], 1)), top[:3]),
        "LegsTop100B": (fix(G.render_legs("Re zeta > 0 on [57/64, 2] + 100i", y, top[3:], 4)), top[3:]),
        "LegsArg100": (pts, [p]),
    }


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="compare with the files on disk, write nothing")
    args = ap.parse_args(argv)
    out = build(G.load_mirror())
    bad = 0
    for name, (text, ds) in out.items():
        path = LEAN_DIR / f"{name}.lean"
        for d in ds:
            v = d.get("slack", d.get("margin"))
            print(f"{name}: {float(v):.6f}")
        if args.check:
            same = path.is_file() and path.read_text(encoding="utf-8") == text
            print(f"  {path.name} {'matches' if same else 'differs from'} the generator")
            bad += 0 if same else 1
        else:
            path.write_text(text, encoding="utf-8")
            print(f"  wrote {path.relative_to(ROOT)} ({len(text.splitlines())} lines)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
