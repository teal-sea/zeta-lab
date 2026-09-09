"""The two-variable law: is the attainable-cell excess really C * N / sqrt(y)?

`hunts/prime_pair_error/frontier/.../RESULTS.md` section 4.1 reports
`E = 0.32 N/sqrt(y)` for the all-cell floor `V*` over four decades, and adds
in one sentence that "the same holds, with constant 0.2" for the
cutoff-indexed relaxation `T*`.  That sentence carries the barrier for the
relaxed family, and it rests on the `y = sqrt(N)` diagonal alone, where `y`
and `N` move together and a floor effect in `y = floor(sqrt(N))` is
indistinguishable from a change in the exponent.

This sweep separates them: hold `N` and move `y`, hold `y` and move `N`, and
report `E * sqrt(y) / N` on the grid.  A law with one constant is a flat
surface; anything else is a two-parameter family being read off a line.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import numpy as np

import lp

ART = Path(__file__).resolve().parent / "artifacts"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--alpha", type=float, nargs="+",
                    default=[0.35, 0.40, 0.45, 0.50, 0.55, 0.60],
                    help="support exponent: y = round(N**alpha)")
    ap.add_argument("--out", default="sweep.json")
    args = ap.parse_args()

    rows = []
    for N in args.N:
        for a in args.alpha:
            y = max(2, int(round(N ** a)))
            if y >= N:
                continue
            r = lp.solve(N, y, verbose=False)
            r["alpha_requested"] = a
            r["alpha_effective"] = math.log(y) / math.log(N)
            if r["excess"] is not None:
                r["E_sqrt_y_over_N"] = r["excess"] * math.sqrt(y) / N
                r["E_over_N_pow_075"] = r["excess"] / N ** 0.75
            rows.append(r)
            print(f"N={N:>9d} y={y:>6d} alpha={r['alpha_effective']:.3f} "
                  f"cells={r['cells']:>6d} E={r['excess']!r:>22s} "
                  f"E*sqrt(y)/N={r.get('E_sqrt_y_over_N')!r:>22s} "
                  f"({r['solve_seconds']}s)", flush=True)
    ART.mkdir(exist_ok=True)
    (ART / args.out).write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / args.out}")


if __name__ == "__main__":
    main()
