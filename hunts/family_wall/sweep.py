"""Phase A of Hunt #84, on one CPU, free.

Float floors c*_n(p) and Phi_n for one n over a pressure grid, using the batched
optimiser in fastf.py. Written to run anywhere a CPU is: a laptop, a GitHub Actions
runner, or a Modal container. No Modal import, no provider dependency.

  python sweep.py --n 12 --out artifacts/phase-a-n12.json

Every floor is the value of F at a point, hence an UPPER bound on inf F, and every
Phi evaluated at one is OPTIMISTIC. The formula Phi_n itself is proved for every n
(lean/bridge, n_point_bound); what is unproved at each n is the certificate.

Seeding: all 2^(n-1) two-zero words at every pressure, because every known minimiser
at n = 7, 8, 9 is a word in the first two positive kernel zeros only; a deeper
alphabet where it is affordable; plus random starts as a control on that assumption.
If a random start ever wins, the two-zero assumption is wrong and the run says so.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import time

import numpy as np

import fastf

H_CONST = 1.5 - (1 / math.sqrt(2)) / math.tan(1 / math.sqrt(2))
CEILING = 0.6818286874638
PRESSURES = (2800, 3200, 3600, 4000, 4400, 4800, 5200, 6000, 6800, 8000)

# alphabet depth per n: 2-zero words everywhere, deeper only while the batch fits
DEPTH = {7: 4, 8: 4, 9: 4, 10: 3, 11: 3, 12: 3, 13: 2, 14: 2, 15: 2, 16: 2, 18: 2, 20: 2}
RANDOM_STARTS = 4000


def phi_n(n_points: int, c: float, p: float):
    k = n_points - 1
    m = k + int(math.floor(1 / c))
    return m, (H_CONST - k * (m - 1) / (p * m)) / (1 - c * (m - k) / m)


def pattern(x):
    out = []
    for g in x:
        j = min(range(4), key=lambda i: abs(fastf.KERNEL_ZEROS[i] - g))
        out.append(str(j + 1) if abs(fastf.KERNEL_ZEROS[j] - g) < 0.3 else f"?{g:.2f}")
    return "-".join(out)


def canon(x):
    return x if x[0] >= x[-1] else x[::-1]


def run_n(n: int, pressures=PRESSURES, seed: int = 0) -> dict:
    k = n - 1
    alpha = DEPTH.get(n, 2)
    rng = np.random.default_rng(seed * 1000003 + n)
    base = fastf.words(k, alpha)
    rand = rng.uniform(0.5, 4.0, size=(RANDOM_STARTS, k))
    seeds = np.vstack([base, rand])
    rows = []
    t0 = time.perf_counter()
    for p in pressures:
        t1 = time.perf_counter()
        x, F, ranked = fastf.minimise_cell(n, float(p), seeds, top=300)
        x = canon(x)
        # did a random start beat every kernel-zero word? that would refute the ansatz
        xb, Fb, _ = fastf.minimise_cell(n, float(p), base, top=200)
        m, phi = phi_n(n, F, float(p))
        rows.append({
            "n_points": n, "p": p,
            "best_F": F,
            "best_F_note": "float value of F at a point: an UPPER bound on inf F",
            "argmin": list(map(float, x)),
            "gap_sum": float(np.sum(x)),
            "pattern": pattern(x),
            "palindromic": bool(np.max(np.abs(x - x[::-1])) < 1e-4),
            "words_only_best_F": Fb,
            "random_start_improved": bool(Fb - F > 1e-12),
            "second_distinct_F": next((f for f, _ in ranked if f - F > 1e-9), None),
            "m_cap": m, "phi_at_cap": phi,
            "distance_to_ceiling": CEILING - phi,
            "seconds": round(time.perf_counter() - t1, 1),
        })
        print(f"n={n} p={p}: F={F:.15f} sum={np.sum(x):.4f} {pattern(x)} "
              f"m={m} Phi={phi:.12f} ({rows[-1]['seconds']}s)", flush=True)
    peak = max(rows, key=lambda r: r["phi_at_cap"])
    return {
        "n_points": n,
        "alphabet": alpha,
        "seeds": int(seeds.shape[0]),
        "random_starts": RANDOM_STARTS,
        "pressures": list(pressures),
        "H": H_CONST,
        "ceiling": CEILING,
        "phi_formula": ("Phi_n(c,m,p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m), "
                        "m = (n-1)+floor(1/c); proved for every n in lean/bridge (n_point_bound)"),
        "peak": {k2: peak[k2] for k2 in ("p", "best_F", "m_cap", "phi_at_cap", "argmin",
                                         "gap_sum", "pattern", "palindromic", "distance_to_ceiling")},
        "peak_on_grid_edge": peak["p"] in (pressures[0], pressures[-1]),
        "table": rows,
        "wall_seconds": round(time.perf_counter() - t0, 1),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out", default=None)
    ap.add_argument("--pressures", default="")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest and not fastf.selftest():
        raise SystemExit("fastf selftest failed")
    ps = tuple(int(v) for v in a.pressures.split(",")) if a.pressures else PRESSURES
    res = run_n(a.n, ps)
    out = a.out or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "artifacts", f"phase-a-n{a.n}.json")
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(res, fh, indent=1)
    pk = res["peak"]
    print(f"\nn={a.n} peak: p={pk['p']} Phi={pk['phi_at_cap']:.12f} "
          f"gap to ceiling {pk['distance_to_ceiling']:.8f}  -> {out}")


if __name__ == "__main__":
    main()
