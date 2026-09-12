"""Exhaustive search: which bijection Z_12 -> hue 12-gon best orders dissonance?

Objective: Spearman correlation, over the 66 unordered pairs, between the hue
distance d(f(x), f(y)) on the 12-gon and the dissonance of interval class
ic(x - y). Three dissonance measures (pc.dissonance_measures) are run
separately and never averaged.

Search space: all 12! bijections modulo hue rotation (fix f(0) = 0) and hue
reflection (require f(1) <= 6), i.e. 11!/2 + a few fixed points = 19,958,400
candidates, evaluated exactly. The null is the same objective on uniformly
random bijections. Writes results_consonance.json.
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.stats import rankdata

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pc  # noqa: E402

N = 12
PAIRS = pc.pair_indices(N)
I, J = PAIRS[:, 0], PAIRS[:, 1]
MEASURES = pc.dissonance_measures(N)
# rank vector of the dissonance per pair, for each measure
RANKS = {name: rankdata([m[pc.ic(j - i)] for i, j in PAIRS]) for name, m in MEASURES.items()}


def spearman_batch(F):
    """F: (B, 12) int array of bijections. Returns dict name -> (B,) Spearman."""
    d = np.abs(F[:, I] - F[:, J]) % N
    d = np.minimum(d, N - d)  # (B, 66) hue distances, each in 1..6
    out = {}
    for name, r in RANKS.items():
        rd = rankdata(d, axis=1)
        x = rd - rd.mean(axis=1, keepdims=True)
        y = r - r.mean()
        out[name] = (x @ y) / np.sqrt((x * x).sum(axis=1) * (y * y).sum())
    return out


def exhaustive(batch=500_000):
    best = {name: (-2.0, None) for name in RANKS}
    hist = {name: {} for name in RANKS}
    count = 0
    buf = []
    t0 = time.time()

    def flush():
        nonlocal count
        F = np.array(buf, dtype=np.int64)
        sc = spearman_batch(F)
        for name, s in sc.items():
            k = int(np.argmax(s))
            if s[k] > best[name][0] + 1e-12:
                best[name] = (float(s[k]), tuple(int(v) for v in F[k]))
            h = hist[name]
            for key, c in zip(*np.unique(np.round(s, 3), return_counts=True)):
                h[float(key)] = h.get(float(key), 0) + int(c)
        count += len(buf)
        buf.clear()

    for perm in itertools.permutations(range(1, N)):
        if perm[0] > 6:
            continue
        buf.append((0,) + perm)
        if len(buf) >= batch:
            flush()
            print(f"  {count:,} evaluated, {time.time() - t0:.0f}s", file=sys.stderr, flush=True)
    if buf:
        flush()
    return best, hist, count


def null(samples=200_000, seed=0):
    rng = np.random.default_rng(seed)
    F = np.array([rng.permutation(N) for _ in range(samples)])
    return spearman_batch(F)


def main():
    affine = pc.affine_maps(N)
    aff_scores = spearman_batch(np.array(affine))
    chrom = spearman_batch(np.array([tuple(range(N))]))
    fifths = spearman_batch(np.array([tuple((7 * x) % N for x in range(N))]))
    nul = null()
    best, hist, count = exhaustive()
    out = {"evaluated": count, "measures": {}}
    for name in RANKS:
        nz = nul[name]
        out["measures"][name] = {
            "dissonance_by_ic": {str(k): float(v) for k, v in MEASURES[name].items()},
            "chromatic": float(chrom[name][0]),
            "fifths": float(fifths[name][0]),
            "affine_distinct_scores": sorted({round(float(v), 6) for v in aff_scores[name]}),
            "best": best[name][0],
            "best_map": best[name][1],
            "best_is_affine": best[name][1] in set(affine),
            "null_mean": float(nz.mean()),
            "null_sd": float(nz.std()),
            "null_max": float(nz.max()),
            "null_frac_ge_fifths": float((nz >= fifths[name][0] - 1e-12).mean()),
            "exhaustive_frac_ge_fifths": sum(c for k, c in hist[name].items() if k >= round(fifths[name][0], 3) - 1e-9) / count,
            "exhaustive_hist_0.001": {str(k): c for k, c in sorted(hist[name].items())},
        }
    Path(__file__).with_name("results_consonance.json").write_text(json.dumps(out, indent=1))
    for name, r in out["measures"].items():
        print(name, "chrom", round(r["chromatic"], 4), "fifths", round(r["fifths"], 4), "best", round(r["best"], 4), r["best_map"], "affine?", r["best_is_affine"], "null mean/sd/max", round(r["null_mean"], 3), round(r["null_sd"], 3), round(r["null_max"], 3), "frac>=fifths exhaustive", r["exhaustive_frac_ge_fifths"])


if __name__ == "__main__":
    main()
