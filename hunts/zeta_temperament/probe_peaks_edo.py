"""Calibration against the known result, and the harmonic horizon.

1. Peaks. With t = 2 pi x / ln 2, |Z(t)| at integer x is a tuning-quality score
   for the x-note equal temperament (Gene Ward Smith; OEIS A117536). This is
   reproduced, not claimed: |Z| at integer x against an independent
   Diophantine tuning error that never mentions zeta, Spearman over x in
   [5, 400], and the rank of the temperaments practice selected.

2. Horizon. The Riemann-Siegel main sum runs over n <= sqrt(t / 2pi) =
   sqrt(x / ln 2). So the zeta score of the x-EDO is decided by the harmonics
   up to about 1.2 sqrt(x), plus a universal remainder of size x^{-1/4} that
   does not depend on how the higher harmonics are tuned. For 12-EDO that is
   harmonics 1 to 4: the score never looks at the major third directly.
Writes results_peaks.json.
"""

from __future__ import annotations

import json
import sys
from math import log
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT))
from zeta.core import rs_theta  # noqa: E402
from zeta.statistics import riemann_siegel_z  # noqa: E402

LN2 = log(2.0)
X2T = 2 * np.pi / LN2
CLASSIC = [12, 19, 22, 31, 41, 53, 72, 99, 118, 152, 171, 224, 270, 311, 342]


def tuning_error(x, primes=(3, 5, 7)):
    """RMS of the x-EDO's error in approximating log2 p, weighted 1/sqrt p."""
    w = [1 / np.sqrt(p) for p in primes]
    e = sum(wt * (x * np.log2(p) - np.round(x * np.log2(p))) ** 2 for p, wt in zip(primes, w))
    return np.sqrt(e / sum(w))


def main():
    out = {}
    xs = np.arange(5, 401)
    Z = np.abs(riemann_siegel_z(X2T * xs.astype(float)))
    xc = np.arange(5.0, 401.0, 0.01)
    zc = np.abs(riemann_siegel_z(X2T * xc))
    scale = np.array([np.sqrt(np.mean(zc[(xc > x - 15) & (xc < x + 15)] ** 2)) for x in xs])
    Zn = Z / scale
    out["spearman_by_prime_set"] = {}
    for primes in [(3,), (3, 5), (3, 5, 7), (3, 5, 7, 11), (3, 5, 7, 11, 13)]:
        e = tuning_error(xs.astype(float), primes)
        out["spearman_by_prime_set"][",".join(map(str, primes))] = {
            "raw": float(spearmanr(Z, e).correlation), "detrended": float(spearmanr(Zn, e).correlation)}
    e = tuning_error(xs.astype(float))
    out["spearman_x_vs_error"] = float(spearmanr(xs, e).correlation)
    rng = np.random.default_rng(0)
    null = np.array([abs(spearmanr(rng.random(len(xs)), e).correlation) for _ in range(2000)])
    out["null_abs_spearman_p999"] = float(np.percentile(null, 99.9))
    order = xs[np.argsort(-Zn)]
    rank = {int(x): int(np.where(order == x)[0][0]) + 1 for x in xs}
    out["top24_detrended"] = sorted(int(v) for v in order[:24])
    out["classic_ranks_of_396"] = {str(c): rank[c] for c in CLASSIC}
    out["classic_in_top24"] = sum(1 for c in CLASSIC if rank[c] <= 24)
    out["classic_in_top24_chance"] = 24 / len(xs) * len(CLASSIC)
    # harmonic horizon
    horizon = []
    for x in (5, 7, 12, 19, 22, 31, 41, 53, 72, 118, 311):
        t = X2T * x
        a = np.sqrt(t / (2 * np.pi))
        N = int(a)
        th = float(rs_theta(t))
        main = 2 * sum(n ** -0.5 * np.cos(th - t * np.log(n)) for n in range(1, N + 1))
        full = float(mp.siegelz(t))
        horizon.append({"x": x, "horizon": float(a), "N": N, "main_sum": main, "Z": full, "remainder": full - main})
    out["horizon"] = horizon
    (HERE / "results_peaks.json").write_text(json.dumps(out, indent=1))
    print(json.dumps({k: v for k, v in out.items() if k != "horizon"}, indent=1))
    for h in horizon:
        print(f"x={h['x']:4d} horizon {h['horizon']:6.2f} harmonics 1..{h['N']:2d} main {h['main_sum']:+7.3f} Z {h['Z']:+7.3f} remainder {h['remainder']:+.3f}")


if __name__ == "__main__":
    main()
