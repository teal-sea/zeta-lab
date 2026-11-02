"""Scan zeta zeros up to T with the repo's Riemann-Siegel scanner and save them in lab/data/.

Run: lab/.venv/bin/python lab/scan_zeros.py 100000

Completeness check, from zeta/statistics.py's own validation: D_n = n - 1 - theta(gamma_n)/pi
equals S(gamma_n) + 1/2, so a missed or spurious zero shifts every later D_n by 1. The
mean of D over blocks of 250 consecutive zeros must stay near 1/2. This is a float-grade
check, OBSERVED, not Turing's method.
"""
import json
import sys
import time
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from zeta.statistics import riemann_siegel_theta, zero_ordinates  # noqa: E402


def main(t_max: float) -> int:
    t0 = time.time()
    g = zero_ordinates(t_max=t_max, use_cache=False)
    secs = time.time() - t0
    n = np.arange(1, g.size + 1)
    d = n - 1 - riemann_siegel_theta(g) / np.pi
    nb = d.size // 250
    blocks = d[: nb * 250].reshape(nb, 250).mean(axis=1)
    ok = bool(g.size > 0 and np.all(np.diff(g) > 0) and 0.3 < blocks.min() and blocks.max() < 0.7)
    out = Path(__file__).resolve().parent / "data" / f"zeros_T{int(t_max)}.npz"
    out.parent.mkdir(exist_ok=True)
    np.savez_compressed(out, gammas=g, t_max=np.float64(t_max))
    report = {
        "t_max": t_max,
        "zeros": int(g.size),
        "seconds": round(secs, 1),
        "first": float(g[0]),
        "last": float(g[-1]),
        "blocks_of_250": int(nb),
        "block_mean_D_min": round(float(blocks.min()), 4),
        "block_mean_D_max": round(float(blocks.max()), 4),
        "max_abs_D_minus_half": round(float(np.max(np.abs(d - 0.5))), 3),
        "complete_by_block_test": ok,
        "saved": str(out.relative_to(ROOT)),
    }
    print(json.dumps(report))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(float(sys.argv[1])))
