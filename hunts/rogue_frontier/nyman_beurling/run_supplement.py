"""Supplementary N points (non powers of 2) for the approach-curve analysis.

Same pipeline as run_ladder.py, solve at 128 bits only (d2 radius ~1e-37,
five orders below anything the analysis reads). Appends to
results/ladder_supplement.json.

Usage: .venv/bin/python run_supplement.py N1 N2 ...
"""

from __future__ import annotations

import gc
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vasyunin import BD_CONSTANT_STR, GramBuilder, ball_record, solve_d2  # noqa: E402
from flint import arb, ctx  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "results" / "ladder_supplement.json"


def main() -> None:
    Ns = sorted(int(a) for a in sys.argv[1:]) or [192, 384, 768, 1536, 3072]
    ctx.threads = 4
    gb = GramBuilder(prec=256)
    records = []
    if OUT.exists():
        records = json.loads(OUT.read_text())["records"]
    t_start = time.time()
    for N in Ns:
        t0 = time.time()
        gb.extend(N)
        G, Gf = gb.gram(N)
        b = gb.rhs(N)
        lam = np.linalg.eigvalsh(Gf)
        s = solve_d2(G, b, prec_solve=128)
        ctx.prec = 256
        d2 = s["d2"]
        logN = arb(N).log()
        C = arb(BD_CONSTANT_STR)
        rec = {
            "N": N,
            "build_prec": 256,
            "headline_prec": 128,
            "d2": ball_record(d2),
            "residual_overlap": s["overlap"],
            "d2_logN": ball_record(d2 * logN),
            "d2_logN_over_C": ball_record(d2 * logN / C),
            "cond_float64": float(lam[-1] / lam[0]),
            "t_total": round(time.time() - t0, 1),
        }
        records.append(rec)
        OUT.write_text(json.dumps({
            "description": "supplementary points, same pipeline as ladder.json",
            "records": sorted(records, key=lambda r: r["N"]),
        }, indent=1))
        print(f"N={N}: d2={d2.str(25)} ratio={rec['d2_logN_over_C']['mid']:.6f} "
              f"({rec['t_total']}s)", flush=True)
        del G, Gf, b, s
        gc.collect()
    print(f"supplement done in {time.time() - t_start:.0f}s", flush=True)


if __name__ == "__main__":
    main()
