"""Li coefficients of W_{1/4} = zeta(s+1/4) zeta(s-1/4) to past its first negative one.

Run from the repository root:

    .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_wa.py [--n-max 9000]

Writes ``artifacts/wa_quarter.json``: the Cauchy table at radius 0.95, a
second Cauchy table at radius 0.93 as a radius-independence control, the
zero-side values at chosen indices (an independent route that reads zeta's
zeros and never evaluates zeta), and the archimedean / arithmetic split at
chosen indices.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

import mpmath  # noqa: E402
from mpmath import mp  # noqa: E402

from hunts.rh_moonshot.li_arithmetic import li_arith_wa as W  # noqa: E402

DPS = 20


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-max", type=int, default=9000)
    ap.add_argument("--n-points", type=int, default=1 << 15)
    ap.add_argument("--out-dir", default=str(_HERE / "artifacts"))
    args = ap.parse_args()
    out = {"target": "W_a = zeta(s+a) zeta(s-a), completed xi(s+a) xi(s-a)", "a": W.A_DEFAULT}
    out["n_max"] = args.n_max
    t0 = time.time()
    main_run = W.wa_lambda_cauchy(args.n_max, radius="0.95", dps=DPS, n_points=args.n_points)
    out["seconds_main"] = round(time.time() - t0, 1)
    t0 = time.time()
    ctrl = W.wa_lambda_cauchy(args.n_max, radius="0.93", dps=DPS, n_points=args.n_points)
    out["seconds_control"] = round(time.time() - t0, 1)
    L = main_run["coefficients"]
    Lc = ctrl["coefficients"]
    with mp.workdps(DPS + 5):
        rel = [abs(L[i] - Lc[i]) / max(abs(L[i]), 1) for i in range(args.n_max)]
        out["radius_control"] = {
            "main": {k: main_run[k] for k in ("radius", "work_digits", "n_points", "imag_residue_over_floor")},
            "control": {k: ctrl[k] for k in ("radius", "work_digits", "n_points", "imag_residue_over_floor")},
            "max_rel_difference": mpmath.nstr(max(rel), 5),
        }
        negatives = [i + 1 for i in range(args.n_max) if L[i] < 0]
        out["first_negative_index"] = negatives[0] if negatives else None
        out["count_negative_up_to_n_max"] = len(negatives)
        imin = min(range(args.n_max), key=lambda i: L[i])
        out["min_index"] = imin + 1
        out["min_value"] = mpmath.nstr(L[imin], 12)
        n0 = out["first_negative_index"]
        picks = [1, 2, 10, 100, 1000, 2000, 5000]
        if n0:
            picks += [n0 - 2, n0 - 1, n0, n0 + 1, n0 + 2, imin + 1]
        picks = sorted({p for p in picks if 1 <= p <= args.n_max})
        t0 = time.time()
        Z = W.wa_lambda_zeros(picks, n_zeros=1000, dps=DPS)
        out["seconds_zero_side"] = round(time.time() - t0, 1)
        out["zero_side"] = {
            str(p): {
                "cauchy": mpmath.nstr(L[p - 1], 15),
                "zeros": mpmath.nstr(Z[j], 15),
                "abs_difference": mpmath.nstr(abs(L[p - 1] - Z[j]), 4),
            }
            for j, p in enumerate(picks)
        }
        split = {}
        for p in picks:
            Aw = W.wa_archimedean(p, dps=DPS)
            split[str(p)] = {
                "lambda": mpmath.nstr(L[p - 1], 15),
                "A_W": mpmath.nstr(Aw, 15),
                "T_W": mpmath.nstr(L[p - 1] - Aw, 15),
            }
        out["split"] = split
        out["lambda"] = [mpmath.nstr(v, 15) for v in L]
    out["generated"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    od = Path(args.out_dir)
    od.mkdir(parents=True, exist_ok=True)
    (od / "wa_quarter.json").write_text(json.dumps(out, indent=1))
    print({k: v for k, v in out.items() if k not in ("lambda", "zero_side", "split")})


if __name__ == "__main__":
    main()
