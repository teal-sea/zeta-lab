"""Compute the archimedean / arithmetic split for zeta and DH and write artifacts.

Run from the repository root:

    .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_split.py [--n-zeta 5000] [--n-dh 5000]

Writes ``artifacts/split_zeta.json`` and ``artifacts/split_dh.json``.  Each
holds, for n = 1..N: the archimedean part A(n) (binomial route), the
arithmetic part T(n) (Cauchy route on log of the arithmetic factor, Arb
evaluator), lambda_n from an independent Cauchy route on the completed
function (zeta only; Arb evaluator), and the identity defect against the
`li_dh_onset` lambda table on its range.  Spot values of A(n) by the series
route are recorded too.  Numbers are stored as decimal strings at 30 digits.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]
if str(_ROOT) not in sys.path:
    sys.path.insert(0, str(_ROOT))

import mpmath  # noqa: E402
from mpmath import mp  # noqa: E402

from hunts.rh_moonshot.li_arithmetic import li_arith_split as S  # noqa: E402

DPS = 30
SPOT = [1, 2, 3, 5, 10, 50, 100, 500, 1000, 2000, 3000, 5000]


def _xi_evaluator(s):
    """xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s) on Arb."""
    from flint import acb, arb

    return s * (s - 1) / 2 * acb(arb.pi()) ** (-s / 2) * (s / 2).gamma() * s.zeta()


def _strs(values, digits=DPS):
    with mp.workdps(digits + 5):
        return [mpmath.nstr(v, digits) for v in values]


def run_zeta(n_max: int, radius: str = "0.95") -> dict:
    out = {"target": "zeta", "n_max": n_max, "dps": DPS, "radius": radius}
    t0 = time.time()
    A = S.zeta_archimedean(n_max, DPS)
    out["seconds_archimedean"] = round(time.time() - t0, 1)
    wd = S.work_digits(n_max, DPS, radius)
    N = S.node_count(n_max, wd, radius)
    t0 = time.time()
    resT = S.cauchy_log_coefficients(S.zeta_arith_evaluator, n_max, radius, wd, N)
    out["seconds_arithmetic"] = round(time.time() - t0, 1)
    t0 = time.time()
    resL = S.cauchy_log_coefficients(_xi_evaluator, n_max, radius, wd, N)
    out["seconds_lambda"] = round(time.time() - t0, 1)
    T = resT["coefficients"]
    L = resL["coefficients"]
    out.update(
        work_digits=wd,
        n_points=N,
        imag_residue_over_floor_T=resT["imag_residue_over_floor"],
        imag_residue_over_floor_lambda=resL["imag_residue_over_floor"],
    )
    ref = S.load_lambda("xi")
    with mp.workdps(DPS + 5):
        defect_identity = [L[i] - A[i] - T[i] for i in range(n_max)]
        defect_vs_ref = [ref[i] - L[i] for i in range(min(n_max, len(ref)))]
        out["max_abs_identity_defect"] = mpmath.nstr(max(abs(d) for d in defect_identity), 5)
        out["max_rel_lambda_vs_li_dh_onset_table"] = mpmath.nstr(
            max(abs(defect_vs_ref[i]) / abs(ref[i]) for i in range(len(defect_vs_ref))), 5
        )
        spot = {}
        for n in SPOT:
            if n <= n_max:
                As = S.zeta_archimedean_series(n, DPS)
                spot[str(n)] = {
                    "A_binomial": mpmath.nstr(A[n - 1], DPS),
                    "A_series": mpmath.nstr(As, DPS),
                    "difference": mpmath.nstr(A[n - 1] - As, 5),
                }
        out["series_spot_checks"] = spot
    out["A"] = _strs(A)
    out["T"] = _strs(T)
    out["lambda"] = _strs(L)
    return out


def run_dh(n_max: int, radius: str = "0.95") -> dict:
    from flint import ctx

    out = {"target": "dh", "n_max": n_max, "dps": DPS, "radius": radius}
    t0 = time.time()
    A = S.dh_archimedean(n_max, DPS)
    out["seconds_archimedean"] = round(time.time() - t0, 1)
    wd = S.work_digits(n_max, DPS, radius)
    N = S.node_count(n_max, wd, radius)
    f = S.dh_f_evaluator(wd + 20)
    t0 = time.time()
    resT = S.cauchy_log_coefficients(f, n_max, radius, wd, N)
    out["seconds_arithmetic"] = round(time.time() - t0, 1)
    T = resT["coefficients"]
    out.update(work_digits=wd, n_points=N, imag_residue_over_floor_T=resT["imag_residue_over_floor"])
    ref = S.load_lambda("dh")
    m = min(n_max, len(ref))
    with mp.workdps(DPS + 5):
        defect = [ref[i] - A[i] - T[i] for i in range(m)]
        out["max_abs_identity_defect_vs_li_dh_onset_table"] = mpmath.nstr(
            max(abs(d) for d in defect), 5
        )
        out["max_rel_identity_defect"] = mpmath.nstr(
            max(abs(defect[i]) / abs(ref[i]) for i in range(m)), 5
        )
        spot = {}
        for n in SPOT:
            if n <= n_max:
                As = S.dh_archimedean_series(n, DPS)
                spot[str(n)] = {
                    "A_binomial": mpmath.nstr(A[n - 1], DPS),
                    "A_series": mpmath.nstr(As, DPS),
                    "difference": mpmath.nstr(A[n - 1] - As, 5),
                }
        out["series_spot_checks"] = spot
    out["A"] = _strs(A)
    out["T"] = _strs(T)
    out["lambda_from_li_dh_onset"] = _strs(ref[:m])
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-zeta", type=int, default=5000)
    ap.add_argument("--n-dh", type=int, default=5000)
    ap.add_argument("--out-dir", default=str(S.ARTIFACTS))
    args = ap.parse_args()
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y-%m-%dT%H:%M:%S")
    if args.n_zeta > 0:
        z = run_zeta(args.n_zeta)
        z["generated"] = stamp
        (out_dir / "split_zeta.json").write_text(json.dumps(z, indent=1))
        print("zeta done", {k: v for k, v in z.items() if not isinstance(v, (list, dict))})
    if args.n_dh > 0:
        d = run_dh(args.n_dh)
        d["generated"] = stamp
        (out_dir / "split_dh.json").write_text(json.dumps(d, indent=1))
        print("dh done", {k: v for k, v in d.items() if not isinstance(v, (list, dict))})


if __name__ == "__main__":
    main()
