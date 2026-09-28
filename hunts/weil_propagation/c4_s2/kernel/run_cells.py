"""Write kernel/cells_dps<dps>.json: prolate data, calibration and mission cells.

Usage (from the worktree root):
    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/kernel/run_cells.py --dps 40
    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/kernel/run_cells.py --dps 60

Measured wall time on the operator laptop: see RESULTS.md s6 (each run < 10 min).
Every number is written as a decimal string at the run's dps.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from mpmath import mp  # noqa: E402

import calibrate as C  # noqa: E402
import sonin as S  # noqa: E402

CALIB_C = ["1.5", "1.9", "2.0"]
MISSION_C = ["2.2", "2.5", "2.9"]
NS = [8, 16, 32]
RHOS = ["1.1", "1.2", "1.5", "2", "2.5", "3"]


def sv(x, dps):
    if x is None:
        return None
    if isinstance(x, (list, tuple)):
        return [sv(y, dps) for y in x]
    if isinstance(x, int):
        return x
    return mp.nstr(x, dps, strip_zeros=False) if not isinstance(x, str) else x


def prolate_block(dps):
    out = {}
    for parity in (0, 1):
        d = S.prolate_data(dps, parity)
        with mp.workdps(dps):
            key = "even" if parity == 0 else "odd"
            out[key] = {
                "lam": sv(d["lam"][:8], dps),
                "sum_lam2": sv(mp.fsum(x**2 for x in d["lam"]), dps),
                "t_edge": sv([v * e**2 for v, e in zip(d["v"][:5], d["edge"][:5])], dps),
                "n_max": d["n_max"],
                "J": d["J"],
                "K": d["K"],
            }
    with mp.workdps(dps):
        out["even"]["sum_lam2_closed"] = sv(2 * (mp.si(4 * mp.pi) / (4 * mp.pi) + 1), dps)
        out["odd"]["sum_lam2_closed"] = sv(2 * (1 - mp.si(4 * mp.pi) / (4 * mp.pi)), dps)
    out["even"]["eps1p_series"] = sv(S.eps_right_derivative_at_1(dps, 0, "series"), dps)
    out["even"]["eps1p_split"] = sv(S.eps_right_derivative_at_1(dps, 0, "split"), dps)
    out["odd"]["eps1p_series"] = sv(S.eps_right_derivative_at_1(dps, 1, "series"), dps)
    out["eps"] = {r: sv(S.eps(mp.mpf(r), dps), dps) for r in RHOS}
    out["delta"] = {r: sv(S.delta(mp.mpf(r), dps), dps) for r in RHOS}
    out["eps_odd"] = {r: sv(S.eps(mp.mpf(r), dps, 1), dps) for r in RHOS}
    return out


def cell_block(c, dps):
    res = {}
    for N in NS:
        t0 = time.time()
        o = C.analyze_cell(mp.mpf(c), N, dps)
        res[str(N)] = {
            k: (v if k in ("N", "dps") else sv(v, dps))
            for k, v in o.items()
            if k != "c"
        }
        res[str(N)]["seconds"] = round(time.time() - t0, 1)
        print(f"  c={c} N={N} dps={dps}: {res[str(N)]['seconds']} s", flush=True)
    return res


def moments_block(c, dps, N=32):
    """Generating sequences (s_k, d_k), k = 0..N, of each block at cutoff c.
    Rebuild any N' <= N matrix with sonin.form_from_moments(s[:N'+1], d[:N'+1], N')."""
    win = S.Window(mp.mpf(c), N, dps)
    out = {}
    with mp.workdps(dps + S.GUARD):
        for name, fn in (
            ("A_even", lambda: S._arch_moments(win, 0)),
            ("A_odd", lambda: S._arch_moments(win, 1)),
            ("E_even", lambda: win.moments(lambda x: S._eps_x(x, S.prolate_data(dps, 0)))),
            ("E_odd", lambda: win.moments(lambda x: S._eps_x(x, S.prolate_data(dps, 1)))),
            ("P", lambda: win.moments(lambda x: 2 * mp.cosh(x / 2))),
        ):
            s, d = fn()
            with mp.workdps(dps):
                out[name] = {"s": sv([+x for x in s], dps), "d": sv([+x for x in d], dps)}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=40)
    args = ap.parse_args()
    dps = args.dps
    t0 = time.time()
    data = {
        "dps": dps,
        "conventions": "hunts/weil_propagation/c4_s2/kernel/INTERFACE.md",
        "prolate": prolate_block(dps),
        "calibration": {},
        "mission": {},
        "moments": {},
    }
    print(f"prolate done {time.time() - t0:.1f} s", flush=True)
    for c in CALIB_C:
        data["calibration"][c] = cell_block(c, dps)
    for c in MISSION_C:
        data["mission"][c] = cell_block(c, dps)
        data["moments"][c] = moments_block(c, dps)
    data["seconds_total"] = round(time.time() - t0, 1)
    out = HERE / f"cells_dps{dps}.json"
    out.write_text(json.dumps(data, indent=1) + "\n")
    print(f"wrote {out} in {data['seconds_total']} s")


if __name__ == "__main__":
    main()
