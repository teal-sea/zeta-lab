"""Ladder driver: enclosure-checked d_N^2 for N = 1, 2, 4, ..., NMAX.

Checkpoints to results/ladder.json after every N, so a partial run still
reports everything it finished. Also writes per-N coefficient midpoints to
results/coeffs_N{N}.json (floats, for shape analysis only; the balls live
in the ladder records).

Usage: .venv/bin/python run_ladder.py [NMAX] [BUILD_PREC]
"""

from __future__ import annotations

import gc
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vasyunin import (  # noqa: E402
    BD_CONSTANT_STR,
    GramBuilder,
    ball_record,
    bcf_upper_bound,
    solve_d2,
)
from flint import arb, ctx  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE / "results" / "ladder.json"


def solve_prec_list(N: int) -> list[int]:
    if N <= 1024:
        return [64, 96, 128, 192]
    if N <= 2048:
        return [96, 128, 192]
    return [128, 192]


def main() -> None:
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4096
    build_prec = int(sys.argv[2]) if len(sys.argv) > 2 else 256
    ctx.threads = 4

    ladder = [1]
    n = 2
    while n <= nmax:
        ladder.append(n)
        n *= 2
    # two extra points aligned with the repo's cached BBLS-basis runs
    for extra in (40, 50):
        if extra <= nmax and extra not in ladder:
            ladder.append(extra)
    ladder.sort()

    gb = GramBuilder(prec=build_prec)
    records: list[dict] = []
    t_start = time.time()

    for N in ladder:
        rec: dict = {"N": N, "build_prec": build_prec}
        t0 = time.time()
        t_v = gb.extend(N)
        rec["t_vtables"] = round(t_v, 2)
        print(f"N={N}: V tables extended in {t_v:.1f}s", flush=True)

        t0 = time.time()
        G, Gf = gb.gram(N)
        b = gb.rhs(N)
        rec["t_assemble"] = round(time.time() - t0, 2)
        print(f"N={N}: Gram assembled in {rec['t_assemble']}s", flush=True)

        # conditioning (float64 estimate on midpoints; the rigorous story is
        # the solve-precision curve below)
        t0 = time.time()
        try:
            lam = np.linalg.eigvalsh(Gf)
            rec["eig_min"] = float(lam[0])
            rec["eig_max"] = float(lam[-1])
            rec["cond_float64"] = float(lam[-1] / lam[0]) if lam[0] > 0 else None
        except Exception as exc:  # pragma: no cover
            rec["cond_float64"] = None
            rec["cond_error"] = repr(exc)
        rec["t_eig"] = round(time.time() - t0, 2)

        # solve at a ladder of precisions; highest successful one is headline
        rec["solves"] = []
        headline = None
        for P in solve_prec_list(N):
            try:
                s = solve_d2(G, b, prec_solve=P)
                entry = {
                    "prec": P,
                    "ok": True,
                    "d2_rad": float(s["d2"].rad()),
                    "x_max_rad": s["x_max_rad"],
                    "overlap_residual": s["overlap"],
                    "t_solve": round(s["t_solve"], 2),
                }
                headline = (P, s)
            except Exception as exc:
                entry = {"prec": P, "ok": False, "error": repr(exc)}
            rec["solves"].append(entry)
            print(f"N={N}: solve @{P} bits -> {entry}", flush=True)

        if headline is None:
            rec["failed"] = True
            records.append(rec)
            _write(records, t_start)
            continue

        P, s = headline
        ctx.prec = build_prec
        d2 = s["d2"]
        logN = arb(N).log() if N > 1 else arb(0)
        C = arb(BD_CONSTANT_STR)
        rec["headline_prec"] = P
        rec["d2"] = ball_record(d2)
        rec["residual"] = ball_record(s["residual"])
        if N > 1:
            rec["d2_logN"] = ball_record(d2 * logN)
            rec["d2_logN_over_C"] = ball_record(d2 * logN / C)

        # BCF smoothed-Mobius vector: rigorous upper bound at the same N
        if N > 1:
            t0 = time.time()
            ub = bcf_upper_bound(G, b, N, build_prec, gb._logs)
            rec["bcf_upper"] = ball_record(ub)
            rec["bcf_upper_logN"] = ball_record(ub * logN)
            rec["t_bcf"] = round(time.time() - t0, 2)

        # coefficient shape (midpoints only, floats)
        x = s["x"]
        xm = [float(x[i, 0].mid()) for i in range(N)]
        (HERE / "results" / f"coeffs_N{N}.json").write_text(
            json.dumps({"N": N, "x_mid": xm})
        )
        rec["x1"] = xm[0]
        rec["x_max_abs"] = max(abs(v) for v in xm)

        # monotonicity in N (true values are non-increasing; compare balls)
        prev = next((r for r in reversed(records) if "d2" in r), None)
        if prev is not None:
            rec["monotone_mid"] = bool(rec["d2"]["mid"] <= prev["d2"]["mid"])

        rec["t_total"] = round(time.time() - t0 + rec["t_assemble"] + t_v, 2)
        records.append(rec)
        _write(records, t_start)
        del G, Gf, b, s, x
        gc.collect()

    print(f"ladder done in {time.time() - t_start:.0f}s", flush=True)


def _write(records: list[dict], t_start: float) -> None:
    payload = {
        "description": (
            "Enclosure-checked d_N^2 for the Baez-Duarte / Nyman-Beurling "
            "criterion on L^2(0,infty), basis e_k = {1/(kt)}, k = 1..N; "
            "Gram entries by Vasyunin's formula in arb balls, solve by "
            "arb_mat.solve. See MISSION.md, SOURCES.md."
        ),
        "C": BD_CONSTANT_STR,
        "elapsed_s": round(time.time() - t_start, 1),
        "records": records,
    }
    OUT.write_text(json.dumps(payload, indent=1))


if __name__ == "__main__":
    main()
