"""Modal float sweep of the n-point family toward its wall (Hunt #82, phase A).

Question: does max_p Phi_n at the floor climb to the configuration ceiling
0.6818286874638 as n grows, or converge short of it?  This phase produces float
floors c*_n(p) for n in {9, 10, 11, 12, 14, 16} over a 10-value pressure grid,
the argmin structure per cell, and Arb enclosures at every winning point.  It
proves nothing: every best F is the value of F at a point, hence an UPPER bound
on inf F, and every Phi is evaluated at that upper bound (OPTIMISTIC).  Phase B
(rigorous certificates via the sharded verifier) is separate and not this file.

The bound formula is no longer inferred: `n_point_bound` (lean/bridge, merged)
proves Phi_n(c, m, p) = (H - (n-1)(m-1)/(pm)) / (1 - c(m-(n-1))/m) for every n,
GIVEN the certificate `F_{n-1} >= c on nonnegative gaps` and the cap
c(m-(n-1)) <= 1.  What stays unproved at each new n is the certificate itself;
the floors below are candidates for one, not one.

Seeding follows the seven-point lessons (TRUST-MAP.md 1.5): multistart alone
missed the non-palindromic floor; exhaustive kernel-zero words found it.  Every
known winner at n = 7, 8, 9 is a word in the first TWO positive kernel zeros
only, so the 2-zero exhaustive pass runs at every cell; deeper alphabets (3- and
4-zero words) run where the one-core benchmark says they are affordable:
14.4 ms per Nelder-Mead run at n=9 rising to 173 ms at n=16, so 4^(n-1) is
affordable through n=10, 3^(n-1) through n=12, 2^(n-1) everywhere.

Controls that must hold in the output:
  n=7 p=3000 exhaustive best within 1e-9 of the Arb value 0.0038262312115073;
  n=9 p=4000 best <= the prior sweep's 0.003927926119847278 (npoint-sweep.json).

Run (from the repo root; the client process must stay alive to collect):
  ZSZ_SRC=... .venv/bin/modal run hunts/family_wall/modal_family_wall.py
"""
from __future__ import annotations

import json
import math
import os
import random
import sys
import time

import modal

ZSZ_SRC = os.environ.get(
    "ZSZ_SRC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".upstream", "zeta-simple-zeros", "src", "zeta_simple_zeros")
)
HERE = os.path.dirname(os.path.abspath(__file__))

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0")
    .add_local_dir(ZSZ_SRC, remote_path="/root/zsz/zeta_simple_zeros")
)
app = modal.App("zeta-hunt82-family-wall", image=image)
vol = modal.Volume.from_name("zeta-hunt82-family-wall", create_if_missing=True)

N_POINTS = (9, 10, 11, 12, 14, 16)
PRESSURES = (2800, 3200, 3600, 4000, 4400, 4800, 5200, 6000, 6800, 8000)

# per-n exhaustive passes: (alphabet size, pressures). The 2-zero pass covers the
# family class every known winner lives in; deeper alphabets guard the cells where
# the one-core benchmark keeps them under ~2.5 core-hours each.
EXHAUSTIVE = {
    9: ((4, (3600, 4000, 4400)), (2, PRESSURES)),
    10: ((4, (4000,)), (3, (3600, 4400)), (2, PRESSURES)),
    11: ((3, (4000, 4800)), (2, PRESSURES)),
    12: ((3, (4400,)), (2, PRESSURES)),
    14: ((2, PRESSURES),),
    16: ((2, (4400, 4800, 5200, 6000)),),
}

CONTAINERS = 24
RESTARTS = 45
COMBO_CHUNK = 2048

CONTROL_F = 0.0038262312115073
CONTROL_ARGMIN = [1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002]
PRIOR_N9_P4000 = 0.003927926119847278  # npoint-sweep.json, coarse grid
CEILING = 0.6818286874638

KERNEL_ZEROS = (1.057278, 2.030068, 3.020243, 4.015236)
BANDS = ((0.95, 1.20), (1.80, 2.35), (2.64, 4.0))

H_CONST = 1.5 - (1 / math.sqrt(2)) / math.tan(1 / math.sqrt(2))


# ----------------------------------------------------------------------------
# float functional and optimiser -- as in modal_npoint_sweep.py
# ----------------------------------------------------------------------------
def _float_F(n_points: int, p: float):
    S2 = math.sqrt(2.0)
    K0 = S2 * math.sin(1 / S2)

    def sinc(x):
        return 1.0 if abs(x) < 1e-12 else math.sin(x) / x

    def w(x):
        f = 2 * math.pi * x
        return (((sinc((S2 - f) / 2) + sinc((S2 + f) / 2)) / 2) / K0) ** 2

    n = n_points
    C = {s: 2.0 / (n - s) for s in range(1, n)}

    def F(g):
        if min(g) < 0:
            return float("inf")
        v = sum(g) / p
        for s in range(1, n):
            for i in range(n - s):
                v += C[s] * w(sum(g[i : i + s]))
        return v

    return F


def _nelder_mead(f, x0, step=0.2, iters=5000, tol=1e-13):
    n = len(x0)
    pts = [list(x0)]
    for i in range(n):
        y = list(x0)
        y[i] += step
        pts.append(y)
    vals = [f(p) for p in pts]
    for _ in range(iters):
        order = sorted(range(n + 1), key=lambda i: vals[i])
        pts = [pts[i] for i in order]
        vals = [vals[i] for i in order]
        if abs(vals[-1] - vals[0]) < tol:
            break
        c = [sum(p[j] for p in pts[:-1]) / n for j in range(n)]
        xr = [c[j] + (c[j] - pts[-1][j]) for j in range(n)]
        fr = f(xr)
        if fr < vals[0]:
            xe = [c[j] + 2 * (c[j] - pts[-1][j]) for j in range(n)]
            fe = f(xe)
            pts[-1], vals[-1] = (xe, fe) if fe < fr else (xr, fr)
        elif fr < vals[-2]:
            pts[-1], vals[-1] = xr, fr
        else:
            xc = [c[j] + 0.5 * (pts[-1][j] - c[j]) for j in range(n)]
            fc = f(xc)
            if fc < vals[-1]:
                pts[-1], vals[-1] = xc, fc
            else:
                for i in range(1, n + 1):
                    pts[i] = [pts[0][j] + 0.5 * (pts[i][j] - pts[0][j]) for j in range(n)]
                    vals[i] = f(pts[i])
    i = min(range(n + 1), key=lambda i: vals[i])
    return pts[i], vals[i]


def _polish(F, x, rounds=4):
    best_x, best_v = list(x), F(x)
    for step in (0.05, 0.01, 0.002, 0.0005)[:rounds]:
        y, v = _nelder_mead(F, best_x, step=step, iters=20000, tol=1e-17)
        if v < best_v:
            best_x, best_v = y, v
    return best_x, best_v


def phi_n(n_points: int, c: float, p: float) -> tuple[int, float]:
    """Phi_n at the m-cap. Formula proved for every n (lean/bridge n_point_bound);
    the value is OPTIMISTIC because c here is a float upper bound on inf F."""
    k = n_points - 1
    m = k + int(math.floor(1 / c))
    phi = (H_CONST - k * (m - 1) / (p * m)) / (1 - c * (m - k) / m)
    return m, phi


def _pattern(gaps) -> str:
    out = []
    for g in gaps:
        j = min(range(len(KERNEL_ZEROS)), key=lambda i: abs(KERNEL_ZEROS[i] - g))
        out.append(str(j + 1) if abs(KERNEL_ZEROS[j] - g) < 0.3 else f"?{g:.2f}")
    return "-".join(out)


def _canon(gaps):
    g = list(gaps)
    return g if g[0] >= g[-1] else g[::-1]


def _combo_seed(index: int, k: int, alphabet: int):
    out = []
    for _ in range(k):
        out.append(KERNEL_ZEROS[index % alphabet])
        index //= alphabet
    return out


# ----------------------------------------------------------------------------
@app.function(cpu=1, timeout=3600)
def n_point_floor(args: tuple) -> dict:
    n_points, p, seed, restarts = args
    F = _float_F(n_points, p)
    rnd = random.Random(seed * 1000003 + n_points * 101 + int(p))
    k = n_points - 1
    best = (float("inf"), None, None)
    per_mode = {"bands": float("inf"), "random": float("inf"), "zeros": float("inf")}
    t0 = time.perf_counter()
    modes = ["bands", "random", "zeros"]
    for r in range(restarts):
        mode = modes[r % 3]
        if mode == "bands":
            x0 = [rnd.uniform(*rnd.choice(BANDS)) for _ in range(k)]
        elif mode == "random":
            x0 = [rnd.uniform(0.5, 4.0) for _ in range(k)]
        else:
            x0 = [rnd.choice(KERNEL_ZEROS[:2] * 3 + KERNEL_ZEROS[2:]) for _ in range(k)]
        x, v = _nelder_mead(F, x0, step=rnd.choice([0.05, 0.2, 0.5]))
        if v < per_mode[mode]:
            per_mode[mode] = v
        if v < best[0]:
            best = (v, x, mode)
    x, v = _polish(F, best[1], rounds=2)
    return {
        "n_points": n_points,
        "p": p,
        "seed": seed,
        "restarts": restarts,
        "best": v,
        "argmin": x,
        "best_mode": best[2],
        "per_mode_best": per_mode,
        "seconds": round(time.perf_counter() - t0, 1),
    }


@app.function(cpu=1, timeout=3600)
def exhaustive_floor(args: tuple) -> dict:
    n_points, p, alphabet, start, end = args
    F = _float_F(n_points, p)
    k = n_points - 1
    best = (float("inf"), None, None)
    t0 = time.perf_counter()
    for idx in range(start, end):
        x, v = _nelder_mead(F, _combo_seed(idx, k, alphabet), step=0.05)
        if v < best[0]:
            best = (v, x, idx)
    x, v = _polish(F, best[1], rounds=2)
    return {
        "n_points": n_points,
        "p": p,
        "alphabet": alphabet,
        "start": start,
        "end": end,
        "best": v,
        "argmin": x,
        "combo_index": best[2],
        "seconds": round(time.perf_counter() - t0, 1),
    }


@app.function(cpu=1, timeout=600)
def arb_at_point(args: tuple) -> dict:
    n_points, p, gaps = args
    sys.path.insert(0, "/root/zsz")
    from flint import arb, ctx

    from zeta_simple_zeros.kernel import kernel_constants, normalized_kernel

    ctx.prec = 256
    consts = kernel_constants()
    n = n_points
    g = [arb(x) for x in gaps]
    v = sum(g, arb(0)) / arb(int(p))
    for s in range(1, n):
        coeff = arb(2) / arb(n - s)
        for i in range(n - s):
            x = sum(g[i : i + s], arb(0))
            v += coeff * normalized_kernel(x, consts) ** 2
    return {
        "n_points": n_points,
        "p": p,
        "arb_str": str(v),
        "arb_upper": float(v.upper()),
        "arb_lower": float(v.lower()),
    }


# ----------------------------------------------------------------------------
@app.function(timeout=10800, volumes={"/vol": vol})
def orchestrate(out: str = "/vol/family-wall-phase-a.json"):
    """Runs the whole sweep server-side so a dead client cannot kill it.
    Launch with `modal run --detach`; results land on the app's volume."""
    t0 = time.perf_counter()

    # pass 0 (control): the seven-point floor at p=3000 by 4-zero exhaustive words
    ctrl_jobs = [(7, 3000.0, 4, s, min(s + COMBO_CHUNK, 4**6)) for s in range(0, 4**6, COMBO_CHUNK)]

    # pass 1: multistart by seed
    jobs1 = [
        (n, float(p), seed, RESTARTS)
        for n in N_POINTS
        for p in PRESSURES
        for seed in range(CONTAINERS)
    ]

    # pass 2: exhaustive kernel-zero words, per-n alphabets, chunked
    jobs2 = list(ctrl_jobs)
    for n in N_POINTS:
        k = n - 1
        for alphabet, plist in EXHAUSTIVE[n]:
            total = alphabet**k
            for p in plist:
                for start in range(0, total, COMBO_CHUNK):
                    jobs2.append((n, float(p), alphabet, start, min(start + COMBO_CHUNK, total)))

    print(f"pass 1: {len(jobs1)} containers x {RESTARTS} restarts; pass 2: {len(jobs2)} exhaustive chunks", flush=True)
    raw1 = [r for r in n_point_floor.map(jobs1, return_exceptions=True) if isinstance(r, dict)]
    print(f"pass 1: {len(raw1)}/{len(jobs1)} returned after {time.perf_counter() - t0:.0f}s", flush=True)
    raw2 = [r for r in exhaustive_floor.map(jobs2, return_exceptions=True) if isinstance(r, dict)]
    print(f"pass 2: {len(raw2)}/{len(jobs2)} returned after {time.perf_counter() - t0:.0f}s", flush=True)

    groups: dict[tuple, list] = {}
    for r in raw1:
        groups.setdefault((r["n_points"], int(r["p"])), []).append(r)
    groups2: dict[tuple, list] = {}
    for r in raw2:
        groups2.setdefault((r["n_points"], int(r["p"])), []).append(r)

    # control check
    ctrl_rows = groups2.get((7, 3000), [])
    ctrl_best = min((r["best"] for r in ctrl_rows), default=float("inf"))
    control = {
        "expected_F": CONTROL_F,
        "found_F": ctrl_best,
        "abs_diff_F": ctrl_best - CONTROL_F,
        "ok": abs(ctrl_best - CONTROL_F) < 1e-9,
        "chunks": len(ctrl_rows),
    }
    print("control:", json.dumps(control), flush=True)

    # pass 3 (local): transfer polish, every cell from the pooled top argmins at its n
    transfer: dict[tuple, tuple] = {}
    for n in N_POINTS:
        pool = []
        for p in PRESSURES:
            pool += [r["argmin"] for r in sorted(groups.get((n, p), []), key=lambda r: r["best"])[:3]]
            pool += [r["argmin"] for r in sorted(groups2.get((n, p), []), key=lambda r: r["best"])[:3]]
        for p in PRESSURES:
            F = _float_F(n, float(p))
            best = (float("inf"), None)
            for x0 in pool:
                x, v = _nelder_mead(F, x0, step=0.01, iters=5000, tol=1e-15)
                if v < best[0]:
                    best = (v, x)
            transfer[(n, p)] = best
    print(f"pass 3: transfer polish done after {time.perf_counter() - t0:.0f}s", flush=True)

    table = []
    for n in N_POINTS:
        for p in PRESSURES:
            rs = groups.get((n, p), [])
            rs2 = groups2.get((n, p), [])
            if not rs and not rs2:
                table.append({"n_points": n, "p": p, "error": "no containers returned"})
                continue
            F = _float_F(n, float(p))
            cands = []
            if rs:
                b = min(rs, key=lambda r: r["best"])
                cands.append(("multistart", b["best"], b["argmin"]))
            if rs2:
                b = min(rs2, key=lambda r: r["best"])
                cands.append(("exhaustive", b["best"], b["argmin"]))
            tv, tx = transfer.get((n, p), (float("inf"), None))
            if tx is not None:
                cands.append(("transfer", tv, tx))
            source, _, x0 = min(cands, key=lambda t: t[1])
            x, v = _polish(F, x0, rounds=4)
            x = _canon(x)
            c = v
            m, phi = phi_n(n, c, float(p))
            row = {
                "n_points": n,
                "gaps": n - 1,
                "p": p,
                "best_F": c,
                "best_F_note": "float value of F at a point: an UPPER bound on inf F",
                "argmin": x,
                "gap_sum": sum(x),
                "pattern": _pattern(x),
                "palindromic": max(abs(x[i] - x[-1 - i]) for i in range(len(x))) < 1e-4,
                "best_source": source,
                "containers_multistart": len(rs),
                "exhaustive_runs": sum(r["end"] - r["start"] for r in rs2),
                "exhaustive_alphabets": sorted({r["alphabet"] for r in rs2}),
                "m_cap": m,
                "phi_at_cap": phi,
                "phi_note": (
                    "OPTIMISTIC: Phi_n at the float floor, an upper bound on inf F. "
                    "Formula proved for every n (lean/bridge n_point_bound); the certificate at this c is NOT proved."
                ),
            }
            table.append(row)

    arb_jobs = [(row["n_points"], float(row["p"]), row["argmin"]) for row in table if "argmin" in row]
    arb_rows = [r for r in arb_at_point.map(arb_jobs, return_exceptions=True) if isinstance(r, dict)]
    arb_by_key = {(r["n_points"], int(r["p"])): r for r in arb_rows}
    for row in table:
        a = arb_by_key.get((row["n_points"], row["p"]))
        if a:
            row["arb_F_at_argmin_upper"] = a["arb_upper"]
            row["arb_F_at_argmin_str"] = a["arb_str"]
            row["float_minus_arb"] = row["best_F"] - a["arb_upper"]

    peaks = {}
    for n in N_POINTS:
        rows = [r for r in table if r["n_points"] == n and "phi_at_cap" in r]
        if not rows:
            continue
        pk = max(rows, key=lambda r: r["phi_at_cap"])
        peaks[f"n{n}"] = {
            "p": pk["p"],
            "best_F": pk["best_F"],
            "m_cap": pk["m_cap"],
            "phi_at_cap": pk["phi_at_cap"],
            "argmin": pk["argmin"],
            "gap_sum": pk["gap_sum"],
            "pattern": pk["pattern"],
            "palindromic": pk["palindromic"],
            "distance_to_ceiling": CEILING - pk["phi_at_cap"],
            "p_on_grid_edge": pk["p"] in (PRESSURES[0], PRESSURES[-1]),
        }

    n9 = peaks.get("n9", {})
    prior_check = {
        "prior_n9_p4000_best_F": PRIOR_N9_P4000,
        "this_n9_p4000_best_F": next((r["best_F"] for r in table if r["n_points"] == 9 and r["p"] == 4000 and "best_F" in r), None),
        "note": "this run must be <= prior (finer search can only lower a float floor)",
    }

    results = {
        "app": "zeta-hunt82-family-wall",
        "phase": "A (float floors; nothing proved)",
        "n_points": list(N_POINTS),
        "pressures": list(PRESSURES),
        "exhaustive_plan": {str(n): [[a, list(pl)] for a, pl in EXHAUSTIVE[n]] for n in N_POINTS},
        "containers_per_cell_multistart": CONTAINERS,
        "restarts_per_container": RESTARTS,
        "H": H_CONST,
        "ceiling": CEILING,
        "phi_formula": "Phi_n(c,m,p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m), m = (n-1)+floor(1/c); proved for every n in lean/bridge (n_point_bound)",
        "control": control,
        "prior_check": prior_check,
        "peaks": peaks,
        "table": table,
        "wall_seconds": round(time.perf_counter() - t0),
    }
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1)
    vol.commit()

    print(f"{'n':>2} {'p':>5} {'best_F':>20} {'gap_sum':>8} {'pattern':>26} {'pal':>3} {'m':>4} {'Phi_at_cap':>16} src")
    for r in table:
        if "error" in r:
            print(f"{r['n_points']:>2} {r['p']:>5} ERROR {r['error']}")
            continue
        print(
            f"{r['n_points']:>2} {r['p']:>5} {r['best_F']:>20.16f} {r['gap_sum']:>8.4f} {r['pattern']:>26} "
            f"{'y' if r['palindromic'] else 'n':>3} {r['m_cap']:>4} {r['phi_at_cap']:>16.12f} {r['best_source']}"
        )
    print("peaks:", json.dumps(peaks, indent=1))
    print(f"wrote {out} after {results['wall_seconds']}s")


@app.local_entrypoint()
def main():
    call = orchestrate.spawn()
    print(f"orchestrator spawned: {call.object_id}")
    print("results: volume zeta-hunt82-family-wall, file family-wall-phase-a.json")
