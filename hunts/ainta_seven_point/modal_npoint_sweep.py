"""Modal float sweep of the n-point floor over the pressure denominator p.

For n in {7, 8, 9} points (n-1 gaps) and p in a 12-value grid, minimise

  F_{n-1}(g) = (1/p) sum g_i + sum_{s=1}^{n-1} (2/(n-s)) sum_{i=1}^{n-s} w(g_i + .. + g_{i+s-1}),
  w(x) = k(x)^2,  k = K(x)/K(0),  K(x) = int_{-1/2}^{1/2} cos(sqrt2 t) cos(2 pi x t) dt,

by pure-python Nelder-Mead multistart, mapped across Modal containers by seed. Every
container runs three seeding modes (kernel-zero bands, fully random in [0.5, 4], and
random combinations of the first four positive zeros of k), because the published
seven-point floor at p = 3000 is non-palindromic with gap-sum 9.085 and symmetric
seeding missed it before (TRUST-MAP.md 1.5).

Float only. Each best F is the value of F at a point, hence an UPPER bound on inf F.
Phi_n is evaluated at that upper bound and is therefore an OPTIMISTIC ceiling estimate.

Phi_n(c, m, p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m),
  H = 3/2 - (1/sqrt2) cot(1/sqrt2), m capped at (n-1) + floor(1/c).
For n = 7 this is the verified formula (TRUST-MAP.md 1.1, 1.2). For n = 8, 9 it is an
INFERRED generalisation (each gap occurs at most n-1 times in the m-(n-1) windows; the
block-defect gain is c(m-(n-1))) and has not been derived from a paper.

Control that must hold: n = 7, p = 3000 best F within 1e-9 of the Arb value
0.0038262312115073 at gaps (1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002).

Run:  ZSZ_SRC=... ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_npoint_sweep.py
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
app = modal.App("zeta-hunt77-npoint-sweep", image=image)

N_POINTS = (7, 8, 9)
PRESSURES = (2000, 2400, 2800, 3000, 3200, 3400, 3600, 4000, 4400, 4800, 5600, 6400)
CONTAINERS = 32
RESTARTS = 60

CONTROL_F = 0.0038262312115073
CONTROL_ARGMIN = [1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002]
PHI7_PEAK_PUBLISHED = 0.673027719  # RESULTS.md section 4, p ~ 3200, m = 280

# first four positive zeros of k (TRUST-MAP.md 1.5)
KERNEL_ZEROS = (1.057278, 2.030068, 3.020243, 4.015236)
BANDS = ((0.95, 1.20), (1.80, 2.35), (2.64, 4.0))

H_CONST = 1.5 - (1 / math.sqrt(2)) / math.tan(1 / math.sqrt(2))


# ----------------------------------------------------------------------------
# float functional (pure python, no deps) -- same as modal_ceiling._float_F
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
    """Re-run Nelder-Mead from the best point with shrinking steps and tight tolerance."""
    best_x, best_v = list(x), F(x)
    for step in (0.05, 0.01, 0.002, 0.0005)[:rounds]:
        y, v = _nelder_mead(F, best_x, step=step, iters=20000, tol=1e-17)
        if v < best_v:
            best_x, best_v = y, v
    return best_x, best_v


def phi_n(n_points: int, c: float, p: float) -> tuple[int, float]:
    """Phi_n at the m-cap. Verified formula for n = 7; INFERRED generalisation otherwise."""
    k = n_points - 1
    m = k + int(math.floor(1 / c))
    phi = (H_CONST - k * (m - 1) / (p * m)) / (1 - c * (m - k) / m)
    return m, phi


def _pattern(gaps) -> str:
    """Nearest kernel-zero index per gap, e.g. '1-2-2-1-2-1'."""
    out = []
    for g in gaps:
        j = min(range(len(KERNEL_ZEROS)), key=lambda i: abs(KERNEL_ZEROS[i] - g))
        out.append(str(j + 1) if abs(KERNEL_ZEROS[j] - g) < 0.3 else f"?{g:.2f}")
    return "-".join(out)


def _canon(gaps):
    """F is invariant under reversing the gap sequence; report the orientation whose
    first gap is the larger (the orientation of the published seven-point argmin)."""
    g = list(gaps)
    return g if g[0] >= g[-1] else g[::-1]


def _combo_seed(index: int, k: int):
    """The index-th of the 4^k combinations of the first four kernel zeros."""
    out = []
    for _ in range(k):
        out.append(KERNEL_ZEROS[index % 4])
        index //= 4
    return out


# ----------------------------------------------------------------------------
# mapped job: one container = one (n, p, seed), RESTARTS Nelder-Mead runs in 3 modes
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
            # exact kernel zeros, biased to the first two (the 1-2 alternation region)
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


# ----------------------------------------------------------------------------
# pass 2: exhaustive polish of the 4^(n-1) kernel-zero combinations (TRUST-MAP.md 1.5:
# the only seeding that recovered the non-palindromic seven-point floor reliably)
# ----------------------------------------------------------------------------
COMBO_CHUNK = 2048


@app.function(cpu=1, timeout=3600)
def exhaustive_floor(args: tuple) -> dict:
    n_points, p, start, end = args
    F = _float_F(n_points, p)
    k = n_points - 1
    best = (float("inf"), None, None)
    t0 = time.perf_counter()
    for idx in range(start, end):
        x, v = _nelder_mead(F, _combo_seed(idx, k), step=0.05)
        if v < best[0]:
            best = (v, x, idx)
    x, v = _polish(F, best[1], rounds=2)
    return {
        "n_points": n_points,
        "p": p,
        "start": start,
        "end": end,
        "best": v,
        "argmin": x,
        "combo_index": best[2],
        "seconds": round(time.perf_counter() - t0, 1),
    }


# ----------------------------------------------------------------------------
# Arb check at the winning point: a rigorous upper bound on inf F_{n-1}
# ----------------------------------------------------------------------------
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
@app.local_entrypoint()
def main(out: str = os.path.join(HERE, "artifacts", "npoint-sweep.json")):
    t0 = time.perf_counter()

    # pass 1: multistart by seed, three seeding modes
    jobs = [
        (n, float(p), seed, RESTARTS)
        for n in N_POINTS
        for p in PRESSURES
        for seed in range(CONTAINERS)
    ]
    print(f"pass 1: mapping {len(jobs)} containers x {RESTARTS} restarts", flush=True)
    raw = [r for r in n_point_floor.map(jobs, return_exceptions=True) if isinstance(r, dict)]
    print(f"pass 1: {len(raw)} containers returned after {time.perf_counter() - t0:.0f}s", flush=True)

    # pass 2: exhaustive kernel-zero combinations, chunked across containers
    jobs2 = []
    for n in N_POINTS:
        total = 4 ** (n - 1)
        for p in PRESSURES:
            for start in range(0, total, COMBO_CHUNK):
                jobs2.append((n, float(p), start, min(start + COMBO_CHUNK, total)))
    print(f"pass 2: mapping {len(jobs2)} containers over 4^(n-1) combos", flush=True)
    raw2 = [r for r in exhaustive_floor.map(jobs2, return_exceptions=True) if isinstance(r, dict)]
    print(f"pass 2: {len(raw2)} containers returned after {time.perf_counter() - t0:.0f}s", flush=True)

    groups: dict[tuple, list] = {}
    for r in raw:
        groups.setdefault((r["n_points"], int(r["p"])), []).append(r)
    groups2: dict[tuple, list] = {}
    for r in raw2:
        groups2.setdefault((r["n_points"], int(r["p"])), []).append(r)

    # pass 3 (local): transfer seeds, every cell polished from every other cell's argmin
    # at the same n, and from the control argmin. Pure python, a few hundred NM runs.
    cand: dict[tuple, list] = {}
    for key in set(groups) | set(groups2):
        xs = [r["argmin"] for r in groups.get(key, [])] + [r["argmin"] for r in groups2.get(key, [])]
        cand[key] = xs
    transfer: dict[tuple, tuple] = {}
    for n in N_POINTS:
        pool = []
        for p in PRESSURES:
            rs = sorted(groups.get((n, p), []), key=lambda r: r["best"])[:3]
            pool += [r["argmin"] for r in rs]
            rs2 = sorted(groups2.get((n, p), []), key=lambda r: r["best"])[:3]
            pool += [r["argmin"] for r in rs2]
        if n == 7:
            pool.append(CONTROL_ARGMIN)
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
            p1 = min(rs, key=lambda r: r["best"]) if rs else None
            p2 = min(rs2, key=lambda r: r["best"]) if rs2 else None
            p3v, p3x = transfer.get((n, p), (float("inf"), None))
            cands = []
            if p1:
                cands.append(("multistart", p1["best"], p1["argmin"]))
            if p2:
                cands.append(("exhaustive", p2["best"], p2["argmin"]))
            if p3x is not None:
                cands.append(("transfer", p3v, p3x))
            source, _, x0 = min(cands, key=lambda t: t[1])
            x, v = _polish(F, x0, rounds=4)  # local final polish
            x = _canon(x)
            c = v
            m, phi = phi_n(n, c, float(p))
            vals = sorted(r["best"] for r in rs) + sorted(r["best"] for r in rs2)
            vals.sort()
            distinct = []
            for val in vals:
                if not distinct or val - distinct[-1] > 1e-9:
                    distinct.append(val)
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
                "restarts_multistart": sum(r["restarts"] for r in rs),
                "restarts_exhaustive": sum(r["end"] - r["start"] for r in rs2),
                "containers_multistart": len(rs),
                "containers_exhaustive": len(rs2),
                "containers_at_best_multistart": sum(1 for r in rs if r["best"] - c < 1e-9),
                "containers_at_best_exhaustive": sum(1 for r in rs2 if r["best"] - c < 1e-9),
                "best_source": source,
                "pass_bests": {
                    "multistart": p1["best"] if p1 else None,
                    "exhaustive": p2["best"] if p2 else None,
                    "transfer": p3v if p3x is not None else None,
                },
                "mode_bests_multistart": {
                    k: min(r["per_mode_best"][k] for r in rs) for k in ("bands", "random", "zeros")
                } if rs else None,
                "next_distinct_local_min": distinct[1] if len(distinct) > 1 else None,
                "m_cap": m,
                "phi_at_cap": phi,
                "phi_note": (
                    "OPTIMISTIC ceiling estimate: Phi_n evaluated at the float floor, "
                    "which is an upper bound on inf F; "
                    + ("verified formula (n=7)" if n == 7 else "INFERRED generalisation of the n=7 formula")
                ),
            }
            table.append(row)

    # Arb enclosure at every winning point (rigorous upper bound on inf F_{n-1})
    arb_jobs = [(row["n_points"], float(row["p"]), row["argmin"]) for row in table if "argmin" in row]
    arb_rows = [r for r in arb_at_point.map(arb_jobs, return_exceptions=True) if isinstance(r, dict)]
    arb_by_key = {(r["n_points"], int(r["p"])): r for r in arb_rows}
    for row in table:
        a = arb_by_key.get((row["n_points"], row["p"]))
        if a:
            row["arb_F_at_argmin_upper"] = a["arb_upper"]
            row["arb_F_at_argmin_str"] = a["arb_str"]
            row["float_minus_arb"] = row["best_F"] - a["arb_upper"]

    # control (F is reversal-invariant, so either orientation of the argmin is accepted)
    ctrl = next(r for r in table if r["n_points"] == 7 and r["p"] == 3000)
    fa = ctrl["argmin"]
    argmin_ok = any(
        all(abs(a - b) < 2e-5 for a, b in zip(o, CONTROL_ARGMIN)) for o in (fa, fa[::-1])
    )
    ctrl_ok = abs(ctrl["best_F"] - CONTROL_F) < 1e-9 and argmin_ok

    # peaks
    peaks = {}
    for n in N_POINTS:
        rows = [r for r in table if r["n_points"] == n and "phi_at_cap" in r]
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
            "phi_minus_phi7_published_peak": pk["phi_at_cap"] - PHI7_PEAK_PUBLISHED,
        }

    results = {
        "app": "zeta-hunt77-npoint-sweep",
        "n_points": list(N_POINTS),
        "pressures": list(PRESSURES),
        "containers_per_cell_multistart": CONTAINERS,
        "restarts_per_container": RESTARTS,
        "seeding": (
            "pass 1 per container: 1/3 kernel-zero bands, 1/3 uniform [0.5,4], 1/3 random exact kernel zeros; "
            "pass 2: all 4^(n-1) combinations of the first four kernel zeros; "
            "pass 3 (local): polish from the top-3 argmins of every other p at the same n"
        ),
        "H": H_CONST,
        "phi_formula": "Phi_n(c,m,p) = (H - (n-1)(m-1)/(p m)) / (1 - c (m-(n-1))/m), m = (n-1)+floor(1/c); verified n=7, INFERRED n=8,9",
        "control": {
            "expected_F": CONTROL_F,
            "expected_argmin": CONTROL_ARGMIN,
            "found_F": ctrl["best_F"],
            "found_argmin": ctrl["argmin"],
            "abs_diff_F": ctrl["best_F"] - CONTROL_F,
            "ok": ctrl_ok,
        },
        "phi7_published_peak": PHI7_PEAK_PUBLISHED,
        "peaks": peaks,
        "table": table,
        "wall_seconds": round(time.perf_counter() - t0),
    }
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1)

    print(f"{'n':>2} {'p':>5} {'best_F':>20} {'gap_sum':>8} {'pattern':>20} {'pal':>3} {'m':>4} {'Phi_at_cap':>16} {'#b1':>4} {'#b2':>4} src")
    for r in table:
        if "error" in r:
            print(f"{r['n_points']:>2} {r['p']:>5} ERROR {r['error']}")
            continue
        print(
            f"{r['n_points']:>2} {r['p']:>5} {r['best_F']:>20.16f} {r['gap_sum']:>8.4f} {r['pattern']:>20} "
            f"{'y' if r['palindromic'] else 'n':>3} {r['m_cap']:>4} {r['phi_at_cap']:>16.12f} "
            f"{r['containers_at_best_multistart']:>4} {r['containers_at_best_exhaustive']:>4} {r['best_source']}"
        )
    print("control:", json.dumps(results["control"]))
    print("peaks:", json.dumps(peaks, indent=1))
    print(f"wrote {out} after {results['wall_seconds']}s")
