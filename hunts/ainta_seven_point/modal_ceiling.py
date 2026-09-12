"""Modal jobs for Hunt #79.

  rigorous_floor   Arb enclosure of F6 at the apparent minimiser and on a small box
                   around it. The upper end of the enclosure is a rigorous UPPER bound
                   on inf F6, which together with the accepted 1913/500000 brackets the
                   floor rigorously from both sides.
  n_point_floor    float Nelder-Mead sweep of the natural n-point analogue
                   F_{n-1}(g) = (1/p) sum g + sum_{s<n} (2/(n-s)) sum_i w(g_i+..+g_{i+s-1})
                   for n = 7 (control) and n = 8, mapped across containers by seed.
                   Float only; an apparent floor, never a bound.
  grid_probe       the published verifier with GRID doubled to 8000 (and the two
                   grid-scaled constants) at the two targets that bracketed the floor
                   at grid 4000. Tests whether the refusal at 0.0038263 is the grid's.

Run:  source <(hunts/ainta_seven_point/fetch_upstream.sh)
      ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_ceiling.py
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
    "ZSZ_SRC",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".upstream", "zeta-simple-zeros", "src", "zeta_simple_zeros"),
)  # populate with: source <(hunts/ainta_seven_point/fetch_upstream.sh)

image = (
    modal.Image.debian_slim(python_version="3.12")
    .pip_install("python-flint==0.9.0")
    .add_local_dir(ZSZ_SRC, remote_path="/root/zsz/zeta_simple_zeros")
)
app = modal.App("zeta-hunt77-ceiling", image=image)

ARGMIN = [1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002]


# ----------------------------------------------------------------------------
# shared float functional (pure python, no deps)
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


# ----------------------------------------------------------------------------
# job 1: rigorous enclosure at and around the minimiser
# ----------------------------------------------------------------------------
@app.function(cpu=2, timeout=1800)
def rigorous_floor(radius: float) -> dict:
    sys.path.insert(0, "/root/zsz")
    from flint import arb, ctx

    from zeta_simple_zeros.kernel import kernel_constants, normalized_kernel

    ctx.prec = 256
    consts = kernel_constants()

    def F6(g):
        v = sum(g) / arb(3000)
        for s in range(1, 7):
            coeff = arb(2) / arb(7 - s)
            for i in range(7 - s):
                x = sum(g[i : i + s], arb(0))
                v += coeff * normalized_kernel(x, consts) ** 2
        return v

    point = [arb(x) for x in ARGMIN]
    at_point = F6(point)
    box = [arb(x, radius) for x in ARGMIN]  # ball of radius r about each coordinate
    on_box = F6(box)
    return {
        "precision_bits": 256,
        "argmin": ARGMIN,
        "F6_at_point_str": str(at_point),
        "F6_at_point_upper": float(at_point.upper()),
        "F6_at_point_lower": float(at_point.lower()),
        "box_radius": radius,
        "F6_on_box_str": str(on_box),
        "F6_on_box_upper": float(on_box.upper()),
        "F6_on_box_lower": float(on_box.lower()),
    }


# ----------------------------------------------------------------------------
# job 2: n-point float floor, mapped by seed
# ----------------------------------------------------------------------------
@app.function(cpu=1, timeout=3600)
def n_point_floor(args: tuple) -> dict:
    n_points, p, seed, restarts = args
    F = _float_F(n_points, p)
    rnd = random.Random(seed)
    comps = [(0.95, 1.20), (1.80, 2.35), (2.64, 4.0)]
    best = (float("inf"), None)
    t0 = time.perf_counter()
    for _ in range(restarts):
        x0 = [rnd.uniform(*rnd.choice(comps)) for _ in range(n_points - 1)]
        x, v = _nelder_mead(F, x0, step=rnd.choice([0.05, 0.2, 0.5]))
        if v < best[0]:
            best = (v, x)
    return {
        "n_points": n_points,
        "p": p,
        "seed": seed,
        "restarts": restarts,
        "best": best[0],
        "argmin": best[1],
        "seconds": round(time.perf_counter() - t0, 1),
    }


# ----------------------------------------------------------------------------
# job 3: the verifier at grid 8000
# ----------------------------------------------------------------------------
@app.function(cpu=4, memory=8192, timeout=4 * 3600)
def grid_probe(args: tuple) -> dict:
    grid, num, den, cutoff = args[:4]
    pressure = args[4] if len(args) > 4 else 3000
    sys.path.insert(0, "/root/zsz")
    import dataclasses
    import importlib
    import types

    import zeta_simple_zeros.verify_seven as vs

    src = open(vs.__file__, encoding="utf-8").read()
    scale = grid // 4000
    src = src.replace("GRID = 4_000", f"GRID = {grid}")
    # The cutoff encodes the target: beyond gap-sum cutoff/grid the linear term alone
    # must exceed the target, so cutoff/grid/3000 >= num/den is required for soundness.
    assert cutoff / grid / pressure >= num / den, "cutoff too low for this target: prune is unsound"
    src = src.replace("PRESSURE_CUTOFF_CELLS = 45_600", f"PRESSURE_CUTOFF_CELLS = {cutoff}")
    src = src.replace("PRESSURE_DENOMINATOR = 3_000", f"PRESSURE_DENOMINATOR = {pressure}")
    src = src.replace("start_index=3_800", f"start_index={3_800 * scale}")
    src = src.replace("TARGET_NUMERATOR = 19\n", f"TARGET_NUMERATOR = {num}\n")
    src = src.replace("TARGET_DENOMINATOR = 5_000\n", f"TARGET_DENOMINATOR = {den}\n")
    mod = types.ModuleType("verify_seven_grid")
    mod.__file__ = vs.__file__
    mod.__package__ = "zeta_simple_zeros"
    exec(compile(src, vs.__file__, "exec"), mod.__dict__)
    t0 = time.perf_counter()
    try:
        rep = mod.verify_seven()
        d = dataclasses.asdict(rep) if dataclasses.is_dataclass(rep) else dict(vars(rep))
        d.pop("details", None)
        return {"grid": grid, "target": f"{num}/{den}", "cutoff": cutoff, "pressure": pressure, "outcome": "ACCEPTED", "report": d,
                "seconds": round(time.perf_counter() - t0)}
    except RuntimeError as e:
        return {"grid": grid, "target": f"{num}/{den}", "cutoff": cutoff, "pressure": pressure, "outcome": "REFUSED-AT-GRID",
                "message": str(e)[:300], "seconds": round(time.perf_counter() - t0)}


# ----------------------------------------------------------------------------
@app.local_entrypoint()
def main(out: str = "artifacts/modal-results.json"):
    t0 = time.perf_counter()
    h_floor = [rigorous_floor.spawn(r) for r in (1e-9, 1e-6, 1e-4)]
    seeds = list(range(48))
    h_seven = n_point_floor.map([(7, 3000.0, s, 60) for s in seeds], return_exceptions=True)
    h_eight = n_point_floor.map([(8, 3000.0, s, 60) for s in seeds], return_exceptions=True)
    h_grid = [grid_probe.spawn(a) for a in ((8000, 1913, 500000, 91_200), (8000, 38263, 10_000_000, 91_200))]

    results = {"floor": [h.get() for h in h_floor]}
    seven = [r for r in h_seven if isinstance(r, dict)]
    eight = [r for r in h_eight if isinstance(r, dict)]
    results["seven_point"] = {
        "containers": len(seven),
        "restarts": sum(r["restarts"] for r in seven),
        "best": min(seven, key=lambda r: r["best"]) if seven else None,
    }
    results["eight_point"] = {
        "containers": len(eight),
        "restarts": sum(r["restarts"] for r in eight),
        "best": min(eight, key=lambda r: r["best"]) if eight else None,
        "top5": sorted((r["best"], r["argmin"]) for r in eight)[:5],
    }
    print(json.dumps({k: results[k] for k in ("floor", "seven_point", "eight_point")}, indent=1))
    print(f"floor + n-point done at {time.perf_counter() - t0:.0f}s; waiting on grid-8000 probes", flush=True)
    results["grid_8000"] = [h.get() for h in h_grid]
    results["wall_seconds"] = round(time.perf_counter() - t0)
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1)
    print(json.dumps(results["grid_8000"], indent=1))
    print(f"wrote {out} after {results['wall_seconds']}s")


@app.local_entrypoint()
def rerun(out: str = "artifacts/modal-rerun-sound-cutoff.json"):
    """Re-run every accepted target with a cutoff that actually covers it.

    45600/4000/3000 = 0.0038 covers only the original 19/5000. For 0.003826 the
    pressure prune needs cutoff/grid/3000 >= 0.003826, i.e. >= 45912 cells at grid
    4000. Use 46400 (gap-sum 11.6, covers up to 0.0038667) at grid 4000 and 92800
    at grid 8000. The refusal at 0.0038263 is unaffected by the cutoff.
    """
    t0 = time.perf_counter()
    jobs = [
        (4000, 191, 50000, 46_400),      # Gohms, sound cutoff
        (4000, 153, 40000, 46_400),      # probe 1, sound cutoff
        (4000, 1913, 500000, 46_400),    # probe 2, sound cutoff
        (8000, 1913, 500000, 92_800),    # grid 8000, sound cutoff
        (4000, 1913, 500000, 60_000),    # control: a much larger cutoff must agree
    ]
    hs = [grid_probe.spawn(a) for a in jobs]
    results = [h.get() for h in hs]
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump({"jobs": results, "wall_seconds": round(time.perf_counter() - t0)}, f, indent=1)
    for r in results:
        rep = r.get("report", {})
        print(r["grid"], r["target"], "cutoff", r["cutoff"], r["outcome"],
              "nodes", rep.get("nodes"), "pressure_pruned", (rep.get("details") or {}).get("pressure_pruned"),
              r.get("message", "")[:80], f"{r['seconds']}s")
    print(f"wrote {out} after {time.perf_counter() - t0:.0f}s")


@app.local_entrypoint()
def peak(out: str = "artifacts/modal-peak-p3200.json"):
    """Verify at the pressure that maximises the family (TRUST-MAP: p ~ 3200, m capped
    at 280, float floor c_p = 0.00363695389206). Cutoff 47200 cells = gap-sum 11.8,
    11.8/3200 = 0.0036875 >= every target below."""
    t0 = time.perf_counter()
    jobs = [
        (4000, 909, 250_000, 47_200, 3200),        # 0.003636     9.5e-7 below floor
        (4000, 36369, 10_000_000, 47_200, 3200),   # 0.0036369    5.4e-8 below floor
        (4000, 363695, 100_000_000, 47_200, 3200), # 0.00363695   3.9e-9 below floor
        (4000, 36370, 10_000_000, 47_200, 3200),   # 0.003637     4.6e-8 ABOVE floor, must refuse
        (8000, 36369, 10_000_000, 94_400, 3200),   # grid 8000 on the middle target
    ]
    hs = [grid_probe.spawn(a) for a in jobs]
    results = [h.get() for h in hs]
    H = 1.5 - (1 / math.sqrt(2)) / math.tan(1 / math.sqrt(2))
    for r in results:
        num, den = map(int, r["target"].split("/"))
        c = num / den
        m = 6 + int(math.floor(1 / c))
        phi = (H - 6 * (m - 1) / (r["pressure"] * m)) / (1 - c * (m - 6) / m)
        r["m_cap"] = m
        r["phi_at_cap"] = phi
        rep = r.get("report", {})
        print(r["grid"], r["target"], "p", r["pressure"], r["outcome"], "nodes", rep.get("nodes"),
              "depth", rep.get("maximum_depth"), "m", m, f"Phi={phi:.12f}", r.get("message", "")[:70], f"{r['seconds']}s")
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    with open(out, "w", encoding="utf-8") as f:
        json.dump({"jobs": results, "wall_seconds": round(time.perf_counter() - t0)}, f, indent=1)
    print(f"wrote {out} after {time.perf_counter() - t0:.0f}s")


@app.local_entrypoint()
def peak3400(out: str = "artifacts/modal-peak-p3400.json"):
    """The n-point sweep put the 7-point peak at p = 3400 rather than 3200 (the trust map
    did not sample 3400). Float floor there: read from artifacts/npoint-sweep.json; targets
    below chosen at 1e-6 and 2e-7 under it, one above. Cutoff 11.8 gap-sum covers all."""
    import json as _json
    sweep = _json.load(open("artifacts/npoint-sweep.json"))
    row = next(r for r in sweep["table"] if r["n_points"] == 7 and r["p"] == 3400)
    floor = row["best_F"]
    print("7-point float floor at p=3400:", floor)
    den = 10_000_000
    lo1 = int(math.floor((floor - 1e-6) * den)); lo2 = int(math.floor((floor - 2e-7) * den)); hi = int(math.ceil((floor + 1e-7) * den))
    cutoff = int(math.ceil(4000 * 3400 * (hi / den))) + 400
    jobs = [(4000, lo1, den, cutoff, 3400), (4000, lo2, den, cutoff, 3400), (4000, hi, den, cutoff, 3400), (8000, lo2, den, 2 * cutoff, 3400)]
    hs = [grid_probe.spawn(a) for a in jobs]
    results = [h.get() for h in hs]
    H = 1.5 - (1 / math.sqrt(2)) / math.tan(1 / math.sqrt(2))
    for r in results:
        num, d = map(int, r["target"].split("/")); c = num / d; m = 6 + int(math.floor(1 / c))
        r["m_cap"] = m; r["phi_at_cap"] = (H - 6 * (m - 1) / (3400 * m)) / (1 - c * (m - 6) / m)
        rep = r.get("report", {})
        print(r["grid"], r["target"], r["outcome"], "nodes", rep.get("nodes"), "depth", rep.get("maximum_depth"), "m", m, f"Phi={r['phi_at_cap']:.12f}", f"{r['seconds']}s")
    with open(out, "w", encoding="utf-8") as f:
        _json.dump({"floor_float": floor, "jobs": results}, f, indent=1)
    print(f"wrote {out}")
