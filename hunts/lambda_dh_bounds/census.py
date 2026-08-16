"""Off-line quadruple census for Davenport-Heilbronn, heights 412 to 600 (WP3).

Extends the census of ``hunts/flow_repair`` (nine quadruples, last height
411.7967) above height 412, and checks prediction P4 of MISSION.md: no pair
below height 600 beats the measured landing floor t* = 0.0576518 (flow_repair
pair 5).

Run from the repo root, stages in order:

    .venv/bin/python hunts/lambda_dh_bounds/census.py line
    .venv/bin/python hunts/lambda_dh_bounds/census.py boxes [--k0 0 --k1 99]
    .venv/bin/python hunts/lambda_dh_bounds/census.py locate
    .venv/bin/python hunts/lambda_dh_bounds/census.py estimate
    .venv/bin/python hunts/lambda_dh_bounds/census.py merge   # fold partials

Writes ``census_results.json`` next to this file, checkpointing as it goes;
``--out`` redirects a stage to a partial file for concurrent runs.

Grade discipline (MISSION.md vocabulary contract): everything in this module
is float grade, the accurate regime.  Winding numbers are measured integers
(mpmath floats, residual defect recorded and required below 1e-6); the line
counts are grid sign-change counts; nothing here is decided in the MISSION.md
sense, because no step carries an interval or ball enclosure.  The strongest
words used are measured and observed.

Method (the technique of ``zeta.epstein.find_offline_zero``, windowed):

1. A sign scan of Z_dh on the critical line over (412, 600) at dps 15, grid
   1/20 of the local mean zero spacing 2 pi / log(5 t / 2 pi).
2. Window edges snapped to midpoints between consecutive line sign changes,
   so no line zero hugs a contour.  Per window, the argument-principle count
   of all zeros of f in [-1.05, 2.05] x [lo, hi] (``count_zeros_box``,
   dps 20) minus the line count is the excess; off-line zeros come in mirror
   pairs beta, 1 - beta, so the excess is even and the accounting closes as

       n_box = n_line + 2 * n_right,

   with n_right the count in the right half-strip [0.55, 2.05] x [lo, hi].
3. Each excess window is bisected on the right half-box count until each
   sub-window holds one zero; a grid minimum of |f| seeds mp.findroot at
   dps 40, and the polished root must pass a unit winding check on a
   side-0.2 box (measured integer, dps 20).
4. Landing estimates: naive y0^2 / 2, and the flow_repair shave model
   shave = (A + B log gamma) * y0^2 with (A, B) least-squares fitted at run
   time to the nine measured (gamma, y0, t*) triples in
   ``hunts/flow_repair/results.json`` (derived from that data, never
   recalled; training residuals are recorded alongside every estimate).
   Any zero with y0 > 0.34 is flagged for an actual Xi-plane t* measurement
   with flow_repair's contour-moment machinery at site_dps precision.
"""

from __future__ import annotations

import argparse
import glob
import json
import math
import os
import time

from mpmath import mp

from zeta.epstein import Z_dh, count_zeros_box, dh_f

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "census_results.json")
FLOW_RESULTS = os.path.join(HERE, "..", "flow_repair", "results.json")

T0_DEFAULT = 412.0
T1_DEFAULT = 600.0
WINDOW = 8.0
LINE_DPS = 15
BOX_DPS = 20
POLISH_DPS = 40
SIGMA_LO, SIGMA_HI = -1.05, 2.05
RIGHT_EDGES = (0.55, 0.53, 0.57, 0.51)  # fallbacks if a zero hugs the edge
Y0_MEASURE_TRIGGER = 0.34  # naive landing within 15 percent of the floor


def mean_gap(t: float) -> float:
    """Mean spacing of the line zeros near height t: 2 pi / log(5 t / 2 pi),
    the conductor-5 analogue used throughout zeta/epstein.py."""
    return float(2 * math.pi / math.log(5 * float(t) / (2 * math.pi)))


# ---------------------------------------------------------------------------
# results plumbing (same pattern as hunts/flow_repair/probe.py)
# ---------------------------------------------------------------------------


def load_results(path: str = RESULTS) -> dict:
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_results(update: dict, path: str = RESULTS) -> None:
    data = load_results(path)
    data.update(update)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


# ---------------------------------------------------------------------------
# stage line: the critical-line sign scan
# ---------------------------------------------------------------------------


def z_sign(t: float, dps: int = LINE_DPS) -> int:
    """Sign of Z_dh(t); on the (rare) imaginary-residue refusal, retry with
    more digits rather than guessing."""
    for d in (dps, dps + 5, dps + 10):
        try:
            v = Z_dh(t, dps=d)
            return 1 if v > 0 else (-1 if v < 0 else 0)
        except ValueError:
            continue
    raise ArithmeticError(f"Z_dh sign undetermined at t={t}")


def stage_line(t0: float, t1: float, out: str) -> None:
    """Grid sign scan of Z_dh over [t0, t1]; records sign-change midpoints.

    Grid step: mean_gap(t1)/20 (the zeros_on_line default).  A pair of zeros
    closer than one grid step would be missed here; the per-window box
    accounting in stage ``locate`` is the check that catches that, and it
    triggers a local 4x refinement when it fails to close.
    """
    started = time.time()
    step = mean_gap(t1) / 20.0
    n = int(math.ceil((t1 - t0) / step)) + 1
    data = load_results(out).get("line_scan", {})
    signs = list(data.get("signs", ""))
    if data.get("t0") != t0 or data.get("step") != step:
        signs = []
    i0 = len(signs)
    for i in range(i0, n + 1):
        t = t0 + step * i
        s = z_sign(t)
        signs.append("+" if s > 0 else ("-" if s < 0 else "0"))
        if i % 400 == 0 or i == n:
            save_results({"line_scan": {
                "t0": t0, "t1": t1, "step": step, "dps": LINE_DPS,
                "n_grid": n + 1, "signs": "".join(signs),
                "complete": bool(i == n),
                "seconds": round(time.time() - started, 1),
            }}, out)
            print(f"line scan {i}/{n} ({t:.1f})", flush=True)
    print(f"line scan done in {time.time() - started:.0f}s", flush=True)


def sign_changes(scan: dict) -> list[float]:
    """Midpoints of grid cells where the recorded sign flips."""
    t0, step, s = scan["t0"], scan["step"], scan["signs"]
    out = []
    for i in range(len(s) - 1):
        if s[i] != s[i + 1] and s[i] != "0" and s[i + 1] != "0":
            out.append(t0 + step * (i + 0.5))
    return out


def line_count_between(scan: dict, lo: float, hi: float) -> int:
    return sum(1 for c in sign_changes(scan) if lo < c < hi)


def line_count_refined(lo: float, hi: float, factor: int = 4) -> int:
    """Fresh, finer sign scan of one window (used when accounting fails)."""
    step = mean_gap(hi) / (20.0 * factor)
    n = int(math.ceil((hi - lo) / step)) + 1
    prev = z_sign(lo)
    count = 0
    for i in range(1, n + 1):
        cur = z_sign(min(lo + step * i, hi))
        if prev != 0 and cur != 0 and prev != cur:
            count += 1
        prev = cur
    return count


def window_edges(scan: dict, t0: float, t1: float, w: float) -> list[float]:
    """Nominal edges t0, t0+w, ... snapped to the nearest midpoint between
    consecutive line sign changes (so edges sit mid-gap, not on zeros)."""
    ch = sign_changes(scan)
    mids = [(a + b) / 2 for a, b in zip(ch, ch[1:])]
    edges = []
    nominal = t0
    while nominal < t1 + w / 2:
        cands = [m for m in mids if m >= t0 - 0.2]
        if not cands:
            raise ArithmeticError("no mid-gap points found; run stage line first")
        e = min(cands, key=lambda m: abs(m - nominal))
        if not edges or e > edges[-1] + 1.0:
            edges.append(e)
        nominal += w

    def clear_of_line(x: float) -> bool:
        return min(abs(x - c) for c in ch) > 0.15

    # boundary edges, so the census covers [t0, t1] and not just mid-gap span
    if edges[0] > t0 + 0.4:
        for x in (t0 + 0.05, t0 + 0.15, t0 + 0.25, t0 + 0.35):
            if clear_of_line(x):
                edges.insert(0, x)
                break
    if edges[-1] < t1 - 0.4:
        for x in (t1, t1 - 0.1, t1 - 0.2, t1 - 0.3, t1 - 0.4):
            if clear_of_line(x):
                edges.append(x)
                break
    return edges


# ---------------------------------------------------------------------------
# stage boxes: the per-window strip counts
# ---------------------------------------------------------------------------


def strip_count(lo: float, hi: float, dps: int = BOX_DPS) -> int:
    return count_zeros_box(
        mp.mpc(SIGMA_LO, lo), mp.mpc(SIGMA_HI, hi), dps=dps
    )


def stage_boxes(t0: float, t1: float, k0: int, k1: int, out: str) -> None:
    """Argument-principle strip counts for windows k0..k1 (inclusive)."""
    started = time.time()
    scan = load_results()["line_scan"]
    if not scan.get("complete"):
        raise SystemExit("run stage line to completion first")
    edges = window_edges(scan, t0, t1, WINDOW)
    key = f"windows_{k0}_{k1}"
    done = load_results(out).get(key, {})
    rows = done.get("rows", [])
    have = {(r["lo"], r["hi"]) for r in rows}
    for k in range(max(k0, 0), min(k1 + 1, len(edges) - 1)):
        lo, hi = edges[k], edges[k + 1]
        if (lo, hi) in have:
            continue
        tk = time.time()
        n_box = None
        note = ""
        # edges are mid-gap so line zeros never hug the contour; an off-line
        # zero still can.  On refusal, retry with the upper edge moved to the
        # next mid-gap candidates (recorded).
        try:
            n_box = strip_count(lo, hi)
        except ArithmeticError:
            ch = sign_changes(scan)
            mids = [(a + b) / 2 for a, b in zip(ch, ch[1:])]
            for cand in sorted(mids, key=lambda m: abs(m - hi)):
                if abs(cand - hi) < 1e-9 or not (lo + 1.0 < cand):
                    continue
                try:
                    n_box = strip_count(lo, cand)
                    note = f"upper edge moved {hi:.4f} -> {cand:.4f}"
                    hi = cand
                    break
                except ArithmeticError:
                    continue
        if n_box is None:
            rows.append({"k": k, "lo": lo, "hi": hi, "failed": True})
            continue
        n_line = line_count_between(scan, lo, hi)
        rows.append({
            "k": k, "lo": lo, "hi": hi,
            "n_box": n_box, "n_line": n_line,
            "excess": n_box - n_line,
            "box_dps": BOX_DPS, "line_dps": LINE_DPS,
            "note": note, "seconds": round(time.time() - tk, 1),
        })
        save_results({key: {"rows": rows}}, out)
        print(f"window {k} [{lo:.3f}, {hi:.3f}]: box={n_box} line={n_line} "
              f"excess={n_box - n_line} [{rows[-1]['seconds']}s]", flush=True)
    save_results({key: {"rows": rows,
                        "seconds": round(time.time() - started, 1)}}, out)


# ---------------------------------------------------------------------------
# stage locate: bisect the excess windows, polish each off-line zero
# ---------------------------------------------------------------------------


def right_count(lo: float, hi: float) -> tuple[int, float]:
    """Zeros of f in the right half-strip [sig, 2.05] x [lo, hi]; the sigma
    edge falls back if a zero hugs it.  Returns (count, sigma edge used)."""
    last = None
    for sig in RIGHT_EDGES:
        try:
            return count_zeros_box(
                mp.mpc(sig, lo), mp.mpc(SIGMA_HI, hi), dps=BOX_DPS
            ), sig
        except ArithmeticError as e:
            last = e
    raise ArithmeticError(f"right_count[{lo}, {hi}]: every sigma edge refused: {last}")


def bisect_to_singles(lo: float, hi: float, n: int) -> list[tuple[float, float]]:
    """Split [lo, hi] holding n right-half zeros into intervals holding 1."""
    if n == 1 or (hi - lo) < 0.6:
        return [(lo, hi)]
    for shift in (0.0, 0.171, -0.223, 0.317):
        mid = (lo + hi) / 2 + shift
        if not (lo + 0.2 < mid < hi - 0.2):
            continue
        try:
            n_lo, _ = right_count(lo, mid)
        except ArithmeticError:
            continue
        n_hi = n - n_lo
        parts = []
        if n_lo > 0:
            parts += bisect_to_singles(lo, mid, n_lo)
        if n_hi > 0:
            parts += bisect_to_singles(mid, hi, n_hi)
        return parts
    return [(lo, hi)]  # could not split cleanly; polish will seed multiples


def polish_in(lo: float, hi: float, sig: float, n_expect: int) -> list[dict]:
    """Seed from |f| grid minima over [sig, 2.05] x [lo, hi], polish each by
    mp.findroot at POLISH_DPS, verify with a unit winding check."""
    ni, nj = 13, max(15, int(8 * (hi - lo)) + 5)
    vals = []
    for i in range(ni):
        for j in range(nj):
            z = mp.mpc(sig + (SIGMA_HI - sig) * i / (ni - 1),
                       lo + (hi - lo) * j / (nj - 1))
            vals.append((abs(dh_f(z, dps=LINE_DPS)), z))
    vals.sort(key=lambda p: float(p[0]))
    roots: list[dict] = []
    for _, seed in vals[: 6 * n_expect]:
        if len(roots) == n_expect:
            break
        with mp.workdps(POLISH_DPS + 10):
            try:
                root = mp.findroot(lambda s: dh_f(s, dps=mp.dps), seed)
            except Exception:
                continue
            resid = abs(dh_f(root, dps=mp.dps))
            beta, gamma = mp.re(root), mp.im(root)
            if resid > mp.mpf("1e-25"):
                continue
            if not (lo - 0.05 < gamma < hi + 0.05 and beta > 0.5 + 0.02):
                continue
            if any(abs(mp.mpf(r["gamma"]) - gamma) < mp.mpf("1e-4")
                   for r in roots):
                continue
            h = mp.mpf(1) / 10
            n_w = count_zeros_box(root - mp.mpc(h, h), root + mp.mpc(h, h),
                                  dps=BOX_DPS)
            if n_w != 1:
                continue
            roots.append({
                "beta": mp.nstr(beta, 30),
                "gamma": mp.nstr(gamma, 30),
                "y0": float(beta - mp.mpf(1) / 2),
                "abs_f_residual": mp.nstr(resid, 3),
                "polish_dps": POLISH_DPS,
                "winding_box_count": 1,
                "grade": "measured (mpmath float, unit winding check at "
                         f"dps {BOX_DPS})",
            })
    return roots


def stage_locate(out: str, k0: int = 0, k1: int = 999) -> None:
    """For each excess window: right-half count, bisect, polish, close the
    per-window accounting n_box = n_line + 2 * n_located."""
    started = time.time()
    data = load_results()
    rows = []
    for key, blob in data.items():
        if key.startswith("windows_"):
            rows += blob["rows"]
    rows = [r for r in rows if k0 <= r.get("k", -1) <= k1]
    rows.sort(key=lambda r: r["lo"])
    found = load_results(out).get("offline_zeros", [])
    have_windows = {tuple(z["window"]) for z in found}
    accounting = load_results(out).get("window_accounting", [])
    acc_have = {(a["lo"], a["hi"]) for a in accounting}
    for r in rows:
        if r.get("failed") or (r["lo"], r["hi"]) in acc_have:
            continue
        tk = time.time()
        entry = {"lo": r["lo"], "hi": r["hi"], "n_box": r["n_box"],
                 "n_line": r["n_line"], "excess": r["excess"]}
        excess = r["excess"]
        if excess < 0 or excess % 2 == 1:
            # the grid line count missed a close pair; refine it locally
            n_line = line_count_refined(r["lo"], r["hi"])
            entry["n_line_refined_4x"] = n_line
            excess = r["n_box"] - n_line
            entry["excess"] = excess
        if excess > 0 and (r["lo"], r["hi"]) not in have_windows:
            n_right, sig = right_count(r["lo"], r["hi"])
            entry["n_right"] = n_right
            entry["right_sigma_edge"] = sig
            zs = []
            for (u, v) in bisect_to_singles(r["lo"], r["hi"], n_right):
                nn, s2 = right_count(u, v)
                zs += polish_in(u, v, s2, nn)
            for z in zs:
                z["window"] = [r["lo"], r["hi"]]
            found += zs
            entry["n_located"] = len(zs)
            entry["closed"] = bool(r["n_box"] == entry.get(
                "n_line_refined_4x", r["n_line"]) + 2 * len(zs))
        else:
            entry["n_located"] = 0
            entry["closed"] = bool(excess == 0)
        entry["seconds"] = round(time.time() - tk, 1)
        accounting.append(entry)
        save_results({"offline_zeros": found,
                      "window_accounting": accounting}, out)
        print(f"[{r['lo']:.2f}, {r['hi']:.2f}] excess={excess} "
              f"located={entry['n_located']} closed={entry['closed']}",
              flush=True)
    save_results({"locate_seconds": round(time.time() - started, 1)}, out)


# ---------------------------------------------------------------------------
# stage estimate: the flow_repair shave model, fitted from its own data
# ---------------------------------------------------------------------------


def flow_repair_pairs() -> list[dict]:
    with open(FLOW_RESULTS, "r", encoding="utf-8") as f:
        d = json.load(f)
    rows = []

    def grab(tst, pol):
        rows.append({
            "gamma": float(mp.mpf(pol["gamma"])),
            "y0": float(mp.mpf(pol["y0"])),
            "tstar": tst["tstar"],
            "tstar_naive": tst["tstar_naive"],
        })

    grab(d["pair1"]["tstar"], d["pair1"]["polished"])
    for k, v in d.items():
        if k.startswith("survey"):
            for pk, tst in v.items():
                if pk.startswith("pair"):
                    grab(tst, tst["polished"])
    rows.sort(key=lambda r: r["gamma"])
    return rows


def fit_shave_model(rows: list[dict]) -> dict:
    """Least squares for shave_fraction / y0^2 = A + B log(gamma), the form
    flow_repair observed (shave tracks y0^2 times local zero density)."""
    xs = [math.log(r["gamma"]) for r in rows]
    ys = [(1.0 - r["tstar"] / r["tstar_naive"]) / r["y0"] ** 2 for r in rows]
    n = len(xs)
    sx, sy = sum(xs), sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    B = (n * sxy - sx * sy) / (n * sxx - sx * sx)
    A = (sy - B * sx) / n
    resid = []
    for r in rows:
        est = r["tstar_naive"] * (1.0 - (A + B * math.log(r["gamma"])) * r["y0"] ** 2)
        resid.append(100.0 * (est / r["tstar"] - 1.0))
    return {"A": A, "B": B,
            "form": "tstar_est = (y0^2/2) * (1 - (A + B*log(gamma)) * y0^2)",
            "training_residuals_percent": [round(x, 3) for x in resid],
            "max_abs_training_residual_percent": round(max(abs(x) for x in resid), 3),
            "n_training_pairs": len(rows)}


def stage_estimate(out: str) -> None:
    started = time.time()
    data = load_results()
    zeros = data.get("offline_zeros", [])
    fr = flow_repair_pairs()
    model = fit_shave_model(fr)
    floor = max(r["tstar"] for r in fr)
    floor_pair = max(fr, key=lambda r: r["tstar"])
    rows = []
    for z in zeros:
        y0 = z["y0"]
        gamma = float(mp.mpf(z["gamma"]))
        naive = 0.5 * y0 * y0
        est = naive * (1.0 - (model["A"] + model["B"] * math.log(gamma)) * y0 * y0)
        rows.append({
            "beta": z["beta"], "gamma": z["gamma"], "y0": y0,
            "tstar_naive": naive,
            "tstar_model_estimate": est,
            "estimate_grade": "observed-model extrapolation, float grade, "
                              "training residuals within "
                              f"{model['max_abs_training_residual_percent']}%",
            "beats_floor_naive": bool(naive > floor),
            "beats_floor_model": bool(est > floor),
            "measure_trigger_y0_gt_0.34": bool(y0 > Y0_MEASURE_TRIGGER),
        })
    save_results({"landing_estimates": {
        "floor": floor,
        "floor_source": f"flow_repair pair at gamma {floor_pair['gamma']:.4f} "
                        "(measured, mpmath float)",
        "shave_model": model,
        "rows": rows,
        "seconds": round(time.time() - started, 1),
    }}, out)
    print(json.dumps(rows, indent=2))


# ---------------------------------------------------------------------------
# stage measure: actual t* via flow_repair's contour moments (expensive)
# ---------------------------------------------------------------------------


def stage_measure(index: int, out: str) -> None:
    """Xi-plane landing time for offline_zeros[index], at site_dps precision.
    Cost note: flow_repair pair 9 (height 412) took ~19 minutes; this grows
    with height.  Run only for a zero that could beat the floor."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "flow_probe", os.path.join(HERE, "..", "flow_repair", "probe.py"))
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)

    data = load_results()
    z = data["offline_zeros"][index]
    gamma = float(mp.mpf(z["gamma"]))
    dps = probe.site_dps(gamma, 20)
    with mp.workdps(dps + 10):
        seed = mp.mpc(mp.mpf(z["beta"]), mp.mpf(z["gamma"]))
        root = mp.findroot(lambda s: dh_f(s, dps=mp.dps), seed)
        pol = {
            "beta": mp.nstr(mp.re(root), min(dps, 40)),
            "gamma": mp.nstr(mp.im(root), min(dps, 40)),
            "y0": mp.nstr(mp.re(root) - mp.mpf(1) / 2, min(dps, 40)),
        }
    started = time.time()
    site = probe.make_site(90 + index, pol)
    tst = probe.find_tstar(site, tol=1e-6)
    tst["seconds"] = round(time.time() - started, 1)
    tst["zero_index"] = index
    measures = load_results(out).get("measured_tstar", [])
    measures.append(tst)
    save_results({"measured_tstar": measures}, out)
    print(json.dumps(tst, indent=2))


# ---------------------------------------------------------------------------
# merge partials
# ---------------------------------------------------------------------------


def stage_merge() -> None:
    for path in sorted(glob.glob(os.path.join(HERE, "census_results_*.json"))):
        part = json.load(open(path, encoding="utf-8"))
        data = load_results()
        for k, v in part.items():
            if k in ("offline_zeros", "window_accounting", "measured_tstar") \
                    and k in data:
                seen = {json.dumps(x, sort_keys=True) for x in data[k]}
                data[k] = data[k] + [x for x in v
                                     if json.dumps(x, sort_keys=True) not in seen]
            elif k.startswith("windows_") and k in data:
                seen = {(r["lo"], r["hi"]) for r in data[k]["rows"]}
                data[k]["rows"] += [r for r in v["rows"]
                                    if (r["lo"], r["hi"]) not in seen]
            else:
                data[k] = v
        with open(RESULTS, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, sort_keys=True)
            f.write("\n")
        os.remove(path)
        print("merged", os.path.basename(path))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", choices=["line", "boxes", "locate", "estimate",
                                      "measure", "merge"])
    ap.add_argument("--t0", type=float, default=T0_DEFAULT)
    ap.add_argument("--t1", type=float, default=T1_DEFAULT)
    ap.add_argument("--k0", type=int, default=0)
    ap.add_argument("--k1", type=int, default=99)
    ap.add_argument("--index", type=int, default=0)
    ap.add_argument("--out", default=RESULTS)
    a = ap.parse_args()
    if a.stage == "line":
        stage_line(a.t0, a.t1, a.out)
    elif a.stage == "boxes":
        stage_boxes(a.t0, a.t1, a.k0, a.k1, a.out)
    elif a.stage == "locate":
        stage_locate(a.out, a.k0, a.k1)
    elif a.stage == "estimate":
        stage_estimate(a.out)
    elif a.stage == "measure":
        stage_measure(a.index, a.out)
    elif a.stage == "merge":
        stage_merge()


if __name__ == "__main__":
    main()
