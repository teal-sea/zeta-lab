"""The zero census of F_k below height 1000, on two code-disjoint routes.

Stages, each checkpointed per unit under ``--ckpt`` (one JSON file per unit,
skipped when present, so an interrupted run resumes where it stopped):

    scanA   route A line scan: Z on a grid of 1/12 the mean zero gap (mpmath fp)
    plan    window boundaries near every 8 units of height, each at the grid
            point of largest |Z| between two consecutive sign changes
    psiA    route A folded counts N(0, T_j) at every boundary
    winA    route A, windows with excess n_box - n_line > 0: right-box counts,
            bisection, Newton; finer line scans where a sign-change pair hides
    scanB   route B line scan: decided Z signs on its own grid (1/10 gap, offset)
    psiB    route B decided folded counts at the same boundaries
    boxB    route B decided boxes around route A's roots: half-width 1/64, then
            a polished root in a box of half-width 2^-30
    merge   both accountings, n_box = n_line + 2 n_right, window by window

Run from the repo root, at most 4 workers (MISSION.md):

    .venv/bin/python hunts/plocal_rivals/census.py --q 17 --stage all --workers 4 --ckpt DIR

Box placement in route B comes from route A (boundaries, box centres).  It
steers placement only: a decided count does not depend on it being right, and
an unexplained excess in route B's own accounting is reported, not absorbed.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

T_END = 1000.0
WINDOW = 8.0
SR_A = 1.7
SR_B = Fraction(17, 10)
DELTA = 0.01          # route A right boxes start at Re s = 1/2 + DELTA
BOX_STEP = 0.08       # forced sampling of right-box edges; refinement does the rest
DEN = 1024            # window boundaries are multiples of 1/1024
CHUNK = 400


def _write(path: str, obj) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh)
    os.replace(tmp, path)


def _read(path: str):
    with open(path) as fh:
        return json.load(fh)


# ---------------------------------------------------------------------------
# route A
# ---------------------------------------------------------------------------

_RVA: dict = {}


def _rvA(q: int):
    import rivals as R

    got = _RVA.get(q)
    if got is None:
        got = R.FpRival(q)
        _RVA[q] = got
    return got


def grid_A(q: int, t_end: float | None = None) -> list[float]:
    if t_end is None:
        t_end = T_END + 6.0
    rv = _rvA(q)
    ts = [0.0]
    while ts[-1] < t_end:
        t = ts[-1]
        ts.append(t + min(rv.mean_gap(t) / 12.0, 0.1))
    return ts


def _scanA_unit(args):
    q, i, ts, path = args
    if os.path.exists(path):
        return path
    rv = _rvA(q)
    t0 = time.time()
    zs = [rv.Z(t) for t in ts]
    _write(path, {"q": q, "chunk": i, "ts": ts, "zs": zs, "seconds": time.time() - t0})
    return path


def stage_scanA(q: int, ckpt: str, workers: int) -> None:
    ts = grid_A(q)
    units = []
    for i in range(0, len(ts), CHUNK):
        units.append((q, i // CHUNK, ts[i:i + CHUNK], os.path.join(ckpt, f"scanA_q{q}_{i // CHUNK:04d}.json")))
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_scanA_unit, units):
            pass


def load_scan(q: int, ckpt: str, tag: str) -> tuple[list, list]:
    files = sorted(f for f in os.listdir(ckpt) if f.startswith(f"{tag}_q{q}_"))
    ts, zs = [], []
    for f in files:
        d = _read(os.path.join(ckpt, f))
        ts.extend(d["ts"])
        zs.extend(d["zs"])
    order = sorted(range(len(ts)), key=lambda j: ts[j])
    return [ts[j] for j in order], [zs[j] for j in order]


def sign_change_intervals(ts, zs) -> list[tuple[float, float]]:
    out = []
    for j in range(len(ts) - 1):
        if zs[j] == 0 or zs[j + 1] == 0:
            raise ArithmeticError(f"exact zero of Z on the grid at {ts[j]}")
        if (zs[j] > 0) != (zs[j + 1] > 0):
            out.append((ts[j], ts[j + 1]))
    return out


def plan_windows(q: int, ckpt: str) -> dict:
    """Window boundaries: for each target height W, 2W, ... (and finally T_END),
    the grid point of largest |Z| strictly inside the gap between the two sign
    changes around the target, rounded to a multiple of 1/DEN and required to
    stay strictly inside that gap.  The last boundary is at least T_END."""
    path = os.path.join(ckpt, f"plan_q{q}.json")
    if os.path.exists(path):
        return _read(path)
    ts, zs = load_scan(q, ckpt, "scanA")
    sc = sign_change_intervals(ts, zs)
    gaps = [(sc[i][1], sc[i + 1][0]) for i in range(len(sc) - 1)]

    def best_in(lo, hi, floor_t=None):
        cand = sorted(((abs(z), t) for t, z in zip(ts, zs)
                       if lo <= t <= hi and (floor_t is None or t >= floor_t)), reverse=True)
        for _, t in cand:
            tb = round(t * DEN) / DEN
            if lo < tb < hi and (floor_t is None or tb >= floor_t):
                return tb
        return None

    bounds = [0.0]
    target = WINDOW
    gi = 0
    while target < T_END:
        while gi < len(gaps) and gaps[gi][1] < target:
            gi += 1
        if gi >= len(gaps):
            raise ArithmeticError("scan does not reach the targets")
        tb = best_in(*gaps[gi])
        if tb is not None and tb > bounds[-1] + 1.0:
            bounds.append(tb)
        target += WINDOW
    gi = 0
    while gi < len(gaps) and gaps[gi][1] < T_END:
        gi += 1
    tb = None
    while tb is None and gi < len(gaps):
        tb = best_in(gaps[gi][0], gaps[gi][1], floor_t=T_END)
        gi += 1
    if tb is None:
        raise ArithmeticError("scan does not reach T_END")
    if tb - bounds[-1] < 1.0:
        bounds[-1] = tb
    else:
        bounds.append(tb)
    out = {"q": q, "bounds": bounds, "n_sign_changes": len(sc),
           "grid_points": len(ts), "window_target": WINDOW}
    _write(path, out)
    return out


def _psiA_unit(args):
    q, j, T, path = args
    if os.path.exists(path):
        return path
    import rivals as R

    rv = _rvA(q)
    t0 = time.time()
    try:
        r = R.psi_fp(rv, T, SR_A)
    except ArithmeticError as exc:
        r = {"T": T, "N": None, "defect": None, "error": f"{type(exc).__name__}: {exc}"}
    r["Z_at_T"] = rv.Z(T)
    r["seconds"] = time.time() - t0
    r["j"] = j
    _write(path, r)
    return path


def stage_psiA(q: int, ckpt: str, workers: int) -> None:
    plan = plan_windows(q, ckpt)
    units = [(q, j, T, os.path.join(ckpt, f"psiA_q{q}_{j:04d}.json"))
             for j, T in enumerate(plan["bounds"]) if j > 0]
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_psiA_unit, units):
            pass


def _countA(q: int, ckpt: str, j: int) -> int:
    if j == 0:
        return 0
    return _read(os.path.join(ckpt, f"psiA_q{q}_{j:04d}.json"))["N"]


def _zA(q: int, ckpt: str, j: int) -> float:
    if j == 0:
        return _rvA(q).Z(0.0)
    return _read(os.path.join(ckpt, f"psiA_q{q}_{j:04d}.json"))["Z_at_T"]


def _line_count_seq(ts, zs, lo: float, hi: float, z_lo, z_hi) -> int:
    """Sign changes of Z on [lo, hi] read from the boundary values and the grid
    points strictly inside: no change is lost to an interval that straddles a
    boundary, and none is counted in two windows."""
    seq = [z_lo] + [z for t, z in zip(ts, zs) if lo < t < hi] + [z_hi]
    if any(z == 0 for z in seq):
        raise ArithmeticError("exact or undecided zero of Z in a window")
    return sum(1 for a, b in zip(seq, seq[1:]) if (a > 0) != (b > 0))


def _right_zeros_A(rv, y0: float, y1: float, n_known=None, depth: int = 0) -> list:
    """Bisect the right box [1/2 + DELTA, SR_A] x [y0, y1] down to unit boxes,
    then Newton from the grid minimum of |F| in each (measured).

    Only the lower half of each split is counted; the upper half's count is the
    difference, by additivity of the winding number (the shared edge cancels).
    A unit box whose Newton step leaves it is split again, down to height 1/16.
    """
    import rivals as R

    if n_known is None:
        bc = R.box_count_fp(rv, 0.5 + DELTA, SR_A, y0, y1, step=BOX_STEP)
        if bc["defect"] > 1e-4:
            raise ArithmeticError(f"right box winding not integral: {bc}")
        n = bc["N"]
    else:
        n = n_known
    if n < 0:
        raise ArithmeticError(f"negative count {n} in [{y0}, {y1}]")
    if n == 0:
        return []
    if n == 1 and (y1 - y0) < 1.0:
        best = None
        nx, ny = 10, 8
        for a in range(nx + 1):
            for b in range(ny + 1):
                sp = complex(0.5 + DELTA + (SR_A - 0.5 - DELTA) * a / nx, y0 + (y1 - y0) * b / ny)
                v = abs(rv.F(sp))
                if best is None or v < best[0]:
                    best = (v, sp)
        try:
            z = R.newton_fp(rv, best[1])
            inside = 0.5 + DELTA < z.real < SR_A and y0 < z.imag < y1
        except ArithmeticError:
            inside = False
        if inside:
            return [{"re": z.real, "im": z.imag, "abs_F": abs(rv.F(z)), "box": [y0, y1]}]
        if (y1 - y0) < 1.0 / 16:
            raise ArithmeticError(f"Newton left its unit box [{y0}, {y1}]")
    if depth > 40:
        raise ArithmeticError("bisection depth exceeded")
    mid = (y0 + y1) / 2
    last = None
    n_lo = None
    for nudge in (0.0, 0.013, -0.017, 0.031, -0.029):
        # only the cut is retried: a zero too near the cut line makes this count
        # fail, and moving the cut fixes that.  A failure further down is not a
        # cut problem, and retrying it at every level would be exponential.
        m = mid + nudge * (y1 - y0)
        try:
            bc = R.box_count_fp(rv, 0.5 + DELTA, SR_A, y0, m, step=BOX_STEP)
            if bc["defect"] > 1e-4:
                raise ArithmeticError(f"right box winding not integral: {bc}")
            n_lo = bc["N"]
            break
        except ArithmeticError as exc:  # noqa: PERF203
            last = exc
    if n_lo is None:
        raise last
    left = _right_zeros_A(rv, y0, m, n_lo, depth + 1)
    right = _right_zeros_A(rv, m, y1, n - n_lo, depth + 1)
    return left + right


def _winA_unit(args):
    q, j, lo, hi, n_box, n_line, path = args
    if os.path.exists(path):
        return path
    rv = _rvA(q)
    t0 = time.time()
    out = {"q": q, "j": j, "lo": lo, "hi": hi, "n_box": n_box, "n_line": n_line}
    try:
        zeros = _right_zeros_A(rv, lo, hi, None)
    except ArithmeticError as exc:
        out.update(error=f"{type(exc).__name__}: {exc}", n_right=None, zeros=[], closes=False,
                   seconds=time.time() - t0)
        _write(path, out)
        return path
    out["n_right"] = len(zeros)
    out["zeros"] = zeros
    refined = None
    if n_box != n_line + 2 * len(zeros):
        # a sign-change pair may hide between grid points: rescan 8x finer
        ts = [lo]
        while ts[-1] < hi:
            ts.append(min(hi, ts[-1] + min(rv.mean_gap(ts[-1]) / 96.0, 0.0125)))
        zs = [rv.Z(t) for t in ts]
        refined = _line_count_seq(ts, zs, lo, hi, zs[0], zs[-1])
        out["n_line_refined"] = refined
    out["closes"] = n_box == (refined if refined is not None else n_line) + 2 * len(zeros)
    out["seconds"] = time.time() - t0
    out["n_evals"] = rv.n_evals
    _write(path, out)
    return path


def windows_A(q: int, ckpt: str) -> list[dict]:
    plan = plan_windows(q, ckpt)
    ts, zs = load_scan(q, ckpt, "scanA")
    b = plan["bounds"]
    rows = []
    for j in range(len(b) - 1):
        c0, c1 = _countA(q, ckpt, j), _countA(q, ckpt, j + 1)
        n_box = c1 - c0 if (c0 is not None and c1 is not None) else None
        try:
            n_line = _line_count_seq(ts, zs, b[j], b[j + 1], _zA(q, ckpt, j), _zA(q, ckpt, j + 1))
        except ArithmeticError:
            n_line = None
        excess = n_box - n_line if (n_box is not None and n_line is not None) else None
        rows.append({"j": j, "lo": b[j], "hi": b[j + 1], "n_box": n_box, "n_line": n_line,
                     "excess": excess})
    return rows


def stage_winA(q: int, ckpt: str, workers: int) -> None:
    rows = windows_A(q, ckpt)
    units = [(q, r["j"], r["lo"], r["hi"], r["n_box"], r["n_line"],
              os.path.join(ckpt, f"winA_q{q}_{r['j']:04d}.json"))
             for r in rows if r["excess"] not in (0, None)]
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_winA_unit, units):
            pass


# ---------------------------------------------------------------------------
# route B
# ---------------------------------------------------------------------------

_RVB: dict = {}


def _rvB(q: int):
    import arb_route as B

    got = _RVB.get(q)
    if got is None:
        got = B.ArbRival(q)
        _RVB[q] = got
    return got


def grid_B(q: int, t_end: float | None = None) -> list[Fraction]:
    """Route B's own grid: 1/10 of the mean gap, dyadic points, offset start."""
    if t_end is None:
        t_end = T_END + 6.0
    out = [Fraction(0)]
    t = Fraction(1, 64)
    while float(t) < t_end:
        out.append(t)
        x = q * max(float(t), 1.0) / (2 * math.pi)
        gap = 2 * math.pi / math.log(max(x, 3.0))
        step = min(gap / 10.0, 0.125)
        t = t + Fraction(max(1, int(step * 4096)), 4096)
    return out


def _scanB_unit(args):
    q, i, ts, path = args
    if os.path.exists(path):
        return path
    rv = _rvB(q)
    t0 = time.time()
    signs = []
    undecided = []
    for t in ts:
        sg = rv.Z_sign(t)
        if sg == 0:
            undecided.append(str(t))
        signs.append(sg)
    _write(path, {"q": q, "chunk": i, "ts": [float(t) for t in ts],
                  "ts_exact": [str(t) for t in ts], "zs": signs, "undecided": undecided,
                  "seconds": time.time() - t0})
    return path


def stage_scanB(q: int, ckpt: str, workers: int) -> None:
    ts = grid_B(q)
    units = []
    for i in range(0, len(ts), CHUNK):
        units.append((q, i // CHUNK, ts[i:i + CHUNK], os.path.join(ckpt, f"scanB_q{q}_{i // CHUNK:04d}.json")))
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_scanB_unit, units):
            pass


def _psiB_unit(args):
    q, j, T, path = args
    if os.path.exists(path):
        return path
    rv = _rvB(q)
    t0 = time.time()
    r = rv.psi(Fraction(T), SR_B)
    r["Z_sign_at_T"] = rv.Z_sign(Fraction(T))
    r["seconds"] = time.time() - t0
    r["j"] = j
    r.pop("leg", None)
    _write(path, r)
    return path


def stage_psiB(q: int, ckpt: str, workers: int) -> None:
    plan = plan_windows(q, ckpt)
    rv = _rvB(q)
    path = os.path.join(ckpt, f"baseB_q{q}.json")
    if not os.path.exists(path):
        dom = rv.domination_holds(SR_B)
        base = rv.arg_change((Fraction(1, 2), Fraction(0)), (SR_B, Fraction(0)))
        FR = rv.F_at(SR_B, Fraction(0))
        _write(path, {"domination_at_sR": dom,
                      "real_segment_decided": base["status"] == "decided",
                      "F_sR_positive": bool(FR.real > 0)})
    units = [(q, j, T, os.path.join(ckpt, f"psiB_q{q}_{j:04d}.json"))
             for j, T in enumerate(plan["bounds"]) if j > 0]
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_psiB_unit, units):
            pass


def zeros_A(q: int, ckpt: str) -> list[dict]:
    out = []
    for f in sorted(os.listdir(ckpt)):
        if f.startswith(f"winA_q{q}_"):
            d = _read(os.path.join(ckpt, f))
            for z in d["zeros"]:
                z = dict(z)
                z["window"] = d["j"]
                out.append(z)
    out.sort(key=lambda z: z["im"])
    return out


def _boxB_unit(args):
    q, i, z, path = args
    if os.path.exists(path):
        return path
    rv = _rvB(q)
    t0 = time.time()
    x, y = z["re"], z["im"]
    w = Fraction(1, 64)
    while Fraction(x) - w <= Fraction(1, 2) + w / 4:
        w /= 2
    cx = Fraction(round(x * 2 ** 20), 2 ** 20)
    cy = Fraction(round(y * 2 ** 20), 2 ** 20)
    try:
        unit = rv.winding_box(cx - w, cx + w, cy - w, cy + w)
    except ArithmeticError as exc:
        unit = {"status": "error", "error": f"{type(exc).__name__}: {exc}"}
    try:
        tiny = rv.tiny_box(x, y, log2_half=30)
    except ArithmeticError as exc:
        tiny = {"status": "error", "error": f"{type(exc).__name__}: {exc}"}
    unit.pop("detail", None)
    tiny.pop("detail", None)
    _write(path, {"q": q, "i": i, "zero_A": z, "unit": unit, "tiny": tiny,
                  "seconds": time.time() - t0})
    return path


def stage_boxB(q: int, ckpt: str, workers: int) -> None:
    zs = zeros_A(q, ckpt)
    units = [(q, i, z, os.path.join(ckpt, f"boxB_q{q}_{i:04d}.json")) for i, z in enumerate(zs)]
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_boxB_unit, units):
            pass


def _fixB_unit(args):
    """Route B's own refinement: a decided re-scan of one window, 8x finer."""
    q, j, lo, hi, path = args
    if os.path.exists(path):
        return path
    rv = _rvB(q)
    t0 = time.time()
    a, b = Fraction(lo), Fraction(hi)
    ts = []
    t = a + Fraction(1, 8192)
    while t < b:
        ts.append(t)
        x = q * max(float(t), 1.0) / (2 * math.pi)
        gap = 2 * math.pi / math.log(max(x, 3.0))
        t = t + Fraction(max(1, int(min(gap / 80.0, 0.0156) * 8192)), 8192)
    signs = [rv.Z_sign(t) for t in ts]
    _write(path, {"q": q, "j": j, "lo": lo, "hi": hi, "ts": [float(t) for t in ts],
                  "zs": signs, "undecided": [str(t) for t, g in zip(ts, signs) if g == 0],
                  "seconds": time.time() - t0})
    return path


def stage_fixB(q: int, ckpt: str, workers: int) -> None:
    m = merge(q, ckpt, use_fix=False)
    units = [(q, w["j"], w["lo"], w["hi"], os.path.join(ckpt, f"fixB_q{q}_{w['j']:04d}.json"))
             for w in m["windows"] if not w["B"]["closes"] and w["B"]["n_box"] is not None]
    if not units:
        return
    with Pool(workers) as pool:
        for _ in pool.imap_unordered(_fixB_unit, units):
            pass


# ---------------------------------------------------------------------------
# merge
# ---------------------------------------------------------------------------


def merge(q: int, ckpt: str, use_fix: bool = True) -> dict:
    plan = plan_windows(q, ckpt)
    b = plan["bounds"]
    rowsA = windows_A(q, ckpt)
    winA = {}
    for f in os.listdir(ckpt):
        if f.startswith(f"winA_q{q}_"):
            d = _read(os.path.join(ckpt, f))
            winA[d["j"]] = d
    tsB, sgB = load_scan(q, ckpt, "scanB")
    baseB = _read(os.path.join(ckpt, f"baseB_q{q}.json"))
    psiB = {0: {"status": "decided", "N": 0, "Z_sign_at_T": _rvB(q).Z_sign(Fraction(0))}}
    for j in range(1, len(b)):
        psiB[j] = _read(os.path.join(ckpt, f"psiB_q{q}_{j:04d}.json"))
    boxes = []
    for f in sorted(os.listdir(ckpt)):
        if f.startswith(f"boxB_q{q}_"):
            boxes.append(_read(os.path.join(ckpt, f)))
    boxes.sort(key=lambda d: d["zero_A"]["im"])
    # route B's own disjointness check of its decided unit boxes
    disjoint = True
    ub = [tuple(Fraction(x) for x in d["tiny"]["box"]) for d in boxes if d["tiny"].get("box")]
    for i in range(len(ub)):
        for k in range(i + 1, len(ub)):
            a, c = ub[i], ub[k]
            if not (a[1] <= c[0] or c[1] <= a[0] or a[3] <= c[2] or c[3] <= a[2]):
                disjoint = False
    # parity: sign Z(T_j) = (-1)^{N(T_j)} on both routes
    parity_A = all(_countA(q, ckpt, j) is not None
                   and (_zA(q, ckpt, j) > 0) == (_countA(q, ckpt, j) % 2 == 0) for j in range(len(b)))
    parity_B = all(psiB[j].get("status") == "decided"
                   and (psiB[j]["Z_sign_at_T"] > 0) == (psiB[j]["N"] % 2 == 0)
                   for j in range(len(b)))
    windows = []
    all_close_A = True
    all_close_B = True
    for r in rowsA:
        j = r["j"]
        lo, hi = r["lo"], r["hi"]
        wa = winA.get(j)
        n_right_A = (wa["n_right"] if wa else 0)
        n_line_A = wa.get("n_line_refined", r["n_line"]) if wa else r["n_line"]
        close_A = (None not in (r["n_box"], n_line_A, n_right_A)
                   and r["n_box"] == n_line_A + 2 * n_right_A)
        pb0, pb1 = psiB[j], psiB[j + 1]
        decided = pb0.get("status") == "decided" and pb1.get("status") == "decided"
        n_box_B = pb1["N"] - pb0["N"] if decided else None
        try:
            n_line_B = _line_count_seq(tsB, sgB, lo, hi, pb0["Z_sign_at_T"], pb1["Z_sign_at_T"])
        except ArithmeticError:
            n_line_B = None
        fixp = os.path.join(ckpt, f"fixB_q{q}_{j:04d}.json")
        n_line_B_refined = None
        if use_fix and os.path.exists(fixp):
            fx = _read(fixp)
            try:
                n_line_B_refined = _line_count_seq(fx["ts"], fx["zs"], lo, hi,
                                                   pb0["Z_sign_at_T"], pb1["Z_sign_at_T"])
            except ArithmeticError:
                n_line_B_refined = None
            n_line_B = n_line_B_refined
        # a zero counts for route B only through its own decided tiny box, which
        # must lie wholly inside the window and wholly in Re s > 1/2
        n_unit_B = 0
        for d in boxes:
            tb = d["tiny"].get("box")
            if not (tb and d["tiny"].get("status") == "decided" and d["tiny"].get("N") == 1):
                continue
            x0, x1, y0, y1 = (Fraction(v) for v in tb)
            if Fraction(lo) < y0 and y1 < Fraction(hi) and x0 > Fraction(1, 2):
                n_unit_B += 1
        close_B = decided and n_line_B is not None and n_box_B == n_line_B + 2 * n_unit_B
        all_close_A &= close_A
        all_close_B &= bool(close_B)
        windows.append({"j": j, "lo": lo, "hi": hi,
                        "A": {"n_box": r["n_box"], "n_line": n_line_A, "n_right": n_right_A,
                              "closes": close_A},
                        "B": {"n_box": n_box_B, "n_line": n_line_B, "n_right_boxed": n_unit_B,
                              "closes": bool(close_B),
                              "line_rescanned": n_line_B_refined is not None}})
    zeros = []
    for d in boxes:
        za = d["zero_A"]
        zeros.append({
            "re_A": za["re"], "im_A": za["im"], "abs_F_A": za["abs_F"],
            "unit_box_B": d["unit"].get("box"), "unit_N_B": d["unit"].get("N"),
            "unit_status_B": d["unit"].get("status"), "tiny_status_B": d["tiny"].get("status"),
            "tiny_box_B": d["tiny"].get("box"), "tiny_N_B": d["tiny"].get("N"),
            "tiny_centre_B": d["tiny"].get("centre"),
            "polish_residual_B": d["tiny"].get("polish_residual"),
        })
    out = {
        "q": q,
        "height": b[-1],
        "n_windows": len(windows),
        "N_total_A": _countA(q, ckpt, len(b) - 1),
        "N_total_B": psiB[len(b) - 1].get("N"),
        "n_line_A": sum(w["A"]["n_line"] for w in windows),
        "n_line_B": sum(w["B"]["n_line"] for w in windows),
        "n_right": len(zeros),
        "all_windows_close_A": all_close_A,
        "all_windows_close_B": all_close_B,
        "unit_boxes_disjoint_B": disjoint,
        "parity_A": parity_A,
        "parity_B": parity_B,
        "base_B": baseB,
        "zeros": zeros,
        "windows": windows,
    }
    return out


STAGES = ("scanA", "plan", "psiA", "winA", "scanB", "psiB", "boxB", "fixB")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, required=True)
    ap.add_argument("--stage", default="all")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--ckpt", required=True)
    ap.add_argument("--out", default=None)
    ap.add_argument("--tend", type=float, default=1000.0)
    a = ap.parse_args()
    global T_END
    T_END = a.tend
    if a.workers > 4:
        raise SystemExit("MISSION.md caps the census at 4 workers")
    os.makedirs(a.ckpt, exist_ok=True)
    todo = STAGES if a.stage == "all" else tuple(a.stage.split(","))
    for st in todo:
        t0 = time.time()
        if st == "scanA":
            stage_scanA(a.q, a.ckpt, a.workers)
        elif st == "plan":
            plan_windows(a.q, a.ckpt)
        elif st == "psiA":
            stage_psiA(a.q, a.ckpt, a.workers)
        elif st == "winA":
            stage_winA(a.q, a.ckpt, a.workers)
        elif st == "scanB":
            stage_scanB(a.q, a.ckpt, a.workers)
        elif st == "psiB":
            stage_psiB(a.q, a.ckpt, a.workers)
        elif st == "boxB":
            stage_boxB(a.q, a.ckpt, a.workers)
        elif st == "fixB":
            stage_fixB(a.q, a.ckpt, a.workers)
        print(f"q={a.q} stage {st} done in {time.time() - t0:.1f} s", flush=True)
    if a.out:
        _write(a.out, merge(a.q, a.ckpt))
        print(f"wrote {a.out}", flush=True)


if __name__ == "__main__":
    main()
