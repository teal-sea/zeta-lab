"""Mirror-pair self-term of the outband dual kernels.

S(y) = g(iy) for the discrete dual on hunts/outband_certificate/artifacts/dual-x80.json,
matching dual.py: Cin = 2h cos(2 pi a x), so

    S(y) = sum 2h khat_in cosh(2 pi alpha y) - sum 2h z cosh(2 pi aout y)

with h = X / len(x). data[1] is the strip-signed kernel; data[0] is the in-band
control (z empty). Crossings are the first y > 0 on [0, 1.5] where S drops below
r(0) or below 0, found by a scan of step 0.005 then bisection. Numpy float64 and
mp.workdps(40) are independent routes.

Run from the worktree root:

    /Users/thomas/zeta-lab/.venv/bin/python hunts/depth_bound_selfterm/probe.py
"""

from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
ARTIFACT = HERE.parent / "outband_certificate" / "artifacts" / "dual-x80.json"

Y_MAX = 1.5
SCAN_STEP = 0.005
BISECT_ITERS = 80


def load_kernel(record: dict) -> dict:
    x = np.asarray(record["x"], dtype=float)
    h = float(record["X"]) / len(x)
    z = np.asarray(record["z"], dtype=float)
    aout = record.get("aout")
    return {
        "label": record["label"],
        "h": h,
        "khat_in": np.asarray(record["khat_in"], dtype=float),
        "alpha": np.asarray(record["alpha"], dtype=float),
        "z": z if z.size else None,
        "aout": None if not aout else np.asarray(aout, dtype=float),
    }


def S_numpy(y, kernel: dict) -> float:
    y = float(y)
    h = kernel["h"]
    s = float(np.sum(2.0 * h * kernel["khat_in"] * np.cosh(2.0 * np.pi * kernel["alpha"] * y)))
    if kernel["z"] is not None:
        s -= float(np.sum(2.0 * h * kernel["z"] * np.cosh(2.0 * np.pi * kernel["aout"] * y)))
    return s


def S_mpmath(y, kernel: dict):
    with mp.workdps(40):
        yy = mp.mpf(y)
        two_h = 2 * mp.mpf(kernel["h"])
        twopi = 2 * mp.pi
        s = mp.mpf(0)
        for k, a in zip(kernel["khat_in"], kernel["alpha"]):
            s += two_h * mp.mpf(float(k)) * mp.cosh(twopi * mp.mpf(float(a)) * yy)
        if kernel["z"] is not None:
            for zi, ao in zip(kernel["z"], kernel["aout"]):
                s -= two_h * mp.mpf(float(zi)) * mp.cosh(twopi * mp.mpf(float(ao)) * yy)
        return s


def _bisect(f, lo: float, hi: float, iters: int = BISECT_ITERS) -> float:
    flo, fhi = f(lo), f(hi)
    if flo == 0:
        return float(lo)
    if fhi == 0:
        return float(hi)
    if flo * fhi > 0:
        raise ValueError(f"bisection bracket [{lo}, {hi}] does not change sign")
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if flo * fm <= 0:
            hi, fhi = mid, fm
        else:
            lo, flo = mid, fm
    return 0.5 * (lo + hi)


def first_below(kernel: dict, threshold: float, y_max: float = Y_MAX, step: float = SCAN_STEP):
    """Smallest y > 0 on [0, y_max] with S(y) < threshold, or None.

    Scans at `step`, then bisects the first bracket. The trivial root of
    S(y) - r(0) at y = 0 is excluded by requiring y > 0 and a strict drop.
    """
    n = int(round(y_max / step))
    ys = np.linspace(0.0, y_max, n + 1)
    prev_y = None
    prev_s = None
    for y in ys:
        s = S_numpy(float(y), kernel)
        if float(y) > 0.0 and s < threshold and prev_s is not None and prev_s >= threshold:
            lo, hi = float(prev_y), float(y)

            def f_np(t, _k=kernel, _thr=threshold):
                return S_numpy(t, _k) - _thr

            def f_mp(t, _k=kernel, _thr=threshold):
                with mp.workdps(40):
                    return S_mpmath(t, _k) - mp.mpf(_thr)

            y_np = _bisect(f_np, lo, hi)
            y_mp = _bisect(lambda t: float(f_mp(t)), lo, hi)
            return {
                "bracket": (lo, hi),
                "y_numpy": y_np,
                "y_mpmath": y_mp,
                "agreement": abs(y_np - y_mp),
                "S_numpy": S_numpy(y_np, kernel),
                "S_mpmath": float(S_mpmath(y_mp, kernel)),
            }
        prev_y, prev_s = float(y), s
    return None


def scan_control(kernel: dict, y_max: float = Y_MAX, step: float = SCAN_STEP) -> dict:
    n = int(round(y_max / step))
    ys = np.linspace(0.0, y_max, n + 1)
    ss = np.array([S_numpy(float(y), kernel) for y in ys])
    return {
        "ys": ys,
        "S": ss,
        "monotonic_increase": bool(np.all(np.diff(ss) > 0.0)),
        "S_at_0.9": S_numpy(0.9, kernel),
        "S_at_1.0": S_numpy(1.0, kernel),
        "S_min": float(ss.min()),
        "S_max": float(ss.max()),
    }


def measure_kernel(kernel: dict) -> dict:
    r0_np = S_numpy(0.0, kernel)
    r0_mp = float(S_mpmath(0.0, kernel))
    return {
        "label": kernel["label"],
        "r0_numpy": r0_np,
        "r0_mpmath": r0_mp,
        "r0_agreement": abs(r0_np - r0_mp),
        "y_r0": first_below(kernel, r0_np),
        "y_0": first_below(kernel, 0.0),
    }


def run_measurements() -> dict:
    records = json.loads(ARTIFACT.read_text())
    control = load_kernel(records[0])
    dual = load_kernel(records[1])
    if control["label"] != "control, in-band only":
        raise RuntimeError(f"data[0] is {control['label']!r}, not the in-band control")
    if dual["label"] != "out-of-band positivity to 1.5":
        raise RuntimeError(f"data[1] is {dual['label']!r}, not the strip-signed kernel")
    if control["z"] is not None:
        raise RuntimeError("in-band control must have empty z")
    ctrl_scan = scan_control(control)
    return {
        "dual": measure_kernel(dual),
        "control": {**measure_kernel(control), "scan": {
            "monotonic_increase": ctrl_scan["monotonic_increase"],
            "S_at_0.9": ctrl_scan["S_at_0.9"],
            "S_at_1.0": ctrl_scan["S_at_1.0"],
            "S_min": ctrl_scan["S_min"],
            "S_max": ctrl_scan["S_max"],
            "step": SCAN_STEP,
            "y_max": Y_MAX,
        }},
        "scan_step": SCAN_STEP,
        "y_max": Y_MAX,
    }


def _fmt_cross(cross, name: str) -> str:
    if cross is None:
        return f"  smallest y > 0 with {name}: None on [0, {Y_MAX}]"
    return (
        f"  smallest y > 0 with {name}: {cross['y_numpy']:.10f} "
        f"(mpmath {cross['y_mpmath']:.10f}, agreement {cross['agreement']:.2e})"
    )


def main() -> None:
    res = run_measurements()
    d = res["dual"]
    c = res["control"]
    print(f"Dual kernel ({d['label']}):")
    print(f"  r(0) = {d['r0_numpy']:.15f}  (mpmath {d['r0_mpmath']:.15f}, agreement {d['r0_agreement']:.2e})")
    print(_fmt_cross(d["y_r0"], "S(y) < r(0)"))
    print(_fmt_cross(d["y_0"], "S(y) < 0"))
    print(f"\nControl kernel ({c['label']}, z empty):")
    print(f"  r(0) = {c['r0_numpy']:.15f}  (mpmath {c['r0_mpmath']:.15f}, agreement {c['r0_agreement']:.2e})")
    print(_fmt_cross(c["y_r0"], "S(y) < r(0)"))
    print(_fmt_cross(c["y_0"], "S(y) < 0"))
    sc = c["scan"]
    print(f"  S(0.9) = {sc['S_at_0.9']:.12f}")
    print(f"  S(1.0) = {sc['S_at_1.0']:.12f}")
    print(f"  monotonic increase on [0, {Y_MAX}] step {sc['step']}: {sc['monotonic_increase']}")


if __name__ == "__main__":
    main()
