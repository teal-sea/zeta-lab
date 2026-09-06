"""The quasicrystal that is a theorem: a golden model set as ground truth.

Run from the repo root:

    .venv/bin/python hunts/golden_control/probe.py all      # every stage
    .venv/bin/python hunts/golden_control/probe.py calibrate
    .venv/bin/python hunts/golden_control/probe.py gold
    .venv/bin/python hunts/golden_control/probe.py silence
    .venv/bin/python hunts/golden_control/probe.py lesions
    .venv/bin/python hunts/golden_control/probe.py pisano
    .venv/bin/python hunts/golden_control/probe.py precision

Writes ``results.json`` next to this file.  Pre-registered predictions in
``MISSION.md``.

Nothing here is remembered from the diffraction literature.  The golden
model set is *defined* (cut-and-project through a unit window), its Fourier
module is the numerically computed dual lattice, its intensity law is the
window transform integrated in closed form inside this file, and the one
free constant of the tapered transform is calibrated on the integer lattice,
where the whole computation is elementary Poisson summation.  Everything is
the accurate regime (numpy float64 plus exact integer arithmetic for the
Pisano stage); the strongest words used are *measured* and *observed*.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results.json")

PHI = (1 + 5 ** 0.5) / 2
PHI_STAR = (1 - 5 ** 0.5) / 2  # the Galois conjugate, = -1/phi

# taper and extent defaults; the precision stage varies both
N_DEFAULT = 30000
T_DEFAULT = 8000.0


# ---------------------------------------------------------------------------
# the point sets
# ---------------------------------------------------------------------------


def golden_points(n_max: int) -> np.ndarray:
    """The model set {m + n*phi : m + n*phi' in [0, 1)}.

    For each integer n there is exactly one admissible m (the unique integer
    in [-n*phi', 1 - n*phi')), so the set is a chain x_n = m(n) + n*phi with
    mean gap sqrt(5), density 1/sqrt(5), measured below rather than assumed.
    """
    n = np.arange(-n_max, n_max + 1, dtype=np.float64)
    m = np.ceil(-n * PHI_STAR)
    # half-open window: the boundary case m + n*phi' == 1 is excluded by ceil
    return m + n * PHI


def integer_points(x_max: int) -> np.ndarray:
    return np.arange(-x_max, x_max + 1, dtype=np.float64)


def tapered_transform(points: np.ndarray, u: float, taper: float) -> complex:
    """S(u) = sum_x exp(-x^2/(2 T^2)) exp(-i u x)."""
    w = np.exp(-(points ** 2) / (2 * taper ** 2))
    ph = u * points
    return complex(np.sum(w * np.cos(ph)), -np.sum(w * np.sin(ph)))


def peak_scale(taper: float) -> float:
    """A Bragg peak of Fourier-Bohr amplitude c appears in S as c * T*sqrt(2pi)
    (the taper's total mass).  Calibrated on Z in stage ``calibrate``."""
    return taper * math.sqrt(2 * math.pi)


# ---------------------------------------------------------------------------
# the derived ground truth: dual lattice and window law
# ---------------------------------------------------------------------------


def dual_module(p_max: int = 60):
    """Frequencies of the embedding lattice's dual, computed numerically.

    The cut-and-project lattice has basis vectors (1, 1) and (phi, phi') in
    (physical, internal) coordinates; the dual basis D solves B^T D = 2 pi I.
    Peaks of the model set live at the physical components k of dual vectors,
    with internal component k_star controlling the amplitude through the
    window transform.
    """
    B = np.array([[1.0, PHI], [1.0, PHI_STAR]])  # columns are basis vectors
    D = 2 * math.pi * np.linalg.inv(B.T)
    covol = abs(np.linalg.det(B))
    out = []
    for p in range(-p_max, p_max + 1):
        for q in range(-p_max, p_max + 1):
            v = p * D[:, 0] + q * D[:, 1]
            out.append((p, q, float(v[0]), float(v[1])))
    return out, covol


def predicted_amplitude(k_star: float, covol: float, win: float = 1.0) -> float:
    """|Fourier-Bohr coefficient| of the model set at a dual point:
    (|W|/covol) * |sinc(k_star |W| / 2)|, the window integral
    int_0^{|W|} e^{i k* t} dt = |W| e^{i k* |W|/2} sinc(k* |W|/2), done in
    closed form here and nowhere else."""
    z = k_star * win / 2
    s = 1.0 if abs(z) < 1e-12 else math.sin(z) / z
    return (win / covol) * abs(s)


def top_peaks(k_lo=0.2, k_hi=20.0, count=12):
    module, covol = dual_module()
    cands = []
    for p, q, k, ks in module:
        if k_lo <= k <= k_hi:
            cands.append((p, q, k, ks, predicted_amplitude(ks, covol)))
    cands.sort(key=lambda r: -r[4])
    return cands[:count], covol, module


def refine_peak(points, k0, taper, half=3e-3, step=2e-4):
    """Local |S| maximum near k0: coarse scan then three-point parabola."""
    grid = np.arange(k0 - half, k0 + half + step / 2, step)
    vals = [abs(tapered_transform(points, u, taper)) for u in grid]
    i = int(np.argmax(vals))
    if 0 < i < len(grid) - 1:
        a, b, c = vals[i - 1], vals[i], vals[i + 1]
        denom = a - 2 * b + c
        shift = 0.0 if denom == 0 else 0.5 * (a - c) / denom
        k_hat = grid[i] + shift * step
    else:
        k_hat = grid[i]
    return float(k_hat), float(abs(tapered_transform(points, float(k_hat), taper)))


# ---------------------------------------------------------------------------
# results bookkeeping
# ---------------------------------------------------------------------------


def save(stage, payload):
    data = {}
    if os.path.exists(RESULTS):
        with open(RESULTS, encoding="utf-8") as fh:
            data = json.load(fh)
    data[stage] = payload
    with open(RESULTS, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=1, sort_keys=True)
    print(f"[{stage}] written")


# ---------------------------------------------------------------------------
# stages
# ---------------------------------------------------------------------------


def stage_calibrate():
    t0 = time.time()
    pts = integer_points(60000)
    rows = []
    for m in (1, 2, 3):
        k = 2 * math.pi * m
        s = abs(tapered_transform(pts, k, T_DEFAULT))
        rows.append({"m": m, "measured_over_predicted": s / peak_scale(T_DEFAULT)})
    off = abs(tapered_transform(pts, math.pi * 1.234567, T_DEFAULT))
    save("calibrate", {
        "rows": rows,
        "max_defect": max(abs(r["measured_over_predicted"] - 1) for r in rows),
        "off_peak_over_scale": off / peak_scale(T_DEFAULT),
        "seconds": round(time.time() - t0, 2),
    })


def stage_gold():
    t0 = time.time()
    pts = golden_points(N_DEFAULT)
    dens = len(pts) / (pts.max() - pts.min())
    peaks, covol, _ = top_peaks()
    scale = peak_scale(T_DEFAULT)
    rows, pos_defects, amp_defects = [], [], []
    for p, q, k, ks, amp in peaks:
        k_hat, s = refine_peak(pts, k, T_DEFAULT)
        a_meas = s / scale
        rows.append({
            "p": p, "q": q, "k_predicted": k, "k_star": ks,
            "k_measured": k_hat, "position_defect": abs(k_hat - k),
            "amp_predicted": amp, "amp_measured": a_meas,
            "amp_rel_defect": abs(a_meas - amp) / amp,
        })
        pos_defects.append(abs(k_hat - k))
        amp_defects.append(abs(a_meas - amp) / amp)
    save("gold", {
        "n_points": len(pts),
        "density_measured": dens,
        "density_derived": 1 / covol,
        "density_rel_defect": abs(dens * covol - 1),
        "peaks": rows,
        "max_position_defect": max(pos_defects),
        "max_amp_rel_defect": max(amp_defects),
        "seconds": round(time.time() - t0, 2),
    })


def stage_silence():
    t0 = time.time()
    pts = golden_points(N_DEFAULT)
    peaks, covol, module = top_peaks()
    scale = peak_scale(T_DEFAULT)
    # every module frequency in range whose predicted amplitude is visible
    visible = [(k, predicted_amplitude(ks, covol))
               for _, _, k, ks in module
               if 0.2 <= k <= 20.0 and predicted_amplitude(ks, covol) > 2e-3]
    rng = np.random.default_rng(20260811)
    samples = []
    while len(samples) < 200:
        u = float(rng.uniform(0.2, 20.0))
        if all(abs(u - k) > 0.03 for k, _ in visible):
            samples.append(abs(tapered_transform(pts, u, T_DEFAULT)) / scale)
    weakest = min(r[4] for r in peaks)
    med = float(np.median(samples))
    save("silence", {
        "n_visible_module_freqs_excluded": len(visible),
        "median_off_module_amp": med,
        "max_off_module_amp": float(max(samples)),
        "weakest_tested_peak_amp": weakest,
        "separation_weakest_over_median": weakest / med,
        "seconds": round(time.time() - t0, 2),
    })


def stage_lesions():
    t0 = time.time()
    pts = golden_points(N_DEFAULT)
    peaks, covol, _ = top_peaks()
    scale = peak_scale(T_DEFAULT)
    rng = np.random.default_rng(5)
    out = {}
    for sigma in (0.05, 0.10):
        jit = pts + rng.normal(0, sigma, size=pts.shape)
        ratios = []
        for p, q, k, ks, amp in peaks:
            s0 = abs(tapered_transform(pts, k, T_DEFAULT))
            s1 = abs(tapered_transform(jit, k, T_DEFAULT))
            if s1 > 0 and s0 > 0:
                ratios.append((k, math.log(s1 / s0)))
        # Debye-Waller: log ratio should be -sigma^2 k^2 / 2; fit the slope
        ks2 = np.array([k * k for k, _ in ratios])
        ys = np.array([y for _, y in ratios])
        slope = float(np.sum(ks2 * ys) / np.sum(ks2 * ks2))
        out[f"jitter_sigma_{sigma}"] = {
            "fitted_slope": slope,
            "predicted_slope": -sigma ** 2 / 2,
            "slope_rel_defect": abs(slope / (-sigma ** 2 / 2) - 1),
        }
    # Poisson null at matched density and extent
    lo, hi = pts.min(), pts.max()
    pois = rng.uniform(lo, hi, size=pts.shape)
    peak_amps = [abs(tapered_transform(pois, k, T_DEFAULT)) / scale
                 for _, _, k, _, _ in peaks]
    out["poisson_null_max_amp_at_peaks"] = float(max(peak_amps))
    out["weakest_true_peak_amp"] = min(r[4] for r in peaks)
    out["seconds"] = round(time.time() - t0, 2)
    save("lesions", out)


def stage_pisano():
    t0 = time.time()
    import sys
    sys.path.insert(0, os.path.join(HERE, os.pardir, os.pardir))
    from zeta.epstein import chi5

    # (a) the DH quartic character squared equals the quadratic chi_5
    legendre5 = {0: 0, 1: 1, 2: -1, 3: -1, 4: 1}
    sq_ok = all(
        complex(chi5(n) ** 2) == complex(legendre5[n % 5]) for n in range(10)
    )

    # (b) Pisano period pi(p) divides p - chi5(p) for primes p < 500, p != 5
    def primes_upto(n):
        s = list(range(n + 1))
        out = []
        for p in range(2, n + 1):
            if s[p]:
                out.append(p)
                for k in range(p * p, n + 1, p):
                    s[k] = 0
        return out

    def pisano(p):
        a, b, per = 0, 1, 0
        while True:
            a, b = b, (a + b) % p
            per += 1
            if (a, b) == (0, 1):
                return per

    # The mission registered pi(p) | p - chi5(p).  That is WRONG, and this
    # exact computation caught it (first counterexample p = 3: pi = 8, which
    # does not divide 4).  The statement that holds is split/inert asymmetric:
    # pi(p) | p - 1 when chi5(p) = 1, but pi(p) | 2(p + 1) when chi5(p) = -1.
    # Both verdicts are recorded; the registered miss stays on the books.
    rows = []
    registered_ok, corrected_ok, first_cx = True, True, None
    for p in primes_upto(499):
        if p == 5:
            continue
        chi = legendre5[p % 5]
        per = pisano(p)
        naive = (p - chi) % per == 0
        corrected = ((p - 1) % per == 0) if chi == 1 else (2 * (p + 1)) % per == 0
        if not naive and first_cx is None:
            first_cx = {"p": p, "pisano": per, "p_minus_chi": p - chi}
        registered_ok = registered_ok and naive
        corrected_ok = corrected_ok and corrected
        if p < 60:
            rows.append({"p": p, "chi5": chi, "pisano": per,
                         "registered_divides": naive,
                         "corrected_divides": corrected})
    save("pisano", {
        "quartic_squared_is_quadratic": bool(sq_ok),
        "primes_tested_below": 500,
        "registered_claim_holds": bool(registered_ok),
        "registered_claim_first_counterexample": first_cx,
        "corrected_claim_holds": bool(corrected_ok),
        "small_prime_table": rows,
        "seconds": round(time.time() - t0, 2),
    })


def stage_precision():
    t0 = time.time()
    peaks, covol, _ = top_peaks(count=6)
    runs = []
    for n_max, taper in ((15000, 4000.0), (30000, 8000.0), (60000, 16000.0)):
        pts = golden_points(n_max)
        scale = peak_scale(taper)
        defects = []
        for p, q, k, ks, amp in peaks:
            _, s = refine_peak(pts, k, taper)
            defects.append(abs(s / scale - amp) / amp)
        runs.append({"n_max": n_max, "taper": taper,
                     "max_amp_rel_defect": max(defects)})
    shrinking = all(runs[i + 1]["max_amp_rel_defect"] <
                    runs[i]["max_amp_rel_defect"] for i in range(len(runs) - 1))
    save("precision", {"runs": runs, "defect_shrinks_monotonically": shrinking,
                       "seconds": round(time.time() - t0, 2)})


STAGES = {
    "calibrate": stage_calibrate,
    "gold": stage_gold,
    "silence": stage_silence,
    "lesions": stage_lesions,
    "pisano": stage_pisano,
    "precision": stage_precision,
}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", choices=sorted(STAGES) + ["all"])
    args = ap.parse_args()
    if args.stage == "all":
        for name in ("calibrate", "gold", "silence", "lesions", "pisano",
                     "precision"):
            STAGES[name]()
    else:
        STAGES[args.stage]()


if __name__ == "__main__":
    main()
