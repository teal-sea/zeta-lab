"""Deep off-line zeros of the Davenport-Heilbronn function: a screen by height.

Hunt #119, phase 2.  The question the hunt asks is whether the crowding shave
vanishes along a sequence of zeros whose depth `y0 = beta - 1/2` approaches
`Delta = 0.62036249819`.  Bombieri and Ghosh (Russian Math. Surveys 66:2
(2011) 221-270, Theorem 7 and section 6) determined `sigma(tau_+, 1) =
1.120362` as the exact least upper bound of the real parts of the zeros of
this function, so zeros with `beta` arbitrarily close to `1.120362` exist.
Their section 9 also says such zeros are extremely rare for `tau_+`: reaching
`Re s > 1` requires the arguments of `p^{it}` to align near `0 mod pi` for
hundreds of primes at once, and the prime-sum margin for `tau_+` is
`1.2940091`, the hard end of the spectrum they survey.  For the easier
`xi = 0` member of the family they searched `1/2 <= sigma < 1.2`,
`0 <= t < 10000` and found no zero at all with real part above 1.  So this
screen is not expected to reach `beta > 1`; what it can do is measure how the
maximum depth grows with height.

Grade discipline (`MISSION.md` vocabulary contract): everything here is float
grade.  The strongest words used are *measured* and *observed*.  Winding
numbers are measured integers, with the residual defect recorded.

Method
------

1. **A fast float64 evaluator for f.**  `zeta.epstein.dh_f` routes through
   mpmath's Hurwitz zeta and costs about 1 s per call at height `10^4`, which
   makes a height screen impossible.  This module re-derives the same value by
   Euler-Maclaurin applied to the four Hurwitz pieces, vectorized in numpy:

       f(s) = sum_{m=1}^{5N-1} a_m m^{-s}
              + sum_{a=1..4} c_a [ (1/5) X_a^{1-s}/(s-1) + (1/2) X_a^{-s}
                + sum_{k=1..M} B_{2k}/(2k)! (s)_{2k-1} 5^{2k-1} X_a^{-s-2k+1} ]

   with `X_a = 5N + a` and `c_a = a_a` the period-5 coefficients.  The
   normalisation of every factor is *checked against* `zeta.epstein.dh_f`
   rather than trusted: `validate()` compares the two at eight points spread
   over the strip and over five decades of height, and the run records the
   worst disagreement in the JSON.  Along a vertical line with equally spaced
   ordinates the head is evaluated by the recurrence
   `m^{-sigma-i(t+dt)} = m^{-sigma-it} * m^{-i dt}`, re-anchored every 256
   steps, which is about 47 times faster than recomputing the exponentials.

2. **A counting function for the deep zeros.**  For the rectangle
   `[sigma_c, R] x [t_a, t_b]` with `R = 2.05` the argument principle gives

       N(t_a, t_b) = (1/2pi) [ W(t_b) - W(t_a) ],
       W(t) = V(t) - U(t) - A(t),

   where `U(t)` is the continuous phase of f along the left edge
   `sigma = sigma_c` accumulated from the bottom of the range, `V(t) =
   arg f(R + it)` (single valued, because `sum_{n>=2} |a_n| n^{-2.05} = 0.25
   < 1` keeps f in the right half plane there), and `A(t)` is the continuous
   phase variation along the horizontal segment `sigma_c -> R` at height `t`.
   The telescoping is what makes the screen cheap: the expensive object `U`
   is computed once as a running total, and each window boundary costs only
   the short horizontal `A`.

3. **Locate.**  A window with a nonzero count is bisected in `t` on the same
   counting function until each part holds one zero, seeded from a grid
   minimum of `|f|` and polished by Newton on the fast evaluator.  Each root
   gets a unit winding check on a small box, and the deepest roots are
   re-polished with `mp.findroot` on `zeta.epstein.dh_f` at dps 40 so the
   digits reported do not come from the float route alone.

4. **Neighbours.**  For every off-line zero the module records the distance to
   the nearest critical-line zero (located by sign changes of the Hardy-style
   `Z` built from the fast evaluator), the mirror distance `2 y0` to the
   partner `1 - conj(rho)` forced by the functional equation, and the local
   mean line-zero gap `2 pi / log(5 gamma / 2 pi)`.

Stages, run from the repo root::

    .venv/bin/python hunts/lambda_dh_exact/deep_zeros.py validate
    .venv/bin/python hunts/lambda_dh_exact/deep_zeros.py screen --t0 8 --t1 10000
    .venv/bin/python hunts/lambda_dh_exact/deep_zeros.py locate
    .venv/bin/python hunts/lambda_dh_exact/deep_zeros.py refine
    .venv/bin/python hunts/lambda_dh_exact/deep_zeros.py report
"""

from __future__ import annotations

import argparse
import json
import math
import os
import time

import numpy as np
from mpmath import mp

from zeta.epstein import dh_f, kappa

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "deep_zeros.json")

SIGMA_C = 0.85          # left edge of the deep box
SIGMA_R = 2.05          # right edge, beyond every zero (sum |a_n| n^-2.05 < 1)
WINDOW = 20.0           # height of one screening window
PTS_PER_UNIT = 16       # uniform samples per unit height on the left edge
EM_M = 10               # Euler-Maclaurin correction terms
EM_RATIO = 3.0          # Hurwitz cutoff N >= ratio * t / (2 pi)

KAP = float(kappa(30))
AVEC = np.array([1.0, KAP, -KAP, -1.0, 0.0])
_BERN = [float(mp.bernoulli(2 * k)) for k in range(1, EM_M + 1)]
_FACT = [float(math.factorial(2 * k)) for k in range(1, EM_M + 1)]


# ---------------------------------------------------------------------------
# the fast evaluator
# ---------------------------------------------------------------------------


class Terms:
    """Cached head arrays for a Hurwitz cutoff good up to height ``t_valid``."""

    def __init__(self, t_valid: float):
        self.t_valid = max(float(t_valid), 10.0)
        N = int(math.ceil(EM_RATIO * self.t_valid / (2 * math.pi)) + 20)
        self.M5 = 5 * N
        idx = np.arange(1, self.M5)
        am = AVEC[(idx - 1) % 5]
        keep = am != 0.0
        self.m = idx[keep].astype(float)
        self.am = am[keep]
        self.logm = np.log(self.m)

    def covers(self, t: float) -> bool:
        return t <= self.t_valid


_terms: Terms | None = None


def terms_for(t: float) -> Terms:
    """Head arrays valid at height ``t``, rebuilt with 15 percent headroom."""
    global _terms
    if _terms is None or not _terms.covers(t):
        _terms = Terms(max(t * 1.15, 50.0))
    return _terms


def _tail(s: np.ndarray, M5: int) -> np.ndarray:
    out = np.zeros(s.shape, dtype=complex)
    for a in range(1, 5):
        ca = AVEC[a - 1]
        X = float(M5 + a)
        Xms = np.exp(-s * math.log(X))
        term = 0.2 * X * Xms / (s - 1.0) + 0.5 * Xms
        poch = s.copy()
        Xpow = Xms / X
        for k in range(1, EM_M + 1):
            if k > 1:
                poch = poch * (s + (2 * k - 3)) * (s + (2 * k - 2))
                Xpow = Xpow / (X * X)
            term = term + (_BERN[k - 1] / _FACT[k - 1]) * poch * (5.0 ** (2 * k - 1)) * Xpow
        out = out + ca * term
    return out


def f_at(svals) -> np.ndarray:
    """f(s) for an array of complex s (float64), Euler-Maclaurin route."""
    s = np.atleast_1d(np.asarray(svals, dtype=complex))
    tv = float(np.max(np.abs(s.imag))) if s.size else 10.0
    T = terms_for(tv)
    out = np.empty(s.size, dtype=complex)
    flat = s.ravel()
    blk = max(1, int(4e6 // max(len(T.m), 1)))
    for i0 in range(0, flat.size, blk):
        ss = flat[i0:i0 + blk]
        head = (T.am[None, :] * np.exp(-ss[:, None] * T.logm[None, :])).sum(axis=1)
        out[i0:i0 + blk] = head + _tail(ss, T.M5)
    return out.reshape(s.shape)


def f_one(z: complex) -> complex:
    return complex(f_at(np.array([complex(z)]))[0])


def f_vline(sigma: float, t0: float, dt: float, npts: int, reanchor: int = 256):
    """f(sigma + it) at t = t0 + j dt, j = 0..npts-1, by the phase recurrence."""
    T = terms_for(t0 + dt * (npts - 1))
    amp = T.am * np.exp(-sigma * T.logm)
    step = np.exp(-1j * dt * T.logm)
    out = np.empty(npts, dtype=complex)
    j = 0
    while j < npts:
        k = min(reanchor, npts - j)
        cur = amp * np.exp(-1j * (t0 + dt * j) * T.logm)
        for i in range(k):
            out[j + i] = cur.sum()
            if i + 1 < k:
                cur = cur * step
        j += k
    s = sigma + 1j * (t0 + dt * np.arange(npts))
    return out + _tail(s, T.M5)


def validate(dps: int = 25) -> dict:
    """Compare the fast evaluator with ``zeta.epstein.dh_f`` at eight points."""
    pts = [
        0.8085171824566374 + 85.69934848537759j,
        0.8469538030920491 + 531.2797268965209j,
        0.85 + 3.5j,
        0.95 + 300.3j,
        1.05 + 77.7j,
        0.85 + 2000.0j,
        SIGMA_R + 4321.0j,
        0.9 + 10000.0j,
    ]
    rows = []
    worst = 0.0
    for p in pts:
        fast = f_one(p)
        ref = complex(dh_f(mp.mpc(p.real, p.imag), dps=dps))
        err = abs(fast - ref)
        scale = max(abs(ref), 1e-12)
        rows.append({
            "s": [p.real, p.imag],
            "fast": [fast.real, fast.imag],
            "mpmath": [ref.real, ref.imag],
            "abs_error": err,
        })
        worst = max(worst, err)
    return {"points": rows, "worst_abs_error": worst, "mpmath_dps": dps}


# ---------------------------------------------------------------------------
# phase bookkeeping
# ---------------------------------------------------------------------------


def _principal(d: np.ndarray | float):
    return (d + math.pi) % (2 * math.pi) - math.pi


def _refine_gap(fn, x0, x1, a0, a1, depth=0, max_depth=30):
    """Continuous arg variation from x0 to x1 given endpoint values, by
    bisection until every accepted step turns less than pi/3."""
    d = _principal(math.atan2(a1.imag, a1.real) - math.atan2(a0.imag, a0.real))
    if abs(d) < math.pi / 3 or depth >= max_depth:
        return d
    xm = (x0 + x1) / 2
    am = fn(xm)
    return (_refine_gap(fn, x0, xm, a0, am, depth + 1, max_depth)
            + _refine_gap(fn, xm, x1, am, a1, depth + 1, max_depth))


def vline_variation(sigma: float, t0: float, t1: float, pts_per_unit=PTS_PER_UNIT):
    """Continuous arg variation of f along sigma + i[t0, t1], upward.

    Returns (variation, n_refinements).  A uniform grid is laid down first and
    every step turning by pi/3 or more is bisected, so a full 2 pi hidden
    inside one step cannot be lost silently.
    """
    npts = max(4, int(math.ceil((t1 - t0) * pts_per_unit)) + 1)
    dt = (t1 - t0) / (npts - 1)
    vals = f_vline(sigma, t0, dt, npts)
    ang = np.angle(vals)
    d = _principal(np.diff(ang))
    bad = np.nonzero(np.abs(d) >= math.pi / 3)[0]
    total = float(d.sum())
    for i in bad:
        fn = lambda t: f_one(complex(sigma, t))
        good = _refine_gap(fn, t0 + dt * i, t0 + dt * (i + 1), vals[i], vals[i + 1])
        total += good - d[i]
    return total, len(bad)


def hvariation(t: float, sa: float | None = None, sb: float = SIGMA_R, n: int = 25):
    """Continuous arg variation of f along the horizontal sa -> sb at height t."""
    sa = SIGMA_C if sa is None else sa
    xs = np.linspace(sa, sb, n)
    vals = f_at(xs + 1j * t)
    ang = np.angle(vals)
    d = _principal(np.diff(ang))
    total = float(d.sum())
    bad = np.nonzero(np.abs(d) >= math.pi / 3)[0]
    for i in bad:
        fn = lambda x: f_one(complex(x, t))
        total += _refine_gap(fn, xs[i], xs[i + 1], vals[i], vals[i + 1]) - d[i]
    return total


def w_of(t: float, u_cum: float) -> float:
    """W(t) = V(t) - U(t) - A(t) with U(t) supplied as the running total."""
    v = math.atan2(f_one(complex(SIGMA_R, t)).imag, f_one(complex(SIGMA_R, t)).real)
    return v - u_cum - hvariation(t)


def count_between(t_a: float, w_a: float, t_b: float, w_b: float):
    """Zeros of f with Re s > SIGMA_C and t_a < Im s < t_b, from two W values."""
    raw = (w_b - w_a) / (2 * math.pi)
    n = int(round(raw))
    return n, abs(raw - n)


# ---------------------------------------------------------------------------
# results plumbing
# ---------------------------------------------------------------------------


def load(path: str = RESULTS) -> dict:
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    return {}


def save(update: dict, path: str = RESULTS) -> None:
    data = load(path)
    data.update(update)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")


# ---------------------------------------------------------------------------
# stage screen
# ---------------------------------------------------------------------------


def stage_screen(t0: float, t1: float, out: str, key: str = "screen") -> None:
    started = time.time()
    data = load(out).get(key, {})
    boundaries = data.get("boundaries", [])
    u_cum = data.get("u_cum", 0.0)
    n_refine = data.get("n_refine", 0)
    if boundaries and abs(boundaries[-1][0] - t1) < 1e-9:
        print("screen already complete", flush=True)
        return
    if not boundaries or abs(boundaries[0][0] - t0) > 1e-9:
        boundaries, u_cum, n_refine = [], 0.0, 0
        w0 = w_of(t0, u_cum)
        boundaries.append([t0, w0, 0.0])
    t_prev = boundaries[-1][0]
    while t_prev < t1 - 1e-9:
        t_next = min(t_prev + WINDOW, t1)
        var, nb = vline_variation(SIGMA_C, t_prev, t_next)
        u_cum += var
        n_refine += nb
        w = w_of(t_next, u_cum)
        boundaries.append([t_next, w, u_cum])
        t_prev = t_next
        if len(boundaries) % 25 == 0 or t_prev >= t1 - 1e-9:
            save({key: {
                "t0": t0, "t1": t1, "sigma_c": SIGMA_C, "sigma_r": SIGMA_R,
                "window": WINDOW, "pts_per_unit": PTS_PER_UNIT,
                "boundaries": boundaries, "u_cum": u_cum,
                "n_refine": n_refine,
                "complete": bool(t_prev >= t1 - 1e-9),
                "seconds": round(time.time() - started, 1),
            }}, out)
            print(f"screen t={t_prev:.0f}/{t1:.0f} "
                  f"({time.time() - started:.0f}s)", flush=True)


def flagged_windows(scan: dict):
    b = scan["boundaries"]
    hits = []
    for (ta, wa, _), (tb, wb, _) in zip(b, b[1:]):
        n, defect = count_between(ta, wa, tb, wb)
        if n != 0:
            hits.append({"t_lo": ta, "t_hi": tb, "count": n, "defect": defect})
    return hits


# ---------------------------------------------------------------------------
# stage locate
# ---------------------------------------------------------------------------


def _w_at(t: float, anchor_t: float, anchor_u: float) -> float:
    var, _ = vline_variation(SIGMA_C, anchor_t, t)
    return w_of(t, anchor_u + var), anchor_u + var


def split_window(ta: float, wa: float, ua: float, tb: float, wb: float, want: int,
                 depth: int = 0):
    """Bisect [ta, tb] on the counting function until each part holds one zero."""
    n, _ = count_between(ta, wa, tb, wb)
    if n <= 1 or depth > 14 or (tb - ta) < 0.02:
        return [(ta, tb, n)] if n >= 1 else []
    tm = (ta + tb) / 2
    wm, um = _w_at(tm, ta, ua)
    left = split_window(ta, wa, ua, tm, wm, 0, depth + 1)
    right = split_window(tm, wm, um, tb, wb, 0, depth + 1)
    return left + right


def newton_root(seed: complex, iters: int = 60) -> complex:
    z = complex(seed)
    h = 1e-6
    for _ in range(iters):
        fz = f_one(z)
        if abs(fz) < 1e-15:
            break
        d = (f_one(z + h) - f_one(z - h)) / (2 * h)
        if d == 0:
            break
        step = fz / d
        z = z - step
        if abs(step) < 1e-15:
            break
    return z


def locate_in(ta: float, tb: float, pts_per_unit: int = 4, nsig: int = 12):
    """Grid minimum of |f| over [SIGMA_C, 1.25] x [ta, tb], then Newton.

    Each row of constant sigma is evaluated by the phase recurrence of
    :func:`f_vline`, which is the only affordable route above height 10^4.
    """
    xs = np.linspace(SIGMA_C - 0.01, 1.25, nsig)
    npts = max(8, int((tb - ta) * pts_per_unit) + 1)
    dt = (tb - ta) / (npts - 1)
    best = (None, None)
    for x in xs:
        vals = np.abs(f_vline(float(x), ta, dt, npts))
        j = int(np.argmin(vals))
        if best[0] is None or vals[j] < best[0]:
            best = (vals[j], complex(x, ta + dt * j))
    return newton_root(best[1])


def winding_check(rho: complex, h: float = 0.02) -> tuple[int, float]:
    """Winding number of f around a box of half side h centred on rho."""
    n = 24
    corners = [complex(rho.real - h, rho.imag - h), complex(rho.real + h, rho.imag - h),
               complex(rho.real + h, rho.imag + h), complex(rho.real - h, rho.imag + h),
               complex(rho.real - h, rho.imag - h)]
    total = 0.0
    for a, b in zip(corners, corners[1:]):
        pts = np.array([a + (b - a) * k / n for k in range(n + 1)])
        vals = f_at(pts)
        d = _principal(np.diff(np.angle(vals)))
        seg = float(d.sum())
        bad = np.nonzero(np.abs(d) >= math.pi / 3)[0]
        for i in bad:
            fn = lambda u, _a=a, _b=b: f_one(_a + (_b - _a) * u)
            seg += _refine_gap(fn, i / n, (i + 1) / n, vals[i], vals[i + 1]) - d[i]
        total += seg
    w = total / (2 * math.pi)
    return int(round(w)), abs(w - round(w))


def stage_locate(out: str, key: str = "screen") -> None:
    started = time.time()
    data = load(out)
    scan = data[key]
    hits = flagged_windows(scan)
    print(f"{len(hits)} flagged windows, "
          f"{sum(h['count'] for h in hits)} zeros with beta > {SIGMA_C}", flush=True)
    b = {row[0]: (row[1], row[2]) for row in scan["boundaries"]}
    zeros = data.get("zeros", [])
    done = {round(z["gamma"], 3) for z in zeros}
    for h in hits:
        ta, tb = h["t_lo"], h["t_hi"]
        wa, ua = b[ta]
        wb, _ = b[tb]
        parts = split_window(ta, wa, ua, tb, wb, h["count"])
        for (pa, pb, n) in parts:
            for _ in range(max(1, n)):
                rho = locate_in(pa, pb)
                if not (pa - 0.5 <= rho.imag <= pb + 0.5):
                    continue
                if round(rho.imag, 3) in done:
                    continue
                wind, defect = winding_check(rho)
                res = abs(f_one(rho))
                zeros.append({
                    "beta": rho.real, "gamma": rho.imag,
                    "y0": rho.real - 0.5,
                    "abs_f_float": res,
                    "winding": wind, "winding_defect": defect,
                    "box": [pa, pb], "screen_window": [ta, tb],
                    "route": "float64 Euler-Maclaurin + Newton",
                })
                done.add(round(rho.imag, 3))
                break
        save({"zeros": sorted(zeros, key=lambda z: z["gamma"]),
              "locate_seconds": round(time.time() - started, 1)}, out)
        print(f"located through t={tb:.0f} ({len(zeros)} zeros)", flush=True)


# ---------------------------------------------------------------------------
# neighbours and the mpmath re-polish
# ---------------------------------------------------------------------------


def _theta(t: float) -> float:
    from scipy.special import loggamma
    return float(np.imag(loggamma(0.75 + 0.5j * t)) - 0.5 * t * math.log(math.pi / 5))


def z_fast(ts: np.ndarray) -> np.ndarray:
    from scipy.special import loggamma
    th = np.imag(loggamma(0.75 + 0.5j * ts)) - 0.5 * ts * math.log(math.pi / 5)
    return np.real(np.exp(1j * th) * f_at(0.5 + 1j * ts))


def line_zeros_near(gamma: float, span_gaps: float = 2.5):
    """Ordinates of the critical-line zeros near ``gamma``.

    A coarse grid (60 samples per mean gap, evaluated by the phase recurrence)
    brackets the sign changes of the Hardy-style Z; the bracket nearest the
    given height is then bisected 14 times.  Nothing here needs more than a
    few thousandths of a unit, because the quantity wanted is a distance to a
    neighbour of order one gap.
    """
    from scipy.special import loggamma

    gap = 2 * math.pi / math.log(5 * max(gamma, 10.0) / (2 * math.pi))
    span = span_gaps * gap
    npts = int(60 * 2 * span_gaps) + 1
    dt = 2 * span / (npts - 1)
    t_lo = gamma - span
    vals = f_vline(0.5, t_lo, dt, npts)
    ts = t_lo + dt * np.arange(npts)
    th = np.imag(loggamma(0.75 + 0.5j * ts)) - 0.5 * ts * math.log(math.pi / 5)
    zz = np.real(np.exp(1j * th) * vals)

    def zed(t: float) -> float:
        v = f_one(complex(0.5, t))
        a = float(np.imag(loggamma(0.75 + 0.5j * t)) - 0.5 * t * math.log(math.pi / 5))
        return float((math.cos(a) * v.real - math.sin(a) * v.imag))

    out = []
    for i in range(npts - 1):
        if zz[i] == 0 or zz[i + 1] == 0:
            continue
        if (zz[i] > 0) != (zz[i + 1] > 0):
            a, b, fa = ts[i], ts[i + 1], zz[i]
            for _ in range(14):
                m = 0.5 * (a + b)
                fm = zed(m)
                if (fa > 0) != (fm > 0):
                    b = m
                else:
                    a, fa = m, fm
            out.append(0.5 * (a + b))
    return out, gap


def stage_refine(out: str, top: int = 6, dps: int = 40) -> None:
    """Neighbour geometry for every zero, plus an mpmath re-polish of the
    deepest ``top`` of them so the reported digits do not rest on float64.

    The landing columns are the isolated-pair prediction ``y0^2/2`` (narrow
    frame; ``2 y0^2`` wide) and the calibrated crowding model of
    ``theory.t_star_gap``, which is the one the mission pre-registered.
    """
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "dh_theory", os.path.join(HERE, "theory.py"))
    theory = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(theory)

    data = load(out)
    zeros = data.get("zeros", [])
    order = sorted(range(len(zeros)), key=lambda i: -zeros[i]["y0"])
    started = time.time()
    for rank, i in enumerate(order):
        z = zeros[i]
        if "mean_line_gap" not in z:
            g, gap = line_zeros_near(z["gamma"])
            rho = complex(z["beta"], z["gamma"])
            if g:
                z["nearest_line_zero_gamma"] = min(
                    g, key=lambda t: abs(complex(0.5, t) - rho))
                z["nearest_line_zero_distance"] = abs(
                    complex(0.5, z["nearest_line_zero_gamma"]) - rho)
                z["line_zeros_in_window"] = len(g)
            z["mean_line_gap"] = gap
            z["mirror_distance"] = 2 * z["y0"]
            z["landing_naive_narrow"] = z["y0"] ** 2 / 2
            z["landing_naive_wide"] = 2 * z["y0"] ** 2
            z["landing_model_narrow"] = float(
                theory.t_star_gap(z["y0"], z["gamma"]))
            z["landing_model_wide"] = 4 * z["landing_model_narrow"]
        if rank < top and "beta_mp" not in z:
            with mp.workdps(dps):
                root = mp.findroot(lambda s: dh_f(s, dps=dps),
                                   mp.mpc(z["beta"], z["gamma"]))
                resid = abs(dh_f(root, dps=dps))
            z["beta_mp"] = mp.nstr(mp.re(root), 25)
            z["gamma_mp"] = mp.nstr(mp.im(root), 25)
            z["y0_mp"] = mp.nstr(mp.re(root) - mp.mpf(1) / 2, 25)
            z["abs_f_mp"] = mp.nstr(resid, 4)
            z["mp_dps"] = dps
            print(f"refined {z['beta_mp']} + {z['gamma_mp']}i "
                  f"({time.time() - started:.0f}s)", flush=True)
        if rank % 10 == 0 or rank < top:
            save({"zeros": zeros}, out)
    save({"zeros": zeros}, out)


def stage_merge(out: str, extra: list[str], zero_files: list[str]) -> None:
    """Fold the side runs into one file and derive the density table.

    ``extra`` are result files holding further screens (the control screens at
    other left edges, the height-10^6 probe); ``zero_files`` hold located
    zeros.  The derived block records, for a ladder of thresholds sigma, the
    count of zeros with beta > sigma below each screened height and the
    implied density per unit height.  Under Bohr-Jessen theory that density
    tends to a constant c(sigma) for each fixed sigma, so the largest beta
    reachable below height T is the sigma solving c(sigma) T = 1: the
    extrapolation column reports the height at which one zero of that depth is
    expected.
    """
    data = load(out)
    for path in extra:
        for k, v in load(path).items():
            if k not in data:
                data[k] = v
    zeros = {round(z["gamma"], 4): z for z in data.get("zeros", [])}
    for path in zero_files:
        for z in load(path).get("zeros", []):
            zeros[round(z["gamma"], 4)] = z
    allz = sorted(zeros.values(), key=lambda z: z["gamma"])
    data["zeros"] = allz

    screened = []
    for key in sorted(k for k in data if k.startswith("screen")):
        sc = data[key]
        b = sc["boundaries"]
        screened.append({"key": key, "sigma_c": sc["sigma_c"],
                         "t_lo": b[0][0], "t_hi": b[-1][0],
                         "height": b[-1][0] - b[0][0],
                         "complete": sc.get("complete", False),
                         "n_zeros": sum(x["count"] for x in flagged_windows(sc)),
                         "pts_per_unit": sc["pts_per_unit"]})
    data["screens"] = screened

    # density ladder over the contiguous sigma_c = 0.85 screens
    height = 0.0
    for row in screened:
        if row["sigma_c"] == SIGMA_C and row["t_hi"] <= 200000:
            height = max(height, row["t_hi"])
    ys = [z["y0"] for z in allz if z["gamma"] <= height]
    ladder = []
    for sig in (0.85, 0.86, 0.87, 0.88, 0.89, 0.90, 0.91, 0.92, 0.93):
        n = sum(1 for y in ys if y + 0.5 > sig)
        ladder.append({"sigma": sig, "count": n, "height": height,
                       "density_per_unit": n / height if height else None,
                       "expected_height_for_one": (height / n) if n else None})
    data["density_ladder"] = ladder
    if allz:
        deep = max(allz, key=lambda z: z["y0"])
        data["summary"] = {
            "screened_height_complete_to": height,
            "n_offline_zeros_beta_above_%.2f" % SIGMA_C: len(ys),
            "deepest_beta": deep["beta"],
            "deepest_gamma": deep["gamma"],
            "deepest_y0": deep["y0"],
            "deepest_y0_over_Delta": deep["y0"] / 0.62036249819,
            "Delta": 0.62036249819,
            "landing_naive_narrow_at_deepest": deep["y0"] ** 2 / 2,
            "max_landing_model_narrow": max(
                (z.get("landing_model_narrow") or 0.0) for z in allz),
            "argmax_landing_model_gamma": max(
                allz, key=lambda z: z.get("landing_model_narrow") or 0.0)["gamma"],
        }
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(json.dumps(data["summary"], indent=2))
    print(json.dumps(data["density_ladder"], indent=2))


def stage_report(out: str) -> None:
    data = load(out)
    zeros = data.get("zeros", [])
    zeros = sorted(zeros, key=lambda z: -z["y0"])
    print(f"{len(zeros)} off-line zeros with beta > {SIGMA_C}")
    for z in zeros[:20]:
        print(f"  beta={z['beta']:.12f} gamma={z['gamma']:.6f} "
              f"y0={z['y0']:.9f} naive t*={z['y0']**2/2:.9f}")
    if zeros:
        summary = {
            "n_zeros": len(zeros),
            "deepest_y0": zeros[0]["y0"],
            "deepest_beta": zeros[0]["beta"],
            "deepest_gamma": zeros[0]["gamma"],
            "delta": 0.62036249819,
            "deepest_over_delta": zeros[0]["y0"] / 0.62036249819,
        }
        save({"summary": summary}, out)
        print(json.dumps(summary, indent=2))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("stage",
                    choices=["validate", "screen", "locate", "refine",
                             "merge", "report"])
    ap.add_argument("--extra", nargs="*", default=[])
    ap.add_argument("--zeros", nargs="*", default=[])
    ap.add_argument("--t0", type=float, default=8.0)
    ap.add_argument("--t1", type=float, default=10000.0)
    ap.add_argument("--out", default=RESULTS)
    ap.add_argument("--key", default="screen")
    ap.add_argument("--top", type=int, default=6)
    ap.add_argument("--sigma-c", type=float, default=None,
                    help="left edge of the deep box (default 0.85)")
    args = ap.parse_args()
    if args.sigma_c is not None:
        globals()["SIGMA_C"] = args.sigma_c
    if args.stage == "validate":
        v = validate()
        save({"validation": v}, args.out)
        print(json.dumps(v, indent=2))
    elif args.stage == "screen":
        stage_screen(args.t0, args.t1, args.out, args.key)
    elif args.stage == "locate":
        stage_locate(args.out, args.key)
    elif args.stage == "refine":
        stage_refine(args.out, top=args.top)
    elif args.stage == "merge":
        stage_merge(args.out, args.extra, args.zeros)
    else:
        stage_report(args.out)


if __name__ == "__main__":
    main()
