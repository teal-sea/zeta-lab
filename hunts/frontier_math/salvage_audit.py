"""What survives today, re-derived from the Lean definitions alone.

Imports NOTHING from hunts/frontier_math.  Every constant recomputed.
Each check prints PASS/FAIL and the residual, so the answer to "what can
be rescued" is a measurement rather than a recollection.

    g u    = cos(sqrt2 u) on |u| <= 1/2, 0 outside      (EForm3/Defs.lean)
    A      = sqrt2 sin(1/sqrt2)
    c2 w   = int g(u) g(u+w) du
    Eng G  = (1/A^2) int_{-1}^{1} c2 w |G w|^2 dw
    D(y,s) = Qim^2 - Qre^2 = -Re ghat(y+is)^2
"""
import cmath
import math
import random

import mpmath as mp
import numpy as np

mp.mp.dps = 30
SQ2 = mp.sqrt(2)
A = SQ2 * mp.sin(1 / SQ2)
A2 = A ** 2
RESULTS = []


def rec(name, ok, detail):
    RESULTS.append((name, ok, detail))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}\n         {detail}")


def ghat(z):
    z = mp.mpmathify(z)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return mp.sinh(zp / 2) / zp + mp.sinh(zm / 2) / zm


def D(y, s):
    return -mp.re(ghat(mp.mpc(y, s)) ** 2)


def phir(v):
    return mp.re(ghat(mp.mpc(0, v)))


def Shq(y):
    return mp.re(ghat(2 * mp.mpf(y))) ** 2 - A2


def c2(w):
    w = mp.mpf(w)
    lo = max(-mp.mpf(1) / 2, -mp.mpf(1) / 2 - w)
    hi = min(mp.mpf(1) / 2, mp.mpf(1) / 2 - w)
    return mp.mpf(0) if hi <= lo else mp.quad(
        lambda u: mp.cos(SQ2 * u) * mp.cos(SQ2 * (u + w)), [lo, hi])


def Eng(G):
    return (1 / A2) * mp.quad(lambda w: c2(w) * abs(G(w)) ** 2, [-1, 0, 1])


# 1 ---------------------------------------------------------------- LEMMA A
def check_lemma_a():
    """margin_k = (4/A^2) slack_k, by quadrature on Eng, k = 1..3."""
    def margin(xs, pairs):
        n, k = len(xs), len(pairs)
        F = lambda w: mp.fsum([mp.e ** (1j * x * w) for x in xs])
        P = lambda w: mp.fsum([2 * mp.cosh(y * w) * mp.e ** (1j * t * w)
                               for y, t in pairs])
        return (Eng(lambda w: F(w) + P(w)) - mp.mpf(199) / 200 * Eng(F)
                - mp.mpf(n) / 200 - 4 * k)

    def slack(xs, pairs):
        gain = mp.fsum([Shq(y) / 2 for y, _ in pairs])
        dam = mp.fsum([D(y, x - t) for y, t in pairs for x in xs])
        rel = mp.fsum([phir(xs[a] - xs[b]) ** 2 for a in range(len(xs))
                       for b in range(a + 1, len(xs))]) / 400
        inter = mp.mpf(0)
        for p, (yp, tp) in enumerate(pairs):
            for q, (yq, tq) in enumerate(pairs):
                if p != q:
                    inter += D(yp + yq, tp - tq) + D(yp - yq, tp - tq)
        return gain - dam + rel - inter / 2

    cases = [([6.517], [(0.5, 0.0)]),
             ([6.5, 6.6, -6.5], [(0.5, 0.0), (0.5, 6.283185307)]),
             ([0.0, 1.1, 2.2, 9.9], [(0.3, -1.0), (0.45, 2.0), (0.5, 8.0)])]
    worst = max(abs(margin(x, p) - 4 / A2 * slack(x, p)) for x, p in cases)
    rec("LEMMA A / k-pair identity  margin = (4/A^2) slack",
        worst < 1e-15, f"worst residual over k=1,2,3 by quadrature: {mp.nstr(worst,3)}")


# 2 ------------------------------------------------------ arm identification
def check_arm():
    """ghat(z) = Phi2(-i z), Phi2(z) = s(z+sqrt2)+s(z-sqrt2), s=sin(u/2)/u."""
    def s(u):
        u = mp.mpmathify(u)
        return mp.mpf(1) / 2 if u == 0 else mp.sin(u / 2) / u
    phi2 = lambda z: s(z + SQ2) + s(z - SQ2)
    worst = mp.mpf(0)
    for zr in (0, 0.25, 0.5, -1):
        for zi in (0, 1, 6.517, 12.755, 30, 59.9):
            z = mp.mpc(zr, zi)
            worst = max(worst, abs(ghat(z) - phi2(-1j * z)))
    rec("BandCert and EForm3 compute one function: ghat(z) = Phi2(-i z)",
        worst < 1e-25, f"worst over 24 points on and off the axis: {mp.nstr(worst,3)}")


# 3 --------------------------------------------------------- mean damage
def check_mean_damage():
    """int D(y,s) ds = -2 pi c2(0), independent of y."""
    c20 = mp.mpf(1) / 2 + mp.sin(SQ2) / (2 * SQ2)
    target = -2 * mp.pi * c20
    ok_cf = abs(c2(0) - c20) < 1e-25
    vals = [mp.quad(lambda s: D(y, s), [-1500, -100, -30, -12, -6, 0, 6, 12,
                                        30, 100, 1500])
            for y in (mp.mpf('0.1'), mp.mpf('0.3'), mp.mpf('0.5'))]
    spread = max(vals) - min(vals)
    rec("mean damage  int D ds = -2 pi c2(0), depth-free",
        ok_cf and spread < 1e-3 and all(abs(v - target) < 5e-3 for v in vals),
        f"c2(0) closed form residual {mp.nstr(abs(c2(0)-c20),3)}; "
        f"target {mp.nstr(target,12)}; spread across y {mp.nstr(spread,3)}")


# 4 ------------------------------------------------------------ Bochner
def check_bochner():
    """-D(y,.) is positive definite (Fourier transform of c2 cosh(yw) dw)."""
    rng = random.Random(3)
    worst = 1e9
    sets = [[0.0] * 8, [0.0, 6.517, -6.517, 12.755], [6.283185307 * i for i in range(9)]]
    for _ in range(60):
        sets.append([rng.uniform(-40, 40) for _ in range(rng.randint(2, 10))])
    for us in sets:
        M = np.array([[float(-D(0.5, ui - uj)) for uj in us] for ui in us])
        worst = min(worst, float(np.linalg.eigvalsh((M + M.T) / 2).min()))
    rec("Bochner: -D(y,.) positive definite",
        worst > -1e-9, f"min eigenvalue over 63 Gram matrices: {worst:.3e}")


# 5 ------------------------------------------------- window structure + bound
def check_window_bound():
    """The k=1 closure: net damage <= 1.957e-2 < Shq/2 = 3.375e-2."""
    y = mp.mpf('0.5')
    zeros, v, step = [], mp.mpf(1), mp.mpf('0.01')
    prev = phir(v)
    while len(zeros) < 60:
        v2 = v + step
        cur = phir(v2)
        if prev * cur < 0:
            zeros.append(mp.findroot(phir, (v, v2), solver='bisect'))
        v, prev = v2, cur
    wins = []
    for z in zeros:
        f = lambda s: D(y, s)
        if f(z) <= 0:
            continue
        lo = mp.findroot(f, (z - 3, z), solver='bisect')
        hi = mp.findroot(f, (z, z + 3), solver='bisect')
        pk = mp.findroot(lambda s: mp.diff(f, s), z, solver='secant')
        wins.append((lo, hi, f(pk)))
    w_max = max(h - l for l, h, _ in wins)
    gamma = phir(w_max)
    c = gamma ** 2 / 800
    total = 2 * mp.fsum([max(n * Dk - c * n * (n - 1) for n in range(40))
                         for _, _, Dk in wins])
    sh = Shq(y) / 2
    rec("k=1 window bound: net damage < Shq/2, NO separation hypothesis",
        total < sh,
        f"{len(wins)} windows, w_max {mp.nstr(w_max,10)}, gamma "
        f"{mp.nstr(gamma,8)}; net <= {mp.nstr(total,8)} vs Shq/2 "
        f"{mp.nstr(sh,8)}  (safety {mp.nstr(sh/total,6)}x)")
    rec("window structure constants",
        abs(min(l for l, _, _ in wins) - mp.mpf('6.06531877')) < 1e-6
        and abs(w_max - mp.mpf('0.9860007')) < 1e-6,
        f"first window edge {mp.nstr(min(l for l,_,_ in wins),12)}, "
        f"w_max {mp.nstr(w_max,10)}")


# 6 ----------------------------------------------------- three-term Gram form
def check_gram():
    """slack_k = B + Cross + R/400 with B = (1/2)[G_T(2y)+G_T(0)] - k A^2."""
    K = lambda kap, s: mp.re(ghat(mp.mpc(kap, s)) ** 2)
    rng = random.Random(11)
    worst = mp.mpf(0)
    Bmin = mp.mpf('1e9')
    for _ in range(10):
        n, k = rng.randint(1, 5), rng.randint(1, 4)
        xs = [mp.mpf(rng.uniform(-30, 30)) for _ in range(n)]
        ts = [mp.mpf(rng.uniform(-30, 30)) for _ in range(k)]
        y = mp.mpf(rng.uniform(0.05, 0.5))
        gain = k * Shq(y) / 2
        dam = mp.fsum([D(y, x - t) for t in ts for x in xs])
        rel = mp.fsum([phir(xs[a] - xs[b]) ** 2 for a in range(n)
                       for b in range(a + 1, n)]) / 400
        inter = mp.fsum([D(2 * y, tp - tq) + D(0, tp - tq)
                         for i, tp in enumerate(ts)
                         for j, tq in enumerate(ts) if i != j])
        direct = gain - dam + rel - inter / 2
        B = (mp.fsum([K(2 * y, a - b) for a in ts for b in ts])
             + mp.fsum([K(0, a - b) for a in ts for b in ts])) / 2 - k * A2
        three = B - dam + rel
        worst = max(worst, abs(direct - three))
        Bmin = min(Bmin, B)
    rec("three-term Gram form  slack = B + Cross + R/400,  B >= 0",
        worst < 1e-20 and Bmin > 0,
        f"worst residual {mp.nstr(worst,3)}; min B over 10 instances "
        f"{mp.nstr(Bmin,6)}")


if __name__ == '__main__':
    print("=== what survives, re-derived from EForm3/Defs.lean alone ===\n")
    check_lemma_a()
    check_arm()
    check_mean_damage()
    check_bochner()
    check_window_bound()
    check_gram()
    n_ok = sum(1 for _, ok, _ in RESULTS if ok)
    print(f"\n=== {n_ok} of {len(RESULTS)} independent checks PASS ===")
    for name, ok, _ in RESULTS:
        if not ok:
            print(f"  FAILED: {name}")
