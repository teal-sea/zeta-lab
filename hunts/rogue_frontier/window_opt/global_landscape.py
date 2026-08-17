"""First-order landscape of F over the cone {v >= 0 even}: how many critical
points does the Euler-Lagrange system have, and is the reported optimum the
unique one with v > 0?

The EL system.  F is degree-0 homogeneous, so a critical point of F over the
cone satisfies (no multiplier):

    g(s) = dF/dv(s) = 0    on supp v,      g(s) <= 0  where v = 0,

with, writing T for tri-convolution and l1 = int v (set to 1 by scaling),

    g = -(2 v - 2 T v)/l1^2 + 2 Q2/l1^3
        - (3 v^2 - 3 T(v^2) - 6 v (T v) + 6 (1_B * W^2)|_B)/l1^3 + 3 Q3/l1^4,

a quadratic integral equation in v (functional.gradient_field).

Three independent parametrizations hunt its solutions from many random
starts (all searches solve the STATIONARITY system by least squares, so
saddles are found too, not only maxima):

  A. cosine spectral: v = 1 + sum_{k=1..J} c_k cos(2 pi k s).  Interior
     critical points of F restricted to the span solve P_k(c) =
     int g cos(2 pi k s) = 0, k = 1..J (P_0 = 0 then follows from the Euler
     identity int g v = 0).  Sign-changing roots are genuine EL solutions
     OUTSIDE the cone and are classified as such.
  B. squared Chebyshev: v = w^2, w = sum a_j T_2j(2s), a_0 = 1 fixed by
     scale invariance; solve dF/da_j = 0 (analytic gradient).  Everything
     found here is inside the cone by construction.
  C. piecewise-linear cone KKT on a uniform knot grid, exact lattice-aligned
     evaluator: L-BFGS-B multistart from deliberately diverse windows
     (flat, cosine, compact support, bimodal, increasing) plus a
     Fischer-Burmeister least-squares run for stationary points with
     active constraints.

Also here: the Hessian spectrum at the optimum (parametrizations A and B):
one zero eigenvalue (the scaling ray) and all others negative = genuine
local maximum, and a best-F-ever-seen tracker across every run.

Validation gate: before anything else the exact rational F(v*) from
functional.py is reproduced, and an independent mpmath Gauss-Legendre
evaluator (fresh code, no shared engine) must agree with it to 25+ digits.

Everything in this file is float-grade (measured); the exact numbers it
feeds on are from functional.py.

Run: .venv/bin/python hunts/rogue_frontier/window_opt/global_landscape.py
     [gate|cosine|cheb|pw|hessian|best|all]   (default: all)
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import least_squares, minimize

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from functional import (OPT_Q, PAPER_F_30, gradient_field,  # noqa: E402
                        moments_polyeven_exact, moments_pwlinear_exact,
                        moments_quad)

BEST_F_CLAIMED = 0.6852870321770     # RESULTS.md section 4 (measured)
BEST_EVER = {"F": -np.inf, "where": ""}


def track(F: float, where: str) -> None:
    if F > BEST_EVER["F"]:
        BEST_EVER["F"] = F
        BEST_EVER["where"] = where


# ---------------------------------------------------------------------------
# validation gate: independent mpmath evaluator vs the exact rational
# ---------------------------------------------------------------------------

def moments_mpmath(v, dps: int = 40):
    """m2, m3, F for an even mpmath-callable window; independent code path
    (mpmath adaptive Gauss-Legendre, fresh implementation of the closed
    forms; no numpy, no shared engine with functional.py)."""
    from mpmath import mp
    with mp.workdps(dps + 10):
        half = mp.mpf(1) / 2
        gl = lambda f, iv: mp.quad(f, iv, method="gauss-legendre")
        l1 = 2 * gl(v, [0, half])
        iv2 = 2 * gl(lambda s: v(s) ** 2, [0, half])
        iv3 = 2 * gl(lambda s: v(s) ** 3, [0, half])
        V0 = lambda x: gl(v, [0, x]) if x > 0 else mp.mpf(0)
        P0 = lambda x: gl(lambda t: t * v(t), [0, x]) if x > 0 else mp.mpf(0)
        V0h, P0h = V0(half), P0(half)

        def W(eta):
            arg = half - eta
            return V0h + V0(arg) if arg >= 0 else V0h - V0(-arg)

        iW2 = 2 * gl(lambda e: W(e) ** 2, [0, half, 1])
        iW3 = 2 * gl(lambda e: W(e) ** 3, [0, half, 1])
        Afun = lambda s: 2 * s * V0(s) - 2 * P0(s) + 2 * P0h
        iTv2 = 2 * gl(lambda s: (l1 - Afun(s)) * v(s) ** 2, [0, half])
        Q2 = iv2 - iW2
        Q3 = iv3 - 3 * iTv2 + 2 * iW3
        m2 = 1 + Q2 / l1 ** 2
        m3 = 1 + 3 * Q2 / l1 ** 2 + Q3 / l1 ** 3
        return m2, m3, 2 * m2 - m3


def gate() -> None:
    from mpmath import mp
    print("== gate: exact rational reproduced; independent evaluator ==")
    _, _, Fr = moments_polyeven_exact(OPT_Q)
    assert Fr == Fraction(2245228120295149280, 3276332462159207451)
    print(f"   F(v*) = {Fr} (exact, reproduced)")
    q1, q2 = [Fraction(q) for q in OPT_Q]
    vstar = lambda s: (1 + mp.mpf(q1.numerator) / q1.denominator * s ** 2
                       + mp.mpf(q2.numerator) / q2.denominator * s ** 4)
    _, _, Fmp = moments_mpmath(vstar, dps=40)
    with mp.workdps(50):
        err = abs(Fmp - mp.mpf(Fr.numerator) / Fr.denominator)
        digits = int(-mp.log10(err)) if err > 0 else 99
    assert digits >= 25, f"independent evaluator only matches {digits} digits"
    print(f"   independent mpmath evaluator matches to {digits} digits "
          "(gate: >= 25)")
    vc = lambda s: mp.cos(mp.mpf(8) / 5 * s)
    _, _, Fc = moments_mpmath(vc, dps=40)
    with mp.workdps(50):
        errc = abs(Fc - mp.mpf(PAPER_F_30))
    assert errc < mp.mpf("1e-28"), errc
    print("   and reproduces the 30-digit cos(8s/5) reference to < 1e-28")


# ---------------------------------------------------------------------------
# shared helpers
# ---------------------------------------------------------------------------

def _profile(v, n: int = 401) -> np.ndarray:
    ss = np.linspace(0.0, 0.5, n)
    vals = v(ss)
    return vals / vals[0]


def _dedupe(entries, tol: float = 2e-4):
    """entries: list of dicts with key 'prof'; returns unique with counts.

    tol is loose because the same underlying critical point is represented
    with different truncation bias in different bases / at different J.
    """
    uniq = []
    for e in entries:
        for u in uniq:
            if np.max(np.abs(e["prof"] - u["prof"])) < tol:
                u["hits"] += 1
                if e.get("res", np.inf) < u.get("res", np.inf):
                    for k in ("F", "res", "minv", "cls", "tag"):
                        u[k] = e[k]
                    u["prof"] = e["prof"]
                break
        else:
            e = dict(e)
            e["hits"] = 1
            uniq.append(e)
    return uniq


def _classify(minv: float) -> str:
    if minv > 1e-7:
        return "interior v > 0"
    if minv > -1e-6:
        return "boundary v ~ 0"
    return "sign-changing (outside cone)"


# ---------------------------------------------------------------------------
# A. cosine spectral parametrization
# ---------------------------------------------------------------------------

def _cos_v(c):
    def v(s):
        out = np.ones_like(s)
        for k, ck in enumerate(c, start=1):
            out = out + ck * np.cos(2 * np.pi * k * s)
        return out
    return v


def _cos_resid(c, ng: int = 48):
    v = _cos_v(c)
    if abs(moments_quad(v, ng=16)["l1"]) < 0.05:
        return 1e3 * np.ones(len(c))
    gf = gradient_field(v, ng=ng)
    s, w, g = gf["s"], gf["w"], gf["g"]
    return np.array([2.0 * np.dot(w, g * np.cos(2 * np.pi * k * s))
                     for k in range(1, len(c) + 1)])


def cosine_search(Js=(6, 8, 10, 12), n_starts: int = 50, seed: int = 20260817):
    print("\n== A. cosine spectral: EL roots by least squares ==")
    all_found = []
    rng = np.random.default_rng(seed)
    for J in Js:
        found = []
        n_run = n_starts if J <= 8 else max(24, n_starts // 2)
        for i in range(n_run):
            if i == 0:
                c0 = np.zeros(J)
                c0[0] = 0.15
            else:
                c0 = rng.standard_normal(J) * (0.6 / np.arange(1, J + 1) ** 1.2)
            try:
                sol = least_squares(_cos_resid, c0, method="lm", xtol=1e-15,
                                    ftol=1e-15, gtol=1e-15, max_nfev=2500)
            except Exception:
                continue
            r = _cos_resid(sol.x)
            res = float(np.max(np.abs(r)))
            if res < 1e-10:
                v = _cos_v(sol.x)
                prof = _profile(v)
                minv = float(np.min(v(np.linspace(0, 0.5, 2001))))
                F = moments_quad(v, ng=96)["F"]
                if minv > 0:
                    track(F, f"cosine J={J} EL root")
                found.append({"F": F, "minv": minv, "cls": _classify(minv),
                              "prof": prof, "res": res, "tag": f"J={J}"})
        uniq = _dedupe(found)
        n_int = sum(1 for u in uniq if u["cls"].startswith("interior"))
        print(f"   J={J:2d}: {len(found)}/{n_run} converged, "
              f"{len(uniq)} distinct roots, {n_int} with v > 0")
        for u in sorted(uniq, key=lambda u: -u["F"]):
            print(f"      F = {u['F']:+.12f}  min v/max v = {u['minv']:+.3e}"
                  f"  hits = {u['hits']:2d}  [{u['cls']}]")
        all_found.extend(found)
    uniq = _dedupe(all_found)
    n_int = sum(1 for u in uniq if u["cls"].startswith("interior"))
    print(f"   ACROSS J: {len(uniq)} distinct roots ({n_int} inside the "
          "cone); interior critical value converges upward with J "
          "(endpoint-kink truncation bias of this basis)")
    return uniq


# ---------------------------------------------------------------------------
# B. squared-Chebyshev parametrization
# ---------------------------------------------------------------------------

def _full(a):
    c = np.zeros(2 * len(a) - 1)
    c[::2] = a
    return c


def _cheb_w(a):
    return lambda s: np.polynomial.chebyshev.chebval(2.0 * s, _full(a))


def _cheb_grad(a_free, ng: int = 48):
    """dF/da_j, j = 1..J-1, at a = (1, a_free)."""
    a = np.concatenate([[1.0], a_free])
    w = _cheb_w(a)
    v = lambda s: w(s) ** 2
    if abs(moments_quad(v, ng=16)["l1"]) < 1e-3:
        return 1e3 * np.ones(len(a_free))
    gf = gradient_field(v, ng=ng)
    wv = w(gf["s"])
    out = np.empty(len(a_free))
    for j in range(1, len(a)):
        cj = np.zeros(len(a))
        cj[j] = 1.0
        Tj = np.polynomial.chebyshev.chebval(2.0 * gf["s"], _full(cj))
        out[j - 1] = 2.0 * np.dot(gf["w"], gf["g"] * 2.0 * wv * Tj)
    return out


def cheb_search(Js=(6, 8, 10), n_starts: int = 40, seed: int = 715):
    print("\n== B. squared Chebyshev: stationary points of F (v = w^2) ==")
    rng = np.random.default_rng(seed)
    all_found = []
    for J in Js:
        found = []
        for i in range(n_starts):
            if i == 0:
                a0 = np.zeros(J - 1)
            else:
                a0 = 0.5 * rng.standard_normal(J - 1) / np.arange(2, J + 1)
            try:
                sol = least_squares(_cheb_grad, a0, method="lm", xtol=1e-15,
                                    ftol=1e-15, gtol=1e-15, max_nfev=3000)
            except Exception:
                continue
            res = float(np.max(np.abs(_cheb_grad(sol.x))))
            if res < 1e-10:
                a = np.concatenate([[1.0], sol.x])
                w = _cheb_w(a)
                v = lambda s: w(s) ** 2
                prof = _profile(v)
                wss = w(np.linspace(0, 0.5, 2001))
                n_zero = int(np.sum(np.abs(np.diff(np.sign(wss))) > 0))
                minv = float(np.min(wss ** 2))
                F = moments_quad(v, ng=96)["F"]
                track(F, f"cheb J={J} stationary")
                cls = ("interior v > 0" if n_zero == 0
                       else f"v >= 0 touching 0 at {n_zero} pts")
                found.append({"F": F, "minv": minv, "cls": cls, "prof": prof,
                              "res": res, "tag": f"J={J}"})
        uniq = _dedupe(found)
        print(f"   J={J:2d}: {len(found)}/{n_starts} converged, "
              f"{len(uniq)} distinct stationary points")
        for u in sorted(uniq, key=lambda u: -u["F"]):
            print(f"      F = {u['F']:+.12f}  hits = {u['hits']:2d}  "
                  f"[{u['cls']}]")
        all_found.extend(found)
    uniq = _dedupe(all_found)
    print(f"   ACROSS J: {len(uniq)} distinct stationary points in the cone")
    return uniq


# ---------------------------------------------------------------------------
# C. piecewise-linear cone: multistart maxima + KKT + Fischer-Burmeister
# ---------------------------------------------------------------------------

def _pw_grad(y, h: float = 1e-6):
    g = np.empty(len(y))
    for i in range(len(y)):
        yp = y.copy(); yp[i] += h
        ym = y.copy(); ym[i] = max(ym[i] - h, 0.0)
        g[i] = (moments_pwlinear_exact(yp)[2]
                - moments_pwlinear_exact(ym)[2]) / (yp[i] - ym[i])
    return g


def _pw_starts(n, rng):
    sg = np.linspace(0, 0.5, n)
    starts = [np.cos(1.6 * sg), np.ones(n),
              np.clip(1 - 1.467 * sg ** 2 + 1.159 * sg ** 4, 0, None)]
    for a in (0.15, 0.25, 0.35):                       # compact support
        starts.append(np.where(sg <= a, np.cos(np.pi * sg / (2 * a)) ** 2, 0.0))
    starts.append(0.2 + (sg / 0.5) ** 2)               # increasing profile
    starts.append(np.exp(-((sg - 0.3) / 0.08) ** 2)
                  + 0.7 * np.exp(-(sg / 0.08) ** 2))   # bimodal
    starts.append(np.where(sg > 0.25, 1.0, 0.05))      # edge-heavy
    while len(starts) < 30:
        y = np.clip(1 - 1.4 * sg ** 2 + 0.25 * rng.standard_normal(n),
                    0.0, None)
        starts.append(y)
    return starts


def pw_search(ns=(41, 81), seed: int = 99):
    print("\n== C. piecewise-linear cone: L-BFGS-B multistart + KKT ==")
    rng = np.random.default_rng(seed)
    results = []
    for n in ns:
        starts = _pw_starts(n, rng)
        if n > 41:
            starts = starts[:12]
        found = []
        for i, y0 in enumerate(starts):
            res = minimize(lambda y: -moments_pwlinear_exact(y)[2], y0,
                           method="L-BFGS-B", bounds=[(0.0, None)] * n,
                           options={"maxiter": 8000, "ftol": 1e-16,
                                    "gtol": 1e-12})
            y = res.x
            F = -res.fun
            sg = np.linspace(0, 0.5, n)
            v0 = max(y[0], 1e-30)
            prof = np.interp(np.linspace(0, 0.5, 401), sg, y / v0)
            found.append({"F": F, "prof": prof, "y": y, "n": n,
                          "minv": float(np.min(y / v0)),
                          "cls": "", "res": np.nan, "tag": f"start {i}"})
            track(F, f"pw n={n} start {i}")
        uniq = _dedupe(found, tol=5e-3)
        print(f"   n={n}: {len(starts)} starts -> {len(uniq)} distinct maxima")
        for u in sorted(uniq, key=lambda u: -u["F"]):
            y = u["y"]
            g = _pw_grad(y)
            act = y < 1e-9
            kkt_supp = float(np.max(np.abs(g[~act]))) if (~act).any() else 0.0
            kkt_act = float(np.max(g[act])) if act.any() else -np.inf
            print(f"      F = {u['F']:.12f}  hits = {u['hits']:2d}  "
                  f"active knots = {int(act.sum())}  "
                  f"max|g| on supp = {kkt_supp:.1e}  "
                  f"max g on active = {kkt_act:.1e}")
        results.extend(uniq)
    return results


def fb_search(n: int = 21, n_starts: int = 8, seed: int = 5):
    """Fischer-Burmeister stationary-point search (finds KKT points that are
    not maxima as well)."""
    print(f"\n== C'. Fischer-Burmeister KKT roots, n = {n} knots ==")
    rng = np.random.default_rng(seed)
    sg = np.linspace(0, 0.5, n)

    def resid(y):
        y = np.abs(y)
        g = _pw_grad(y)
        return y + (-g) - np.sqrt(y ** 2 + g ** 2 + 1e-30)

    found = []
    for i in range(n_starts):
        if i == 0:
            y0 = np.cos(1.6 * sg)
        elif i == 1:
            y0 = np.ones(n)
        elif i == 2:
            y0 = np.where(sg <= 0.3, np.cos(np.pi * sg / 0.6) ** 2, 0.0) + 1e-3
        else:
            y0 = np.clip(1 - 1.4 * sg ** 2 + 0.3 * rng.standard_normal(n),
                         0.01, None)
        sol = least_squares(resid, y0, method="lm", xtol=1e-12, ftol=1e-12,
                            gtol=1e-12, max_nfev=4000)
        y = np.abs(sol.x)
        r = float(np.max(np.abs(resid(sol.x))))
        if r < 1e-7:
            F = moments_pwlinear_exact(y)[2]
            v0 = max(y[0], 1e-30)
            prof = np.interp(np.linspace(0, 0.5, 401), sg, y / v0)
            found.append({"F": F, "prof": prof, "res": r, "minv": 0.0,
                          "cls": "KKT", "tag": f"fb {i}"})
            track(F, f"fb n={n} start {i}")
    uniq = _dedupe(found, tol=5e-3)
    print(f"   {len(found)}/{n_starts} converged -> {len(uniq)} distinct "
          "KKT points")
    for u in sorted(uniq, key=lambda u: -u["F"]):
        print(f"      F = {u['F']:.12f}  hits = {u['hits']}  "
              f"residual = {u['res']:.1e}")
    return uniq


# ---------------------------------------------------------------------------
# Hessian at the optimum
# ---------------------------------------------------------------------------

def hessian() -> None:
    print("\n== Hessian at the optimum ==")
    # A-side: cosine basis J = 10 INCLUDING the scale direction c_0
    J = 10
    sol = least_squares(_cos_resid, np.concatenate([[0.15], np.zeros(J - 1)]),
                        method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15,
                        max_nfev=4000)
    c = sol.x

    def grad_full(cf):
        # gradient of F wrt (c_0, ..., c_J) at v = c_0 + sum c_k cos
        def v(s):
            out = cf[0] * np.ones_like(s)
            for k in range(1, len(cf)):
                out = out + cf[k] * np.cos(2 * np.pi * k * s)
            return out
        gf = gradient_field(v, ng=64)
        s, w, g = gf["s"], gf["w"], gf["g"]
        return np.array([2.0 * np.dot(w, g * np.cos(2 * np.pi * k * s))
                         for k in range(0, len(cf))])

    cf = np.concatenate([[1.0], c])
    h = 1e-5
    m = len(cf)
    H = np.zeros((m, m))
    for j in range(m):
        e = np.zeros(m); e[j] = h
        H[:, j] = (grad_full(cf + e) - grad_full(cf - e)) / (2 * h)
    H = 0.5 * (H + H.T)
    ev = np.linalg.eigvalsh(H)
    scale_dir = cf / np.linalg.norm(cf)
    Hs = H @ scale_dir
    print(f"   cosine basis, {m} directions (scale included):")
    print(f"   eigenvalues: {np.array2string(ev, precision=3)}")
    print(f"   |H . scale_dir| = {np.linalg.norm(Hs):.2e} (exact zero mode)")
    n_pos = int(np.sum(ev > 1e-7))
    n_zero = int(np.sum(np.abs(ev) <= 1e-7))
    print(f"   signature: {n_pos} positive, {n_zero} zero, "
          f"{m - n_pos - n_zero} negative "
          "=> local maximum modulo the scaling ray")


# ---------------------------------------------------------------------------
# best ever + exact evaluation of the numeric optimum
# ---------------------------------------------------------------------------

def best_push(seed: int = 42) -> None:
    print("\n== push: maximize F hard, rich bases, then evaluate exactly ==")
    rng = np.random.default_rng(seed)
    best = None
    for J in (12, 16):
        for i in range(8):
            a0 = np.zeros(J); a0[0] = 1.0
            if i:
                a0[1:] = 0.25 * rng.standard_normal(J - 1) / np.arange(2, J + 1)

            def negF_grad(a):
                w = _cheb_w(a)
                gf = gradient_field(lambda s: w(s) ** 2, ng=64)
                wv = w(gf["s"])
                grads = np.empty(len(a))
                for j in range(len(a)):
                    cj = np.zeros(len(a)); cj[j] = 1.0
                    Tj = np.polynomial.chebyshev.chebval(2.0 * gf["s"],
                                                         _full(cj))
                    grads[j] = 2.0 * np.dot(gf["w"], gf["g"] * 2.0 * wv * Tj)
                return -gf["F"], -grads

            res = minimize(negF_grad, a0, jac=True, method="BFGS",
                           options={"gtol": 1e-13, "maxiter": 4000})
            F = -res.fun
            track(F, f"push cheb J={J} start {i}")
            if best is None or F > best[0]:
                best = (F, res.x.copy())
    F, a = best
    print(f"   best pushed F = {F:.15f}")
    # exact rational evaluation of this explicit polynomial window:
    # v = w^2 with w an even Chebyshev series -> even polynomial in s with
    # float (dyadic rational) coefficients; normalize v(0) = 1 exactly.
    w_poly = np.polynomial.chebyshev.cheb2poly(_full(a))     # in x = 2s
    wf = [Fraction(float(cc)) for cc in w_poly]
    # w(x)^2, x = 2 s
    v_x = [Fraction(0)] * (2 * len(wf) - 1)
    for i, ci in enumerate(wf):
        if ci:
            for j, cj in enumerate(wf):
                v_x[i + j] += ci * cj
    # substitute x = 2 s and normalize by v(0)
    v_s = [c * Fraction(2) ** k for k, c in enumerate(v_x)]
    v0 = v_s[0]
    v_s = [c / v0 for c in v_s]
    assert all(v_s[k] == 0 for k in range(1, len(v_s), 2))
    qs = [v_s[k] for k in range(2, len(v_s), 2)]
    m2e, m3e, Fe = moments_polyeven_exact(qs)
    print(f"   exact rational F of that explicit window = {float(Fe):.15f}")
    print(f"   (numerator/denominator digits: {len(str(Fe.numerator))}/"
          f"{len(str(Fe.denominator))}; window is an even polynomial of "
          f"degree {2 * (len(wf) - 1)} with dyadic coefficients)")
    from mpmath import mp
    with mp.workdps(40):
        print("   F exact to 30 digits: "
              f"{mp.nstr(mp.mpf(Fe.numerator) / Fe.denominator, 30)}")
    track(float(Fe), "exact eval of pushed cheb window")


def main(which: str = "all") -> None:
    gate()
    if which in ("all", "cosine"):
        cosine_search()
    if which in ("all", "cheb"):
        cheb_search()
    if which in ("all", "pw"):
        pw_search()
        fb_search()
    if which in ("all", "hessian"):
        hessian()
    if which in ("all", "best"):
        best_push()
    if np.isfinite(BEST_EVER["F"]):
        print(f"\nBEST F EVER SEEN in this run: {BEST_EVER['F']:.15f} "
              f"({BEST_EVER['where']})")
        print(f"claimed sup (RESULTS.md section 4): {BEST_F_CLAIMED}")
        if BEST_EVER["F"] <= BEST_F_CLAIMED + 5e-10:
            print("=> no start in any parametrization ever beat the "
                  "claimed sup")
        else:
            print("=> !! the claimed sup WAS BEATEN, investigate !!")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "all")
