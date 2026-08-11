"""The Jensen clock: finite Jensen degree as a de Bruijn-Newman heat time.

Run from the repo root:

    .venv/bin/python hunts/jensen_clock/probe.py validate
    .venv/bin/python hunts/jensen_clock/probe.py trajectory
    .venv/bin/python hunts/jensen_clock/probe.py dstar
    .venv/bin/python hunts/jensen_clock/probe.py pair2
    .venv/bin/python hunts/jensen_clock/probe.py planted
    .venv/bin/python hunts/jensen_clock/probe.py additivity
    .venv/bin/python hunts/jensen_clock/probe.py precision
    .venv/bin/python hunts/jensen_clock/probe.py figure

Writes ``results.json`` (each stage updates its own key) and
``jensen_clock.png`` next to this file.  Pre-registered predictions in
``MISSION.md``.

The object under test.  For an even entire function with weight Phi,

    E(x) = sum_n gamma(n) x^n / n!,   gamma(n) = n!/(2n)! * M_{2n},
    M_{2m}(t) = int_0^inf u^{2m} e^{t u^2} Phi(u) du,

so that E(z^2) = int Phi(u) cosh(zu) du is the completed function read off the
critical line, and its zeros in the x-plane sit at x = (rho - 1/2)^2: on the
negative real axis when rho is on the critical line, off it otherwise.  The
degree-d Jensen polynomial J^{d,0}(y) = sum_j C(d,j) gamma(j) y^j satisfies
exactly

    F_d(x) := J^{d,0}(x/d) = sum_j gamma(j)/j! * prod_{i<j}(1 - i/d) * x^j,

so J^{d,0} is non-hyperbolic iff F_d has a non-real root, and the binomial
damping prod(1 - i/d) ~ e^{-j^2/2d} is a Gaussian coefficient multiplier --
de Bruijn's smoothing, applied by the *degree itself*.  Read at the cosh-series
saddle j ~ z*u/2 it matches the flow multiplier e^{t u^2} with

    t_eff(d) = |x0| / (8 d)

at the pair's image x0.  Everything below measures that dictionary against
hunt #4's PDE flow measurements (``hunts/flow_repair/results.json``).

Vocabulary note (the probe discipline, ``tests/test_hunt_probe_discipline.py``):
everything in this hunt is the accurate regime -- mpmath floats with measured
cross-route defects.  The strongest words used are *measured* and *observed*.
The truncated-series detector reports a validity margin (series tail bound vs
minimum modulus on its contour) instead of assuming the truncation away.
"""

from __future__ import annotations

import argparse
import json
import os
import time

from mpmath import mp

from zeta.epstein import kappa
from zeta.heatflow import Phi as phi_zeta
from zeta.li import xi_taylor_coefficients

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results.json")
FLOW_REPAIR = os.path.join(HERE, os.pardir, "flow_repair", "results.json")

# Default instrument settings for pair 1 (cancellation there is ~85 digits,
# measured by stage validate; dps 130 leaves a ~45-digit working floor).
DPS = 130
U_DEFAULT = "4.2"
SEGS_DEFAULT = 16
GLDEG_DEFAULT = 7
JMAX_DEFAULT = 320


# ---------------------------------------------------------------------------
# weights and moment tables
# ---------------------------------------------------------------------------


def omega_dh(x, kap):
    """omega(x) = sum_{n>=1} n a_n exp(-pi n^2 x/5), a_n period 5:
    (1, kappa, -kappa, -1, 0).  Same construction as hunts/flow_repair."""
    a_pat = (mp.mpf(1), kap, -kap, mp.mpf(-1), mp.mpf(0))
    total = mp.mpf(0)
    floor = mp.mpf(10) ** (-(mp.dps + 8))
    n, small = 1, 0
    while small < 3:
        e = mp.exp(-mp.pi * n * n * x / 5)
        if n * e < floor:
            small += 1
        else:
            small = 0
            a = a_pat[(n - 1) % 5]
            if a != 0:
                total += n * a * e
        n += 1
    return total


def make_nodes(weight, U, segs, gldeg, dps):
    """Composite Gauss-Legendre nodes on [0, U] with the weight pre-evaluated:
    returns [(u, w * weight(u))].  The weight is paid once; every moment and
    every flow time reuses the same table."""
    from mpmath.calculus.quadrature import GaussLegendre

    with mp.workdps(dps):
        rule = GaussLegendre(mp).calc_nodes(gldeg, mp.prec)
        U = mp.mpf(U)
        out = []
        for k in range(segs):
            a, b = U * k / segs, U * (k + 1) / segs
            half, mid = (b - a) / 2, (a + b) / 2
            for x, w in rule:
                u = mid + half * x
                out.append((u, w * half * weight(u)))
    return out


def dh_nodes(dps, U=U_DEFAULT, segs=SEGS_DEFAULT, gldeg=GLDEG_DEFAULT):
    kap = kappa(dps)
    with mp.workdps(dps):
        return make_nodes(
            lambda u: 4 * mp.exp(mp.mpf(3) / 2 * u) * omega_dh(mp.exp(2 * u), kap),
            U, segs, gldeg, dps,
        )


def zeta_nodes(dps, U=U_DEFAULT, segs=SEGS_DEFAULT, gldeg=GLDEG_DEFAULT):
    with mp.workdps(dps):
        return make_nodes(lambda u: phi_zeta(u, dps=dps), U, segs, gldeg, dps)


def gammas_from_nodes(nodes, jmax, dps, t=0):
    """gamma(n) = n!/(2n)! * M_{2n}(t) for n = 0..jmax."""
    with mp.workdps(dps):
        t = mp.mpf(t)
        if t == 0:
            wts = [(u, wphi) for u, wphi in nodes]
        else:
            wts = [(u, wphi * mp.exp(t * u * u)) for u, wphi in nodes]
        out = []
        for n in range(jmax + 1):
            m2n = mp.fsum(w * (u ** (2 * n)) for u, w in wts)
            out.append(mp.factorial(n) / mp.factorial(2 * n) * m2n)
    return out


# ---------------------------------------------------------------------------
# the damped series F_d and its root machinery
# ---------------------------------------------------------------------------


def damped_coeffs(G, d, dps):
    """c_j = gamma(j)/j! * prod_{i<j}(1 - i/d);  d=None means no damping.
    d may be any positive real -- the product is defined for real d and the
    landing degree is found as a real root, then bracketed by integers."""
    with mp.workdps(dps):
        out, p = [], mp.mpf(1)
        d = None if d is None else mp.mpf(d)
        for j in range(len(G)):
            out.append(G[j] / mp.factorial(j) * p)
            if d is not None:
                p *= 1 - j / d
                if p <= 0:
                    out.extend([mp.mpf(0)] * (len(G) - j - 1))
                    break
    return out


def F_eval(c, x, deriv=False):
    """Horner evaluation of F(x) = sum c_j x^j (and F' if asked)."""
    f, fp = mp.mpf(0), mp.mpf(0)
    for cj in reversed(c):
        if deriv:
            fp = fp * x + f
        f = f * x + cj
    return (f, fp) if deriv else f


def newton_root(c, x, dps, tol_exp=-40, iters=80):
    with mp.workdps(dps):
        x = mp.mpc(x)
        step = mp.mpf(1)
        for _ in range(iters):
            f, fp = F_eval(c, x, deriv=True)
            step = f / fp
            x = x - step
            if abs(step) < mp.mpf(10) ** tol_exp:
                break
    return x, abs(step)


def contour_moments(c, center, radius, dps, npts=96, ks=(0, 1, 2)):
    """q_k = (1/2 pi i) oint (x - center)^k F'/F dx on a circle, trapezoid on
    equispaced angles (spectrally accurate for a periodic analytic integrand).
    Also returns min |F| on the contour, for the truncation-margin check."""
    with mp.workdps(dps):
        center, radius = mp.mpc(center), mp.mpf(radius)
        sums = {k: mp.mpc(0) for k in ks}
        minmod = None
        for i in range(npts):
            th = 2 * mp.pi * i / npts
            e = mp.expjpi(2 * mp.mpf(i) / npts)
            x = center + radius * e
            f, fp = F_eval(c, x, deriv=True)
            a = abs(f)
            minmod = a if minmod is None else min(minmod, a)
            base = fp / f * radius * e  # dx/(2 pi i) absorbed by the mean below
            for k in ks:
                sums[k] += ((x - center) ** k) * base
        q = {k: sums[k] / npts for k in ks}
    return q, minmod


def tail_bound(G, x_abs, dps):
    """Numeric bound on the series tail beyond the gamma table at |x|: the
    damping factors are at most 1, so the undamped tail bounds every F_d.
    The last two tabulated terms give the geometric ratio for the extension;
    the terms are factorially decaying there, so the ratio is conservative."""
    with mp.workdps(dps):
        x_abs = mp.mpf(x_abs)
        j = len(G) - 1
        last = abs(G[j]) * x_abs ** j / mp.factorial(j)
        prev = abs(G[j - 1]) * x_abs ** (j - 1) / mp.factorial(j - 1)
        r = last / prev if prev > 0 else mp.mpf("0.5")
        if r >= 1:
            return mp.inf
        return last * r / (1 - r)


def pair_delta(c, center, radius, dps, npts=96):
    """(x1 - x2)^2 for the two zeros of F inside the contour, via moments that
    stay analytic through the collision (hunt #4's method, in the x-plane):
    Delta = 2 q2 - q1^2, count check N = q0 = 2."""
    q, minmod = contour_moments(c, center, radius, dps, npts=npts)
    n_inside = mp.re(q[0])
    delta = 2 * q[2] - q[1] ** 2
    centroid = center + q[1] / 2
    return {
        "count": n_inside,
        "delta": delta,
        "centroid": centroid,
        "min_mod_on_contour": minmod,
    }


# ---------------------------------------------------------------------------
# flow-repair inputs (the PDE-side measurements this hunt tests against)
# ---------------------------------------------------------------------------


def flow_repair_pair1():
    with open(FLOW_REPAIR, encoding="utf-8") as fh:
        d = json.load(fh)
    pol = d["pair1"]["polished"]
    tstar = d["precision"]["runs"][0]["tstar"]
    return {
        "beta": pol["beta"],
        "gamma": pol["gamma"],
        "y0": pol["y0"],
        "tstar": tstar,
        "tstar_naive": pol["tstar_naive"],
        "sweep": d["pair1"]["sweep"],
        "slope0": d["pair1"]["slope0_measured"],
    }


def flow_repair_pair2():
    with open(FLOW_REPAIR, encoding="utf-8") as fh:
        d = json.load(fh)
    p2 = d["survey_2_3"]["pair2"]
    pol = p2["polished"]
    lo, hi = p2["bracket"]
    return {
        "beta": pol["beta"],
        "gamma": pol["gamma"],
        "y0": pol["y0"],
        "tstar": (lo + hi) / 2,
        "tstar_naive": pol["tstar_naive"],
    }


def pair_x0(pair, dps):
    """x0 = (y0 + i gamma)^2 for a polished pair record."""
    with mp.workdps(dps):
        z = mp.mpc(mp.mpf(pair["y0"]), mp.mpf(pair["gamma"]))
        return z * z


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
        json.dump(data, fh, indent=1, sort_keys=True, default=str)
    print(f"[{stage}] written to {os.path.relpath(RESULTS)}")


def nstr(x, n=17):
    return mp.nstr(x, n)


# ---------------------------------------------------------------------------
# stages
# ---------------------------------------------------------------------------


def stage_validate():
    t0 = time.time()
    out = {"dps": DPS}

    # (a) zeta control against the packaged, twice-derived gamma table:
    #     gamma_li(n) = 64 * 4^n * n!/(2n)! * M_2n  because H_0(z) = Xi(z/2)/8.
    nz = zeta_nodes(DPS)
    Gz = gammas_from_nodes(nz, 40, DPS)
    ref = xi_taylor_coefficients(40, dps=50)
    with mp.workdps(DPS):
        rel = []
        for n in range(41):
            mine = 64 * mp.power(4, n) * Gz[n]
            rel.append(abs(mine - ref[n]) / abs(ref[n]))
        out["zeta_gamma_max_rel_defect_vs_li"] = nstr(max(rel), 3)

    # (b) DH: the undamped root from the pair-1 seed against hunt #4's polish.
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, DPS)
    nd = dh_nodes(DPS)
    G = gammas_from_nodes(nd, JMAX_DEFAULT, DPS)
    c = damped_coeffs(G, None, DPS)
    with mp.workdps(DPS):
        root, resid = newton_root(c, x0, DPS, tol_exp=-(DPS - 40))
        out["x0_from_flow_repair"] = nstr(x0, 40)
        out["undamped_root"] = nstr(root, 40)
        out["undamped_root_vs_x0_rel"] = nstr(abs(root - x0) / abs(x0), 3)
        out["newton_last_step"] = nstr(resid, 3)
        # cancellation actually present at the pair: largest series term vs |E|
        biggest = max(abs(cj) * abs(x0) ** j for j, cj in enumerate(c))
        e_near = abs(F_eval(c, x0 + 300))
        out["largest_term_log10"] = nstr(mp.log10(biggest), 6)
        out["E_at_offset_log10"] = nstr(mp.log10(e_near), 6)
        out["cancellation_digits"] = nstr(mp.log10(biggest / e_near), 4)

    # (c) independent quadrature route: different U, segmentation and degree.
    nd2 = dh_nodes(DPS, U="3.9", segs=13, gldeg=8)
    G2 = gammas_from_nodes(nd2, JMAX_DEFAULT, DPS)
    with mp.workdps(DPS):
        rel = max(
            abs(G[n] - G2[n]) / abs(G[n]) for n in range(JMAX_DEFAULT + 1) if G[n] != 0
        )
        out["gamma_two_quadratures_max_rel_defect"] = nstr(rel, 3)

    out["seconds"] = round(time.time() - t0, 2)
    save("validate", out)


def _trajectory_ladder(G, x_seed, ds, dps):
    rows, x = [], x_seed
    for d in ds:
        c = damped_coeffs(G, d, dps)
        x, resid = newton_root(c, x, dps, tol_exp=-(dps - 40))
        rows.append({"d": d, "root_re": nstr(mp.re(x)), "root_im": nstr(mp.im(x)),
                     "newton_step": nstr(resid, 3)})
    return rows, x


def stage_trajectory():
    t0 = time.time()
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, DPS)
    nd = dh_nodes(DPS)
    G = gammas_from_nodes(nd, JMAX_DEFAULT, DPS)

    with mp.workdps(DPS):
        ds = [10 ** 9, 3 * 10 ** 8, 10 ** 8, 3 * 10 ** 7, 10 ** 7, 3 * 10 ** 6,
              10 ** 6, 3 * 10 ** 5, 10 ** 5, 60000, 40000, 30000, 26000, 24000,
              23000, 22000, 21500]
        rows, _ = _trajectory_ladder(G, x0, ds, DPS)

        # drift constant: C(d) = d * (Im x0 - Im x(d)); Richardson-extrapolate
        # the three largest d (C(d) = C + a/d + ...).
        im0 = mp.im(x0)
        Cs = [(d, d * (im0 - mp.mpf(r["root_im"]))) for d, r in zip(ds, rows)]
        c1, c2 = Cs[0][1], Cs[1][1]
        d1, d2 = mp.mpf(Cs[0][0]), mp.mpf(Cs[1][0])
        C_extrap = (c1 * d1 - c2 * d2) / (d1 - d2)  # eliminate the a/d term

        # prediction from hunt #4's PDE-side numbers: Im X = 2 y gamma, so
        # dImX/dt = 2 (gamma dy/dt + y dgamma/dt) with dy/dt = -slope0/(8 y0)
        # and dgamma/dt read from the first two sweep rows.
        y0 = mp.mpf(pair["y0"])
        gam = mp.mpf(pair["gamma"])
        dy_dt = -mp.mpf(pair["slope0"]) / (8 * y0)
        s0, s1 = pair["sweep"][0], pair["sweep"][1]
        dgam_dt = (mp.mpf(s1["x"]) - mp.mpf(s0["x"])) / (mp.mpf(s1["t"]) - mp.mpf(s0["t"]))
        dImX_dt = 2 * (gam * dy_dt + y0 * dgam_dt)
        C_pred = abs(dImX_dt) * abs(x0) / 8

        # pointwise dictionary defect: PDE sweep gives Im X_pde(t) = x*sqrt(-Delta)
        # (Delta = -4 y^2 in the z-plane, Im X = 2 y gamma with gamma = sweep x).
        pde = []
        for row in pair["sweep"]:
            dl = mp.mpf(row["Delta"])
            if dl >= 0:
                break
            pde.append((mp.mpf(row["t"]), mp.mpf(row["x"]) * mp.sqrt(-dl)))
        # Jensen rows mapped to t_eff, compared against linear interpolation of
        # the PDE curve.
        defects = []
        for d, r in zip(ds, rows):
            t_eff = abs(x0) / (8 * mp.mpf(d))
            imx = mp.mpf(r["root_im"])
            for (ta, va), (tb, vb) in zip(pde, pde[1:]):
                if ta <= t_eff <= tb:
                    v = va + (vb - va) * (t_eff - ta) / (tb - ta)
                    defects.append(
                        {"d": d, "t_eff": nstr(t_eff, 8), "im_jensen": nstr(imx, 8),
                         "im_pde": nstr(v, 8), "rel_defect": nstr(abs(imx - v) / v, 3)}
                    )
                    break

        out = {
            "dps": DPS,
            "ladder": rows,
            "drift_constant_measured": nstr(C_extrap, 8),
            "drift_constant_pred_from_flow_repair": nstr(C_pred, 8),
            "drift_rel_defect": nstr(abs(C_extrap - C_pred) / C_pred, 3),
            "dictionary_pointwise": defects,
            "seconds": round(time.time() - t0, 2),
        }
    save("trajectory", out)


def _find_dstar(G, x0, d_hi, d_lo, dps, radius=70, npts=96):
    """Landing degree: root of Delta(d) = 0 with Delta = (x1-x2)^2 from
    collision-safe contour moments around the pair, secant in 1/d.

    Delta < 0 while the pair is complex (conjugate pair: (2i Im x)^2), > 0
    once it has landed and split along the real axis."""
    with mp.workdps(dps):
        center = mp.re(x0)  # the pair straddles the real axis near Re x0

        def delta_at(d):
            c = damped_coeffs(G, d, dps)
            rec = pair_delta(c, center, radius, dps, npts=npts)
            n = rec["count"]
            if abs(n - 2) > mp.mpf("1e-6"):
                raise RuntimeError(f"contour count {nstr(n, 5)} != 2 at d={d}")
            return mp.re(rec["delta"]), rec

        a, b = mp.mpf(1) / d_hi, mp.mpf(1) / d_lo  # work in s = 1/d
        fa, _ = delta_at(1 / a)
        fb, _ = delta_at(1 / b)
        if fa >= 0 or fb <= 0:
            raise RuntimeError(f"bracket does not straddle: {nstr(fa,5)}, {nstr(fb,5)}")
        for _ in range(80):
            s = (a + b) / 2
            fm, rec = delta_at(1 / s)
            if fm < 0:
                a, fa = s, fm
            else:
                b, fb = s, fm
            if (b - a) / a < mp.mpf(10) ** (-12):
                break
        dstar = 2 / (a + b)
    return dstar, rec


def stage_dstar():
    t0 = time.time()
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, DPS)
    nd = dh_nodes(DPS)
    G = gammas_from_nodes(nd, JMAX_DEFAULT, DPS)
    with mp.workdps(DPS):
        dstar, rec = _find_dstar(G, x0, d_hi=30000, d_lo=20000, dps=DPS)
        t_j = abs(x0) / (8 * dstar)
        tstar = mp.mpf(pair["tstar"])
        tnaive = mp.mpf(pair["tstar_naive"])
        # truncation margin at the final contour
        tb = tail_bound(G, abs(x0) + 70, DPS)
        out = {
            "dps": DPS,
            "dstar": nstr(dstar, 12),
            "t_jensen": nstr(t_j, 12),
            "t_pde": nstr(tstar, 12),
            "t_naive_isolated": nstr(tnaive, 12),
            "rel_defect_vs_pde": nstr(abs(t_j - tstar) / tstar, 4),
            "rel_defect_vs_naive": nstr(abs(t_j - tnaive) / tnaive, 4),
            "contour_count": nstr(rec["count"], 8),
            "contour_min_mod_log10": nstr(mp.log10(rec["min_mod_on_contour"]), 5),
            "tail_bound_log10": nstr(mp.log10(tb), 5),
            "seconds": round(time.time() - t0, 2),
        }
    save("dstar", out)


def stage_pair2():
    t0 = time.time()
    dps, jmax = 180, 400
    pair = flow_repair_pair2()
    x0 = pair_x0(pair, dps)
    nd = dh_nodes(dps, U="4.2", segs=18, gldeg=7)
    G = gammas_from_nodes(nd, jmax, dps)
    with mp.workdps(dps):
        # approach along a short ladder so Newton stays on the pair's branch
        ds = [3 * 10 ** 6, 10 ** 6, 5 * 10 ** 5, 3 * 10 ** 5, 2 * 10 ** 5]
        c = damped_coeffs(G, None, dps)
        root, resid = newton_root(c, x0, dps, tol_exp=-(dps - 40))
        rows, x_last = _trajectory_ladder(G, root, ds, dps)
        dstar, rec = _find_dstar(G, x0, d_hi=200000, d_lo=100000, dps=dps, radius=90)
        t_j = abs(x0) / (8 * dstar)
        tstar = mp.mpf(pair["tstar"])
        out = {
            "dps": dps,
            "jmax": jmax,
            "undamped_root_vs_x0_rel": nstr(abs(root - x0) / abs(x0), 3),
            "ladder": rows,
            "dstar": nstr(dstar, 12),
            "t_jensen": nstr(t_j, 12),
            "t_pde": nstr(tstar, 12),
            "t_naive_isolated": nstr(mp.mpf(pair["tstar_naive"]), 12),
            "rel_defect_vs_pde": nstr(abs(t_j - tstar) / tstar, 4),
            "contour_count": nstr(rec["count"], 8),
            "contour_min_mod_log10": nstr(mp.log10(rec["min_mod_on_contour"]), 5),
            "seconds": round(time.time() - t0, 2),
        }
    save("pair2", out)


def stage_planted():
    t0 = time.time()
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, DPS)
    nz = zeta_nodes(DPS)
    Gz = gammas_from_nodes(nz, JMAX_DEFAULT, DPS)
    with mp.workdps(DPS):
        # (a) specificity: zeta with no plant.  Newton from the DH pair seed
        # must fall onto the real axis, and a winding box that would contain
        # the DH pair must count zero.
        cz = damped_coeffs(Gz, None, DPS)
        root, _ = newton_root(cz, x0, DPS, tol_exp=-(DPS - 40))
        q, minmod = contour_moments(cz, mp.mpc(mp.re(x0), mp.im(x0)), 40, DPS)
        specificity = {
            "newton_abs_im_over_abs": nstr(abs(mp.im(root)) / abs(root), 3),
            "winding_count_at_pair_box": nstr(mp.re(q[0]), 5),
            "min_mod_on_box": nstr(mp.log10(minmod), 5),
        }

        # (b) the lesion: multiply E_zeta by (x - x0)(x - conj x0), i.e.
        # x^2 - 2 Re(x0) x + |x0|^2, an exact three-term recurrence on gamma:
        a2, b2 = 2 * mp.re(x0), abs(x0) ** 2
        Gp = []
        for n in range(len(Gz)):
            v = b2 * Gz[n]
            if n >= 1:
                v -= a2 * n * Gz[n - 1]
            if n >= 2:
                v += n * (n - 1) * Gz[n - 2]
            Gp.append(v)
        cp = damped_coeffs(Gp, None, DPS)
        rootp, resid = newton_root(cp, x0, DPS, tol_exp=-(DPS - 40))
        planted_seed_defect = abs(rootp - x0) / abs(x0)

        ds = [10 ** 7, 10 ** 6, 10 ** 5, 40000, 30000, 25000, 22000, 20500]
        rows, _ = _trajectory_ladder(Gp, rootp, ds, DPS)
        dstar, rec = _find_dstar(Gp, x0, d_hi=25000, d_lo=17500, dps=DPS, radius=70)
        t_j = abs(x0) / (8 * dstar)
        # isolated-pair reference: t = y0^2/2 where y0 is the pair's distance
        # from the real axis in the real-rooted z-plane (x = -z^2 there), i.e.
        # y0 = |Im sqrt(-x0)| = Re sqrt(x0)
        y0z = mp.re(mp.sqrt(x0))
        t_iso = y0z ** 2 / 2
        t_ode = nbody_landing_planted(x0)
        out = {
            "dps": DPS,
            "specificity_no_plant": specificity,
            "planted_root_vs_x0_rel": nstr(planted_seed_defect, 3),
            "ladder": rows,
            "dstar_planted": nstr(dstar, 12),
            "t_jensen_planted": nstr(t_j, 12),
            "t_isolated_pair": nstr(t_iso, 12),
            "t_pde_dh_pair1": nstr(mp.mpf(pair["tstar"]), 12),
            "t_nbody_null": nstr(t_ode, 8),
            "rel_defect_vs_nbody_null": nstr(abs(t_j - mp.mpf(t_ode)) / mp.mpf(t_ode), 4),
            "rel_defect_vs_isolated": nstr(abs(t_j - t_iso) / t_iso, 4),
            "rel_separation_from_dh_clock": nstr(
                abs(t_j - mp.mpf(pair["tstar"])) / mp.mpf(pair["tstar"]), 4
            ),
            "contour_count": nstr(rec["count"], 8),
            "seconds": round(time.time() - t0, 2),
        }
    save("planted", out)



def nbody_landing_planted(x0, n_ordinates=80, dt=2e-4):
    """Arithmetic-free null for the planted configuration (hunt #4's method):
    integrate dz/dt = 2 sum 1/(z - z') for the union of the planted pair and
    the zeros of E_zeta in the real-rooted w-plane (x = -w^2, so line zeros
    sit at w = +-2 gamma_k), and return the pair's landing time.  The pair is
    tracked in the collision-safe variables (x_c, Q = -y^2):

        dQ/dt = 2 - 4 Q sum_a 1/((x_c - a)^2 - Q),
        dx_c/dt = sum_a 2 (x_c - a)/((x_c - a)^2 - Q),

    exact for the N-body dynamics and analytic through Q = 0.  External real
    zeros evolve under the same dynamics; mirrors at -a and the mirrored pair
    are included explicitly.  Plain float arithmetic: the target here is the
    ~1% level, and hunt #4 measured the same ODE against the PDE at 0.04%."""
    w = mp.sqrt(-x0)          # pair at (Re w, -+ Im w), Im w < 0
    x_c, y0 = float(mp.re(w)), abs(float(mp.im(w)))
    Q = -y0 * y0
    ext = [2 * float(mp.im(mp.zetazero(k))) for k in range(1, n_ordinates + 1)]

    def derivs(x_c, Q, ext):
        # pair equations: sum over all externals and both mirror images,
        # plus the mirrored pair (two complex members, conjugate sum -> real)
        sum_inv, sum_drift = 0.0, 0.0
        for a in ext:
            for aa in (a, -a):
                den = (x_c - aa) ** 2 - Q
                sum_inv += 1.0 / den
                sum_drift += 2.0 * (x_c - aa) / den
        y = (-Q) ** 0.5 if Q < 0 else 0.0
        for sgn in (1.0, -1.0):
            zm = complex(-x_c, sgn * y)
            den = (x_c - zm) ** 2 - Q
            sum_inv += (1.0 / den).real
            sum_drift += (2.0 * (x_c - zm.real) / den).real
        dQ = 2.0 - 4.0 * Q * sum_inv
        dx = sum_drift
        # external equations
        dext = []
        for i, a in enumerate(ext):
            si = 0.0
            for j, b in enumerate(ext):
                if j != i:
                    si += 1.0 / (a - b)
                si += 1.0 / (a + b)
            for xc_s in (x_c, -x_c):
                si += 2.0 * (a - xc_s) / ((a - xc_s) ** 2 - Q)
            dext.append(2.0 * si)
        return dx, dQ, dext

    t = 0.0
    state = (x_c, Q, ext)
    while state[1] < 0.0 and t < 0.2:
        x_c, Q, ext = state

        def step(sx, sQ, se, h, dx, dQ, de):
            return (sx + h * dx, sQ + h * dQ, [a + h * d for a, d in zip(se, de)])

        k1 = derivs(x_c, Q, ext)
        s2 = step(x_c, Q, ext, dt / 2, *k1)
        k2 = derivs(*s2)
        s3 = step(x_c, Q, ext, dt / 2, *k2)
        k3 = derivs(*s3)
        s4 = step(x_c, Q, ext, dt, *k3)
        k4 = derivs(*s4)
        Q_prev, t_prev = Q, t
        state = (
            x_c + dt / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]),
            Q + dt / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]),
            [a + dt / 6 * (d1 + 2 * d2 + 2 * d3 + d4)
             for a, d1, d2, d3, d4 in zip(ext, k1[2], k2[2], k3[2], k4[2])],
        )
        t += dt
    # linear interpolation of the Q = 0 crossing inside the last step
    Q_new = state[1]
    if Q_new >= 0.0 and Q_new != Q_prev:
        return t_prev + dt * (-Q_prev) / (Q_new - Q_prev)
    return t


def stage_additivity():
    t0 = time.time()
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, DPS)
    nd = dh_nodes(DPS)
    with mp.workdps(DPS):
        tstar = mp.mpf(pair["tstar"])
        rows = []
        for d in (60000, 120000):
            t_eff = abs(x0) / (8 * mp.mpf(d))
            # land the flow at fixed degree: root of Delta(t) = 0 in t
            center = mp.re(x0)

            def delta_at(t):
                G = gammas_from_nodes(nd, JMAX_DEFAULT, DPS, t=t)
                c = damped_coeffs(G, d, DPS)
                rec = pair_delta(c, center, 70, DPS)
                if abs(rec["count"] - 2) > mp.mpf("1e-6"):
                    raise RuntimeError(f"count {nstr(rec['count'],5)} != 2")
                return mp.re(rec["delta"])

            a, b = tstar - t_eff - mp.mpf("0.004"), tstar - t_eff + mp.mpf("0.004")
            fa, fb = delta_at(a), delta_at(b)
            if fa >= 0 or fb <= 0:
                raise RuntimeError(
                    f"additivity bracket failed at d={d}: {nstr(fa,5)}, {nstr(fb,5)}"
                )
            for _ in range(40):
                mid = (a + b) / 2
                if delta_at(mid) < 0:
                    a = mid
                else:
                    b = mid
                if b - a < mp.mpf(10) ** (-9):
                    break
            t_land = (a + b) / 2
            total = t_land + t_eff
            rows.append({
                "d": d,
                "t_eff": nstr(t_eff, 10),
                "t_land": nstr(t_land, 10),
                "sum": nstr(total, 10),
                "t_pde": nstr(tstar, 10),
                "rel_defect": nstr(abs(total - tstar) / tstar, 4),
            })
        out = {"dps": DPS, "rows": rows, "seconds": round(time.time() - t0, 2)}
    save("additivity", out)


def stage_precision():
    t0 = time.time()
    pair = flow_repair_pair1()
    runs = []
    for dps, jmax, U, segs, gldeg in (
        (110, 280, "4.2", 16, 7),
        (130, 320, "4.2", 16, 7),
        (160, 360, "4.5", 20, 7),
        (130, 320, "3.9", 13, 8),
    ):
        x0 = pair_x0(pair, dps)
        nd = dh_nodes(dps, U=U, segs=segs, gldeg=gldeg)
        G = gammas_from_nodes(nd, jmax, dps)
        with mp.workdps(dps):
            c = damped_coeffs(G, 30000, dps)
            root, _ = newton_root(c, x0, dps, tol_exp=-(dps - 40))
            dstar, _ = _find_dstar(G, x0, d_hi=30000, d_lo=20000, dps=dps)
            runs.append({
                "dps": dps, "jmax": jmax, "U": U, "segs": segs, "gldeg": gldeg,
                "root_im_at_d30000": nstr(mp.im(root), 20),
                "dstar": nstr(dstar, 14),
            })
    base = mp.mpf(runs[1]["dstar"])
    spread = max(abs(mp.mpf(r["dstar"]) - base) / base for r in runs)
    save("precision", {
        "runs": runs,
        "dstar_max_rel_spread": nstr(spread, 3),
        "seconds": round(time.time() - t0, 2),
    })


def stage_figure():
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    with open(RESULTS, encoding="utf-8") as fh:
        data = json.load(fh)
    pair = flow_repair_pair1()
    x0 = pair_x0(pair, 40)
    absx0 = float(abs(x0))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.2))

    # left: the dictionary -- PDE trajectory vs Jensen ladder at t_eff
    pde_t, pde_im = [], []
    for row in pair["sweep"]:
        if row["Delta"] >= 0:
            break
        pde_t.append(row["t"])
        pde_im.append(row["x"] * (-row["Delta"]) ** 0.5)
    ax1.plot(pde_t, pde_im, "-", color="#2166ac", lw=2,
             label="PDE flow $H_t$ (hunt #4 sweep)")
    lad = data["trajectory"]["ladder"]
    ts = [absx0 / (8 * r["d"]) for r in lad]
    ims = [float(r["root_im"]) for r in lad]
    ax1.plot(ts, ims, "o", ms=5, color="#b2182b", mfc="none",
             label=r"Jensen root of $J^{d,0}$ at $t_{\rm eff}=|x_0|/8d$")
    ax1.set_xlabel("flow time $t$")
    ax1.set_ylabel(r"Im $x$ of the off-line pair image")
    ax1.set_xlim(0, float(pair["tstar"]) * 1.1)
    ax1.axvline(float(pair["tstar"]), color="gray", ls=":", lw=1)
    ax1.legend(fontsize=8)
    ax1.set_title("degree is heat: one trajectory, two clocks")

    # right: the clocks
    labels, vals, colors = [], [], []
    labels.append("PDE $t^*$ (pair 1)")
    vals.append(float(pair["tstar"])); colors.append("#2166ac")
    if "dstar" in data:
        labels.append("Jensen $|x_0|/8d^*$ (DH)")
        vals.append(float(data["dstar"]["t_jensen"])); colors.append("#b2182b")
    labels.append("isolated pair $y_0^2/2$")
    vals.append(float(pair["tstar_naive"])); colors.append("gray")
    if "planted" in data:
        labels.append("Jensen $|x_0|/8d^*$ (planted on $\\zeta$)")
        vals.append(float(data["planted"]["t_jensen_planted"])); colors.append("#762a83")
    ax2.barh(range(len(vals)), vals, color=colors, alpha=0.75)
    ax2.set_yticks(range(len(vals)))
    ax2.set_yticklabels(labels, fontsize=8)
    ax2.set_xlabel("flow time")
    ax2.set_xlim(0.04, 0.05)
    ax2.set_title("the clock reads configuration")
    fig.tight_layout()
    out = os.path.join(HERE, "jensen_clock.png")
    fig.savefig(out, dpi=140)
    print("figure written to", os.path.relpath(out))


STAGES = {
    "validate": stage_validate,
    "trajectory": stage_trajectory,
    "dstar": stage_dstar,
    "pair2": stage_pair2,
    "planted": stage_planted,
    "additivity": stage_additivity,
    "precision": stage_precision,
    "figure": stage_figure,
}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", choices=sorted(STAGES))
    args = ap.parse_args()
    STAGES[args.stage]()


if __name__ == "__main__":
    main()
