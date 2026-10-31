"""How the CvS ground state's transform approaches Xi_X as the window grows.

Usage (from the repo root):

    .venv/bin/python hunts/rh_moonshot/ccm_arithmetic/measure.py KIND [c:N ...]

KIND is one of zeta, dh, epstein, dedekind, wa.  Without cells, the default
grid for KIND runs.  Results go to ``data/measure_<KIND>.json`` beside this
file, checkpointed after every cell; a rerun skips finished cells.

Per cell (c, N), even sector:

* lambda_1..lambda_4 (Rayleigh-quotient balls of the refined eigenvectors)
  and residual norms;
* the radical misfit 1 - cos^2(v_1, r) with r the radical vector (samples of
  Xi_X at the nodes), and the squared distance of v_1 from the radical
  subspace R_m = span(r^(0..m)), m = 0..4;
* the ratio profile rho_j = (F_v1 / Xi_X)(om_j) / (F_v1 / Xi_X)(0) and the
  fitted log rho = a2 om^2 + a4 om^4 on om <= 13;
* sup over a compact of |F/F(0) - Xi/Xi(0)| on the real segment [0, T_K] and
  on the lines Im z = 0.25, 0.45 (absolute, and relative to |Xi/Xi(0)| on
  the two lines);
* real zeros of F_v1 against Xi_X's zeros (zeta: mpmath zetazero; DH: the
  lab's cached on-line scan), and for DH the real zeros of F_v1 and F_v2
  inside the on-line gap (83.109, 87.647) around the off-line ordinate;
* Sturm counts: real zeros of F_vk (k = 1..3) on [0, T_S] minus Xi_X's;
* radical capture at m = 2: kappa = lambda_min(A on R_m), mu = lambda_min(A
  on the orthogonal complement), eta = ||(1 - P_R) A P_R||, the bound
  eta / (mu - lambda_1) on dist(v_1, R_m) when mu > lambda_1, and the actual
  distance.

Grades: float-grade eigenvectors refined at the working precision (measured);
Rayleigh quotients are Arb balls for the stated vectors.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ccm_common as C  # noqa: E402
from flint import acb_mat, arb, arb_mat, ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import wp_common as WP  # noqa: E402

DATA = os.path.join(HERE, "data")

GRIDS = {
    "zeta": [(c, N) for c in (6, 9, 13, 19, 25, 31, 37, 43, 50, 60) for N in (32, 64, 128)],
    "dh": [(c, N) for c in (6, 9, 13, 19, 25, 29, 30, "61/2", 31, 33, 37, 43, 50, 60) for N in (32, 64, 128)],
    "dedekind": [(c, N) for c in (13, 19, 25, 27, 28, 29, "59/2", 30, 31, 37, 43, 50, 60) for N in (64, 128)],
    "epstein": [(c, N) for c in (13, 19, 25, 27, 28, 29, "59/2", 30, 31, 37, 50) for N in (64,)],
    "wa": [(c, N) for c in (2, 3, 4, 5, 6, 9, 13, 19, 31) for N in (32, 64)],
}

# compact for the F vs Xi comparison and node cut for the radical vector
T_K = {"zeta": 30, "dh": 30, "dedekind": 20, "epstein": 20, "wa": 20}
DT_K = {"zeta": 0.25, "dh": 0.25, "dedekind": 0.5, "epstein": 0.5, "wa": 0.5}
# nodes above T_CUT get r_k = 0: |Xi(t)/Xi(0)| < 1e-50 there for degree 1
# (t >= 160) and < 1e-25 for degree 2 (t >= 32..60); see NOTES.md s4
T_CUT = {"zeta": 160, "dh": 160, "dedekind": 40, "epstein": 32, "wa": 60}
MP_DPS = {"zeta": 130, "dh": 80, "dedekind": 80, "epstein": 80, "wa": 80}


def _cache_path(kind):
    return os.path.join(DATA, f"xi_cache_{kind}.json")


class XiCache:
    """Xi_X values keyed by the string of z at 40 digits (real or complex)."""

    def __init__(self, kind):
        self.kind = kind
        self.path = _cache_path(kind)
        self.d = WP.load(self.path, {})
        self.dirty = 0

    def get(self, z, dps=30):
        with mp.workdps(45):
            z = mp.mpc(z)
            key = mp.nstr(mp.re(z), 30) + "|" + mp.nstr(mp.im(z), 30)
        if key in self.d:
            re, im = self.d[key]
            return mp.mpc(mp.mpf(re), mp.mpf(im))
        v = C.xi_kind(self.kind, z, dps)
        with mp.workdps(dps + 10):
            self.d[key] = [mp.nstr(mp.re(v), dps + 5), mp.nstr(mp.im(v), dps + 5)]
        self.dirty += 1
        if self.dirty >= 20:
            self.flush()
        return v

    def flush(self):
        if self.dirty:
            WP.save(self.path, self.d)
            self.dirty = 0


def radical_vectors(kind, c, N, cache, powers=5, dps=30):
    """r^(0..powers-1) as mpf lists; nodes beyond T_CUT[kind] set to 0."""
    L = C.L_mp(c)
    xs = []
    for k in range(N + 1):
        om = 2 * mp.pi * k / L
        if float(om) > T_CUT[kind]:
            xs.append(mp.mpf(0))
        else:
            xs.append(mp.re(cache.get(om, dps)))
    out = []
    for p in range(powers):
        vec = []
        for k in range(N + 1):
            om = 2 * mp.pi * k / L
            if k == 0:
                vec.append(xs[0] / mp.sqrt(L) if p == 0 else mp.mpf(0))
            else:
                vec.append(mp.sqrt(2 / L) * (-1) ** k * om ** (2 * p) * xs[k])
        out.append(vec)
    return out


def to_arb_col(vals, prec):
    ctx.prec = prec
    return arb_mat(len(vals), 1, [arb(mp.nstr(x, int(prec / 3.32) + 10)) for x in vals])


def capture(A, prec, qs, lam1):
    """kappa, mu, eta for the orthonormal basis qs (mp lists) of R_m."""
    ctx.prec = prec
    n = A.nrows()
    m = len(qs)
    Q = arb_mat(n, m)
    for j, q in enumerate(qs):
        col = to_arb_col(q, prec)
        for i in range(n):
            Q[i, j] = col[i, 0].mid()
    Am = A.mid()
    AQ = Am * Q
    H = Q.transpose() * AQ
    with mp.workdps(int(prec / 3.32)):
        Hm = mp.matrix(m)
        for i in range(m):
            for j in range(m):
                Hm[i, j] = mp.mpf(H[i, j].mid().str(int(prec / 3.32), radius=False))
        ev = mp.eigsy(Hm)[0]
        kappa = min(ev[i] for i in range(m))
    B = AQ - Q * (Q.transpose() * AQ)
    G = B.transpose() * B
    with mp.workdps(int(prec / 3.32)):
        Gm = mp.matrix(m)
        for i in range(m):
            for j in range(m):
                Gm[i, j] = mp.mpf(G[i, j].mid().str(int(prec / 3.32), radius=False))
        eta = mp.sqrt(max(mp.eigsy(Gm)[0][i] for i in range(m)))
    sigma = arb(10) ** 6
    Ap = Am + (Q * Q.transpose()) * sigma
    E = acb_mat(Ap.mid()).eig(algorithm="approx")
    mu = min(float(e.real.mid()) for e in E)
    # mu as an mp number at the precision of the eigenvalue
    mu_s = sorted(E, key=lambda e: float(e.real.mid()))[0].real.mid().str(30, radius=False)
    out = {"kappa": mp.nstr(kappa, 12), "mu": mu_s, "eta": mp.nstr(eta, 12)}
    with mp.workdps(60):
        mu_mp = mp.mpf(mu_s)
        lam = mp.mpf(lam1)
        if mu_mp > lam:
            out["bound_dist"] = mp.nstr(eta / (mu_mp - lam), 12)
        else:
            out["bound_dist"] = None
    return out


def zero_list(kind, tmax):
    if kind == "zeta":
        path = os.path.join(DATA, "zeta_zeros_T200.json")
        d = WP.load(path, None)
        if d is None:
            zs = []
            with mp.workdps(40):
                k = 1
                while True:
                    g = mp.im(mp.zetazero(k))
                    if g > 200:
                        break
                    zs.append(mp.nstr(g, 35))
                    k += 1
            d = {"source": "mpmath.zetazero at dps 40", "zeros": zs}
            WP.save(path, d)
        return [mp.mpf(x) for x in d["zeros"] if float(x) <= tmax]
    if kind == "dh":
        d = json.load(open(os.path.join(C.ROOT, "data", "dh_zeros_online_T120.json")))
        return [mp.mpf(x) for x in d["zeros"] if x <= tmax]
    return None


def measure_cell(kind, c, N, cache):
    t0 = time.time()
    prec = C.prec_for(kind, c, N)
    A = C.matrix(kind, c, N, prec)
    pairs = C.lowest_pairs(A, k=4)
    ctx.prec = prec
    rec = {"kind": kind, "c": WP.cstr(c), "N": N, "prec": prec}
    rec["lambdas"] = [p[0].str(12, radius=True) for p in pairs]
    rec["lambda_mid"] = [p[0].mid().str(20, radius=False) for p in pairs]
    rec["residuals"] = [C.residual(A, p[1], p[0].mid()) for p in pairs]
    with mp.workdps(MP_DPS[kind]):
        _measure_body(kind, c, N, cache, A, prec, pairs, rec)
    rec["elapsed_s"] = round(time.time() - t0, 1)
    return rec


def _measure_body(kind, c, N, cache, A, prec, pairs, rec):
    L = C.L_mp(c)
    vs = [C.to_mp(p[1]) for p in pairs]
    v = vs[0]
    rs = radical_vectors(kind, c, N, cache)
    r = rs[0]
    rec["misfit0"] = mp.nstr(C.overlap_misfit(v, r), 8)
    proj = []
    qs_keep = None
    for m in range(5):
        res, qs = C.project_residual(v, rs[: m + 1])
        proj.append(mp.nstr(res, 8))
        if m == 2:
            qs_keep = qs
    rec["proj_residual"] = proj
    # the polynomial factor: v ~ sum_j alpha_j r^(j)  =>  F_v ~ sqrt(L) Xi(t) P(t),
    # P(t) = sum_j alpha_j t^(2j); report alpha_j / alpha_0 and the roots in t^2
    for m in (2, 4):
        G = mp.matrix(m + 1)
        b = mp.matrix(m + 1, 1)
        for i in range(m + 1):
            b[i] = mp.fsum(x * y for x, y in zip(rs[i], v))
            for j in range(m + 1):
                G[i, j] = mp.fsum(x * y for x, y in zip(rs[i], rs[j]))
        alpha = mp.lu_solve(G, b)
        coef = [alpha[j] / alpha[0] for j in range(m + 1)]
        rec[f"P_coeffs_m{m}"] = [mp.nstr(x, 10) for x in coef]
        try:
            roots = mp.polyroots(list(reversed(coef)), maxsteps=200, extraprec=200)
            rec[f"P_roots_t2_m{m}"] = [mp.nstr(z, 8) for z in roots]
        except Exception as ex:  # noqa: BLE001
            rec[f"P_roots_t2_m{m}"] = f"polyroots failed: {ex}"
    # radical defect of r itself, Rayleigh quotient in balls
    rcol = to_arb_col(r, prec)
    rec["radical_defect"] = (C._dot(rcol, A * rcol) / C._dot(rcol, rcol)).str(10, radius=True)
    # ratio profile
    rho = []
    oms = []
    for j in range(N + 1):
        om = 2 * mp.pi * j / L
        if om > 40 or r[j] == 0:
            break
        rho.append((v[j] / r[j]) / (v[0] / r[0]))
        oms.append(om)
    rec["rho"] = [[mp.nstr(o, 8), mp.nstr(x, 12)] for o, x in zip(oms, rho)]
    fit_pts = [(o, x) for o, x in zip(oms, rho) if 0 < o <= 13 and x > 0]
    if len(fit_pts) >= 2:
        # least squares log rho = a2 om^2 + a4 om^4
        S22 = mp.fsum(o**4 for o, _ in fit_pts)
        S24 = mp.fsum(o**6 for o, _ in fit_pts)
        S44 = mp.fsum(o**8 for o, _ in fit_pts)
        b2 = mp.fsum(o**2 * mp.log(x) for o, x in fit_pts)
        b4 = mp.fsum(o**4 * mp.log(x) for o, x in fit_pts)
        det = S22 * S44 - S24 * S24
        a2 = (b2 * S44 - b4 * S24) / det
        a4 = (S22 * b4 - S24 * b2) / det
        rec["fit_a2"] = mp.nstr(a2, 8)
        rec["fit_a4"] = mp.nstr(a4, 8)
        o1, x1 = fit_pts[0]
        rec["a2_first_node"] = mp.nstr((x1 - 1) / o1**2, 8)
    # compact comparison
    F0 = C.F_at0(v, L)
    X0 = mp.re(cache.get(0))
    errs = {}
    for y in (0, mp.mpf("0.25"), mp.mpf("0.45")):
        amax = mp.mpf(0)
        rmax = mp.mpf(0)
        t = mp.mpf(DT_K[kind])
        while t <= T_K[kind] + 1e-9:
            z = mp.mpc(t, y)
            Fz = C.F_mp(v, L, z) / F0
            Xz = cache.get(z) / X0
            d = abs(Fz - Xz)
            amax = max(amax, d)
            if y != 0 and abs(Xz) > 0:
                rmax = max(rmax, d / abs(Xz))
            t += DT_K[kind]
        errs[mp.nstr(y, 3)] = {"abs": mp.nstr(amax, 6), "rel": (mp.nstr(rmax, 6) if y != 0 else None)}
    rec["compact"] = errs
    cache.flush()
    # zeros
    zl = zero_list(kind, 200)
    omN = 2 * mp.pi * N / L
    if zl is not None:
        TZ = min(mp.mpf("0.9") * omN, mp.mpf(100))

        def fr(tt, vv=v):
            return mp.re(C.F_mp(vv, L, mp.mpc(tt, 0)))

        fz = C.real_zeros(fr, mp.mpf("0.3"), TZ, mp.mpf("0.05"))
        xz = [g for g in zl if g <= TZ]
        devs = []
        for g in xz:
            dmin = min((abs(g - f) for f in fz), default=mp.inf)
            devs.append(dmin)
        rec["zeros"] = {
            "TZ": mp.nstr(TZ, 6),
            "n_F": len(fz),
            "n_Xi": len(xz),
            "dev_first10": [mp.nstr(d, 4) for d in devs[:10]],
            "n_matched_1e-8": sum(1 for d in devs if d < 1e-8),
            "n_matched_1e-3": sum(1 for d in devs if d < 1e-3),
            "max_dev": mp.nstr(max(devs), 4) if devs else None,
        }
        # Sturm counts on [0, 40] (or TZ)
        TS = min(mp.mpf(40), TZ)
        st = []
        for vv in vs[:3]:
            zz = C.real_zeros(lambda tt, vv=vv: mp.re(C.F_mp(vv, L, mp.mpc(tt, 0))), mp.mpf("0.3"), TS, mp.mpf("0.05"))
            st.append(len(zz) - len([g for g in zl if g <= TS]))
        rec["sturm_extra_zeros"] = st
        if kind == "dh" and omN > 89:
            gap = []
            for vv in vs[:2]:
                zz = C.real_zeros(
                    lambda tt, vv=vv: mp.re(C.F_mp(vv, L, mp.mpc(tt, 0))),
                    mp.mpf(C.DH_GAP[0]),
                    mp.mpf(C.DH_GAP[1]),
                    mp.mpf("0.02"),
                )
                gap.append([mp.nstr(x, 8) for x in zz])
            rec["dh_gap_zeros_v1_v2"] = gap
    # radical capture, m = 2
    rec["capture_m2"] = capture(A, prec, qs_keep, rec["lambda_mid"][0])
    with mp.workdps(40):
        rec["capture_m2"]["actual_dist"] = mp.nstr(mp.sqrt(max(mp.mpf(proj[2]), 0)), 8)


def main(argv):
    kind = argv[1]
    cells = GRIDS[kind]
    if len(argv) > 2:
        cells = []
        for a in argv[2:]:
            cs, ns = a.split(":")
            cells.append((cs, int(ns)))
    os.makedirs(DATA, exist_ok=True)
    path = os.path.join(DATA, f"measure_{kind}.json")
    store = WP.load(path, {"meta": {"kind": kind, "script": "measure.py"}, "cells": {}})
    cache = XiCache(kind)
    for c, N in cells:
        key = f"{WP.cstr(c)}:{N}"
        if key in store["cells"]:
            continue
        rec = measure_cell(kind, c, N, cache)
        store["cells"][key] = rec
        WP.save(path, store)
        cache.flush()
        lam = rec["lambda_mid"][0]
        print(
            f"{kind} c={key} lam1={float(lam):.3e} misfit={rec['misfit0']} proj2={rec['proj_residual'][2]} "
            f"a2={rec.get('fit_a2')} comp0={rec['compact']['0']['abs']} t={rec['elapsed_s']}s",
            flush=True,
        )


if __name__ == "__main__":
    main(sys.argv)
