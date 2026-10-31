"""Inertia of T and W = T - eps_N, and the spectrum of D'' against the zeros.

Usage (from the repo root):

    .venv/bin/python hunts/rh_moonshot/spectral_operator/spo_run.py KIND c:N [c:N ...]

Per cell writes data/cell_<kind>_<c>_<N>.json:

* inertia (pos, neg, conclusive) by Arb ball LDL^T of the even sector (N+1)
  and the odd sector (N) at shift 0 (Weil positivity on E_N), at
  sigma_lo = eps - rho and sigma_hi = eps + rho with
  rho = (min(lambda_2 even, lambda_1 odd) - eps) / 2 from midpoint estimates:
  (N+1, 0) and (N, 1) for the even sector and (N, 0) for the odd one, all
  conclusive, place exactly one eigenvalue of T in (sigma_lo, sigma_hi), even,
  so T is even-simple (CCM's hypothesis) and W = T - eps >= 0 has the even
  vector as its only null direction;
* the spectrum of D' (acb_mat.eig, approx) as z = 2 pi s / L, its largest
  imaginary part, and the real zeros of the transform F_xi (sign changes,
  bisected) as the second route;
* the table against the target zeros (zeta: mpmath zetazero 1..100; DH: the
  lab's on-line list to 120 plus the off-line ordinate), with residuals, and
  the Gram-point control for zeta.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import spo_common as S  # noqa: E402
import ccm_common as C  # noqa: E402
from flint import ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import wp_common as WP  # noqa: E402

DATA = os.path.join(HERE, "data")
NZ = 100
EIG_PREC = 500


def _transform_zeros(v, L, tmax, step):
    """Real zeros of F_v (the transform of xi; CCM Theorem finmain (iii) says
    they are the spectrum of D''), by sign changes and bisection.  F_v has no
    poles, and its only zeros at nodes are at |k| > N, above tmax."""
    return C.real_zeros(lambda t: mp.re(C.F_mp(v, L, mp.mpc(t, 0))), mp.mpf("0.3"), tmax, step)


def targets(kind):
    if kind == "zeta":
        return S.zeta_ordinates(NZ, os.path.join(DATA, "zeta_zeros_100.json"))
    with open(os.path.join(S.ROOT, "data", "dh_zeros_online_T120.json")) as fh:
        d = json.load(fh)
    return [mp.mpf(x) for x in d["zeros"]]


def cell(kind, c, N):
    t0 = time.time()
    prec = S.prec_for(kind, c, N)
    rec = {"kind": kind, "c": WP.cstr(c), "N": N, "prec": prec, "eig_prec": EIG_PREC}
    bt, Te, To = S.sectors(kind, c, N, prec)
    rec["t_build"] = round(time.time() - t0, 1)
    rq, v = S.ground(Te)
    digits = int(prec / 3.32)
    with mp.workdps(digits):
        import ccm_common as CC

        pe = CC.lowest_pairs(Te, k=2)
        lam2 = pe[1][0].mid()
        lo_odd = S.lowest_odd_mid(To)
        eps = rq.mid()
        rho = (min(lam2, lo_odd) - eps) / 2
        rec["eps"] = rq.str(12, radius=True)
        rec["lambda2_even_mid"] = lam2.str(12, radius=False)
        rec["lambda1_odd_mid"] = lo_odd.str(12, radius=False)
        t1 = time.time()
        rec["inertia"] = {
            "even_at_0": S.inertia(Te, 0),
            "odd_at_0": S.inertia(To, 0),
            "even_at_lo": S.inertia(Te, eps - rho),
            "even_at_hi": S.inertia(Te, eps + rho),
            "odd_at_hi": S.inertia(To, eps + rho),
        }
        rec["t_ldl"] = round(time.time() - t1, 1)
        I = rec["inertia"]
        rec["even_simple_hardened"] = bool(
            all(x[2] for x in I.values())
            and tuple(I["even_at_lo"][:2]) == (N + 1, 0)
            and tuple(I["even_at_hi"][:2]) == (N, 1)
            and tuple(I["odd_at_hi"][:2]) == (N, 0)
        )
        L = C.L_mp(c)
        xi = S.xi_full(v)
        t2 = time.time()
        sp = S.spectrum_matrix(S.operator(xi), L, EIG_PREC)
        ctx.prec = prec
        rec["t_eig"] = round(time.time() - t2, 1)
        rec["max_abs_imag"] = mp.nstr(max(abs(mp.im(z)) for z in sp), 5)
        zs = sorted(mp.re(z) for z in sp if mp.re(z) > mp.mpf("0.1"))
        omN = 2 * mp.pi * N / L
        T = targets(kind)
        tmax = min(mp.mpf("0.9") * omN, max(T) + 1)
        zs = [z for z in zs if z <= tmax]
        t3 = time.time()
        sec = [z for z in _transform_zeros(v, L, tmax, mp.mpf("0.05")) if z <= tmax]
        rec["t_transform"] = round(time.time() - t3, 1)
        rec["n_eig"] = len(zs)
        rec["n_transform"] = len(sec)
        rec["eig_vs_transform_max"] = mp.nstr(max((abs(a - b) for a, b in zip(zs, sec)), default=mp.mpf(-1)), 5) if len(zs) == len(sec) else "count mismatch"
        table = []
        for k, g in enumerate([g for g in T if g <= tmax]):
            near = min(zs, key=lambda z: abs(z - g)) if zs else None
            table.append([k + 1, mp.nstr(g, 15), mp.nstr(near, 15) if near is not None else None, mp.nstr(abs(near - g), 4) if near is not None else None])
        rec["table"] = table
        rec["eig"] = [mp.nstr(z, 15) for z in zs]
        rec["transform"] = [mp.nstr(z, 15) for z in sec]
        if kind == "zeta":
            gp = S.gram_points(len(table) + 1)
            rec["gram_residual_max"] = mp.nstr(max(abs(mp.mpf(r[1]) - min(gp, key=lambda x: abs(x - mp.mpf(r[1])))) for r in table), 4)
            rec["gram_residual_median"] = mp.nstr(sorted(abs(mp.mpf(r[1]) - min(gp, key=lambda x: abs(x - mp.mpf(r[1])))) for r in table)[len(table) // 2], 4)
        if kind == "dh":
            rec["eig_in_gap_83_88"] = [mp.nstr(z, 10) for z in zs if 83.109 < z < 87.647]
    rec["elapsed_s"] = round(time.time() - t0, 1)
    return rec


def main(argv):
    kind = argv[1]
    os.makedirs(DATA, exist_ok=True)
    for a in argv[2:]:
        cs, ns = a.split(":")
        path = os.path.join(DATA, f"cell_{kind}_{cs.replace('/', '-')}_{ns}.json")
        if os.path.exists(path):
            continue
        rec = cell(kind, cs, int(ns))
        with open(path, "w") as fh:
            json.dump(rec, fh)
        short = {k: v for k, v in rec.items() if k not in ("table", "eig", "transform")}
        print(json.dumps(short)[:900], flush=True)


if __name__ == "__main__":
    main(sys.argv)
