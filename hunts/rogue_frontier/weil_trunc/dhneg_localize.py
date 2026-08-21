"""Localization + dictionary attribution for the DH negativity cells.

Evidence that the negative eigenvalue is the off-line zero pair speaking:

A. Coefficient profile of the negative-direction eigenvector at (31, 60):
   |u_k| against mode frequency 2 pi k / L should peak at the off-line
   ordinate gamma_off = 85.699..., i.e. near k_off = gamma_off L / (2 pi).
B. The transform F_v(z) on the real axis should concentrate its mass in
   the on-line gap (83.11 .. 87.65) that contains gamma_off.
C. The finite dictionary (G2 Thm 2.5, ported): lambda = <v, Q v> equals
   the zero-side sum  sum_{gamma > 0} 2 g_v(r_gamma)  over zeros of the
   completed DH function, where the first off-line quadruple contributes
       quad = 2 * (g_v(gamma_off - i delta) + g_v(gamma_off + i delta))
            = 4 Re g_v(gamma_off - i delta),  delta = 0.30851718...
   Attribution claim to measure: lambda < 0 but lambda - quad > 0, and
   lambda - quad matches the (positive) on-line partial sum + tail.
D. Same profile check for the second negative eigenvector at (47, 128),
   which should sit at the SECOND on-line gap (112.38 .. 116.72), plus a
   box-vs-line argument-principle count in that window to confirm the
   second off-line pair is really there.

Emits into dhneg_scan.json under "localization".
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))

from mpmath import mp  # noqa: E402

import galerkin as G  # noqa: E402
from dhneg_scan import load_scan, save_scan, GAMMA_OFF, DELTA_OFF  # noqa: E402


def put(key, value):
    d = load_scan()
    d.setdefault("localization", {})[key] = value
    save_scan(d)


def eigvec_min(c, N, dps):
    with mp.workdps(dps):
        t = G.Truncation(c, N, kind="dh")
        E = t.even_matrix()
        ev, vecs = G.eigsy_sorted(E)
        return t, E, ev, vecs


def profile(v, L, tag, gamma_target):
    """|u_k| profile facts for an even-sector vector."""
    N = len(v) - 1
    tot = mp.fsum(x * x for x in v)
    kpk = max(range(N + 1), key=lambda k: abs(v[k]))
    f_of = lambda k: 2 * mp.pi * k / L
    # mass within +-6 of the target ordinate
    lo, hi = gamma_target - 6, gamma_target + 6
    win = mp.fsum(v[k] * v[k] for k in range(N + 1) if lo <= f_of(k) <= hi)
    rec = {
        "peak_k": kpk,
        "peak_freq": float(f_of(kpk)),
        "target_freq": float(gamma_target),
        "k_target": float(gamma_target * L / (2 * mp.pi)),
        "mass_fraction_within_6_of_target": float(win / tot),
        "top5": [
            [int(k), float(f_of(k)), float(v[k] / mp.sqrt(tot))]
            for k in sorted(range(N + 1), key=lambda k: -abs(v[k]))[:5]
        ],
    }
    put(tag, rec)
    return rec


def fpeak(v, L, tag, zmax=140):
    """Largest |F_v| location on a real grid (0.25 step)."""
    F = G.F_even(v, L)
    best, bestz = -1, None
    z = mp.mpf("0.5")
    while z <= zmax:
        a = abs(F(z))
        if a > best:
            best, bestz = a, z
        z += mp.mpf("0.25")
    rec = {"argmax_F": float(bestz), "max_F": float(best)}
    put(tag, rec)
    return rec


def refine_online_zeros(seeds, dps):
    """Bisect Z_dh around float seeds (same route as run_dh.dh_ordinates)."""
    from zeta.epstein import Z_dh

    out = []
    for s in seeds:
        lo, hi = mp.mpf(s) - mp.mpf("0.01"), mp.mpf(s) + mp.mpf("0.01")
        flo, fhi = Z_dh(lo, dps=dps), Z_dh(hi, dps=dps)
        if flo * fhi > 0:
            out.append(mp.mpf(s))
            continue
        for _ in range(int(dps * 3.4) + 10):
            mid = (lo + hi) / 2
            fm = Z_dh(mid, dps=dps)
            if fm == 0:
                lo = hi = mid
                break
            if flo * fm < 0:
                hi = mid
            else:
                lo, flo = mid, fm
        out.append((lo + hi) / 2)
    return out


def dictionary_attribution(c, N, dps=60, refine_top=24, refine_dps=50):
    """Stage C at (c, N): lambda vs quadruple vs on-line partial sum."""
    t0 = time.time()
    t, E, ev, vecs = eigvec_min(c, N, dps)
    with mp.workdps(dps):
        lam = ev[0]
        v = vecs[0]
        gv = G.g_even(v, t.L)
        gamma = mp.mpf(GAMMA_OFF)
        delta = mp.mpf(DELTA_OFF)
        quad = 2 * (gv(mp.mpc(gamma, -delta)) + gv(mp.mpc(gamma, delta)))
        quad_re = mp.re(quad)
        quad_im = mp.im(quad)
        # on-line partial sum over the cached ordinates (float seeds),
        # with the largest terms recomputed at refined ordinates
        seeds = json.load(open(os.path.join(HERE, "..", "..", "..",
                               "data", "dh_zeros_online_T120.json")))["zeros"]
        terms = [(s, 2 * gv(mp.mpf(s))) for s in seeds]
        order = sorted(range(len(terms)), key=lambda i: -abs(terms[i][1]))
        top = order[:refine_top]
        refined = refine_online_zeros([seeds[i] for i in top], refine_dps)
        for i, znew in zip(top, refined):
            terms[i] = (znew, 2 * gv(znew))
        online = mp.fsum(x for _, x in terms)
        # crude tail estimate above the cache ceiling T=120: integrate
        # g_v against the mean density (1/2pi) log(5 r / 2pi) up to 600
        dens = lambda r: mp.log(5 * r / (2 * mp.pi)) / (2 * mp.pi)
        tail = mp.quad(lambda r: gv(r) * dens(r), [120, 200, 400, 600])
        resid = lam - quad_re - online
        rec = {
            "c": c, "N": N, "dps": dps,
            "lambda_min": mp.nstr(lam, 20),
            "offline_quadruple": mp.nstr(quad_re, 20),
            "quad_imag_residue": float(abs(quad_im)),
            "online_partial_sum_T120": mp.nstr(online, 20),
            "online_terms_all_nonneg": bool(all(x >= 0 for _, x in terms)),
            "largest_online_term_at": float(sorted(terms, key=lambda p: -abs(p[1]))[0][0]),
            "tail_estimate_over_120": mp.nstr(tail, 10),
            "lambda_minus_quad": mp.nstr(lam - quad_re, 20),
            "residual_lambda_minus_quad_minus_online": mp.nstr(resid, 10),
            "residual_minus_tail": mp.nstr(resid - tail, 10),
            "elapsed_s": round(time.time() - t0, 1),
        }
    put(f"dictionary_{c}_{N}", rec)
    return rec


def second_pair_check():
    """Second negative eigenvector at (47, 128) + box-vs-line count."""
    t0 = time.time()
    with mp.workdps(40):
        t = G.Truncation(47, 128, kind="dh")
        ev, vecs = G.eigsy_sorted(t.even_matrix())
        neg = [(i, x) for i, x in enumerate(ev) if x < 0]
        rec = {"eigs_negative": [mp.nstr(x, 12) for _, x in neg]}
        # the second-most-negative eigenvector
        i2 = neg[1][0] if len(neg) > 1 else neg[0][0]
        v2 = vecs[i2]
        p = profile(v2, t.L, "profile_47_128_second", mp.mpf("114.5"))
        rec["second_vec_peak_freq"] = p["peak_freq"]
        rec["elapsed_s"] = round(time.time() - t0, 1)
    put("second_pair_47_128", rec)
    print("second pair profile:", p, flush=True)
    # argument-principle corroboration: box vs line in the second gap
    from zeta.epstein import count_zeros_box, zeros_on_line

    t1 = time.time()
    box = count_zeros_box(mp.mpc("-1", "112.0"), mp.mpc("2", "117.0"), dps=30)
    line = zeros_on_line(112.0, 117.0, dps=20)
    put("second_gap_box_vs_line", {
        "window_t": [112.0, 117.0], "box_count": int(box),
        "line_count": int(line), "elapsed_s": round(time.time() - t1, 1),
    })
    print(f"box vs line on 112<t<117: box={box} line={line}", flush=True)


def main():
    stages = sys.argv[1:] or ["main31", "dict31", "dict4764", "second"]
    if "main31" in stages:
        t, E, ev, vecs = eigvec_min(31, 60, 60)
        with mp.workdps(60):
            print("(31,60) lam_min =", mp.nstr(ev[0], 15), flush=True)
            p = profile(vecs[0], t.L, "profile_31_60",
                        mp.mpf(GAMMA_OFF))
            print("profile:", p, flush=True)
            f = fpeak(vecs[0], t.L, "fpeak_31_60")
            print("F peak:", f, flush=True)
    if "dict31" in stages:
        r = dictionary_attribution(31, 60)
        print("dictionary (31,60):", json.dumps(r, indent=1), flush=True)
    if "dict4764" in stages:
        r = dictionary_attribution(47, 64, dps=50)
        print("dictionary (47,64):", json.dumps(r, indent=1), flush=True)
    if "second" in stages:
        second_pair_check()


if __name__ == "__main__":
    main()
