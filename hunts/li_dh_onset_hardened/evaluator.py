"""Step 2: the Arb evaluator on the production circle, its iv cross-check, and
the positive controls of the ball trapezoid.

1. Timing: g(z_k) = log G(s_k) + log |f(s_k)| (+ i arg, tracked separately) at
   1000 nodes spread over the upper half of the c = 5000 circle with N = 2^20,
   at 200 and 250 bits, single process.
2. Second route: at 20 nodes chosen by height (``IV_HEIGHTS``), f(s_k) and log G(s_k) from ``iv_route``
   (mpmath.iv, its own node, its own kappa).  Every Arb ball must meet the iv box,
   and an Arb leg with kappa moved by 2^-120 must miss it at some node.
3. xi positive control: the ball trapezoid pointed at xi (r = 1/2, aliasing
   circle 7/10) must contain every value of the committed table
   data/li_lambda_dps30_methodcauchy_n48_radius0.5.json (to its 30 digits).
   Two planted faults must flip it: a Gamma argument shifted by 2^-60, and a
   2 pi i branch slip in half the samples.
4. Two radii for DH: r = 0.9 (rho 0.95) and r = 0.99 (rho 0.995), n <= 200, each
   with its own M(rho) bound and node count; the balls must intersect, and each
   must contain hunt #128's float table (lambda_dh_n2000_r0.9.json) to 1e-26.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/evaluator.py
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction as Q

from flint import arb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import iv_route  # noqa: E402
from balls import HERE, ROOT, f_ball, logG_ball, prec_guard, q_arb  # noqa: E402
from trapezoid import (DHModel, XiModel, bound_M, li_balls, node,  # noqa: E402
                       nodes_needed, s_of)

ART = os.path.join(HERE, "artifacts")
C, NPROD = 5000, 2 ** 20
XI_TABLE = os.path.join(ROOT, "data", "li_lambda_dps30_methodcauchy_n48_radius0.5.json")
DH_TABLE = os.path.join(ROOT, "hunts", "li_dh_onset", "artifacts", "lambda_dh_n2000_r0.9.json")


def _arb_q(x: arb) -> Q:
    m, e = x.man_exp()
    return Q(int(m)) * Q(2) ** int(e)


def ball_box(z) -> tuple:
    """Exact Fraction box of an acb ball.  Built from midpoint and radius, which
    are exact; ``arb.lower()`` would round to the ambient ``ctx.prec`` (53 bits
    outside a guard), and an earlier version of this function did exactly that,
    which made the comparison vacuous until the planted kappa fault exposed it."""
    out = []
    for x in (z.real, z.imag):
        m, r = _arb_q(x.mid()), _arb_q(x.rad())
        out += [m - r, m + r]
    return tuple(out)


def meets(a: tuple, b: tuple) -> bool:
    return a[0] <= b[1] and b[0] <= a[1] and a[2] <= b[3] and b[2] <= a[3]


def timing(prec: int, count: int = 1000) -> dict:
    ks = [j * (NPROD // 2) // count for j in range(count)]
    with prec_guard(prec):
        r = (1 - 1 / q_arb(C)).sqrt()
        f_ball(s_of(node(r, 1, NPROD)), prec)            # warm the constants
        t0 = time.time()
        worst = 0.0
        for k in ks:
            s = s_of(node(r, k, NPROD))
            v = logG_ball(s, prec) + abs(f_ball(s, prec)).log()
            worst = max(worst, float(v.real.rad() / (abs(v.real).upper() + 1)))
        dt = time.time() - t0
    return {"prec": prec, "nodes": count, "seconds": round(dt, 2),
            "seconds_per_node": dt / count, "worst_relative_radius": worst}


#: target heights for the iv nodes: node k sits near Im s = N/(2 pi k), so these
#: cover the low zeros, both off-line pairs (85.7, 114.2), the box top (160)
#: and the large-|s| stretch where log G dominates.
IV_HEIGHTS = (0.6, 1, 2, 3, 5, 8, 13, 20, 30, 45, 60, 85.7, 100, 114.2, 130, 150,
              300, 1000, 3000, 9000)


def iv_crosscheck(prec: int = 160) -> dict:
    import math
    ks = [max(1, round(NPROD / (2 * math.pi * t))) for t in IV_HEIGHTS]
    kap = iv_route.kappa(prec)
    rows, all_meet, planted_caught = [], True, 0
    t0 = time.time()
    for k in ks:
        s_iv = iv_route.node_s(C, k, NPROD, prec)
        f_iv = iv_route.f_iv(s_iv, prec, kap)
        g_iv = iv_route.logG_iv(s_iv, prec)
        with prec_guard(prec):
            r = (1 - 1 / q_arb(C)).sqrt()
            s = s_of(node(r, k, NPROD))
            fb, gb = f_ball(s, prec), logG_ball(s, prec)
            k_bad = f_ball(s, prec).real * 0 + arb(2) ** -120   # planted: kappa + 2^-120
            from balls import _const
            fb_bad = f_ball(s, prec, kappa_override=_const(prec)[0] + k_bad)
        mf = meets(ball_box(fb), iv_route.bounds(f_iv))
        mg = meets(ball_box(gb), iv_route.bounds(g_iv))
        mbad = meets(ball_box(fb_bad), iv_route.bounds(f_iv))
        all_meet &= mf and mg
        planted_caught += int(not mbad)
        rows.append({"k": k, "s": [float(s.real.mid()), float(s.imag.mid())],
                     "f_meets": mf, "logG_meets": mg, "planted_kappa_meets": mbad,
                     "f_arb": fb.str(12, radius=True),
                     "iv_f_width": float(iv_route.bounds(f_iv)[1] - iv_route.bounds(f_iv)[0])})
    return {"prec": prec, "nodes": rows, "all_meet": all_meet,
            "planted_kappa_fault_caught_at": planted_caught,
            "iv_kappa": str(kap), "seconds": round(time.time() - t0, 1)}


def xi_control(prec: int = 160) -> dict:
    tab = json.load(open(XI_TABLE))["values"]
    n = len(tab)
    with prec_guard(prec):
        r, rho = q_arb(Q(1, 2)), q_arb(Q(7, 10))
    bm = bound_M(rho, prec, model=XiModel())
    M = bm["M_upper"]
    N = nodes_needed(n, 0.5, 0.7, M, 1e-28)
    N = max(N + N % 2, 2 * n + 2)
    out = {"table": os.path.relpath(XI_TABLE, ROOT), "n": n, "N": N, "M_upper": M,
           "M_closure_contains_0": bm["closure_contains_0"]}
    for label, model_fault, sample_fault in (("clean", None, None),
                                             ("gamma_shift", "gamma_shift", None),
                                             ("branch_slip", None, "skip_unwrap")):
        res = li_balls(XiModel(fault=model_fault), r, N, n, prec, rho, M, fault=sample_fault)
        with prec_guard(prec):
            hits = sum(bool((res["lambda"][i] - arb(tab[i]) + arb(0, 1e-29)).contains(0))
                       for i in range(n))
        out[label] = {"contained": hits, "passes": hits == n,
                      "worst_radius": res["stats"]["worst_radius"]}
    out["control_ok"] = out["clean"]["passes"] and not out["gamma_shift"]["passes"] \
        and not out["branch_slip"]["passes"]
    return out


def dh_two_radii(prec: int = 192, n: int = 200) -> dict:
    old = json.load(open(DH_TABLE))["lambda"]
    res, out = {}, {"n": n, "table": os.path.relpath(DH_TABLE, ROOT)}
    for rq, rhoq in ((Q(9, 10), Q(95, 100)), (Q(99, 100), Q(995, 1000))):
        t0 = time.time()
        with prec_guard(prec):
            r, rho = q_arb(rq), q_arb(rhoq)
        bm = bound_M(rho, prec)
        M = bm["M_upper"]
        N = nodes_needed(n, float(rq), float(rhoq), M, 1e-30)
        N += N % 2
        lb = li_balls(DHModel(), r, N, n, prec, rho, M)
        res[rq] = lb["lambda"]
        with prec_guard(prec):
            hits = sum(bool((lb["lambda"][i] - arb(str(old[i])) + arb(0, 1e-26)).contains(0))
                       for i in range(n))
        out[str(rq)] = {"rho": str(rhoq), "M_upper": M, "N": N,
                        "contains_128_table": hits, "worst_radius": lb["stats"]["worst_radius"],
                        "closure_contains_0": lb["stats"]["closure_contains_0"],
                        "cover_balls": lb["stats"]["cover_balls"],
                        "all_positive": all(bool(x > 0) for x in lb["lambda"]),
                        "seconds": round(time.time() - t0, 1)}
    with prec_guard(prec):
        a, b = res[Q(9, 10)], res[Q(99, 100)]
        out["radii_intersect"] = all(a[i].overlaps(b[i]) for i in range(n))
        out["max_abs_difference"] = max(float(abs(a[i] - b[i]).upper()) for i in range(n))
        out["lambda_1"] = a[0].str(35, radius=True)
        out["lambda_200"] = a[n - 1].str(35, radius=True)
    return out


def main() -> None:
    out = {"generated": time.strftime("%Y-%m-%dT%H:%M:%S"), "c": C, "N_production": NPROD}
    out["timing"] = [timing(200), timing(250)]
    print(json.dumps(out["timing"], indent=1))
    out["iv"] = iv_crosscheck()
    print("iv all meet:", out["iv"]["all_meet"], out["iv"]["seconds"], "s")
    out["xi_control"] = xi_control()
    print("xi control:", {k: out["xi_control"][k] for k in ("clean", "gamma_shift",
                                                            "branch_slip", "control_ok")})
    out["dh_two_radii"] = dh_two_radii()
    print("dh radii:", json.dumps(out["dh_two_radii"], indent=1))
    os.makedirs(ART, exist_ok=True)
    with open(os.path.join(ART, "evaluator.json"), "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
