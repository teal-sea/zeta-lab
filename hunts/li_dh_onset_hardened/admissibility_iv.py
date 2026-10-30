"""The admissibility certificate replayed with the independent evaluator.

Pre-registered in MISSION.md ("Pre-registration of the iv replay of the
admissibility certificate"). Same five pieces as ``admissibility.py``, with
every value of f, log G and S computed in mpmath.iv (``iv_fast``,
``iv_route``). Boxes are converted to Arb balls exactly and outward
(``ivpipe.to_arb``/``to_iv``) only so the shared argument arithmetic of
``balls.segment_arg_change`` can be reused.

The one piece that differs in route: near s = 1 the certificate used
f(1) from Arb's ``dirichlet_l``. The Euler-Maclaurin sum cannot evaluate at the
removable pole, so the replay uses an exact point s0 = 1 + 2 eps and the bound

    |f(sigma) - f(s0)| <= 3 eps M_R / (R - 2 eps),   sigma in [1 - eps, 1 + eps],

with M_R the maximum of |f| on |s - 1| = R from an iv arc cover. The segment
from sigma to s0 stays in |s - 1| <= 2 eps, where Cauchy's estimate gives
|f'| <= M_R/(R - 2 eps).

Every comparison with Arb listed in the pre-registration is computed here and
written to ``artifacts/admissibility_iv.json``.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/admissibility_iv.py
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import acb, arb  # noqa: E402  (containers and argument arithmetic only)
from mpmath import iv  # noqa: E402

import admissibility as A  # noqa: E402
import iv_fast  # noqa: E402
from balls import (HERE, S_tail, box_zero_count, f_ball, logG_ball, point,  # noqa: E402
                   prec_guard, q_arb, rect, segment_arg_change, unique_integer)
from iv_route import _ivprec, _q, bounds  # noqa: E402
from iv_route import hurwitz as hurwitz_iv  # noqa: E402
from ivpipe import to_arb, to_iv  # noqa: E402

ART = os.path.join(HERE, "artifacts")
PREC = 128
_C = {}


def ctx() -> iv_fast.Ctx:
    if "C" not in _C:
        _C["C"] = iv_fast.Ctx(PREC)
    return _C["C"]


def f_iv(s: acb, prec: int = PREC) -> acb:
    """f over the Arb ball s, evaluated in iv, returned as an Arb ball."""
    with _ivprec(PREC):
        w = iv_fast.f_fast(to_iv(s), ctx())
    with prec_guard(prec):
        return to_arb(w)


def logG_iv(s: acb, prec: int = PREC) -> acb:
    with _ivprec(PREC):
        w = iv_fast.logG_fast(to_iv(s), ctx())
    with prec_guard(prec):
        return to_arb(w)


def F_iv(s: acb) -> acb:
    with _ivprec(PREC):
        si = to_iv(s)
        w = iv.exp(iv_fast.logG_fast(si, ctx())) * iv_fast.f_fast(si, ctx())
    with prec_guard(PREC):
        return to_arb(w)


def S_iv(sigma: Q) -> arb:
    C = ctx()
    with _ivprec(PREC):
        sg = iv.mpc(_q(sigma), 0)
        z = lambda a: hurwitz_iv(sg, a, PREC).real
        S = iv.exp(-_q(sigma) * iv.log(5)) * (
            z(Q(6, 5)) + C.kappa * (z(Q(2, 5)) + z(Q(3, 5))) + z(Q(4, 5)))
        w = iv.mpc(S, 0)
    with prec_guard(PREC):
        return to_arb(w).real


def _meets(a, b) -> bool:
    with prec_guard(PREC):
        return bool(a.overlaps(b))


# ---------------------------------------------------------------------------

def half_plane() -> dict:
    out = {}
    for sg, key in ((Q(3, 2), "S(3/2)"), (A.SIGMA_H, "S(sigma_h)")):
        si, sa = S_iv(sg), S_tail(sg, PREC)
        out[key] = {"iv": si.str(20, radius=True), "below_1": bool(si < 1),
                    "meets_arb": _meets(si, sa)}
    out["ok"] = out["S(3/2)"]["below_1"] and out["S(sigma_h)"]["below_1"]
    return out


def _positive_on(lo: Q, hi: Q, depth: int = 0) -> int:
    with prec_guard(PREC):
        v = f_iv(acb(arb(q_arb((lo + hi) / 2), q_arb((hi - lo) / 2))))
        if v.real > 0:
            return 1
    if depth > 40:
        raise RuntimeError(f"f > 0 not decided on [{lo}, {hi}]")
    m = (lo + hi) / 2
    return _positive_on(lo, m, depth + 1) + _positive_on(m, hi, depth + 1)


def real_axis(eps: Q = Q(1, 512), R: Q = Q(1, 4), arcs: int = 1024) -> dict:
    n1 = _positive_on(Q(1, 2), 1 - eps)
    n2 = _positive_on(1 + eps, A.SIGMA_H)
    s0 = 1 + 2 * eps
    with prec_guard(PREC):
        fs0 = f_iv(point(s0, 0))
        fs0_arb = f_ball(point(s0, 0), PREC)
        M = 0.0
        pi = arb.pi()
        for j in range(arcs):
            th = (2 * j + 1) * pi / arcs
            c = acb(1) + q_arb(R) * acb(th.cos(), th.sin())
            half = q_arb(R) * pi / arcs * q_arb(Q(11, 10))
            ball = acb(arb(c.real.mid(), half), arb(c.imag.mid(), half))
            M = max(M, float(abs(f_iv(ball)).upper()) * (1 + 1e-12))
        drift = 3 * q_arb(eps) * q_arb(Q(M)) / (q_arb(R) - 2 * q_arb(eps))
        ok = bool(fs0.real - drift > 0) and bool(fs0.imag.contains(0))
    return {"balls_left_of_1": n1, "balls_right_of_1": n2, "eps": str(eps),
            "f(s0)": fs0.str(20, radius=True), "f(s0)_meets_arb": _meets(fs0, fs0_arb),
            "max_abs_f_on_circle_R": M, "drift_bound": float(drift.upper()),
            "f_positive_near_1": ok, "ok": ok}


def box_count(T: Q) -> dict:
    stats: dict = {}
    with prec_guard(PREC):
        fr = f_iv(point(A.SIGMA_H, T))
        if not (fr.real > 0):
            raise RuntimeError("Re f(sigma_h + iT) not positive")
        a_right = (fr.imag / fr.real).atan()
    d_top = segment_arg_change(f_iv, (A.SIGMA_H, T), (Q(1, 2), T), PREC, max_depth=60,
                               stats=stats)
    with prec_guard(PREC):
        lg = logG_iv(point(Q(1, 2), T))
        N = (lg.imag + a_right + d_top) / arb.pi()
    arb_ball = arb(json.load(open(os.path.join(ART, "admissibility.json")))
                   ["box_count"]["N_box_ball"])
    return {"N_box_ball": N.str(20, radius=True), "N_box": unique_integer(N),
            "meets_arb": _meets(N, arb_ball), "top_edge_stats": stats}


def line_count(T: Q, grid: int = A.GRID) -> dict:
    n = int(T * grid)
    signs, misses = [], []
    for j in range(n + 1):
        t = Q(j, grid)
        with prec_guard(PREC):
            s = point(Q(1, 2), t)
            v = F_iv(s)
            va = logG_ball(s, PREC).exp() * f_ball(s, PREC)
            if not v.overlaps(va):
                misses.append(float(t))
            if not v.imag.contains(0):
                raise RuntimeError(f"iv F(1/2 + i{t}) not real")
            sg = 1 if v.real > 0 else (-1 if v.real < 0 else 0)
        if sg == 0:
            raise RuntimeError(f"iv sign of Z undecided at t = {t}")
        signs.append(sg)
    changes = sum(1 for j in range(n) if signs[j] != signs[j + 1])
    return {"points": n + 1, "N_line": changes, "arb_misses": misses[:20],
            "arb_miss_count": len(misses)}


def locate(beta: Q, gamma: Q, delta: Q = A.DELTA) -> dict:
    stats: dict = {}
    cnt = box_zero_count(f_iv, beta - delta, beta + delta, gamma - delta, gamma + delta,
                         PREC, pieces=2, stats=stats)
    with _ivprec(PREC):
        s = iv.mpc(iv.mpf([_q(beta - delta).a, _q(beta + delta).b]),
                   iv.mpf([_q(gamma - delta).a, _q(gamma + delta).b]))
        mod = abs(1 - 1 / s)
    with prec_guard(PREC):
        m = to_arb(iv.mpc(mod, 0)).real
        sa = rect(beta - delta, beta + delta, gamma - delta, gamma + delta)
        ma = abs(1 - 1 / sa)
    return {"count": unique_integer(cnt), "evals": stats,
            "abs_z": m.str(20, radius=True), "abs_z_meets_arb": _meets(m, ma), "_m": m}


def main() -> None:
    T = Q(160)
    t0 = time.time()
    out = {"generated": None, "prec_bits": PREC, "T": str(T), "evaluator": "mpmath.iv"}
    out["half_plane"] = half_plane()
    print("half plane", out["half_plane"]["ok"], flush=True)
    out["real_axis"] = real_axis()
    print("real axis", out["real_axis"]["ok"], round(time.time() - t0), flush=True)
    out["box_count"] = box_count(T)
    print("box", out["box_count"]["N_box"], out["box_count"]["top_edge_stats"], flush=True)
    out["line"] = line_count(T)
    print("line", out["line"]["N_line"], out["line"]["arb_miss_count"], round(time.time() - t0),
          flush=True)
    located = []
    for r in A.recorded_offline(T):
        L = locate(Q(r["beta"]), Q(r["gamma"]))
        L["label"] = r["label"]
        located.append(L)
        print("square", r["label"], L["count"], L["evals"], flush=True)
    q = sum(1 for L in located if L["count"] == 1)
    Nb, Nl = out["box_count"]["N_box"], out["line"]["N_line"]
    closes = bool(Nb is not None and Nb == Nl + 2 * q and out["half_plane"]["ok"]
                  and out["real_axis"]["ok"])
    with prec_guard(PREC):
        r = (1 - 1 / q_arb(A.C_TARGET)).sqrt()
        above = (1 - 2 / (q_arb(T) ** 2)).sqrt()
        lows = [L["_m"].lower() for L in located if L["count"] == 1] + [above.lower()]
        Ra = lows[0]
        for x in lows[1:]:
            if x < Ra:
                Ra = x
        r_below = bool(r < Ra)
    for L in located:
        L.pop("_m")
    out["located"] = located
    out["q"] = q
    out["equality"] = {"N_box": Nb, "N_line": Nl, "two_q": 2 * q, "closes": closes}
    first = A.recorded_offline(T)[0]
    displaced = locate(Q(first["beta"]) + 10 * A.DELTA, Q(first["gamma"]))["count"]
    out["faults"] = {"drop_one_quadruple_closes": bool(Nb == Nl + 2 * (q - 1)),
                     "displaced_square": displaced,
                     "displaced_square_closes": bool(Nb == Nl + 2 * (q - 1 + (displaced or 0)))}
    out["radius"] = {"R_a_lower": float(Ra.mid()), "r_c5000_below_R_a": r_below}
    agree = (out["half_plane"]["S(3/2)"]["meets_arb"]
             and out["half_plane"]["S(sigma_h)"]["meets_arb"]
             and out["real_axis"]["f(s0)_meets_arb"]
             and out["box_count"]["meets_arb"] and out["line"]["arb_miss_count"] == 0
             and all(L["abs_z_meets_arb"] for L in located))
    out["rule"] = {"conclusion_reproduced": bool(closes and Nb == 98 and Nl == 94 and q == 2
                                                  and r_below),
                   "balls_meet_arb_everywhere_compared": bool(agree),
                   "faults_break_it": bool(not out["faults"]["drop_one_quadruple_closes"]
                                           and not out["faults"]["displaced_square_closes"])}
    out["seconds"] = round(time.time() - t0, 1)
    out["generated"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    with open(os.path.join(ART, "admissibility_iv.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: out[k] for k in ("equality", "faults", "radius", "rule", "seconds")},
                     indent=1))


if __name__ == "__main__":
    main()
