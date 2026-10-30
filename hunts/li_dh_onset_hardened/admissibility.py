"""The admissibility certificate: every zero right of the line is located.

What it establishes, in Arb balls at ``PREC`` bits, for the completed
Davenport-Heilbronn function F = G f (``balls.py``):

1. **No zero with Re s >= 3/2**, hence by F(s) = F(1-s) none with Re s <= -1/2:
   S(3/2) < 1 (``balls.S_tail``).  Also S(SIGMA_H) < 1, so Re f > 0 on the
   whole line Re s = SIGMA_H, and f > 0 there on the real axis.
2. **No real zero**: f(sigma) > 0 for sigma in [1/2, SIGMA_H] (Hurwitz balls
   away from s = 1; near s = 1, f(1) from Arb's ``dirichlet_l`` plus a Cauchy
   bound on f' from a ball cover of the circle |s - 1| = 1/4).  G > 0 on the
   real axis, F(1-s) = F(s), so F has no zero on [1 - SIGMA_H, SIGMA_H].
3. **N_box**: the argument-principle count of zeros of F in
   B = [1 - SIGMA_H, SIGMA_H] x (0, T).  By the two symmetries the boundary
   integral folds to Backlund's form

       N_box = ( Im log G(1/2 + iT) + arg f(1/2 + iT) ) / pi,

   where arg f is continued from arg f(SIGMA_H) = 0 up the right edge (where
   Re f > 0, so the continuation is the principal value) and then left along
   the top edge to 1/2 + iT by ``balls.segment_arg_change``.  It must be a
   ball containing exactly one integer.
4. **N_line**: ball-decided signs of the real function Z(t) = F(1/2 + it) on the
   grid t = j/GRID, 0 <= j <= GRID*T, and the number of sign changes.
5. **q located off-line zeros**: for every recorded zero with Re > 1/2 and
   0 < Im < T, a square of half-width DELTA around it whose argument-principle
   count is exactly 1, and a lower bound on |1 - 1/s| over the square.

If N_box = N_line + 2q, every zero in B is accounted for: the sign changes give
N_line distinct zeros on the line, the squares q zeros right of it and, by
s -> 1 - conj(s), q left of it, and nothing is left over.  So every zero with
Re s > 1/2 and 0 < Im s < T is one of the q located ones.  Zeros with
Re s > 1 (Davenport and Heilbronn 1936 proved there are infinitely many) are
inside B because Re s < 3/2 < SIGMA_H, so the equality counts them too: below T
there are none except those located.  Above T a zero with Re rho = sigma in
(1/2, 3/2) has |1 - 1/rho|^2 = 1 - (2 sigma - 1)/|rho|^2 > 1 - 2/T^2.  Hence

    R_a = min over zeros with Re > 1/2 of |1 - 1/rho|
       >= min( min over located squares of |1 - 1/s|,  sqrt(1 - 2/T^2) ).

The planted faults: dropping one located quadruple, and displacing one square
off its zero, must each break the equality.

Usage: .venv/bin/python hunts/li_dh_onset_hardened/admissibility.py [--T 160]
Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction as Q

from flint import acb, arb, dirichlet_char

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from balls import (HERE, ROOT, S_tail, box_zero_count, f_ball, logG_ball,  # noqa: E402
                   point, prec_guard, q_arb, rect, segment_arg_change,
                   unique_integer, _const)

ART = os.path.join(HERE, "artifacts")
PREC = 128
SIGMA_H = Q(7, 4)
GRID = 64
DELTA = Q(1, 10 ** 15)
C_TARGET = 5000


def fmt(x) -> str:
    return x.str(30, radius=True) if hasattr(x, "str") else str(x)


# ---------------------------------------------------------------------------
# 1, 2: half-plane bound and the real axis
# ---------------------------------------------------------------------------

def half_plane_bounds(prec: int = PREC) -> dict:
    s15 = S_tail(Q(3, 2), prec)
    sh = S_tail(SIGMA_H, prec)
    return {"S(3/2)": fmt(s15), "S(sigma_h)": fmt(sh),
            "no_zero_re_ge_3/2": bool(s15 < 1), "re_f_positive_on_sigma_h": bool(sh < 1)}


def _f_positive_on(lo: Q, hi: Q, prec: int, depth: int = 0) -> int:
    """Number of real balls used to show f > 0 on [lo, hi] (1 not in [lo, hi])."""
    with prec_guard(prec):
        v = f_ball(acb(arb(q_arb((lo + hi) / 2), q_arb((hi - lo) / 2))), prec)
        if v.real > 0:
            return 1
    if depth > 30:
        raise RuntimeError(f"f > 0 not decided on [{lo}, {hi}]")
    m = (lo + hi) / 2
    return _f_positive_on(lo, m, prec, depth + 1) + _f_positive_on(m, hi, prec, depth + 1)


def real_axis(prec: int = PREC, eps: Q = Q(1, 64), R: Q = Q(1, 4), arcs: int = 256) -> dict:
    """f > 0 on [1/2, SIGMA_H]; near s = 1 by f(1) and a Cauchy bound."""
    n1 = _f_positive_on(Q(1, 2), 1 - eps, prec)
    n2 = _f_positive_on(1 + eps, SIGMA_H, prec)
    k, _, _ = _const(prec)
    with prec_guard(prec):
        L1 = acb.dirichlet_l(acb(1), dirichlet_char(5, 2))     # chi(2) = i
        f1 = (L1 * acb(1, -k)).real                            # 2 Re(c L), c = (1 - i kappa)/2
        # max |f| on |s - 1| = R from a cover by rectangle balls around arcs
        M = arb(0)
        pi = arb.pi()
        for j in range(arcs):
            th = (2 * j + 1) * pi / arcs
            c = acb(1) + q_arb(R) * acb(th.cos(), th.sin())
            half = q_arb(R) * pi / arcs * q_arb(Q(11, 10))  # covers the arc's disc
            ball = acb(arb(c.real.mid(), half), arb(c.imag.mid(), half))
            val = abs(f_ball(ball, prec))
            M = M.union(val) if j else val
        Mup = arb(M.upper())
        drift = q_arb(eps) * Mup / (q_arb(R) - q_arb(eps))
        ok = bool(f1 - drift > 0)
    return {"balls_left_of_1": n1, "balls_right_of_1": n2, "f(1)": fmt(f1),
            "max_abs_f_on_circle_R": fmt(Mup), "cauchy_drift_bound": fmt(drift),
            "f_positive_near_1": ok,
            "f_positive_on_[1/2,sigma_h]": ok}


# ---------------------------------------------------------------------------
# 3: the box count
# ---------------------------------------------------------------------------

def box_count(T: Q, prec: int = PREC) -> dict:
    stats: dict = {}
    with prec_guard(prec):
        fr = f_ball(point(SIGMA_H, T), prec)
        if not (fr.real > 0):
            raise RuntimeError("Re f(sigma_h + iT) not positive")
        a_right = (fr.imag / fr.real).atan()
    d_top = segment_arg_change(f_ball, (SIGMA_H, T), (Q(1, 2), T), prec, stats=stats)
    with prec_guard(prec):
        lg = logG_ball(point(Q(1, 2), T), prec)
        N = (lg.imag + a_right + d_top) / arb.pi()
    return {"N_box_ball": fmt(N), "N_box": unique_integer(N), "top_edge_stats": stats,
            "arg_f_right_edge": fmt(a_right), "arg_f_top_change": fmt(d_top)}


# ---------------------------------------------------------------------------
# 4: the line
# ---------------------------------------------------------------------------

def Z_sign(t: Q, prec: int) -> int:
    with prec_guard(prec):
        s = point(Q(1, 2), t)
        v = logG_ball(s, prec).exp() * f_ball(s, prec)
        if not v.imag.contains(0):
            raise RuntimeError(f"F(1/2 + i{t}) not real: {v}")
        if v.real > 0:
            return 1
        if v.real < 0:
            return -1
    return 0


def line_count(T: Q, prec: int = PREC, grid: int = GRID) -> dict:
    n = int(T * grid)
    signs = []
    shifted = 0
    for j in range(n + 1):
        t = Q(j, grid)
        sg = Z_sign(t, prec)
        if sg == 0:                       # a zero within the ball: nudge inward
            for nudge in (Q(1, 997 * grid), -Q(1, 997 * grid)):
                if 0 < t + nudge < T:
                    sg = Z_sign(t + nudge, prec)
                    if sg:
                        shifted += 1
                        break
        if sg == 0:
            raise RuntimeError(f"sign of Z undecided at t = {t}")
        signs.append(sg)
    changes = [Q(j, grid) for j in range(n) if signs[j] != signs[j + 1]]
    return {"grid_step": f"1/{grid}", "points": n + 1, "nudged": shifted,
            "N_line": len(changes),
            "sign_change_brackets_lo": [float(c) for c in changes]}


# ---------------------------------------------------------------------------
# 5: the located off-line zeros
# ---------------------------------------------------------------------------

def recorded_offline(T: Q) -> list[dict]:
    """Off-line zeros recorded by hunts/flow_repair and lambda_dh_bounds, Im < T."""
    sys.path.insert(0, os.path.join(ROOT, "hunts", "li_dh_onset"))
    from zero_side import offline_quadruples
    rows = []
    for r in offline_quadruples():
        if Q(str(r["gamma"])) < T:
            rows.append({"label": r["label"], "beta": str(r["beta"]),
                         "gamma": str(r["gamma"]), "source": r["source"]})
    return rows


def locate(beta: Q, gamma: Q, prec: int = PREC, delta: Q = DELTA) -> dict:
    stats: dict = {}
    cnt = box_zero_count(f_ball, beta - delta, beta + delta, gamma - delta,
                         gamma + delta, prec, pieces=2, stats=stats)
    with prec_guard(prec):
        s = rect(beta - delta, beta + delta, gamma - delta, gamma + delta)
        z = 1 - 1 / s
        mod = abs(z)
        one_minus_mod2 = 1 - mod * mod
    return {"count_ball": fmt(cnt), "count": unique_integer(cnt), "evals": stats,
            "abs_z_ball": fmt(mod), "abs_z_lower": float(mod.lower()),
            "one_minus_abs_z_squared": fmt(one_minus_mod2),
            "_abs_z": mod}


# ---------------------------------------------------------------------------
# assembly
# ---------------------------------------------------------------------------

def certificate(T: Q, prec: int = PREC) -> dict:
    t0 = time.time()
    out: dict = {"prec_bits": prec, "T": str(T), "sigma_h": str(SIGMA_H),
                 "box": f"[{1 - SIGMA_H}, {SIGMA_H}] x (0, {T})"}
    out["half_plane"] = half_plane_bounds(prec)
    out["real_axis"] = real_axis(prec)
    out["box_count"] = box_count(T, prec)
    t1 = time.time()
    out["line"] = line_count(T, prec)
    t2 = time.time()
    located = []
    for r in recorded_offline(T):
        b, g = Q(r["beta"]), Q(r["gamma"])
        loc = locate(b, g, prec)
        loc.update(r)
        located.append(loc)
    q = sum(1 for L in located if L["count"] == 1 and Q(L["beta"]) > Q(1, 2))
    Nb, Nl = out["box_count"]["N_box"], out["line"]["N_line"]
    closes = (Nb is not None and Nb == Nl + 2 * q
              and out["half_plane"]["no_zero_re_ge_3/2"]
              and out["half_plane"]["re_f_positive_on_sigma_h"]
              and out["real_axis"]["f_positive_on_[1/2,sigma_h]"])
    with prec_guard(prec):
        Tb = q_arb(T)
        above = (1 - 2 / (Tb * Tb)).sqrt()
        lows = [L["_abs_z"].lower() for L in located if L["count"] == 1] + [above.lower()]
        Ra_lo_b = lows[0]
        for x in lows[1:]:
            if x < Ra_lo_b:
                Ra_lo_b = x
        binding = min(located, key=lambda L: float(L["_abs_z"].mid()))
        Ra_hi_b = binding["_abs_z"].upper()
        Ra_lo, Ra_hi = float(Ra_lo_b.mid()), float(Ra_hi_b.mid())
        c = q_arb(C_TARGET)
        r = (1 - 1 / c).sqrt()
        r_1e4 = (1 - 1 / q_arb(10000)).sqrt()
        r_below = bool(r < Ra_lo_b)
        gap = float((Ra_lo_b.log() - r.log()).mid())
        beyond = bool((1 + r_1e4) / 2 > Ra_hi_b)
    for L in located:
        L.pop("_abs_z")
    out["located"] = located
    out["q"] = q
    out["equality"] = {"N_box": Nb, "N_line": Nl, "two_q": 2 * q, "closes": bool(closes)}
    out["faults"] = {
        "drop_one_quadruple_closes": bool(Nb == Nl + 2 * (q - 1)),
        "displaced_square": locate(Q(located[0]["beta"]) + 10 * DELTA,
                                   Q(located[0]["gamma"]), prec)["count"],
    }
    out["faults"]["displaced_square_closes"] = bool(
        Nb == Nl + 2 * (q - 1 + (out["faults"]["displaced_square"] or 0)))
    out["radius"] = {
        "sqrt(1-2/T^2)_lower": float(above.lower().mid()),
        "R_a_lower": Ra_lo, "R_a_upper": Ra_hi, "binding_zero": binding["label"],
        "c": C_TARGET, "r": float(r.mid()), "one_minus_r": float((1 - r).mid()),
        "r_below_R_a": r_below,
        "gap_ln_Ra_over_r": gap,
        "c_1e4_r": float(r_1e4.mid()),
        "c_1e4_midpoint_circle": float(((1 + r_1e4) / 2).mid()),
        "c_1e4_midpoint_circle_beyond_R_a": beyond,
    }
    out["seconds"] = {"box": round(t1 - t0, 1), "line": round(t2 - t1, 1),
                      "total": round(time.time() - t0, 1)}
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--T", default="160")
    ap.add_argument("--out", default=os.path.join(ART, "admissibility.json"))
    a = ap.parse_args()
    out = certificate(Q(a.T))
    out["generated"] = time.strftime("%Y-%m-%dT%H:%M:%S")
    os.makedirs(os.path.dirname(a.out), exist_ok=True)
    with open(a.out, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: out[k] for k in ("equality", "faults", "radius", "seconds")},
                     indent=1))


if __name__ == "__main__":
    main()
