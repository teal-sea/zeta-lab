"""The other route to lambda_n(DH): sum over the zeros, never touching F.

This exists to be *different* from the Cauchy route, not to be better than it.
The Cauchy route reads one contour integral of log F and never learns where a
zero is; this route reads a zero list and never evaluates F off the critical
line.  They share the definition and nothing else, so agreement at small n is
the load-bearing cross-check that the Cauchy pipeline is computing the Li
coefficients of the Davenport-Heilbronn function and not of something adjacent.

It is deliberately partial.  The head runs over the critical-line ordinates up
to a truncation height plus the known off-line quadruples below it; the tail is
the smooth Davenport-Heilbronn zero density; the boundary term is the
k-independent form ``zeta.li._li_zeros`` derives.  Its accuracy is limited by
the truncation, so it pins the Cauchy numbers at the 1e-4 level and not at the
1e-30 level, and that is enough to catch a wrong normalisation, a wrong
conductor, a dropped quadruple or a factor of two.

Why the off-line quadruples must be put in by hand.  A sign-change scan of Z_f
sees critical-line zeros only.  For zeta that costs nothing; for f it is exactly
the undercount that makes f a counterexample, so a zero-side sum built from
sign changes alone would be summing the *wrong multiset* and would agree with
nothing.  The quadruples come from the measurements this repository already
holds, and the argument-principle box count is what says the list is complete
below the truncation height.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zeta.epstein import Z_dh, _dh_mean_spacing, count_zeros_box, dh_theta
from zeta.li import _phi

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ART = os.path.join(HERE, "artifacts")


def offline_quadruples() -> list[dict]:
    """(beta, gamma) for every off-line zero this repository has measured.

    Nine from ``hunts/flow_repair`` (the backward-heat repair study) and six
    more from ``hunts/lambda_dh_bounds``'s census.  Read from those files rather
    than transcribed, because a transcribed constant is a constant nobody can
    re-derive.
    """
    rows = []
    fr = json.load(open(os.path.join(ROOT, "hunts", "flow_repair", "results.json")))
    for key, sub in (("pair1", None), ("survey_2_3", ("pair2", "pair3")),
                     ("survey_4_5", ("pair4", "pair5")),
                     ("survey_6_7", ("pair6", "pair7")),
                     ("survey_8_9", ("pair8", "pair9"))):
        node = fr[key]
        targets = [node] if sub is None else [node[k] for k in sub]
        for t in targets:
            p = t["polished"]
            rows.append({"beta": p["beta"], "gamma": p["gamma"],
                         "source": "hunts/flow_repair/results.json",
                         "label": f"pair{p['pair']}"})
    cen = json.load(
        open(os.path.join(ROOT, "hunts", "lambda_dh_bounds", "census_results.json"))
    )
    for i, z in enumerate(cen["offline_zeros"]):
        rows.append({"beta": z["beta"], "gamma": z["gamma"],
                     "source": "hunts/lambda_dh_bounds/census_results.json",
                     "label": f"census{i + 1}"})
    rows.sort(key=lambda r: float(r["gamma"]))
    return rows


def quadruple_growth(beta, gamma, dps: int = 40) -> dict:
    """R = |1 - 1/(1 - rho)| and psi = arg(1 - 1/(1 - rho)) for one quadruple.

    The identity that makes the quadruple's Li contribution readable:
    with sigma = 1 - rho, (1 - 1/rho)(1 - 1/sigma) = 1 exactly, so the four
    terms collapse to

        4 - 2 (R^n + R^-n) cos(n psi),    R = |1 - 1/sigma| > 1 for Re rho > 1/2.

    R - 1 is what decides which quadruple drives the first negative index, and
    it is (2 beta - 1)/(2 |1 - rho|^2) to leading order.
    """
    with mp.workdps(dps):
        rho = mp.mpc(mp.mpf(beta), mp.mpf(gamma))
        sig = 1 - rho
        u = 1 - 1 / sig
        return {"R": mp.mpf(abs(u)), "psi": mp.arg(u),
                "R_minus_1": mp.mpf(abs(u)) - 1}


def line_ordinates(t_max: float, dps: int = 15, refine: int = 24,
                   bisections: int = 55) -> list:
    """Critical-line ordinates of f in (0, t_max], by sign change and bisection.

    A sign-change scan can miss a pair and can never invent one, so the count it
    returns is a lower bound; :func:`completeness` is what turns it into a
    statement about the multiset.

    The precision here is deliberately modest, and the reason is worth stating
    because the first version of this function spent thirty-five minutes buying
    digits nothing reads.  The head term is 2(1 - cos(n phi(gamma))) with
    phi(t) ~ 1/t, so its gamma-derivative is O(n^2/gamma^2); at n <= 12,
    gamma >= 10 and three hundred ordinates, an ordinate error of 1e-14 moves
    lambda_n by about 1e-13, while the comparison this feeds is limited by the
    truncation tail at the 1e-4 level.  Each bisection step now reuses the sign
    at the left endpoint instead of re-evaluating it, which is the other half of
    the same lesson: the old loop spent two evaluations per halving and one of
    them was of a value it already had.
    """
    out = []
    with mp.workdps(dps):
        t = mp.mpf("0.05")
        step = _dh_mean_spacing(t_max) / refine
        prev_t, prev_v = t, Z_dh(t, dps=dps)
        while t < t_max:
            t = t + step
            v = Z_dh(t, dps=dps)
            if prev_v != 0 and v != 0 and (prev_v > 0) != (v > 0):
                lo, hi, lo_pos = prev_t, t, prev_v > 0
                for _ in range(bisections):
                    mid = (lo + hi) / 2
                    if (Z_dh(mid, dps=dps) > 0) == lo_pos:
                        lo = mid
                    else:
                        hi = mid
                out.append((lo + hi) / 2)
            prev_t, prev_v = t, v
    return out


def smooth_count(t, dps: int = 30):
    """theta_f(t)/pi: the smooth Davenport-Heilbronn zero count, no constant.

    The constant is *measured* in :func:`completeness` rather than carried over
    from zeta's ``theta(T)/pi + 1``, whose ``+1`` comes from the s(s-1) factor
    in xi that F has no analogue of.
    """
    with mp.workdps(dps):
        return dh_theta(t, dps) / mp.pi


def density(t, dps: int = 30):
    """d/dt of :func:`smooth_count`: [Re psi(3/4 + it/2)/2 - log(pi/5)/2]/pi."""
    with mp.workdps(dps):
        return (mp.re(mp.digamma(mp.mpc(mp.mpf(3) / 4, mp.mpf(t) / 2))) / 2
                - mp.log(mp.pi / 5) / 2) / mp.pi


def completeness(t_max: float, ordinates, quads, dps: int = 20) -> dict:
    """Box count against (line zeros found) + 2 per off-line quadruple below t_max.

    Two zeros per quadruple have positive imaginary part (rho and 1 - conj rho),
    so equality here is the statement that the multiset being summed is the
    whole multiset up to t_max.
    """
    n_line = sum(1 for g in ordinates if float(g) <= t_max)
    n_off = sum(1 for q in quads if float(q["gamma"]) <= t_max)
    box = count_zeros_box(mp.mpc(-1.0, 0.0), mp.mpc(2.0, t_max), dps=dps)
    return {"t_max": t_max, "box": int(box), "line_found": n_line,
            "offline_quadruples_below": n_off,
            "accounted": n_line + 2 * n_off,
            "unaccounted": int(box) - (n_line + 2 * n_off),
            "smooth_count_theta_over_pi": float(smooth_count(t_max)),
            "measured_minus_smooth": float(box) - float(smooth_count(t_max))}


def li_from_zeros(n_values, ordinates, quads, T, dps: int = 25) -> dict:
    """Sum over the multiset, with the smooth tail and the boundary term."""
    work = dps + 10
    with mp.workdps(work):
        Tm = mp.mpf(T)
        gam = [g for g in ordinates if g <= Tm]
        quad_uv = []
        for q in quads:
            if float(q["gamma"]) > float(T):
                continue
            rho = mp.mpc(mp.mpf(q["beta"]), mp.mpf(q["gamma"]))
            quad_uv.append((1 - 1 / rho, 1 - 1 / (1 - rho)))
        n_counted = len(gam) + 2 * len(quad_uv)
        S_T = mp.mpf(n_counted) - smooth_count(Tm, work)
        out = {}
        for n in n_values:
            n = int(n)
            head = mp.fsum(2 * (1 - mp.cos(n * _phi(g))) for g in gam)
            head += mp.fsum(
                4 - 2 * mp.re(mp.power(u, n)) - 2 * mp.re(mp.power(v, n))
                for u, v in quad_uv
            )
            f_T = 2 * (1 - mp.cos(n * _phi(Tm)))
            tail = mp.quad(
                lambda t, n=n: 2 * (1 - mp.cos(n * _phi(t))) * density(t, work),
                [Tm, 2 * Tm, 10 * Tm, 100 * Tm, mp.inf],
            )
            out[n] = head + tail - f_T * S_T
        return {"T": mp.nstr(Tm, 12), "S_T": mp.nstr(S_T, 10),
                "n_line": len(gam), "n_quadruples": len(quad_uv),
                "values": {str(k): mp.nstr(v, 20) for k, v in out.items()}}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--t-max", type=float, default=430.0)
    ap.add_argument("--n-max", type=int, default=12)
    args = ap.parse_args()
    t0 = time.time()
    quads = offline_quadruples()
    for q in quads:
        g = quadruple_growth(q["beta"], q["gamma"])
        q["R_minus_1"] = mp.nstr(g["R_minus_1"], 12)
        q["psi"] = mp.nstr(g["psi"], 12)
        q["period_in_n"] = float(2 * mp.pi / abs(g["psi"]))
    print("quadruples", len(quads), flush=True)
    ords = line_ordinates(args.t_max)
    print("line ordinates", len(ords), "in %.0f s" % (time.time() - t0), flush=True)
    comp = [completeness(t, ords, quads) for t in (100.0, 200.0, 300.0, args.t_max)]
    for c in comp:
        print("completeness", c, flush=True)
    zs = li_from_zeros(range(1, args.n_max + 1), ords, quads, args.t_max)
    print("zero side", zs["values"], flush=True)
    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "t_max": args.t_max,
        "quadruples": quads,
        "n_line_ordinates": len(ords),
        "first_line_ordinates": [mp.nstr(g, 20) for g in ords[:10]],
        "completeness": comp,
        "zero_side": zs,
        "seconds": round(time.time() - t0, 1),
    }
    os.makedirs(ART, exist_ok=True)
    path = os.path.join(ART, "zero_side.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", path)


if __name__ == "__main__":
    main()
