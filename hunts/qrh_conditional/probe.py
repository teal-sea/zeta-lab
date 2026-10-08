"""Hunt #121: which priced walls move under QRH(theta), and by how much.

QRH(theta) is the HYPOTHESIS "for every Dirichlet character chi mod q and every
s with Re s > theta, L(s, chi) is nonzero except the principal pole", with
theta = 7/8 (OpenAI preprint of 2026-09-30) and theta = 11/12 (companion of
2026-10-05).  Neither has been replayed by anyone known here.  Nothing in this
file turns the hypothesis into a theorem; every number below is conditional on
it, and the exponents are consequences of UPPER_BOUND.md's displayed
inequalities plus the one standard step

    QRH(theta)  =>  psi(x; q, a) = x/phi(q) + O(x^theta (log qx)^2)  uniformly,

whose dependencies RESULTS.md section 1 lists (Davenport chapters 16, 17, 19,
20).  Three computations:

  A. exact exponent arithmetic (fractions, no floats) for every component of
     hunts/prime_pair_error that reads a prime-counting remainder;
  B. the height past which x^theta (log x)^2 beats an explicit, published
     de la Vallee Poussin remainder, as a root of a one-variable equation in
     u = log x, bisected at dps 30;
  C. the Li-coefficient algebra: what a strip does to |1 - 1/rho| for a
     hypothetical off-line zero, with a numeric illustration.

Run:   .venv/bin/python hunts/qrh_conditional/probe.py
Writes hunts/qrh_conditional/results.json.  Pinned by test_qrh_conditional.py.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Fr
from pathlib import Path

import mpmath
from mpmath import mp

HERE = Path(__file__).resolve().parent

THETAS = {"7/8": Fr(7, 8), "11/12": Fr(11, 12), "1/2": Fr(1, 2)}

# Explicit de la Vallee Poussin remainder used in section B.  Johnston and
# Yang, "Some explicit estimates for the error term in the prime number
# theorem", arXiv:2204.01980, Theorem 1.1: for all x >= 2,
#     |psi(x) - x| <= A x (log x)^B exp(-C sqrt(log x)),  A = 9.39, B = 1.515,
#     C = 0.8274.
# Read from the arXiv HTML rendering on 2026-10-08; the journal version was not
# checked, so the digits are hedged to that reading.  SW_EFFECTIVE.md names no
# explicit constant of its own, which is why one is imported here.
JY = {"A": "9.39", "B": "1.515", "C": "0.8274", "x_min": 2,
      "source": "Johnston and Yang, arXiv:2204.01980, Theorem 1.1 (arXiv HTML, read 2026-10-08)"}

# The first ordinate of zeta (AGENTS.md ground truth) and the verified height of
# RH as cited in docs/05 (Platt and Trudgian 2021, 3e12).  Both are inputs to
# the illustration in section C, not results of it.
GAMMA_1 = "14.134725141734694"
T0_VERIFIED = "3e12"


# ---------------------------------------------------------------------------
# A. exponent arithmetic, exact
# ---------------------------------------------------------------------------

def strip_exponents(theta: Fr) -> dict[str, Fr]:
    """Every exponent in RESULTS.md, as a function of theta, in exact fractions.

    Inputs are UPPER_BOUND.md's displayed inequalities and the uniform
    remainder Delta(x; q, a) << x^theta (log qx)^2.  Each line names the
    display it comes from; RESULTS.md carries the derivation in prose.
    """
    if not (Fr(1, 2) <= theta < 1):
        raise ValueError("a strip exponent lies in [1/2, 1)")
    out: dict[str, Fr] = {}
    # (29): T_N = sum Delta(t)^2 + sum (Delta(N) - Delta(t))^2 <= 4 N max|Delta|^2
    out["rank1_T_N_exponent"] = 1 + 2 * theta            # N^{1+2theta} (log N)^4
    out["rank1_gap_to_31"] = (1 + 2 * theta) - 2         # power short of N^{2+eps}
    out["rank1_saving_over_N3"] = 3 - (1 + 2 * theta)    # power saved over N^3 L^{-2H}
    # pointwise level of distribution: x^theta (log qx)^2 < x/phi(q) needs
    # q < x^{1-theta-eps}
    out["pointwise_level"] = 1 - theta
    # section 5 of UPPER_BOUND.md with Q = N^a under the strip:
    #   cross term   (8 |P|^2 |R|^2 summed over arcs)  << Q N^{1+2theta} L^5
    #   fourth power (2 |R|^4 summed over arcs)        << Q^5 N^{4theta-1} L^8
    #                                                 and << Q^2 N^{1+2theta} L^6
    #   minor arcs, (20), unchanged                    << N^3 L^6 / Q + N^{13/5} L^6
    out["arc_exponent_cross_constraint"] = 1 - theta           # a + 1 + 2theta <= 3 - a
    out["arc_exponent_quartic_constraint"] = (2 - 2 * theta) / 3  # 5a + 4theta - 1 <= 3 - a
    a = min(out["arc_exponent_cross_constraint"], out["arc_exponent_quartic_constraint"])
    out["arc_exponent"] = a
    out["circle_total_exponent"] = 3 - a                       # (7 + 2theta)/3
    out["circle_saving_over_N3"] = a
    out["circle_gap_to_target"] = (3 - a) - 2
    # CHHL Theorem 2 + a bound E << N^c forces Theta <= (c - 1)/2
    out["bootstrap_theta"] = ((3 - a) - 1) / 2                 # (2 + theta)/3
    out["bootstrap_drift"] = out["bootstrap_theta"] - theta    # 2(1 - theta)/3 > 0
    # RESULTS.md section 17, Theorem A: W << N^{Theta + Theta_chi} L^4
    out["theorem_A_exponent"] = 2 * theta
    out["theorem_A_gap_to_T"] = 2 * theta - 1
    # RESULTS.md section 18, Theorem B: E = Omega(N^{1 + 2 Theta_chi - eps}), capped
    out["theorem_B_cap"] = 1 + 2 * theta
    # FRONTIER_2026_09_12.md: B_N = N R(N) + R(N)^2/2 + O(N L^2), M_N = 2|B_N|^2/N
    out["frontier_M_N_exponent"] = 1 + 2 * theta
    # FRONTIER_2026_09_12.md: D_N from the envelope |R(u)| << u^theta L^2 at K = sqrt N
    out["frontier_D_N_exponent"] = (1 + theta) / 2
    # section 6 of UPPER_BOUND.md keeps Q = sqrt(N)/3; the partial-summation
    # factor (1 + N|beta|) <= Q then costs N^{1/2}, so the strip's pointwise
    # bound for 2 <= q <= R_0 gives Q N^{1+2theta} L^5 = N^{3/2 + 2theta} L^5
    out["rank3_sqrt_arc_exponent"] = Fr(3, 2) + 2 * theta
    return out


def exponent_table() -> dict[str, dict[str, str]]:
    return {name: {k: str(v) for k, v in strip_exponents(t).items()} for name, t in THETAS.items()}


# ---------------------------------------------------------------------------
# B. crossover heights
# ---------------------------------------------------------------------------

def log_ratio_jy(u, theta, strip_const=1):
    """log[ strip_const x^theta (log x)^2 ] - log[ A x (log x)^B e^{-C sqrt(log x)} ], x = e^u.

    Negative means the strip-shaped bound is the smaller one at that height.
    """
    A, B, C = mp.mpf(JY["A"]), mp.mpf(JY["B"]), mp.mpf(JY["C"])
    u = mp.mpf(u)
    return (mp.log(strip_const) + (mp.mpf(theta) - 1) * u + (2 - B) * mp.log(u)
            - mp.log(A) + C * mp.sqrt(u))


def log_ratio_shape(u, theta, strip_const=1, c1=None):
    """Same comparison against the bare shape x exp(-c1 sqrt(log x)) with K = 1.

    This is a labelled convention (the hunt's own SW_EFFECTIVE.md uses K = 1 the
    same way), not a published theorem; c1 defaults to Johnston-Yang's C.
    """
    c1 = mp.mpf(JY["C"]) if c1 is None else mp.mpf(c1)
    u = mp.mpf(u)
    return mp.log(strip_const) + (mp.mpf(theta) - 1) * u + 2 * mp.log(u) + c1 * mp.sqrt(u)


def sign_change_roots(f, u_lo, u_hi, step, tol="1e-20"):
    """Every root of f on [u_lo, u_hi] found by a grid scan then bisection.

    A grid of pitch `step` can miss a pair of roots closer than `step`; the
    pitch used below (1/4 in u) is far below the root separations observed.
    """
    u_lo, u_hi, step, tol = mp.mpf(u_lo), mp.mpf(u_hi), mp.mpf(step), mp.mpf(tol)
    roots = []
    a = u_lo
    fa = f(a)
    while a < u_hi:
        b = min(a + step, u_hi)
        fb = f(b)
        if fa == 0:
            roots.append(a)
        elif fa * fb < 0:
            lo, hi, flo = a, b, fa
            while hi - lo > tol:
                mid = (lo + hi) / 2
                fm = f(mid)
                if fm == 0:
                    lo = hi = mid
                elif flo * fm < 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            roots.append((lo + hi) / 2)
        a, fa = b, fb
    return roots


def crossovers(theta: Fr, strip_consts=(1, 10, 100, 10**4), dps=30) -> dict:
    """For each convention constant on the strip side, the heights at which
    the two bounds cross, as u = log x, x and log10 x."""
    out = {}
    with mp.workdps(dps):
        th = mp.mpf(theta.numerator) / theta.denominator
        for cst in strip_consts:
            rec = {}
            for label, f in (("johnston_yang", lambda u, c=cst: log_ratio_jy(u, th, c)),
                              ("bare_shape_K1", lambda u, c=cst: log_ratio_shape(u, th, c))):
                roots = sign_change_roots(f, mp.log(2), 5000, mp.mpf(1) / 4)
                rec[label] = {
                    "roots_u": [mpmath.nstr(r, 17) for r in roots],
                    "crossover_u": mpmath.nstr(roots[-1], 17) if roots else None,
                    "crossover_log10_x": mpmath.nstr(roots[-1] / mp.log(10), 17) if roots else None,
                    "crossover_x": mpmath.nstr(mp.e ** roots[-1], 6) if roots else None,
                    "sign_at_u_5000": "negative" if f(5000) < 0 else "positive",
                }
            out[str(cst)] = rec
    return out


# ---------------------------------------------------------------------------
# C. Li coefficients: the per-zero factor |1 - 1/rho|
# ---------------------------------------------------------------------------

def r_direct(beta, gamma):
    """|1 - 1/rho'| for the zero rho' = (1 - beta) + i gamma, i.e. the partner,
    reflected in Re s = 1/2, of a zero at beta + i gamma with beta > 1/2.
    Computed directly from the complex number, no algebra."""
    rho = mp.mpc(1 - mp.mpf(beta), mp.mpf(gamma))
    return abs(1 - 1 / rho)


def r2_minus_1_closed(beta, gamma):
    """The algebra: |1 - 1/rho'|^2 - 1 = (2 beta - 1) / ((1 - beta)^2 + gamma^2)."""
    beta, gamma = mp.mpf(beta), mp.mpf(gamma)
    return (2 * beta - 1) / ((1 - beta) ** 2 + gamma ** 2)


def r_cap(theta, gamma):
    """The largest |1 - 1/rho| any zero at height gamma can have under a strip
    Re rho <= theta (and, by the functional equation, Re rho >= 1 - theta)."""
    theta, gamma = mp.mpf(theta), mp.mpf(gamma)
    return mp.sqrt((theta ** 2 + gamma ** 2) / ((1 - theta) ** 2 + gamma ** 2))


def li_illustration(dps=30) -> dict:
    out = {}
    with mp.workdps(dps):
        g1, t0 = mp.mpf(GAMMA_1), mp.mpf(T0_VERIFIED)
        # algebra check at three points
        checks = []
        for beta, gamma in (("0.875", GAMMA_1), ("0.75", "100"), ("0.9166666666666666667", "0.5")):
            direct = r_direct(beta, gamma) ** 2 - 1
            closed = r2_minus_1_closed(beta, gamma)
            checks.append({"beta": beta, "gamma": gamma,
                           "direct": mpmath.nstr(direct, 20), "closed": mpmath.nstr(closed, 20),
                           "defect": mpmath.nstr(abs(direct - closed), 3)})
        out["algebra_checks"] = checks
        # the cap at two heights, three strips, plus the no-strip cap (theta -> 1)
        heights = {"gamma_1": g1, "T0_verified": t0}
        caps = {}
        for hname, h in heights.items():
            row = {}
            for tname, th in (("7/8", mp.mpf(7) / 8), ("11/12", mp.mpf(11) / 12), ("1", mp.mpf(1))):
                r = r_cap(th, h)
                logr = mp.log(r)
                row[tname] = {
                    "r_cap": mpmath.nstr(r, 20),
                    "r_cap_minus_1": mpmath.nstr(r - 1, 12),
                    "log_r_cap": mpmath.nstr(logr, 12),
                    "n_at_which_r_cap_pow_n_is_2": mpmath.nstr(mp.log(2) / logr, 12),
                }
            # ratio of growth exponents, strip over no strip; tends to 2theta - 1
            for tname in ("7/8", "11/12"):
                row[tname]["log_r_ratio_to_no_strip"] = mpmath.nstr(
                    mp.mpf(row[tname]["log_r_cap"]) / mp.mpf(row["1"]["log_r_cap"]), 12)
            caps[hname] = row
        out["caps"] = caps
        out["limit_of_log_r_ratio_as_gamma_grows"] = {"7/8": "3/4", "11/12": "5/6"}
        out["r_cap_at_gamma_0"] = {"7/8": "7", "11/12": "11"}   # theta / (1 - theta)
    return out


# ---------------------------------------------------------------------------

def main(out_path: Path) -> dict:
    results = {
        "hypothesis": ("QRH(theta): L(s, chi) != 0 for Re s > theta, every chi mod every q, "
                       "except the principal pole; theta = 7/8 and 11/12.  A hypothesis "
                       "throughout; withdrawn or refuted, every number here is void."),
        "A_exponents": exponent_table(),
        "B_crossover": {name: crossovers(t) for name, t in THETAS.items() if name != "1/2"},
        "B_remainder_used": JY,
        "C_li": li_illustration(),
        "cited_not_recomputed": {
            "de_bruijn_newman_under_strip_7_8": "9/32 = 0.28125, from the lab's document 38 section 6",
            "de_bruijn_newman_record": "0.2, Platt and Trudgian 2021, as cited in docs/05",
            "verified_height_T0": T0_VERIFIED,
        },
    }
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    return results


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=HERE / "results.json")
    args = ap.parse_args()
    res = main(args.out)
    for name, row in res["A_exponents"].items():
        print(f"theta = {name}: T_N ~ N^{row['rank1_T_N_exponent']}, gap to (31) {row['rank1_gap_to_31']}, "
              f"circle total N^{row['circle_total_exponent']} (a = {row['arc_exponent']}), "
              f"Theorem A N^{row['theorem_A_exponent']}")
    for name, row in res["B_crossover"].items():
        for cst, rec in row.items():
            print(f"theta = {name}, C = {cst}: JY crossover u = {rec['johnston_yang']['crossover_u']} "
                  f"(log10 x = {rec['johnston_yang']['crossover_log10_x']}), roots {rec['johnston_yang']['roots_u']}; "
                  f"bare shape u = {rec['bare_shape_K1']['crossover_u']}")
    for h, row in res["C_li"]["caps"].items():
        print(h, {k: (v["r_cap_minus_1"], v["n_at_which_r_cap_pow_n_is_2"]) for k, v in row.items()})
    print("wrote", args.out)
