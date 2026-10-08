"""Exact exponent algebra for the Linnik exponent from a zero-free half-plane.

The deduction in RESULTS.md section 3 turns a single-modulus zero-density bound

    sum_{chi mod q} N(sigma, T, chi) << (qT)^{A(sigma)(1-sigma) + eps}

and a zero-free half-plane Re s > theta into the Linnik exponent

    L(theta) = max(2, sup_{1/2 < sigma <= theta} A(sigma)),

and the almost-all exponent max(1, L(theta)/2).  This module computes that
supremum exactly.  Every density exponent below is a rational function of sigma
(and of alpha = log q1 / log q for the divisor refinement) that is monotone on
[1/2, 1], so the envelope min(...) of increasing and decreasing pieces attains
its supremum at an interval endpoint or at a crossing of two pieces.  The exact
route enumerates those points with sympy; `grid_sup` is the independent float
route the tests compare it with.

Sources of the exponents, as stated at source (RESULTS.md section 2):

* ``ingham``: 3/(2 - sigma), Montgomery, Topics in Multiplicative Number
  Theory (LNM 227, 1971), Theorem 12.1; Chen-Gupta-Li (CGL) display (1.4).
* ``huxley``: 3/(3 sigma - 1), Huxley, Acta Arith. 26 (1975); CGL (1.5).
* ``cgl_terms``: the four terms of CGL arXiv:2507.08296v2 Theorem 1.2 for a
  divisor q1 = q^alpha of q, with T = q^{o(1)}, valid for 0.7 <= sigma <= 0.8
  (CGL section 12 uses (1.4) below 0.7 and (1.5) above 0.8), plus the class-II
  exponent 2 of CGL section 12.2.
* ``smooth``: CGL Lemma 12.1 for q that is T-smooth: 15/(3 + 5 sigma).
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations

import numpy as np
import sympy as sp

SIGMA = sp.Symbol("sigma", real=True)
HALF = sp.Rational(1, 2)
CGL_LO = sp.Rational(7, 10)
CGL_HI = sp.Rational(4, 5)
THETA_OAI = sp.Rational(7, 8)


def ingham(s):
    """Montgomery's Ingham-type single-modulus exponent 3/(2 - sigma)."""
    return 3 / (2 - s)


def huxley(s):
    """Huxley's single-modulus exponent 3/(3 sigma - 1)."""
    return 3 / (3 * s - 1)


def cgl_terms(s, alpha=1, alpha_hi=None, c=sp.Rational(1, 3)):
    """CGL Theorem 1.2 exponents for a divisor q1 = q**alpha, T = q**o(1).

    Each entry C satisfies term = q^{C (1 - sigma) + o(1)}:
      T1 (q1^{1/3} q T)^{3(1-s)/(1+s)}   -> (3 + alpha)/(1 + s)
      T2 (qT (q1 T)^{-1/2})^{3(1-s)/s}   -> 3 (1 - alpha/2)/s
      T3 (q1 T)^{-1/2} (qT)^{(21-20s)/6} -> (21 - 20 s - 3 alpha)/(6 (1 - s))
      T4 (qT)^{15(1-s)/(3+5s)}           -> 15/(3 + 5 s)
      class-II zeros (CGL 12.2)          -> 2

    With ``alpha_hi`` the divisor is only known to lie in [q^alpha, q^alpha_hi];
    T1 increases with alpha and T2, T3 decrease, so the worst case takes T1 at
    alpha_hi and T2, T3 at alpha.  ``c`` replaces the exponent 1/3 of q1 in T1;
    it is a lesion and shadow-price knob, CGL prove c = 1/3.
    """
    lo = sp.nsimplify(alpha)
    hi = lo if alpha_hi is None else sp.nsimplify(alpha_hi)
    c = sp.nsimplify(c)
    return [
        3 * (1 + c * hi) / (1 + s),
        3 * (1 - lo / 2) / s,
        (21 - 20 * s - 3 * lo) / (6 * (1 - s)),
        15 / (3 + 5 * s),
        sp.Integer(2) + 0 * s,
    ]


def smooth_terms(s):
    """CGL Lemma 12.1, T-smooth moduli: max(15/(3+5s), 2) on [0.7, 0.8]."""
    return [15 / (3 + 5 * s), sp.Integer(2) + 0 * s]


@dataclass(frozen=True)
class Family:
    """A density family: always-on pieces, plus an optional max-block on a window."""

    name: str
    always: tuple  # callables s -> expr, combined by min
    window_block: tuple = ()  # callables s -> list of exprs, combined by max
    window: tuple = (CGL_LO, CGL_HI)

    def pieces(self, s):
        return [f(s) for f in self.always]

    def block(self, s):
        out = []
        for g in self.window_block:
            out.extend(g(s))
        return out

    def envelope(self, s, side=0):
        """Exact density exponent A(s).  side=-1 evaluates the left limit at a
        window endpoint (window block off), side=+1 the right limit."""
        vals = self.pieces(s)
        lo, hi = self.window
        inside = lo <= s <= hi
        if side == -1 and s == lo:
            inside = False
        if side == +1 and s == hi:
            inside = False
        if self.window_block and inside:
            vals = vals + [sp.Max(*self.block(s))]
        return sp.Min(*vals)


CLASSICAL = Family("classical (Montgomery 1971 + Huxley 1975)", (ingham, huxley))


def cgl_family(alpha=1, alpha_hi=None, c=sp.Rational(1, 3), huxley_on=True):
    """CGL family for divisor exponent alpha (or a window [alpha, alpha_hi]).

    ``huxley_on=False`` removes Huxley's piece: a lesion used by the tests."""
    always = (ingham, huxley) if huxley_on else (ingham,)
    return Family(
        f"CGL Theorem 1.2, divisor q^{alpha}" + ("" if alpha_hi is None else f"..q^{alpha_hi}"),
        always,
        (lambda s, a=alpha, b=alpha_hi, cc=c: cgl_terms(s, a, b, cc),),
    )


CGL = cgl_family(1)
SMOOTH = Family("CGL, T-smooth moduli", (ingham, huxley), (smooth_terms,))


def _real_roots_in(expr_a, expr_b, lo, hi):
    """Exact real roots of expr_a = expr_b in [lo, hi]."""
    num = sp.numer(sp.together(expr_a - expr_b))
    poly = sp.Poly(sp.expand(num), SIGMA)
    if poly.is_zero or poly.degree() <= 0:
        return []
    out = []
    for r in sp.real_roots(poly):
        if lo <= r <= hi:
            out.append(sp.nsimplify(r) if r.is_rational else r)
    return out


def candidates(family: Family, theta):
    """Endpoints and pairwise crossings that can carry the supremum."""
    theta = sp.nsimplify(theta)
    lo, hi = family.window
    pts = {HALF, theta}
    for p in (lo, hi):
        if HALF <= p <= theta:
            pts.add(p)
    exprs = family.pieces(SIGMA) + family.block(SIGMA)
    for a, b in combinations(exprs, 2):
        for r in _real_roots_in(a, b, HALF, theta):
            pts.add(r)
    return sorted(pts, key=lambda v: float(v))


def exact_sup(family: Family, theta=THETA_OAI):
    """Exact sup of A over (1/2, theta], with the argmax.

    Returns (value, sigma_star).  Exact because every piece is monotone on
    [1/2, 1]: on each interval between consecutive candidates the envelope is a
    single monotone piece, so its sup is at an end (one-sided limits at the
    window endpoints are included)."""
    best, arg = None, None
    for c in candidates(family, theta):
        for side in (-1, 0, +1):
            v = sp.nsimplify(family.envelope(c, side)) if c.is_rational else family.envelope(c, side)
            if best is None or bool(v > best):
                best, arg = v, c
    return sp.simplify(best), arg


def linnik_exponent(family: Family, theta=THETA_OAI):
    """L(theta) = max(2, sup A) and its binding sigma."""
    value, arg = exact_sup(family, theta)
    if bool(value < 2):
        return sp.Integer(2), HALF
    return value, arg


def almost_all_exponent(family: Family, theta=THETA_OAI):
    """Exponent for all but O(phi(q) x^{-delta}) residues: max(1, L/2)."""
    value, _ = linnik_exponent(family, theta)
    return sp.Max(1, value / 2)


def grid_sup(family: Family, theta=THETA_OAI, n=200001):
    """Independent float route: dense grid on [1/2, theta], numpy only."""
    s = np.linspace(0.5, float(theta), n)
    s = s[s > 0.5 + 1e-12]
    pieces = [sp.lambdify(SIGMA, f(SIGMA), "numpy")(s) * np.ones_like(s) for f in family.always]
    env = np.minimum.reduce(pieces)
    if family.window_block:
        lo, hi = (float(w) for w in family.window)
        mask = (s >= lo) & (s <= hi)
        blk = [
            sp.lambdify(SIGMA, e, "numpy")(s) * np.ones_like(s)
            for g in family.window_block
            for e in g(SIGMA)
        ]
        bmax = np.maximum.reduce(blk)
        env = np.where(mask, np.minimum(env, bmax), env)
    i = int(np.argmax(env))
    return max(2.0, float(env[i])), float(s[i])


def divisor_profile(alpha):
    """L for a modulus with a divisor q1 = q^alpha, theta = 7/8 (exact)."""
    return linnik_exponent(cgl_family(sp.nsimplify(alpha)))[0]


def proof_bookkeeping(A, theta, eps0):
    """Parameters and term exponents of Lemma 5 (RESULTS.md section 3).

    For X >= q^(A + eps0), worst case q = X^(1/(A + eps0)), returns the exponent
    of X in each of the three bounds of Lemma 5 (log factors dropped) and the
    claimed saving kappa.  Exact rationals throughout."""
    A, theta, eps0 = (sp.nsimplify(v) for v in (A, theta, eps0))
    lam = eps0 / (A + eps0)
    eta = lam / (4 * A)
    eps = lam * (1 - theta) / 8
    k = int(sp.ceiling(3 / eta)) + 1 if eta > 0 else 1  # eta = 0: no height decay to spend
    kappa = lam * (1 - theta) / 4
    q_exp = 1 / (A + eps0)
    high = 1 + q_exp + eta * (1 - k)
    first = sp.Rational(1, 2) + q_exp + eta
    # integrand (qT0)^{A(1-s)+2 eps} X^s is largest at s = theta here
    second = 1 - (1 - theta) * (1 - A * (q_exp + eta)) + 2 * eps * (q_exp + eta)
    return {
        "lambda": lam, "eta": eta, "eps": eps, "k": k, "kappa": kappa,
        "q_exp": q_exp, "high": high, "first": first, "second": second,
    }


#: minimiser of the divisor profile: 2 + a/3 = B(a), i.e. a^2 + 31 a - 30 = 0.
ALPHA_STAR = (sp.sqrt(1081) - 31) / 2
LAMBDA_STAR = (sp.sqrt(1081) - 19) / 6


def report():
    rows = {}
    for fam in (CLASSICAL, CGL, SMOOTH):
        val, arg = linnik_exponent(fam)
        rows[fam.name] = {
            "L": str(val),
            "L_float": float(val),
            "sigma_star": str(arg),
            "almost_all": str(almost_all_exponent(fam)),
            "grid": grid_sup(fam),
        }
    thetas = ["1/2", "3/5", "2/3", "7/10", "5/7", "3/4", "7/8", "11/12", "99/100"]
    rows["theta_profile_CGL"] = {
        t: str(linnik_exponent(CGL, sp.Rational(t))[0]) for t in thetas
    }
    rows["divisor_profile"] = {
        a: float(divisor_profile(sp.Rational(a)))
        for a in ["1", "19/20", "47/50", "93/100", "12/13", "9/10", "4/5", "1/2"]
    }
    rows["alpha_star"] = float(ALPHA_STAR)
    rows["lambda_star"] = float(LAMBDA_STAR)
    return rows


if __name__ == "__main__":  # pragma: no cover
    import json

    print(json.dumps(report(), indent=2))
