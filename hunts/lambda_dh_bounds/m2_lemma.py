"""M2 as a lemma: an independent, fully decided verification of the bound.

Companion to ``M2-LEMMA.md``.  ``winding.py`` computes the uniform bound
``M2 >= sup |H_t''|`` that makes its segment-argument winding count valid,
from a shifted-contour derivation written in prose.  This file re-derives
the same bound from the lemma's statement, in a second implementation that
shares no line of code with ``winding.second_derivative_bound``, and turns
every constant the prose asserted into a reported ball with exact endpoints.

Four routes to |H_t''| live here, and they check each other:

  R1  ``shifted_bound``    the lemma's bound.  Independent re-implementation
                           of the shifted-contour majorant, exact rational
                           panel endpoints, every hypothesis of the proof
                           reported as a decided predicate rather than
                           assumed.
  R2  ``direct_bound``     the unshifted majorant
                           int_0^inf e^{t s^2} |Phi_DH(s)| s^2 cosh(y_hi s) ds.
                           Valid, fully decided, and roughly 10^86 times
                           larger: it is what the lemma would give without
                           the contour shift, and it is why the shift is the
                           load-bearing step rather than an optimisation.
  R3  ``H2_ball``          a pointwise ENCLOSURE of H_t''(z) by Arb's
                           rigorous integrator, with its own two tail balls.
                           Gives a decided LOWER bound for sup |H_t''| over
                           the box, so the cushion M2 / sup becomes decided
                           instead of measured.
  R4  ``measured_sup``     the float route ``winding.measured_h2_guard``
                           already runs (mpmath, Gauss-Legendre), kept so the
                           published cushion 55.7 can be reproduced.

R3 cannot replace R1.  A ball evaluation of H_t'' over a segment of the box
carries the segment's own width, and at Re z ~ 240 the true |H_t''| is ~1e-80
against an O(1) integrand, so an enclosure over anything wider than ~1e-80
contains 0 and decides nothing.  That asymmetry (pointwise enclosures cheap,
uniform enclosures impossible) is exactly why the uniform bound has to come
from a contour shift, and it is worth stating because it is also the reason
the guard in ``winding.py`` can only ever be a finite sample.

Nothing here writes to ``winding_results.json`` or changes any decided
winding number.  It writes ``m2_lemma_results.json`` only.

Backend python-flint 0.9.0 (Arb) throughout for the decided parts; the one
float route is labelled measured and is used for nothing but reproduction.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
FLOW_REPAIR = os.path.abspath(os.path.join(HERE, os.pardir, "flow_repair"))

from flint import acb, arb, ctx, fmpq  # noqa: E402

from instrument import (  # noqa: E402
    _default_nmax,
    _exact_q,
    _omega_tail_upper,
    _prec_guard,
    _q_to_arb,
    default_U,
    kappa_ball,
)

RESULTS_PATH = os.path.join(HERE, "m2_lemma_results.json")
BACKEND = "python-flint 0.9.0 (Arb)"

# the two boxes, verbatim from winding_results.json (exact dyadic rationals)
BOX_T1 = (Fraction(122929, 512), Fraction(123185, 512),
          Fraction(3, 512), Fraction(61, 1024))
T1 = Fraction(23, 400)
BOX_T2 = (Fraction(245909, 1024), Fraction(123159, 512),
          Fraction(3, 1024), Fraction(35, 1024))
T2 = Fraction(36, 625)

# the two M2 values winding.py decided and the count consumed
M2_WINDING = {"23/400": 1.1886642645115153e-78, "36/625": 1.137082903400534e-78}


def _fr(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


def _ball(b: arb) -> dict:
    """A ball reported by its exact endpoints, as floats and as strings."""
    return {
        "lower": float(b.lower()),
        "upper": float(b.upper()),
        "str": b.str(12, radius=True),
    }


# ---------------------------------------------------------------------------
# Step 3 of the proof: the majorant for the theta-like sum
# ---------------------------------------------------------------------------


def omega_majorant(rho: arb, route: str = "best", collapse: bool = True) -> tuple[arb, str]:
    """An upper bound for Omega(rho) := sum_{n>=1} n exp(-pi n^2 rho / 5).

    Three routes, each proved in M2-LEMMA.md step 3, all valid for decided
    rho > 0.  ``rho`` may be a wide ball (a panel hull); the returned ball's
    upper endpoint then dominates Omega at every point of that ball, because
    each route is evaluated by ball arithmetic on the ball.

      "unimodal"   f(x) = x e^{-a x^2} rises then falls, so all but the at
                   most two terms straddling the peak are dominated by
                   disjoint unit integrals of f:
                       Omega <= int_0^inf f + 2 max f
                              = 1/(2a) + 2 e^{-1/2} / sqrt(2a),  a = pi rho/5.
      "geometric"  n^2 >= n for n >= 1 gives Omega <= sum n q^n
                   = q/(1-q)^2 with q = e^{-a}; needs decided q < 1.
      "truncated"  the honest sum to N plus the tail of
                   ``instrument._omega_tail_upper`` at the ball's lower rho.
                   Sharpest of the three; used only to CHECK the other two,
                   never to shrink the published M2.

    Returns (bound, route_used).  "best" tries all three and keeps the one
    with the smallest upper endpoint; ties fall through to "unimodal", which
    is finite for every rho > 0.  ``collapse`` returns the bound as a point
    ball at its own upper endpoint, which is what a majorant needs; pass
    False when the ball's width is itself the object under test, as in
    ``check_omega_routes``, since a collapsed ball cannot show overlap.
    """
    a = arb.pi() * rho / 5
    if not (a > 0):
        raise ValueError("omega_majorant needs a decided rho > 0")
    cands: list[tuple[arb, str]] = []
    b_uni = 1 / (2 * a) + 2 * (arb(-1) / 2).exp() / (2 * a).sqrt()
    cands.append((b_uni, "unimodal"))
    q = (-a).exp()
    one_minus = 1 - q
    if one_minus.lower() > 0:
        cands.append((q / (one_minus * one_minus), "geometric"))
    if route in ("truncated", "best"):
        rho_lo = arb(rho.lower())
        if rho_lo > 0:
            N = min(max(int(math.ceil(math.sqrt(60.0 * 5.0 /
                                                (math.pi * float(rho_lo))))), 8),
                    4000)
            s = arb(0)
            for n in range(1, N + 1):
                s = s + n * (-a * n * n).exp()
            tl = _omega_tail_upper(rho_lo, N)
            if tl is not None:
                cands.append((s + tl, "truncated"))
    if route != "best":
        for b, name in cands:
            if name == route:
                return (arb(b.abs_upper()) if collapse else b), name
        raise ValueError(f"route {route!r} unavailable at this rho")
    best = min(cands, key=lambda bn: float(bn[0].abs_upper()))
    return (arb(best[0].abs_upper()) if collapse else best[0]), best[1]


def check_omega_routes(prec: int = 300, n_probe: int = 24) -> dict:
    """Try to FALSIFY the two closed-form majorants of step 3.

    The proof that each closed form dominates Omega is in M2-LEMMA.md; this
    is the attack on it.  At each probe rho the sharp truncated-sum-plus-tail
    enclosure of Omega is computed, and a closed form is REFUTED when its
    upper endpoint is decidedly below the sharp bound's lower endpoint, which
    would prove it is not an upper bound for Omega.  Ties are not refutations
    and are not scored as such: at large rho every route collapses onto the
    n = 1 term e^{-pi rho/5} and the two balls overlap, which is agreement,
    not failure.  ``strictly_above`` records where the gap is decided, so a
    reader can see that the non-refutations are mostly strict.
    """
    out = {"n_probe": n_probe, "prec_bits": prec,
           "test": ("refuted iff closed_form.upper() < sharp.lower(); "
                    "overlap is agreement, not refutation"),
           "rows": []}
    refuted = []
    with _prec_guard(prec):
        for k in range(n_probe):
            # rho over the range the panels actually meet: e^{2s} cos 2v for
            # s in [0, 5] and cos 2v ~ 1/128, plus the unshifted rho = e^{2s}
            expo = Fraction(-8) + Fraction(20 * k, n_probe)
            rho = (_q_to_arb(expo)).exp()
            sharp, _ = omega_majorant(rho, "truncated", collapse=False)
            uni, _ = omega_majorant(rho, "unimodal", collapse=False)
            row = {"rho": float(rho), "sharp_upper": float(sharp.abs_upper()),
                   "unimodal_upper": float(uni.abs_upper())}
            row["unimodal_refuted"] = bool(uni.upper() < sharp.lower())
            row["unimodal_strictly_above"] = bool(uni.lower() > sharp.upper())
            if row["unimodal_refuted"]:
                refuted.append(["unimodal", float(rho)])
            try:
                geo, _ = omega_majorant(rho, "geometric", collapse=False)
                row["geometric_upper"] = float(geo.abs_upper())
                row["geometric_refuted"] = bool(geo.upper() < sharp.lower())
                row["geometric_strictly_above"] = bool(geo.lower() > sharp.upper())
                if row["geometric_refuted"]:
                    refuted.append(["geometric", float(rho)])
            except ValueError:
                row["geometric_upper"] = None
            out["rows"].append(row)
    out["refutations"] = refuted
    out["all_dominate"] = not refuted
    out["verdict"] = "PASS" if not refuted else "FAIL"
    return out


# ---------------------------------------------------------------------------
# R1: the lemma's bound (shifted contour)
# ---------------------------------------------------------------------------


def shifted_bound(
    x_lo: Fraction,
    y_hi: Fraction,
    t: Fraction,
    eps: Fraction,
    prec: int = 300,
    S: Fraction = Fraction(5),
    n_panels: int = 800,
    omega_route: str = "unimodal_or_geometric",
) -> dict:
    """M2 for one contour height v = pi/4 - eps, with every hypothesis decided.

    Independent re-implementation of the proof in M2-LEMMA.md.  Differences
    from ``winding.second_derivative_bound``, all deliberate: exact rational
    panel endpoints (so panel coverage of [0, S] is exact rather than
    inherited from a rounded step), each hypothesis of the proof returned as
    a named decided predicate with its ball, and the tail's own constants
    reported.  Returns None-valued ``M2`` when a hypothesis fails to decide,
    never a bound.
    """
    t0 = time.time()
    checks: dict = {}
    with _prec_guard(prec):
        t_b = _q_to_arb(_exact_q(t))
        x_b = _q_to_arb(_exact_q(x_lo))
        y_b = _q_to_arb(_exact_q(y_hi))
        S_b = _q_to_arb(_exact_q(S))
        v = arb.pi() / 4 - _q_to_arb(_exact_q(eps))
        cos2v = (2 * v).cos()

        # hypothesis (H1): 0 < v < pi/4, so the shifted rays stay inside the
        # strip of holomorphy |Im u| < pi/4 and cos(2 Im u) stays positive.
        checks["H1_v_positive"] = bool(v > 0)
        checks["H1_v_below_pi_over_4"] = bool(v < arb.pi() / 4)
        checks["H1_cos2v_positive"] = bool(cos2v > 0)
        checks["cos2v"] = _ball(cos2v)
        checks["v"] = _ball(v)
        if not (checks["H1_v_positive"] and checks["H1_v_below_pi_over_4"]
                and checks["H1_cos2v_positive"]):
            return {"M2": None, "eps": _fr(eps), "checks": checks,
                    "reason": "H1 undecided"}

        # main range [0, S]: exact rational panels, ball hull per panel
        total = arb(0)
        routes_used: dict[str, int] = {}
        for j in range(n_panels):
            a_q = S * Fraction(j, n_panels)
            b_q = S * Fraction(j + 1, n_panels)
            s = _q_to_arb(a_q).union(_q_to_arb(b_q))
            width = _q_to_arb(b_q - a_q)
            rho = (2 * s).exp() * cos2v
            om, route = omega_majorant(
                rho, "best" if omega_route == "best" else "unimodal")
            if omega_route == "unimodal_or_geometric":
                try:
                    geo, _ = omega_majorant(rho, "geometric")
                    if geo.abs_upper() < om.abs_upper():
                        om, route = geo, "geometric"
                except ValueError:
                    pass
            routes_used[route] = routes_used.get(route, 0) + 1
            integrand = (
                (s * s + v * v)
                * (t_b * s * s).exp()
                * 4
                * (3 * s / 2).exp()
                * om
                * (y_b * s).cosh()
            )
            total = total + arb(integrand.abs_upper()) * width
        checks["omega_routes_used"] = routes_used

        # tail [S, inf): hypotheses (H2) q_S <= 29/100 and (H3) c > 0
        V = (2 * S_b).exp()
        q_S = (-arb.pi() / 5 * V * cos2v).exp()
        beta = arb(3) / 2 + y_b + 2          # 3/2 + y_hi + k, k = 2
        c = arb.pi() / 5 * cos2v - (t_b * S_b * S_b + beta * S_b) / V
        checks["H2_qS_below_29_100"] = bool(q_S < arb(fmpq(29, 100)))
        checks["H3_c_positive"] = bool(c > 0)
        checks["q_S"] = _ball(q_S)
        checks["c"] = _ball(c)
        checks["beta"] = _ball(beta)
        checks["V_eq_exp_2S"] = float(V)
        if not (checks["H2_qS_below_29_100"] and checks["H3_c_positive"]):
            return {"M2": None, "eps": _fr(eps), "checks": checks,
                    "reason": "tail hypothesis undecided"}
        tail = 4 * (2 * v).exp() * (-c * V).exp() / (c * V)

        # the far-side connector, bounded by the same c: it is the R -> inf
        # limit that licenses the contour shift, and it is decided here at
        # R = S so the proof's "vanishes" carries a number.
        connector_at_S = v * 8 * (2 * v).exp() * (-c * V).exp()

        J = total + tail
        M2 = (-x_b * v - t_b * v * v).exp() * J
        M2_up = arb(M2.abs_upper())
        out = {
            "M2": M2_up,
            "M2_upper_float": float(M2_up.abs_upper()),
            "M2_ball": _ball(M2),
            "v": f"pi/4 - {_fr(eps)}",
            "eps": _fr(eps),
            "prec_bits": prec,
            "S": _fr(S),
            "n_panels": n_panels,
            "J_upper_float": float(J.abs_upper()),
            "J_ball": _ball(J),
            "panel_sum_upper_float": float(total.abs_upper()),
            "tail_upper_float": float(tail.abs_upper()),
            "connector_bound_at_R_eq_S": float(connector_at_S.abs_upper()),
            "prefactor_exp_minus_xv_minus_tv2": float(
                (-x_b * v - t_b * v * v).exp().abs_upper()),
            "checks": checks,
            "scope": (f"sup |H_t''| over Re z >= {_fr(x_lo)}, "
                      f"|Im z| <= {_fr(y_hi)}"),
            "backend": BACKEND,
            "seconds": round(time.time() - t0, 2),
        }
    return out


def shifted_bound_best(
    x_lo: Fraction, y_hi: Fraction, t: Fraction, prec: int = 300,
    eps_list: tuple[Fraction, ...] = (Fraction(1, 128), Fraction(1, 256),
                                      Fraction(1, 512), Fraction(1, 1024)),
    **kw,
) -> dict:
    """Smallest M2 over the eps candidates; every candidate is itself decided."""
    cands = [shifted_bound(x_lo, y_hi, t, e, prec=prec, **kw) for e in eps_list]
    live = [c for c in cands if c.get("M2") is not None]
    if not live:
        raise ValueError("no eps candidate decided its hypotheses")
    best = min(live, key=lambda c: c["M2_upper_float"])
    best["all_candidates"] = [
        {"eps": c["eps"], "M2_upper_float": c.get("M2_upper_float"),
         "decided": c.get("M2") is not None} for c in cands
    ]
    return best


# ---------------------------------------------------------------------------
# R2: the unshifted majorant (the route the task named first)
# ---------------------------------------------------------------------------


def direct_bound(
    y_hi: Fraction, t: Fraction, prec: int = 300, S: Fraction = Fraction(5),
    n_panels: int = 800,
) -> dict:
    """int_0^inf e^{t s^2} |Phi_DH(s)| s^2 cosh(y_hi s) ds, decided.

    The bound that follows from |cos(zu)| <= cosh(y_hi u) applied to the
    defining integral with no contour shift.  It is a genuine uniform bound
    on the whole strip |Im z| <= y_hi and it needs neither the evenness of
    Phi_DH nor Cauchy's theorem, so it is the cheapest complete proof of
    "H_t'' is bounded on the strip".  It is also useless for the winding
    count: it does not see Re z at all, so it cannot carry the factor
    e^{-x_lo v} that makes M2 ~ 1e-78 rather than ~1e+4.
    """
    t0 = time.time()
    with _prec_guard(prec):
        t_b = _q_to_arb(_exact_q(t))
        y_b = _q_to_arb(_exact_q(y_hi))
        S_b = _q_to_arb(_exact_q(S))
        total = arb(0)
        for j in range(n_panels):
            a_q = S * Fraction(j, n_panels)
            b_q = S * Fraction(j + 1, n_panels)
            s = _q_to_arb(a_q).union(_q_to_arb(b_q))
            width = _q_to_arb(b_q - a_q)
            om, _ = omega_majorant((2 * s).exp(), "best")
            integrand = ((t_b * s * s).exp() * 4 * (3 * s / 2).exp() * om
                         * s * s * (y_b * s).cosh())
            total = total + arb(integrand.abs_upper()) * width
        V = (2 * S_b).exp()
        q_S = (-arb.pi() / 5 * V).exp()
        beta = arb(3) / 2 + y_b + 2
        c = arb.pi() / 5 - (t_b * S_b * S_b + beta * S_b) / V
        ok = bool(q_S < arb(fmpq(29, 100))) and bool(c > 0)
        tail = 4 * (-c * V).exp() / (c * V) if ok else None
        M = total + (tail if tail is not None else arb(0))
        out = {
            "M_direct_upper_float": float(M.abs_upper()) if ok else None,
            "panel_sum_upper_float": float(total.abs_upper()),
            "tail_upper_float": float(tail.abs_upper()) if ok else None,
            "hypotheses_decided": ok,
            "c": _ball(c),
            "prec_bits": prec, "S": _fr(S), "n_panels": n_panels,
            "scope": f"sup |H_t''| over the whole strip |Im z| <= {_fr(y_hi)}",
            "backend": BACKEND,
            "seconds": round(time.time() - t0, 2),
        }
    return out


# ---------------------------------------------------------------------------
# R3: pointwise enclosures of H_t''
# ---------------------------------------------------------------------------


def _h2_integrand(z_b: acb, t_b: arb, N: int, kap: arb):
    """The truncated integrand of H_t''(z) = -int e^{tu^2} Phi_DH(u) u^2 cos(zu) du.

    Same theta recurrence as ``instrument._truncated_integrand`` with the
    extra factor -u^2; a finite sum of entire functions of u, so holomorphic
    on every ball and the integrator's ``analytic`` flag needs no branch.
    """
    pi5 = arb.pi() / 5
    three_half = arb(3) / 2
    a_pat = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: None}
    coeffs = []
    for n in range(1, N + 1):
        a = a_pat[n % 5]
        coeffs.append(None if a is None else arb(n) * a)

    def f(u, analytic):
        x = (2 * u).exp()
        q = (-pi5 * x).exp()
        q2 = q * q
        p = q
        w = q2 * q
        s = coeffs[0] * p
        for n in range(2, N + 1):
            p = p * w
            w = w * q2
            cn = coeffs[n - 1]
            if cn is not None:
                s = s + cn * p
        return -4 * (t_b * u * u + three_half * u).exp() * s * u * u * (z_b * u).cos()

    return f


def H2_ball(z, t, prec: int, U=None, nmax: int | None = None,
            eval_limit: int = 10 ** 7) -> acb:
    """An acb ball enclosing H_t''(z) = -int_0^inf e^{t u^2} Phi_DH(u) u^2 cos(zu) du.

    Assembly identical to ``instrument.H_ball`` with the extra u^2, so the two
    explicit tail balls each gain exactly two factors of U:

    1. series truncation on [0, U].  The discarded part is
       e^{tu^2} 4 e^{3u/2} (omega - omega_N)(e^{2u}) u^2 cos(zu); on the real
       path e^{2u} >= 1 so the omega tail is at most its value at x = 1
       (``instrument._omega_tail_upper`` at rho = 1), and
       e^{tu^2} <= e^{tU^2}, e^{3u/2} <= e^{3U/2}, |cos(zu)| <= e^{yU},
       u^2 <= U^2, path length U.
    2. the discarded integral over [U, inf).  Same c-argument as
       ``instrument._u_tail`` with the integrand carrying u^2 = ((log v)/2)^2
       after v = e^{2u}; (log v)^2 / v decreases for v >= e^2, and U >= 1
       gives V = e^{2U} >= e^2, so
       int_V^inf 4 ((log v)/2)^2 e^{-cv} dv/v <= 4 U^2 e^{-cV}/(cV).

    Both extra factors are the k = 2 case of the k-fold rule the instrument
    already carries for k = 0 and k = 1, and the derivation is written out in
    M2-LEMMA.md step 1.
    """
    with _prec_guard(prec):
        t_q = _exact_q(t)
        if t_q < 0:
            raise ValueError("H2_ball requires t >= 0")
        t_b = _q_to_arb(t_q)
        z_b = acb(_q_to_arb(_exact_q(z[0])), _q_to_arb(_exact_q(z[1]))) \
            if isinstance(z, (tuple, list)) else acb(z)
        y_hi = arb(z_b.imag.abs_upper())
        U_q = _exact_q(U) if U is not None else default_U(t_q, float(y_hi), prec)
        U_b = _q_to_arb(U_q)
        kap = kappa_ball(max(prec + 40, 300))
        N = nmax if nmax is not None else _default_nmax(prec, 1.0)
        f = _h2_integrand(z_b, t_b, N, kap)
        I = acb.integral(f, 0, U_b, eval_limit=eval_limit)

        if not (U_b >= 1):
            raise ValueError("H2_ball tail bounds need U >= 1")
        tail1 = _omega_tail_upper(arb(1), N)
        V = (2 * U_b).exp()
        r_at_V = (-arb.pi() * V / 5).exp()
        beta = arb(3) / 2 + y_hi
        c = arb.pi() / 5 - (t_b * U_b * U_b + beta * U_b) / V
        if (tail1 is None or not (r_at_V.abs_upper() < arb(fmpq(29, 100)))
                or not (c.lower() > 0)):
            raise ValueError(f"H2_ball tail bound not established at U={U_q}")
        e1 = (U_b * U_b * U_b
              * 4 * (t_b * U_b * U_b + (arb(3) / 2 + y_hi) * U_b).exp()
              * tail1).abs_upper()
        e2 = (4 * U_b * U_b * (-c * V).exp() / (c * V)).abs_upper()
        err = arb(0, (arb(e1) + arb(e2)).abs_upper())
        return I + acb(err, err)


def decided_sup_lower(box, t: Fraction, prec: int = 420,
                      n_re: int = 41, n_im: int = 9,
                      edge_extra: int = 64) -> dict:
    """A DECIDED lower bound for sup |H_t''| over the closed box.

    Every grid point's |H_t''| is enclosed by ``H2_ball``; the largest lower
    endpoint found is a decided lower bound for the sup, because the sup is
    at least the value at that one point.  This is the direction ball
    arithmetic can supply here: the opposite direction (a decided UPPER bound
    for the sup over the box) is exactly what the lemma exists to give and
    what direct evaluation cannot, since a z-ball wide enough to cover the
    box produces an enclosure of H_t'' containing 0.

    The top edge gets ``edge_extra`` further points because the measured sup
    sits there.
    """
    t0 = time.time()
    x_lo, x_hi, y_lo, y_hi = box
    best = arb(0)
    best_at = None
    n_pts = 0
    pts = []
    for i in range(n_re):
        x = x_lo + (x_hi - x_lo) * Fraction(i, max(n_re - 1, 1))
        for j in range(n_im):
            y = y_lo + (y_hi - y_lo) * Fraction(j, max(n_im - 1, 1))
            pts.append((x, y))
    for i in range(edge_extra):
        x = x_lo + (x_hi - x_lo) * Fraction(i, max(edge_extra - 1, 1))
        pts.append((x, y_hi))
    for x, y in pts:
        b = H2_ball((x, y), t, prec)
        with _prec_guard(prec):
            m = abs(b)
            n_pts += 1
            if m.lower() > best.lower():
                best = arb(m.lower())
                best_at = (_fr(x), _fr(y))
    return {
        "decided_sup_lower_bound": float(best.lower()),
        "attained_at": best_at,
        "attained_at_floats": [float(Fraction(best_at[0])),
                               float(Fraction(best_at[1]))] if best_at else None,
        "n_points": n_pts,
        "grid": {"n_re": n_re, "n_im": n_im, "top_edge_extra": edge_extra},
        "prec_bits": prec,
        "grade": "decided (Arb enclosure of H_t'' at each point)",
        "backend": BACKEND,
        "seconds": round(time.time() - t0, 1),
    }


def enclosure_width_probe(box, t: Fraction, prec: int = 420) -> dict:
    """Why a uniform bound cannot come from a ball evaluation over the box.

    Encloses H_t'' at one box point (narrow input) and over three z-balls of
    growing radius centred there, and reports whether each enclosure still
    excludes 0.  The point is not the numbers but the crossover: past a
    radius far below the box's own width the enclosure contains 0 and decides
    nothing, which is the quantitative form of "direct ball evaluation of
    H_t'' over a whole segment is useless here".
    """
    x_lo, x_hi, y_lo, y_hi = box
    xc = (x_lo + x_hi) / 2
    yc = (y_lo + y_hi) / 2
    rows = []
    with _prec_guard(prec):
        for rad_q in (Fraction(0), Fraction(1, 2 ** 80), Fraction(1, 2 ** 40),
                      Fraction(1, 2 ** 20), Fraction(1, 8)):
            re_ball = (_q_to_arb(xc - rad_q).union(_q_to_arb(xc + rad_q))
                       if rad_q else _q_to_arb(xc))
            zb = acb(re_ball, _q_to_arb(yc))
            try:
                b = H2_ball(zb, t, prec)
                m = abs(b)
                rows.append({
                    "z_re_radius": float(rad_q),
                    "enclosure_lower": float(m.lower()),
                    "enclosure_upper": float(m.upper()),
                    "excludes_zero": bool(m.lower() > 0),
                })
            except Exception as exc:                      # noqa: BLE001
                rows.append({"z_re_radius": float(rad_q), "error": str(exc)})
    return {
        "box_re_width": float(x_hi - x_lo),
        "rows": rows,
        "reading": (
            "the enclosure stops excluding 0 far below the box width, so no "
            "ball evaluation over a box-sized region can bound sup |H_t''| "
            "from above; the uniform bound must come from the contour shift"
        ),
    }


def check_h2_vs_finite_difference(box, t: Fraction, prec: int = 500,
                                  h: Fraction = Fraction(1, 1024)) -> dict:
    """Attack step 1: is H2_ball really the second derivative of H_ball?

    The lemma's step 1 claims
    H_t''(z) = -int_0^inf e^{t u^2} Phi_DH(u) u^2 cos(zu) du.  A sign slip, a
    missing factor or a wrong power would leave every later step formally
    intact and every number wrong, and no other check in this file would see
    it: the majorant machinery would faithfully bound the wrong integral.

    So the identity is attacked from outside: the second central difference
    of ``instrument.H_ball`` at an exact dyadic step h is compared with
    ``H2_ball`` at the same point.  Both sides are enclosures, so the
    comparison is decided up to the difference quotient's own O(h^2)
    truncation, which is reported rather than hidden: the agreement should be
    about h^2 relative, and a formula error would show as O(1).
    """
    from instrument import H_ball

    t0 = time.time()
    x_lo, x_hi, y_lo, y_hi = box
    rows = []
    worst = 0.0
    for frac in (Fraction(1, 8), Fraction(1, 2), Fraction(7, 8)):
        x = x_lo + (x_hi - x_lo) * frac
        y = y_hi
        with _prec_guard(prec):
            hb = _q_to_arb(h)
            a = H_ball((x - h, y), t, prec)
            b = H_ball((x, y), t, prec)
            c = H_ball((x + h, y), t, prec)
            fd = (a - 2 * b + c) / (hb * hb)
            direct = H2_ball((x, y), t, prec)
            rel = abs(fd - direct) / abs(direct)
            rel_up = float(rel.abs_upper())
            rows.append({
                "z": [_fr(x), _fr(y)],
                "finite_difference": fd.str(12, radius=True),
                "H2_ball": direct.str(12, radius=True),
                "relative_gap_upper": rel_up,
            })
            worst = max(worst, rel_up)
    return {
        "step_h": _fr(h),
        "expected_gap_order_h2": float(h) ** 2,
        "worst_relative_gap": worst,
        "verdict": "PASS" if worst < 100 * float(h) ** 2 else "FAIL",
        "reading": ("a formula error in step 1 would give a relative gap of "
                    "order 1; the observed gap is of order h^2, which is the "
                    "difference quotient's own truncation"),
        "rows": rows,
        "prec_bits": prec,
        "grade": "decided (both sides are Arb enclosures)",
        "seconds": round(time.time() - t0, 1),
    }


def check_h2_tail_consistency(box, t: Fraction, prec: int = 420) -> dict:
    """Attack the two k = 2 tail balls of ``H2_ball`` by moving U.

    ``H2_ball``'s error balls are the k = 2 case of the k-fold rule
    ``instrument`` already carries at k = 0 and k = 1 (whose domination is
    checked in ``validate.py`` check 6, blindness factor 8.02).  The k = 2
    case gains two factors of U in each tail, and a slip there would inflate
    or deflate the returned radius without changing the midpoint.

    The test: evaluate at the default U and at U + 1/2, U + 1.  Truncating
    the integral at a different place moves the true discarded remainder by
    orders of magnitude, so the three balls can only overlap if each one's
    error ball really covers its own remainder.  Reported as pairwise
    overlap plus the observed midpoint spread against the smallest radius.
    """
    x_lo, x_hi, y_lo, y_hi = box
    x = (x_lo + x_hi) / 2
    z = (x, y_hi)
    rows, balls = [], []
    U0 = default_U(_exact_q(t), float(y_hi), prec)
    for du in (Fraction(0), Fraction(1, 2), Fraction(1)):
        U = U0 + du
        b = H2_ball(z, t, prec, U=U)
        balls.append(b)
        with _prec_guard(prec):
            rows.append({"U": _fr(U), "ball": b.str(15, radius=True),
                         "radius_re": float((b.real.upper() - b.real.lower()) / 2)})
    ok = True
    with _prec_guard(prec):
        for i in range(len(balls)):
            for j in range(i + 1, len(balls)):
                d = balls[i] - balls[j]
                if not (d.real.contains(arb(0)) and d.imag.contains(arb(0))):
                    ok = False
    return {
        "z": [_fr(z[0]), _fr(z[1])],
        "default_U": _fr(U0),
        "rows": rows,
        "all_pairs_overlap": ok,
        "verdict": "PASS" if ok else "FAIL",
        "reading": ("three different truncation points give three different "
                    "true remainders; overlapping balls means each error ball "
                    "covers its own remainder"),
        "prec_bits": prec,
        "grade": "decided",
    }


def decay_probe(box, t: Fraction, prec: int = 420, span: int = 40,
                step: int = 4) -> dict:
    """Does the lemma's bound carry the TRUE exponential decay rate in Re z?

    M2 depends on x_lo only through the factor e^{-x_lo v}, v = pi/4 - eps.
    Phi_DH is holomorphic exactly on |Im u| < pi/4, so pi/4 is the largest
    rate any contour shift could give, and the true |H_t''(x + iy)| cannot
    decay faster than e^{-(pi/4) x} times subexponential factors.  If the
    measured rate matches v, the cushion M2 / sup |H_t''| is a CONSTANT in x
    rather than a gap that grows with the height of the box, which is what
    makes the number 55.7 mean something beyond this one rectangle.

    Reported: decided |H_t''| at Re z = x_lo + d for d = 0, step, ..., span
    on the top edge, the empirical rate over the whole span, v, and pi/4.
    |H_t''| oscillates in x, so the rate is read over the full span rather
    than between neighbours.
    """
    t0 = time.time()
    x_lo, x_hi, y_lo, y_hi = box
    rows = []
    for d in range(0, span + 1, step):
        x = x_lo + d
        with _prec_guard(prec):
            b = H2_ball((x, y_hi), t, prec)
            m = abs(b)
            lo, up = float(m.lower()), float(m.upper())
        m2_here = shifted_bound_best(x, y_hi, t)["M2_upper_float"]
        rows.append({"d": d, "abs_H2_lower": lo, "abs_H2_upper": up,
                     "M2_at_this_x_lo": m2_here,
                     "cushion_M2_over_absH2": m2_here / lo if lo > 0 else None})
    first = rows[0]["abs_H2_lower"]
    last = rows[-1]["abs_H2_upper"]
    rate = math.log(first / last) / span if last > 0 else None
    cush = [r["cushion_M2_over_absH2"] for r in rows
            if r["cushion_M2_over_absH2"] is not None]
    return {
        "rows": rows,
        "cushion_min_over_probe": min(cush) if cush else None,
        "cushion_max_over_probe": max(cush) if cush else None,
        "span": span,
        "empirical_rate_over_span": rate,
        "v_used_by_M2": math.pi / 4 - 1 / 256,
        "pi_over_4": math.pi / 4,
        "reading": ("the lemma's rate v = pi/4 - eps is within eps of the "
                    "strip half-width pi/4, which is the fastest rate any "
                    "shift of this contour can give; a measured rate near "
                    "pi/4 means the cushion is a constant in Re z, not a "
                    "gap that grows with the box's height"),
        "grade": "decided (Arb enclosures at each probe point)",
        "prec_bits": prec,
        "seconds": round(time.time() - t0, 1),
    }


# ---------------------------------------------------------------------------
# R4: the float route, kept for reproduction of the published cushion
# ---------------------------------------------------------------------------


def measured_sup(box, t: Fraction, dps: int = 112, n_re: int = 9,
                 n_im: int = 3) -> dict:
    """The measured sup |H_t''| on a grid (mpmath, float grade).

    Same evaluator and default grid as ``winding.measured_h2_guard`` so its
    published number can be reproduced here without importing it.
    """
    from mpmath import mp

    t0 = time.time()
    if FLOW_REPAIR not in sys.path:
        sys.path.insert(0, FLOW_REPAIR)
    from probe import DHFlow

    x_lo, x_hi, y_lo, y_hi = box
    flow = DHFlow(dps=dps, z_scale=242.0)
    with mp.workdps(dps):
        tt = mp.mpf(t.numerator) / t.denominator

        def h2(x: Fraction, y: Fraction):
            z = mp.mpc(mp.mpf(x.numerator) / x.denominator,
                       mp.mpf(y.numerator) / y.denominator)
            tot = mp.mpc(0)
            for u, w, ph in zip(flow.nodes, flow.weights, flow.phis):
                e = mp.expj(z * u)
                tot += w * ph * mp.exp(tt * u * u) * u * u * (e + 1 / e)
            return -(tot / 2)

        best = mp.mpf(0)
        best_at = None
        for i in range(n_re):
            x = x_lo + (x_hi - x_lo) * Fraction(i, max(n_re - 1, 1))
            for j in range(n_im):
                y = y_lo + (y_hi - y_lo) * Fraction(j, max(n_im - 1, 1))
                val = abs(h2(x, y))
                if val > best:
                    best = val
                    best_at = (float(x), float(y))
    return {
        "measured_sup_absH2": float(best),
        "measured_sup_at": best_at,
        "grid": {"n_re": n_re, "n_im": n_im},
        "dps": dps,
        "grade": "measured (mpmath float, no enclosure)",
        "seconds": round(time.time() - t0, 1),
    }


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def run_box(name: str, box, t: Fraction, prec_bound: int = 300,
            prec_ball: int = 420) -> dict:
    x_lo, x_hi, y_lo, y_hi = box
    print(f"--- {name}: t = {_fr(t)}, box "
          f"[{_fr(x_lo)}, {_fr(x_hi)}] x [{_fr(y_lo)}, {_fr(y_hi)}]", flush=True)

    r1 = shifted_bound_best(x_lo, y_hi, t, prec=prec_bound)
    print(f"  R1 shifted  M2 = {r1['M2_upper_float']:.10e}  (v = {r1['v']})",
          flush=True)
    r2 = direct_bound(y_hi, t, prec=prec_bound)
    print(f"  R2 direct   M  = {r2['M_direct_upper_float']:.6e}", flush=True)
    r3 = decided_sup_lower(box, t, prec=prec_ball)
    print(f"  R3 decided sup >= {r3['decided_sup_lower_bound']:.6e} at "
          f"{r3['attained_at_floats']}  ({r3['seconds']} s, "
          f"{r3['n_points']} pts)", flush=True)
    r4 = measured_sup(box, t)
    print(f"  R4 measured sup = {r4['measured_sup_absH2']:.6e}", flush=True)
    r5 = check_h2_vs_finite_difference(box, t)
    print(f"  step-1 finite-difference attack: {r5['verdict']} "
          f"(worst relative gap {r5['worst_relative_gap']:.2e} against "
          f"h^2 = {r5['expected_gap_order_h2']:.2e})", flush=True)
    r7 = check_h2_tail_consistency(box, t)
    print(f"  H2 tail-ball attack (U moved): {r7['verdict']}", flush=True)
    r6 = decay_probe(box, t)
    print(f"  decay rate over Re z span {r6['span']}: "
          f"{r6['empirical_rate_over_span']:.4f} vs v = "
          f"{r6['v_used_by_M2']:.4f}, pi/4 = {r6['pi_over_4']:.4f}; "
          f"cushion along the probe {r6['cushion_min_over_probe']:.1f} to "
          f"{r6['cushion_max_over_probe']:.1f}", flush=True)

    m2_mine = r1["M2_upper_float"]
    m2_code = M2_WINDING[_fr(t)]
    sup_dec = r3["decided_sup_lower_bound"]
    sup_meas = r4["measured_sup_absH2"]
    out = {
        "t": _fr(t),
        "box": {"re_lo": _fr(x_lo), "re_hi": _fr(x_hi),
                "im_lo": _fr(y_lo), "im_hi": _fr(y_hi),
                "floats": [float(x_lo), float(x_hi), float(y_lo), float(y_hi)]},
        "R1_shifted_bound": {k: v for k, v in r1.items() if k != "M2"},
        "R2_direct_bound": r2,
        "R3_decided_sup_lower": r3,
        "R4_measured_sup": r4,
        "R5_step1_finite_difference_attack": r5,
        "R6_decay_rate_probe": r6,
        "R7_h2_tail_consistency": r7,
        "comparison": {
            "M2_lemma_upper": m2_mine,
            "M2_winding_py": m2_code,
            "relative_difference": (m2_mine - m2_code) / m2_code,
            "lemma_bound_is_at_most_winding_bound": bool(m2_mine <= m2_code),
            "direct_over_shifted": r2["M_direct_upper_float"] / m2_mine,
            "cushion_decided_M2_over_decided_sup": m2_code / sup_dec,
            "cushion_lemma_M2_over_decided_sup": m2_mine / sup_dec,
            "cushion_measured_published_style": m2_code / sup_meas,
            "decided_sup_over_measured_sup": sup_dec / sup_meas,
        },
    }
    c = out["comparison"]
    print(f"  M2(lemma)/M2(winding) - 1 = {c['relative_difference']:+.3e}; "
          f"cushion (decided) = {c['cushion_decided_M2_over_decided_sup']:.2f}; "
          f"direct/shifted = {c['direct_over_shifted']:.3e}", flush=True)
    return out


def main() -> None:
    t_all = time.time()
    out: dict = {
        "hunt": "lambda_dh_bounds",
        "artifact": "M2-LEMMA.md",
        "purpose": ("independent decided verification of the uniform bound "
                    "M2 >= sup |H_t''| that the winding count consumes"),
        "backend": BACKEND,
        "kappa": None,
    }
    with _prec_guard(500):
        kap = kappa_ball(500)
        out["kappa"] = {
            "ball": _ball(kap),
            "decides_0_lt_kappa_lt_1": bool(arb(0) < kap) and bool(kap < arb(1)),
            "used_for": "|a_n| <= 1 in the majorant of step 3",
            "prec_bits": 500,
        }
    print(f"kappa = {out['kappa']['ball']['str']}, "
          f"0 < kappa < 1 decided: {out['kappa']['decides_0_lt_kappa_lt_1']}",
          flush=True)

    out["omega_majorant_check"] = check_omega_routes()
    print(f"omega majorant domination check: "
          f"{out['omega_majorant_check']['verdict']}", flush=True)

    out["t1"] = run_box("t1", BOX_T1, T1)
    out["t2"] = run_box("t2 (stretch)", BOX_T2, T2)
    out["enclosure_width_probe_t1"] = enclosure_width_probe(BOX_T1, T1)

    ok = (out["t1"]["comparison"]["lemma_bound_is_at_most_winding_bound"]
          and out["t2"]["comparison"]["lemma_bound_is_at_most_winding_bound"]
          and out["omega_majorant_check"]["all_dominate"]
          and out["kappa"]["decides_0_lt_kappa_lt_1"]
          and out["t1"]["R5_step1_finite_difference_attack"]["verdict"] == "PASS"
          and out["t2"]["R5_step1_finite_difference_attack"]["verdict"] == "PASS"
          and out["t1"]["R7_h2_tail_consistency"]["verdict"] == "PASS"
          and out["t2"]["R7_h2_tail_consistency"]["verdict"] == "PASS")
    out["verdict"] = "PASS" if ok else "FAIL"
    out["verdict_note"] = (
        "PASS means: every hypothesis of the lemma decided on both boxes, the "
        "independently re-derived bound is at most the bound winding.py uses "
        "(so the lemma holds a fortiori for the value the count consumed), the "
        "two closed-form majorants for the theta-like sum survive falsification "
        "at every probe point, and the step-1 identity for H_t'' survives a "
        "finite-difference attack that shares none of the majorant machinery."
    )
    out["wall_seconds_total"] = round(time.time() - t_all, 1)
    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nverdict {out['verdict']}; wrote {RESULTS_PATH} "
          f"({out['wall_seconds_total']} s)", flush=True)


if __name__ == "__main__":
    main()
