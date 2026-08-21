"""WP1 route 2: direct ball quadrature of the winding integral for H_t1.

Computes N = (1/(2 pi i)) oint_R H'(z)/H(z) dz over the pair-5 rectangle at
t1 = 0.0575, every evaluation an Arb ball, each edge integrated by Arb's
rigorous adaptive integrator (``acb.integral``) with the integrand
``Hprime_ball(z) / H_ball(z)`` along the edge parameterization.  The result
ball must contain exactly one integer, and that integer must be 1.  This
route shares no segment bookkeeping with route 1 (segment-argument tracking);
its only common dependency is ``instrument.py``.

Measured obstruction, and the fix
---------------------------------

A literal nested quadrature (call ``H_ball`` on the wide complex balls the
outer integrator probes) is infeasible at this height, and the reason is
worth recording: ``H_ball`` over a z-ball of radius d returns a ball of
radius about 0.34 * d (measured at prec 420: d = 1e-3 gives radius 3.4e-4;
d = 1e-90 gives radius 3.4e-91; the factor is the L1 mass of the u-integrand,
which is O(1)), while |H_t1| itself is about 5e-83 near height 240.  Ball
arithmetic propagates the pointwise magnitude of the u-integrand, not the
analytic cancellation in z, so H can only be shown nonzero on z-balls of
radius below ~1e-83.  Subdividing an edge of length 0.5 to that scale is
impossible, for this route and for any route that encloses H over a
continuum by direct integrand arithmetic.

The fix keeps the quadrature and repairs the wide-ball queries with
rigorous PANEL-LOCAL Taylor enclosures: each edge carries a row of exact
rational centres (10 per horizontal edge, 2 per vertical edge), each
covering a disc of radius R = 0.08.  Locality matters and was measured to
matter: with a single global centre the ball-arithmetic Horner radius at
|w| ~ 0.25 carries the sum of ABSOLUTE coefficient magnitudes, a factor
~e^{omega |w|} (omega the local log-derivative scale, ~10-30 here) above
the true variation, and the first budget run exhausted the outer
subdivision on the bottom edge.  At |w| <= 0.08 the factor is O(1) and the
subdivision converges.  For a centre m (an exact rational point) and
w = z - m:

    H(z)  = sum_{k=0}^{K} c_k w^k + R_H(w),      |w| <= R,
    H'(z) = sum_{k=1}^{K} k c_k w^{k-1} + R_D(w),
    c_k   = H^(k)(m) / k!,

where every H^(k)(m) is an inner ball integral AT THE EXACT POINT m (so
Arb's integrator handles the oscillatory cancellation, as it does for
``H_ball`` at points), and the two remainders carry explicit balls derived
below.  The outer ``acb.integral`` then uses:

  * the direct instrument quotient ``Hprime_ball(z)/H_ball(z)`` whenever the
    queried z-ball is (numerically) a point, which covers the Gauss-Legendre
    nodes whose values dominate the computed integral, and
  * the Taylor enclosure quotient on wide balls, which is what lets the
    integrator verify holomorphy (the enclosure excluding 0 proves H /= 0 on
    the ball) and bound the integrand on Bernstein ellipses.

Both branches return enclosures of the same function, so mixing them inside
one integrand callable is sound; when neither branch can exclude 0 from its
H enclosure the callable returns a non-finite ball, which is exactly the
refusal the ``analytic`` flag demands, and the integrator subdivides.

Derivatives at the centre (with T_k the k-th derivative of cos, i.e.
cos, -sin, -cos, sin cyclically, and y_m = |Im m|):

    H^(k)(m) = int_0^inf e^{t u^2} Phi_DH(u) u^k T_k(m u) du,

computed as ``acb.integral`` of the truncated integrand on [0, U] plus two
error balls, exactly the ``instrument.py`` pattern with one extra factor
u^k <= U^k on the path and, on [U, inf), u^k <= U^k e^{-2Uk} e^{2ku}
(from u <= U e^{-2U} e^{2u} for u >= U >= 1, raised to the k-th power), so

    series tail on [0,U]:  e1_k = U^k * (series tail of instrument.py),
    u-tail:                e2_k = 4 U^k e^{-2Uk} e^{-c_k V} / (c_k V),
    c_k = pi/5 - e^{-2U} (t U^2 + (3/2 + y_m) U + 2 k U),   V = e^{2U},

with c_k > 0 checked in balls (U = 4 makes c_k > 0.4 for all k <= K+1 here).

Taylor remainders on |w| <= R: |c_k| <= M_k / k! with
M_k = int_0^inf u^k g(u) du, g(u) = 4 e^{t u^2 + (3/2 + y_m) u} obar(u),
obar(u) = r/(1-r)^2 >= |omega(e^{2u})| for real u >= 0, r = e^{-pi e^{2u}/5}
(term bound n e^{-pi n^2 e^{2u}/5} <= n r^n, summed in closed form).  Using
sum_{k>K} x^k/k! <= x^{K+1}/(K+1)! e^x with x = R u:

    |R_H(w)| <= (R^{K+1}/(K+1)!) * J,     |R_D(w)| <= (R^K/K!) * J,
    J = int_0^inf u^{K+1} g(u) e^{R u} du,

and J is bounded above by a 512-panel interval Riemann sum on [0, U] (the
integrand is a positive real arb expression, evaluated on each panel ball)
plus a u-tail of the same e^{-c e^{2u}} shape as above with k = K+1 and the
linear coefficient 3/2 + y_m + R.  The second inequality for R_D follows the
same way from sum_{k>K} M_k R^{k-1}/(k-1)! after shifting the index.

Everything is python-flint (Arb).  Working precision for the winding
quadrature and instrument calls is 420 bits; the Taylor coefficients are
computed at 700 bits (raised so the u^k integrand magnitudes, up to ~1e12
at k = 80, leave the coefficient balls far tighter than anything the
decision needs).  The box is the route 1 recipe box; route 1's own output
file did not exist when this script ran, so the recipe is recorded here for
the assembler to compare.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from flint import acb, arb, ctx  # noqa: E402

from instrument import (  # noqa: E402
    H_ball,
    Hprime_ball,
    kappa_ball,
    _default_nmax,
    _exact_q,
    _nonfinite_acb,
    _prec_guard,
    _q_to_arb,
    _series_tail_finite,
)

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "winding_quad_results.json")

# ---------------------------------------------------------------------------
# configuration (all exact rationals)
# ---------------------------------------------------------------------------

T1 = Fraction("0.0575")            # pre-registered t1 = 23/400
PREC = 420                          # winding quadrature + instrument calls
PREC_MOM = 700                      # Taylor coefficient integrals
K = 48                              # Taylor degree of each local model
U_MOM = Fraction(4)                 # moment integration limit (exact)
R_MODEL = Fraction(2, 25)           # local disc radius 0.08: covers a panel
                                    # (half-length <= 0.025) plus the
                                    # integrator's Bernstein-ellipse
                                    # excursions in the complex s-plane
N_PANELS_LONG = 10                  # local centres per horizontal edge
N_PANELS_SHORT = 2                  # local centres per vertical edge
J_PANELS = 512
DIRECT_RAD_MAX = 1e-100             # z-ball radius below which the direct
                                    # instrument quotient is used (GL nodes
                                    # sit at ~1e-126; anything wider goes to
                                    # the Taylor enclosure)
DIRECT_CAP_PER_EDGE = 250
INNER_EVAL_LIMIT = 10 ** 6
OUTER_EVAL_LIMIT = 500000

# route 1 recipe box: float-locate pair 5 at t1, Re centre +/- 1/4,
# Im in [0.004, 0.06] = [1/250, 3/50].  MISSION.md's guidance value for the
# pair-5 site ("about 240.4165") is the t = 0 neighbourhood; tracing the
# zero under the flow (Newton continuation from the t = 0 position
# 240.4047 + 0.3695i) lands it at 240.34528 + 0.01743i at t1 = 0.0575, so
# the recipe's "float-locate at t1" step fixes the centre there.  The
# centre is pinned to an exact rational and re-verified in main() against
# the fresh float location.
XC = Fraction("240.3453")
HALF_W = Fraction(1, 4)
Y0 = Fraction(1, 250)
Y1 = Fraction(3, 50)


def _f(x) -> float:
    return float(x)


# ---------------------------------------------------------------------------
# measured (float grade) preliminaries: locate the pair, scan the axis
# ---------------------------------------------------------------------------


def _H_mid_complex(z, t, prec: int) -> complex:
    b = H_ball(z, t, prec)
    m = b.mid()
    return complex(float(m.real), float(m.imag))


def _Hp_mid_complex(z, t, prec: int) -> complex:
    b = Hprime_ball(z, t, prec)
    m = b.mid()
    return complex(float(m.real), float(m.imag))


def float_locate_pair(seed: complex, t=None, prec: int = 300) -> dict:
    """Newton on ball midpoints from the seed: measured, float grade."""
    if t is None:
        t = T1
    z = seed
    steps = []
    for _ in range(14):
        h = _H_mid_complex((z.real, z.imag), t, prec)
        hp = _Hp_mid_complex((z.real, z.imag), t, prec)
        step = h / hp
        z = z - step
        steps.append(abs(step))
        if abs(step) < 1e-14:
            break
    resid = abs(_H_mid_complex((z.real, z.imag), t, prec))
    return {"re": z.real, "im": z.imag, "last_step": steps[-1],
            "n_steps": len(steps), "abs_H_residual": resid,
            "grade": "measured (Newton on Arb ball midpoints, "
                     f"backend python-flint, prec {prec})"}


def pair5_trajectory() -> list[dict]:
    """Continuation of the pair-5 zero from its known t = 0 position
    (flow_repair polished: 240.4046723514407 + 0.3695305796406431i) up to
    t1, establishing that the zero the box encloses is pair 5.  Measured,
    float grade."""
    z = complex(240.4046723514407, 0.36953057964064307)
    out = []
    for t_s in ("0", "0.02", "0.04", "0.05", "0.055", "0.057", "0.0575"):
        loc = float_locate_pair(z, t=Fraction(t_s))
        z = complex(loc["re"], loc["im"])
        out.append({"t": t_s, "re": loc["re"], "im": loc["im"],
                    "abs_H_residual": loc["abs_H_residual"]})
    return out


def real_axis_zeros(x_lo: float, x_hi: float, n: int = 49,
                    prec: int = 300) -> list[float]:
    """Sign-change scan of H_t1 on the real axis, bisected: measured."""
    xs = [x_lo + i * (x_hi - x_lo) / (n - 1) for i in range(n)]
    vals = [_H_mid_complex((x, 0), T1, prec).real for x in xs]
    zeros = []
    for i in range(n - 1):
        if vals[i] == 0.0:
            zeros.append(xs[i])
            continue
        if vals[i] * vals[i + 1] < 0:
            a, b = xs[i], xs[i + 1]
            fa = vals[i]
            for _ in range(50):
                mid = 0.5 * (a + b)
                fm = _H_mid_complex((mid, 0), T1, prec).real
                if fm == 0.0:
                    a = b = mid
                    break
                if fa * fm < 0:
                    b = mid
                else:
                    a, fa = mid, fm
            zeros.append(0.5 * (a + b))
    return zeros


# ---------------------------------------------------------------------------
# Taylor coefficients at the exact centre (decided enclosures)
# ---------------------------------------------------------------------------


def moment_integrals(m_re: Fraction, m_im: Fraction) -> tuple[list, dict]:
    """c_k = H^(k)(m)/k! for k = 0..K as acb balls, at PREC_MOM bits.

    Tail derivations are in the module docstring.  Raises when any tail
    hypothesis fails (loud, per the hunt's refusal contract).  Called once
    per local panel centre.
    """
    info: dict = {}
    t0 = time.time()
    with _prec_guard(PREC_MOM):
        kap = kappa_ball(PREC_MOM + 40)
        N = _default_nmax(PREC_MOM, 1.0)
        t_b = _q_to_arb(_exact_q(T1))
        m_c = acb(_q_to_arb(m_re), _q_to_arb(m_im))
        y_m = _q_to_arb(abs(m_im))
        U_b = _q_to_arb(U_MOM)
        V = (2 * U_b).exp()
        pi5 = arb.pi() / 5
        three_half = arb(3) / 2

        r_V = (-pi5 * V).exp()
        if not (r_V.abs_upper() < arb(29) / 100):
            raise ValueError("moment u-tail: e^{-pi V/5} not below 0.29")

        a_pat = {1: arb(1), 2: kap, 3: -kap, 4: arb(-1), 0: None}
        coeffs = [None if a_pat[n % 5] is None else arb(n) * a_pat[n % 5]
                  for n in range(1, N + 1)]

        base_series_tail = _series_tail_finite(N, U_b, t_b, y_m, deriv=False)
        if base_series_tail is None:
            raise ValueError("moment series tail not established at U=4")

        tol = arb(2) ** (-460)
        cks = []
        for k in range(K + 1):
            r = k % 4

            def f(u, analytic, _r=r, _k=k):
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
                pref = 4 * (t_b * u * u + three_half * u).exp() * s
                if _k:
                    pref = pref * u ** _k
                arg = m_c * u
                if _r == 0:
                    tr = arg.cos()
                elif _r == 1:
                    tr = -arg.sin()
                elif _r == 2:
                    tr = -arg.cos()
                else:
                    tr = arg.sin()
                return pref * tr

            I_k = acb.integral(f, 0, U_b, abs_tol=tol, rel_tol=tol,
                               eval_limit=INNER_EVAL_LIMIT)
            Uk = U_b ** k if k else arb(1)
            e1 = (Uk * base_series_tail).abs_upper()
            c_k_tail = (pi5 - ((t_b * U_b * U_b
                                + (three_half + y_m) * U_b
                                + 2 * k * U_b) / V))
            if not (c_k_tail.lower() > 0):
                raise ValueError(f"moment u-tail constant c_{k} not positive")
            e2 = (4 * Uk * (-2 * U_b * k).exp()
                  * (-c_k_tail * V).exp() / (c_k_tail * V)).abs_upper()
            err = arb(0, (e1 + e2).abs_upper())
            D_k = I_k + acb(err, err)
            cks.append(D_k / math.factorial(k))

        info["n_series_terms"] = N
        info["prec"] = PREC_MOM
        info["abs_tol_log2"] = -460
        info["seconds"] = round(time.time() - t0, 2)
        info["c0"] = {"mid": str(cks[0].mid()), "rad": str(cks[0].rad())}
        info["cK"] = {"mid": str(cks[K].mid()), "rad": str(cks[K].rad())}
    return cks, info


def taylor_remainders(y_abs_hi: Fraction) -> tuple[arb, arb, dict]:
    """Upper bounds for |R_H| and |R_D| on |w| <= R_MODEL, per docstring.

    ``y_abs_hi`` is an upper bound for |Im m| over every local centre, so
    one remainder pair serves all panels (the bound is monotone in |Im m|).
    """
    with _prec_guard(PREC_MOM):
        t_b = _q_to_arb(_exact_q(T1))
        y_m = _q_to_arb(abs(y_abs_hi))
        R_b = _q_to_arb(R_MODEL)
        U_b = _q_to_arb(U_MOM)
        V = (2 * U_b).exp()
        pi5 = arb.pi() / 5
        beta = arb(3) / 2 + y_m + R_b

        # 512-panel interval Riemann sum of u^{K+1} g(u) e^{Ru} on [0, U]
        h = U_MOM / J_PANELS                      # exact dyadic 1/128
        h_b = _q_to_arb(h)
        total = arb(0)
        for j in range(J_PANELS):
            mid = h * j + h / 2
            ub = _q_to_arb(mid) + arb(0, _q_to_arb(h / 2))
            x = (2 * ub).exp()
            r = (-pi5 * x).exp()
            one_minus = 1 - r
            if not (one_minus.lower() > 0):
                raise ValueError("J panel: 1 - r not positive")
            obar = r / (one_minus * one_minus)
            g = 4 * (t_b * ub * ub + beta * ub).exp() * obar
            total = total + (ub ** (K + 1)) * g * h_b
        # u-tail with k = K+1 (u^{K+1} <= U^{K+1} e^{-2U(K+1)} e^{2(K+1)u},
        # |obar| <= 2 r for r <= 0.29, checked in moment_integrals at V)
        c_J = pi5 - ((t_b * U_b * U_b + beta * U_b
                      + 2 * (K + 1) * U_b) / V)
        if not (c_J.lower() > 0):
            raise ValueError("J u-tail constant not positive")
        tail = (8 * (U_b ** (K + 1)) * (-2 * U_b * (K + 1)).exp()
                * (-c_J * V).exp() / (2 * c_J * V))
        J = (total + tail).abs_upper()
        rem_H = ((R_b ** (K + 1)) * J / math.factorial(K + 1)).abs_upper()
        rem_D = ((R_b ** K) * J / math.factorial(K)).abs_upper()
        info = {"J_upper": str(J), "rem_H_upper": str(rem_H),
                "rem_Hp_upper": str(rem_D), "panels": J_PANELS,
                "prec": PREC_MOM}
    return rem_H, rem_D, info


# ---------------------------------------------------------------------------
# the winding quadrature
# ---------------------------------------------------------------------------


def main() -> None:
    t_start = time.time()
    results: dict = {
        "route": "WP1 route 2: direct ball quadrature of H'/H over the "
                 "pair-5 rectangle",
        "backend": "python-flint (Arb)",
        "t1": str(T1),
        "prec_winding": PREC,
        "prec_taylor": PREC_MOM,
    }

    # -- measured preliminaries --------------------------------------------
    t0 = time.time()
    traj = pair5_trajectory()
    results["pair5_trajectory"] = {
        "values": traj,
        "grade": "measured (Newton continuation from the flow_repair t = 0 "
                 "position, prec 300)",
    }
    loc = float_locate_pair(complex(240.3453, 0.0174))
    results["located_zero"] = loc
    if abs(loc["re"] - traj[-1]["re"]) > 1e-6 or \
            abs(loc["im"] - traj[-1]["im"]) > 1e-6:
        raise ValueError("fresh location disagrees with the continuation "
                         "trace; box identity not established")
    x0, x1 = XC - HALF_W, XC + HALF_W
    axis = real_axis_zeros(_f(x0) - 0.03, _f(x1) + 0.03)
    results["real_axis_zeros_nearby"] = {
        "values": axis,
        "grade": "measured (ball-midpoint sign scan + bisection, prec 300)",
    }
    edge_clearance = min([min(abs(z - _f(x0)), abs(z - _f(x1)))
                          for z in axis], default=float("inf"))
    results["min_real_zero_to_vertical_edge"] = edge_clearance
    if edge_clearance < 0.02:
        raise ValueError(
            f"a real zero sits {edge_clearance:.4f} from a vertical edge; "
            "shift the box and rerun")
    if not (_f(x0) + 0.01 < loc["re"] < _f(x1) - 0.01
            and _f(Y0) + 0.002 < loc["im"] < _f(Y1) - 0.002):
        raise ValueError("located pair-5 zero is not safely inside the box")
    results["preliminaries_seconds"] = round(time.time() - t0, 2)

    # -- the box (route 1 recipe; route 1 output absent at run time) -------
    box = {"re_lo": str(x0), "re_hi": str(x1),
           "im_lo": str(Y0), "im_hi": str(Y1),
           "re_centre": str(XC), "half_width": str(HALF_W)}
    results["box"] = box
    results["route1_box"] = {
        "status": "route 1 output file not present when this route ran; "
                  "the shared recipe box was used (float-locate pair 5 at "
                  "t1, Re centre +/- 1/4, Im in [1/250, 3/50])",
        "recipe_box": dict(box),
        "boxes_identical_to_recipe": True,
        "guidance_note": "MISSION.md's guidance Re ~ 240.4165 is the t = 0 "
                         "neighbourhood of the quadruple; the recipe's "
                         "float-locate step at t1 = 0.0575 puts the zero at "
                         "240.34528 + 0.01743i (continuation trace recorded "
                         "under pair5_trajectory), so the centre is the "
                         "measured t1 location, pinned to 240.3453 exactly.",
    }

    # -- Taylor enclosures: panel-local centres along each edge -------------
    # A single global centre was tried first and measured to fail: at
    # |w| ~ 0.25 the ball-arithmetic Horner radius carries the sum of
    # ABSOLUTE coefficient values, a factor ~e^{omega |w|} (omega the local
    # log-derivative scale, ~10-30 here) above the true local variation, so
    # the wide-ball enclosures could not exclude 0 and the outer budget was
    # exhausted on the bottom edge.  Local centres keep |w| <= 0.08 and the
    # factor stays O(1).
    x0, x1 = XC - HALF_W, XC + HALF_W  # (recomputed; exact)
    centres: dict[str, list[tuple[Fraction, Fraction]]] = {}
    w_long = 2 * HALF_W / N_PANELS_LONG
    centres["bottom"] = [(x0 + w_long * j + w_long / 2, Y0)
                         for j in range(N_PANELS_LONG)]
    centres["top"] = [(x0 + w_long * j + w_long / 2, Y1)
                      for j in range(N_PANELS_LONG)]
    h_short = (Y1 - Y0) / N_PANELS_SHORT
    centres["right"] = [(x1, Y0 + h_short * j + h_short / 2)
                        for j in range(N_PANELS_SHORT)]
    centres["left"] = [(x0, Y0 + h_short * j + h_short / 2)
                       for j in range(N_PANELS_SHORT)]

    results["taylor"] = {
        "scheme": "panel-local Taylor models on each edge",
        "degree": K, "disc_radius": str(R_MODEL), "moment_U": str(U_MOM),
        "centres": {e: [[str(a), str(b)] for a, b in cs]
                    for e, cs in centres.items()},
    }
    t_mom = time.time()
    coeff_store: dict[str, list] = {}
    for e_name, cs in centres.items():
        coeff_store[e_name] = []
        for (mr, mi) in cs:
            cks, _info = moment_integrals(mr, mi)
            coeff_store[e_name].append(cks)
    results["taylor"]["moments_seconds"] = round(time.time() - t_mom, 2)
    results["taylor"]["moments_prec"] = PREC_MOM
    rem_H, rem_D, rem_info = taylor_remainders(Y1)
    results["taylor"]["remainders"] = rem_info

    # -- edge integrals -----------------------------------------------------
    with _prec_guard(PREC):
        errH = acb(arb(0, rem_H), arb(0, rem_H))
        errD = acb(arb(0, rem_D), arb(0, rem_D))
        R_f = _f(R_MODEL)

        # per-edge: list of (centre acb, centre float, C list, D1 list)
        models: dict[str, list] = {}
        for e_name, cs in centres.items():
            models[e_name] = []
            for (mr, mi), cks in zip(cs, coeff_store[e_name]):
                m_c = acb(_q_to_arb(mr), _q_to_arb(mi))
                C = [acb(c) for c in cks]
                D1 = [(j + 1) * C[j + 1] for j in range(K)]
                models[e_name].append((m_c, complex(_f(mr), _f(mi)), C, D1))

        def model_pair(e_name: str, z: acb):
            """(H enclosure, H' enclosure) from the nearest panel model,
            or (None, None) when no panel disc covers the z-ball."""
            zm = z.mid()
            zc = complex(float(zm.real), float(zm.imag))
            best = min(models[e_name], key=lambda t: abs(zc - t[1]))
            m_c, _, C, D1 = best
            w = z - m_c
            if float(abs(w).abs_upper()) > R_f:
                return None, None
            s = C[K]
            for k in range(K - 1, -1, -1):
                s = s * w + C[k]
            sp = D1[K - 1]
            for k in range(K - 2, -1, -1):
                sp = sp * w + D1[k]
            return s + errH, sp + errD

        corners = [
            acb(_q_to_arb(x0), _q_to_arb(Y0)),
            acb(_q_to_arb(x1), _q_to_arb(Y0)),
            acb(_q_to_arb(x1), _q_to_arb(Y1)),
            acb(_q_to_arb(x0), _q_to_arb(Y1)),
        ]
        edge_names = ["bottom", "right", "top", "left"]
        tolo = arb(2) ** (-40)
        zero = acb(0)

        edge_results = []
        W = acb(0)
        for e in range(4):
            a_c = corners[e]
            b_c = corners[(e + 1) % 4]
            delta = b_c - a_c
            counters = {"direct": 0, "model": 0,
                        "refused_direct": 0, "refused_model": 0}

            def g(s, analytic, _a=a_c, _d=delta, _cnt=counters,
                  _en=edge_names[e]):
                z = _a + s * _d
                zrad = max(float(z.real.rad()), float(z.imag.rad()))
                if (zrad <= DIRECT_RAD_MAX
                        and _cnt["direct"] < DIRECT_CAP_PER_EDGE):
                    _cnt["direct"] += 1
                    Hz = H_ball(z, T1, PREC, eval_limit=INNER_EVAL_LIMIT)
                    if (not Hz.is_finite()) or Hz.contains(zero):
                        _cnt["refused_direct"] += 1
                        return _nonfinite_acb()
                    Hp = Hprime_ball(z, T1, PREC,
                                     eval_limit=INNER_EVAL_LIMIT)
                    return (Hp / Hz) * _d
                _cnt["model"] += 1
                Pz, Pp = model_pair(_en, z)
                if Pz is None or (not Pz.is_finite()) or Pz.contains(zero):
                    _cnt["refused_model"] += 1
                    return _nonfinite_acb()
                return (Pp / Pz) * _d

            # cross-check the two enclosure branches at three exact points
            checks = []
            for s_q in (Fraction(3, 10), Fraction(1, 2), Fraction(7, 10)):
                # exact point on the edge (chosen off panel joints)
                s_b = _q_to_arb(s_q)
                z_pt = a_c + s_b * delta
                Hd = H_ball(z_pt, T1, PREC, eval_limit=INNER_EVAL_LIMIT)
                Hpd = Hprime_ball(z_pt, T1, PREC,
                                  eval_limit=INNER_EVAL_LIMIT)
                Hm, Hpm = model_pair(edge_names[e], z_pt)
                if Hm is None:
                    raise ValueError(
                        f"cross-check point on edge {edge_names[e]} not "
                        "covered by any panel model")
                ok = ((Hd - Hm).contains(zero)
                      and (Hpd - Hpm).contains(zero))
                checks.append({"s": str(s_q), "overlap": bool(ok)})
                if not ok:
                    raise ValueError(
                        f"instrument and Taylor enclosures disagree on edge "
                        f"{edge_names[e]} at s={s_q}")

            t_edge = time.time()
            I_e = acb.integral(g, 0, 1, rel_tol=tolo, abs_tol=tolo,
                               eval_limit=OUTER_EVAL_LIMIT)
            dt_edge = time.time() - t_edge
            if not I_e.is_finite():
                raise ValueError(
                    f"edge {edge_names[e]}: integral did not converge to a "
                    "finite ball inside the budget; no count is claimed")
            W = W + I_e
            edge_results.append({
                "edge": edge_names[e],
                "from": {"re": str(a_c.real.mid()), "im": str(a_c.imag.mid())},
                "to": {"re": str(b_c.real.mid()), "im": str(b_c.imag.mid())},
                "integral_mid": {"re": str(I_e.real.mid()),
                                 "im": str(I_e.imag.mid())},
                "integral_rad": {"re": str(I_e.real.rad()),
                                 "im": str(I_e.imag.rad())},
                "evals": dict(counters),
                "cross_checks": checks,
                "seconds": round(dt_edge, 2),
            })
            print(f"edge {edge_names[e]}: {counters} in {dt_edge:.1f}s",
                  flush=True)

        two_pi_i = acb(0, 2 * arb.pi())
        N_ball = W / two_pi_i

        # decision: the ball must contain exactly one integer, and it is 1
        re_off = (N_ball.real - 1).abs_upper()
        im_off = N_ball.imag.abs_upper()
        decided = (N_ball.real.contains(arb(1))
                   and N_ball.imag.contains(arb(0))
                   and float(re_off) < 0.5 and float(im_off) < 0.5)
        if not decided:
            raise ValueError(
                "winding ball does not decide N = 1: "
                f"N = {N_ball}; no lower-bound claim is made (kill "
                "condition 2 of MISSION.md)")

        results["edges"] = edge_results
        results["N_ball"] = {
            "re_mid": str(N_ball.real.mid()),
            "re_rad": str(N_ball.real.rad()),
            "im_mid": str(N_ball.imag.mid()),
            "im_rad": str(N_ball.imag.rad()),
        }
        results["decided_N"] = 1
        results["decision"] = (
            "decided: the winding ball contains exactly one integer, N = 1; "
            "H_t1 has exactly one zero in the open box (Arb ball "
            f"quadrature, backend python-flint, prec {PREC}; Taylor "
            f"coefficients at prec {PREC_MOM})")

    results["total_seconds"] = round(time.time() - t_start, 2)
    results["notes"] = [
        "The literal nested wide-ball quadrature is measured infeasible: "
        "H_ball over a z-ball of radius d has radius ~0.34*d (measured at "
        "prec 420) against |H_t1| ~ 5e-83 at this height, so H can be "
        "shown nonzero only on z-balls of radius below ~1e-83.",
        "Fix: Gauss-Legendre node values use the direct instrument "
        "quotient Hprime_ball/H_ball at (numerically) exact points; wide "
        "balls use panel-local degree-48 Taylor enclosures (24 exact "
        "rational centres on the edges, disc radius 0.08) whose "
        "coefficients are ball integrals at exact points and whose "
        "remainder is an explicit ball (derivations in the module "
        "docstring).  A single global centre was tried first and failed "
        "its budget: absolute-value coefficient sums grow like "
        "e^{omega |w|} at |w| ~ 0.25, and the enclosures could not "
        "exclude 0.",
        "Both branches enclose the same function; each edge cross-checks "
        "them at three exact points and requires overlap.",
    ]
    with open(OUT, "w") as fh:
        json.dump(results, fh, indent=1)
    print(json.dumps({"decided_N": results["decided_N"],
                      "N_re_mid": results["N_ball"]["re_mid"][:30],
                      "N_re_rad": results["N_ball"]["re_rad"][:12],
                      "total_seconds": results["total_seconds"]}, indent=1))


if __name__ == "__main__":
    main()
