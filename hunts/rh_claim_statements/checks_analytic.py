"""Ball-arithmetic checks for the zeta, Gamma, L-function and real-analysis claims.

Each function takes the claim's parameters (the constants of the Lean statement,
so that a mutant is the same function with one constant changed) and returns a
`common.result` record. `holds=False` is returned only with a rigorous witness:
a point at which an Arb enclosure, or exact arithmetic, violates the statement.
"""
from __future__ import annotations

import math
from fractions import Fraction

from flint import acb, acb_series, arb, ctx, dirichlet_char, dirichlet_group, fmpq

from . import common as C
from .common import A, Q, ball, cball, lo, up, result, sup_bnb, verdict_from_sup


def _is_point(box):
    return all(a == b for a, b in box)


def _inf_ball():
    return arb(0).union(arb.pos_inf())


def _abs_ball(z):
    return z.abs_lower().union(z.abs_upper())


def _sharp(res, K):
    """[lo, hi] for the smallest admissible value of a multiplicative constant K."""
    return [float(K) * res["lo"], float(K) * res["hi"]]


def _zeta_tb(S, order=6):
    """(zeta, zeta') on the complex ball S by the Taylor model; None if the disc reaches s = 1."""
    return C.taylor_ball(lambda c, n: list(acb_series([c, 1], prec=n).zeta()),
                         lambda B: up(B.zeta().abs_upper()), S, order=order, poles=((1.0, 0.0),))


# ---------------------------------------------------------------------------
# Z01  |zeta(s)| <= K on the circle |s - c| = R
# ---------------------------------------------------------------------------

def zeta_circle(p):
    c, R, K = Q(p["center"]), Q(p["radius"]), Q(p["K"])
    with ctx.workprec(C.bits(p)):
        def f(box):
            th = ball(*box[0]) * 2
            s = acb(A(c)) + A(R) * acb(th.cos_pi(), th.sin_pi())
            if _is_point(box):
                return _abs_ball(s.zeta()) / A(K)
            tb = _zeta_tb(s)
            return _inf_ball() if tb is None else _abs_ball(tb[0]) / A(K)
        res = sup_bnb(f, [(b,) for b in C.grid(0.0, 1.0, p.get("arcs", 64))], tol=p.get("tol", 1e-5),
                      stop_above=1.0)
    th = res["argmax"][0]
    v = verdict_from_sup(res)
    spt = [float(c) + float(R) * math.cos(2 * math.pi * th), float(R) * math.sin(2 * math.pi * th)]
    return result(v, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(theta_turns=th, s=spt),
                  sharp=_sharp(res, K) if v else None, slack=[1 / res["hi"], 1 / res["lo"]] if v else None,
                  sup_ratio=[res["lo"], res["hi"]], tight=res["tight"],
                  witness=dict(s=spt, ratio_lower=res["lo"]) if v is False else None,
                  notes="the whole circle is covered by arcs; sup |zeta| on it is K times sup_ratio")


# ---------------------------------------------------------------------------
# Z02  |t| > t0, |z - (a + it)| <= r  ==>  Re z >= h, z != 1, |zeta z| <= K(|t| + 2)
# ---------------------------------------------------------------------------

def zeta_near_abscissa(p):
    a, r, K, h, t0 = Q(p["a"]), Q(p["r"]), Q(p["K"]), Q(p["half"]), Q(p["t0"])
    T = p["T"]
    # (i) Re z >= h on the closed discs: exact, the minimum of Re z is a - r
    if a - r < h:
        return result(False, 1, witness=dict(z=[float(a - r), 3.0], t=3.0,
                                             why="Re z = a - r < h, exact rationals"),
                      notes="first conjunct fails")
    # (ii) z != 1: |1 - (a + it)|^2 = (1-a)^2 + t^2 > t0^2 >= r^2 needs r < sqrt((1-a)^2 + t0^2)
    if r * r >= (1 - a) ** 2 + t0 * t0:
        return result(False, 1, witness="z = 1 lies in a disc", notes="second conjunct fails")
    with ctx.workprec(C.bits(p)):
        aa, rr = A(a), A(r)

        def f(box):
            X, Y = ball(*box[0]), ball(*box[1])
            d2 = rr * rr - (X - aa) * (X - aa)
            if _is_point(box):
                if not (d2 > 0):
                    return arb(-1)
                d = d2.sqrt()
                if not (Y > A(t0) - d):          # the point lies in no admissible disc
                    return arb(-1)
                t = (Y - d).max(A(t0))           # the smallest admissible |t| for this z
                return _abs_ball(acb(X, Y).zeta()) / (A(K) * (t + 2))
            d_up = math.sqrt(max(0.0, up(d2))) * (1 + 1e-12)
            if box[1][1] < float(t0) - d_up:     # the whole box lies in no admissible disc
                return arb(-1)
            t_lo = max(float(t0), box[1][0] - d_up)
            tb = _zeta_tb(acb(X, Y))
            if tb is None:
                return _inf_ball()
            return _abs_ball(tb[0]) / (A(K) * arb(t_lo + 2))
        x0, x1 = float(a - r), float(a + r)
        boxes = C.boxes2((x0, x1), (float(t0) - float(r), T + float(r)), 8, max(8, int(4 * T)))
        res = sup_bnb(f, boxes, tol=p.get("tol", 5e-4), max_boxes=p.get("max_boxes", 200000), stop_above=1.0)
    v = verdict_from_sup(res)
    return result(v, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(z=res["argmax"]), sharp=_sharp(res, K) if v else None,
                  slack=[1 / res["hi"], 1 / res["lo"]] if v else None, sup_ratio=[res["lo"], res["hi"]],
                  tight=res["tight"], tested_range=f"{float(t0)} < |t| <= {T} (t < 0 by conjugation)",
                  re_margin=float(a - r - h),
                  witness=dict(z=res["argmax"], ratio_lower=res["lo"]) if v is False else None,
                  notes="Re z >= 1/2 and z != 1 are exact (Re z = 1/2 is attained: the radius is sharp); "
                        "the zeta bound is a complete cover of the union of discs for t up to T, each z "
                        "taken with its smallest admissible |t|")


# ---------------------------------------------------------------------------
# Z03  Re(-zeta'/zeta(sigma + it)) <= K log(|t| + 2)
# ---------------------------------------------------------------------------

def zeta_logderiv(p):
    s0, s1, K, t0, T = Q(p["sigma_lo"]), Q(p["sigma_hi"]), Q(p["K"]), Q(p["t0"]), p["T"]
    with ctx.workprec(C.bits(p)):
        def f(box):
            S = cball(box)
            if _is_point(box):
                z = acb_series([S, 1], prec=2).zeta()
                val, der = z[0], z[1]
            else:
                tb = _zeta_tb(S)
                if tb is None:
                    return _inf_ball()
                val, der = tb
            if not (val.abs_lower() > 0):
                return _inf_ball()
            return (-(der / val)).real / (A(K) * (S.imag + 2).log())
        boxes = C.boxes2((float(s0), float(s1)), (float(t0), T), 2, max(4, int(2 * T)))
        res = sup_bnb(f, boxes, tol=p.get("tol", 1e-5), stop_above=1.0,
                      max_boxes=p.get("max_boxes", 200000))
    v = verdict_from_sup(res)
    return result(v, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(s=res["argmax"]), sharp=_sharp(res, K) if v else None,
                  slack=[1 / res["hi"], 1 / res["lo"]] if v and res["lo"] > 0 else None,
                  sup_ratio=[res["lo"], res["hi"]], tight=res["tight"],
                  witness=dict(s=res["argmax"], ratio_lower=res["lo"]) if v is False else None,
                  tested_range=f"{float(s0)} <= sigma <= {float(s1)}, {float(t0)} <= t <= {T} (t < 0 by conjugation)",
                  notes="closed rectangle (closure of the stated strip), complete cover")


# ---------------------------------------------------------------------------
# Z04  |zeta(1 - w)| <= K |w + 1|^E |zeta(w)| on 1/2 <= Re w <= sigma_hi
# ---------------------------------------------------------------------------

def _chi_factor(w):
    """zeta(1 - w) / zeta(w) = 2 (2 pi)^(-w) cos(pi w / 2) Gamma(w)."""
    return 2 * (-(w * (2 * acb.pi()).log())).exp() * (w / 2).cos_pi() * w.gamma()


def zeta_one_sub(p):
    s0, s1, K, E, T = Q(p["sigma_lo"]), Q(p["sigma_hi"]), Q(p["K"]), int(p["E"]), p["T"]
    with ctx.workprec(C.bits(p)):
        def f(box):
            w = cball(box)
            return _abs_ball(_chi_factor(w)) / (A(K) * _abs_ball(w + 1) ** E)
        boxes = C.boxes2((float(s0), float(s1)), (0.0, T), 8, max(4, int(8 * T)))
        res = sup_bnb(f, boxes, tol=p.get("tol", 1e-4), stop_above=1.0,
                      max_boxes=p.get("max_boxes", 400000))
        # the statement itself, with no functional equation assumed, at sample points
        defect, direct_ok, n = 0.0, True, 0
        for sg in (Fraction(1, 2), Fraction(3, 4), Fraction(3, 2), Fraction(3), s1):
            for t in (Fraction(1, 2), Fraction(3), Fraction(14134725, 10 ** 6), Fraction(30)):
                if sg > s1 or t > T:
                    continue
                w = acb(A(sg), A(t))
                l = (1 - w).zeta(); r = w.zeta()
                defect = max(defect, up((l - _chi_factor(w) * r).abs_upper() / (r.abs_lower() + l.abs_lower())))
                ok = l.abs_upper() <= A(K) * (w + 1).abs_lower() ** E * r.abs_lower()
                if not ok and res["lo"] <= 1.0:
                    direct_ok = False
                n += 1
    v = verdict_from_sup(res)
    if v and not direct_ok:
        v = None
    return result(v, res["boxes"] + n, margin=None if v is False else 1 - res["hi"],
                  tightest=dict(w=res["argmax"]), sharp=_sharp(res, K) if v else None,
                  slack=[1 / res["hi"], 1 / res["lo"]] if v else None,
                  sup_ratio=[res["lo"], res["hi"]], tight=res["tight"],
                  witness=dict(w=res["argmax"], ratio_lower=res["lo"]) if v is False else None,
                  fe_defect_at_samples=defect, direct_samples=n,
                  tested_range=f"{float(s0)} <= Re w <= {float(s1)}, |Im w| <= {T}",
                  notes="cover of the quotient zeta(1-w)/zeta(w) written by the functional equation; "
                        "the literal inequality is evaluated at sample points, where the functional "
                        "equation's relative defect is also measured")


# ---------------------------------------------------------------------------
# Z05/Z06  |zeta(s) - sum_{n<=M} n^-s - M^(1-s)/(s-1)| <= c |s|/Re s * M^(-Re s)
# ---------------------------------------------------------------------------
#
# f_M(s) = zeta(s) - sum_{n<=M} n^-s - M^(1-s)/(s-1) is entire. With g(s) = zeta(s) - 1/(s-1)
# (Arb's deflated zeta) and u = (1 - s) log M,
#     f_M(s) = g(s) - sum_{n<=M} n^-s + log M * phi(u),      phi(u) = (e^u - 1)/u,
# which has no singularity at s = 1.

_PHI_TERMS = 30
_PHI_TAIL = 1e-18      # > L^j 2^(N+1)/(N+1)! for N = 30, L <= log 1000, j <= 8, |u| <= 1/2


def _hM_series(c, n, M):
    """Taylor coefficients at c of h_M(s) = M^s f_M(s)."""
    x = acb_series([c, 1], prec=n)
    tot = x.zeta(1, True)
    for k in range(1, M + 1):
        tot = tot - (x * (-arb(k).log())).exp() if k > 1 else tot - 1
    if M > 1:
        L = arb(M).log()
        u = (1 - x) * L
        if abs(float((1 - c).abs_upper()) * float(L.mid())) >= 0.5:
            tot = tot - (u.exp() - 1) / (x - 1)
        else:
            phi = acb_series([acb(0)], prec=n)
            for k in range(_PHI_TERMS - 1, -1, -1):
                phi = phi * u + arb(1) / arb.fac_ui(k + 1)
            tot = tot + L * phi
            tot = acb_series([tot[k] + acb(arb(0, _PHI_TAIL), arb(0, _PHI_TAIL)) for k in range(n)], prec=n)
        tot = tot * (x * L).exp()
    return [tot[k] for k in range(n)]


def _fM_ball(B, M):
    tot = acb_series([B, 1], prec=1).zeta(1, True)[0]
    for k in range(1, M + 1):
        tot = tot - (B * (-arb(k).log())).exp() if k > 1 else tot - 1
    if M > 1:
        L = arb(M).log()
        u = (1 - B) * L
        if u.abs_lower() > 0.5:
            tot = tot + L * ((u.exp() - 1) / u)
        elif u.abs_upper() < 1:
            phi = acb(0)
            for k in range(_PHI_TERMS - 1, -1, -1):
                phi = phi * u + arb(1) / arb.fac_ui(k + 1)
            tot = tot + L * (phi + acb(arb(0, 1e-25), arb(0, 1e-25)))     # tail < 2/31!
        else:
            return acb(arb("nan"))
    return tot


def _hM_ball(B, M):
    v = _fM_ball(B, M)
    return v * (B * arb(M).log()).exp() if M > 1 else v


def zeta_partial_sum(p):
    M, c, s1, T = int(p["M"]), Q(p["c"]), Q(p["sigma_hi"]), p["T"]
    with ctx.workprec(C.bits(p)):
        # the ratio LHS/RHS equals |h_M(s)| * (Re s/|s|) / c, and Re s/|s| <= 1 is largest at the
        # corner of a box nearest the real axis and farthest to the right
        def f(box):
            (x0, x1), (y0, y1) = box
            if _is_point(box):
                s = acb(arb(x0), arb(y0))
                return _abs_ball(_hM_ball(s, M)) * (s.real / s.abs_lower()) / A(c) if y0 else _abs_ball(_hM_ball(s, M)) / A(c)
            tb = C.taylor_ball(lambda cc, n: _hM_series(cc, n, M),
                               lambda B: up(_hM_ball(B, M).abs_upper()), cball(box), order=8)
            if tb is None:
                return _inf_ball()
            geo = arb(x1) / (arb(x1) ** 2 + arb(y0) ** 2).sqrt() if y0 else arb(1)
            return ball(0.0, up(tb[0].abs_upper() * geo / A(c)))
        boxes = C.boxes2((0.0, float(s1)), (0.0, T), 16, max(4, int(4 * T)))
        res = sup_bnb(f, boxes, tol=p.get("tol", 2e-3), stop_above=1.0,
                      max_boxes=p.get("max_boxes", 200000),
                      probes=lambda b: [(0.5 * (b[0][0] + b[0][1]), b[1][0])])     # the edge nearest the real axis
    v = verdict_from_sup(res)
    return result(v, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(s=res["argmax"]),
                  sharp=[float(c) * res["lo"], float(c) * res["hi"]] if v else None,
                  slack=[1 / res["hi"], 1 / res["lo"]] if v else None, sup_ratio=[res["lo"], res["hi"]],
                  tight=res["tight"],
                  witness=dict(s=res["argmax"], ratio_lower=res["lo"]) if v is False else None,
                  tested_range=f"0 < Re s <= {float(s1)}, |Im s| <= {T} (Im < 0 by conjugation)",
                  notes="complete cover of the closed rectangle, the removable singularity at s = 1 "
                        "included (deflated zeta); the supremum 1/2 is approached as s -> 0+ and is "
                        "not attained")


# ---------------------------------------------------------------------------
# Z07  c <= |zeta_1(a + it)|, zeta_1(s) = (s - 1) zeta(s)
# ---------------------------------------------------------------------------

def zeta1_lower(p):
    c, a, T = Q(p["c"]), Q(p["a"]), p["T"]
    with ctx.workprec(C.bits(p)):
        def f(box):
            s = acb(A(a), ball(*box[0]))
            z = (s - 1) * s.zeta()
            if not (z.abs_lower() > 0):
                return _inf_ball()
            return A(c) / _abs_ball(z)
        res = sup_bnb(f, [(b,) for b in C.grid(0.0, T, max(8, int(8 * T)))], tol=p.get("tol", 1e-4),
                      stop_above=1.0)
        # the tail: |zeta(a + it)| >= zeta(2a)/zeta(a) for a > 1 (Euler product), |s - 1| >= a - 1
        aa = A(a)
        floor_all_t = (aa - 1) * (2 * aa).zeta() / aa.zeta()
        tail_ok = bool(floor_all_t >= A(c))
    v = verdict_from_sup(res)
    grade_note = ("every t: the elementary floor (a-1) zeta(2a)/zeta(a) = %.6f is at least c"
                  % float(floor_all_t.mid())) if tail_ok else "tail not covered by the elementary floor"
    return result(v if (v is not True or tail_ok) else True, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(t=res["argmax"][0]), sharp=[float(c) / res["hi"], float(c) / res["lo"]],
                  slack=[1 / res["hi"], 1 / res["lo"]], sup_ratio=[res["lo"], res["hi"]],
                  tail_covered=tail_ok, witness=dict(t=res["argmax"][0]) if v is False else None,
                  tested_range=f"|t| <= {T} by cover; all t by the Euler-product floor" if tail_ok else f"|t| <= {T}",
                  notes=grade_note)


# ---------------------------------------------------------------------------
# Z08a  zeta (or a decoy Hurwitz zeta) has no zero on the real interval (a, b), b <= 1
# ---------------------------------------------------------------------------

def _sign(x):
    if x > 0:
        return 1
    if x < 0:
        return -1
    return 0


def real_nonvanishing(p):
    a, b = Q(p["a"]), Q(p["b"])
    hur = p.get("hurwitz")                 # None for zeta, else the Hurwitz parameter (decoy)
    r_in, r_out = 0.25, 0.3125
    with ctx.workprec(C.bits(p)):
        def fz(s):
            return s.zeta(A(Q(hur))) if hur else s.zeta()

        def enclose(x0, x1):
            S = acb(ball(x0, x1))
            if hur:
                tb = C.taylor_ball(lambda c, n: list(acb_series([c, 1], prec=n).zeta(A(Q(hur)))),
                                   lambda B: up(fz(B).abs_upper()), S, poles=((1.0, 0.0),))
            else:
                tb = _zeta_tb(S)
            return fz(S).real if tb is None else tb[0].real
        top = float(b) - r_in if b == 1 else float(b)
        # phase 1: signs at points; two opposite strict signs, or an exact zero, refute the statement
        n, prev = 0, None
        steps = 2048
        for i in range(1, steps + 1):
            x = float(a) + (top - float(a)) * i / steps
            v = fz(acb(arb(x))).real
            n += 1
            if v.is_zero():
                return result(False, n, witness=dict(point=x, why="the value is an exact zero (a trivial zero)"))
            sg = _sign(v)
            if prev is not None and sg * prev[1] < 0:
                return result(False, n, witness=dict(bracket=[prev[0], x],
                              why="opposite strict signs at the two ends: a zero by continuity"))
            if sg:
                prev = (x, sg)
        # phase 2: sign enclosure on (a, top]
        stack = C.grid(float(a), top, 64)
        min_abs, where = math.inf, None
        while stack:
            x0, x1 = stack.pop()
            n += 1
            v = enclose(x0, x1)
            if _sign(v):
                m = lo(v.abs_lower())
                if m < min_abs:
                    min_abs, where = m, [x0, x1]
                continue
            if x1 - x0 < 2 ** -30:
                return result(None, n, notes=f"undecided near {x0}")
            m = 0.5 * (x0 + x1)
            stack += [(x0, m), (m, x1)]
        near_one = None
        if b == 1:
            def fc(box):
                th = ball(*box[0]) * 2
                z = 1 + arb(r_out) * acb(th.cos_pi(), th.sin_pi())
                return _abs_ball((z - 1) * fz(z) - 1)
            near_one = sup_bnb(fc, [(bx,) for bx in C.grid(0.0, 1.0, 256)], tol=1e-2)
            n += near_one["boxes"]
    ok = near_one is None or near_one["hi"] < 1
    return result(True if ok else None, n, margin=min_abs, tightest=dict(interval=where),
                  inf_abs_value_lower=min_abs,
                  near_one_sup_of_h_minus_1=None if near_one is None else near_one["hi"],
                  notes="sign enclosure on (a, 3/4]; on |s - 1| <= 5/16 the entire function (s-1)f(s) stays "
                        "within distance < 1 of its value 1 at s = 1 (maximum principle on the circle), so f "
                        "has no zero there; the infimum of |f| is approached at the left end")


# ---------------------------------------------------------------------------
# Z08b / L05 / L06  real characters: values, L at points, real zeros
# ---------------------------------------------------------------------------

def _conrey_with_values(q, values):
    """The Dirichlet character mod q with the given values on units (dict a -> +-1 or exponent)."""
    G = dirichlet_group(q)
    ex = G.exponent()
    for n in range(1, q + 1):
        if math.gcd(n, q) != 1:
            continue
        ch = dirichlet_char(q, n)
        if all(ch.chi_exponent(a) == (0 if v == 1 else ex // 2) for a, v in values.items()):
            return ch
    raise ValueError("no such character")


def _real_char(q, d):
    """Kronecker symbol (d/.) restricted to residues mod q, as a flint character."""
    vals = {a: C.kronecker(d, a) for a in range(1, q) if math.gcd(a, q) == 1}
    return _conrey_with_values(q, vals), vals


def _l_hurwitz(q, vals, s):
    """L(s, chi) = q^-s sum_a chi(a) zeta(s, a/q), an independent route."""
    v = acb(0)
    for a, x in vals.items():
        v += x * s.zeta(arb(a) / q)
    return v * acb(q) ** (-s)


def _bern_poly(k, x):
    x = Fraction(x)
    return {1: x - Fraction(1, 2), 2: x * x - x + Fraction(1, 6),
            3: x ** 3 - Fraction(3, 2) * x * x + Fraction(1, 2) * x}[k]


def _l_nonpositive_exact(q, vals, k):
    """L(1 - k, chi) = -B_{k,chi}/k with B_{k,chi} = q^(k-1) sum_a chi(a) B_k(a/q), exact."""
    B = q ** (k - 1) * sum(x * _bern_poly(k, Fraction(a, q)) for a, x in vals.items())
    return -B / k


def chi8_real_nonvanishing(p):
    """L(sigma, chi) != 0 for sigma > a (or >= a when closed), chi the Mathlib ZMod.chi_8."""
    a, closed = Q(p["a"]), bool(p.get("closed", False))
    vals = {1: 1, 7: 1, 3: -1, 5: -1}                      # Mathlib ZModChar.lean:118
    ch = _conrey_with_values(8, vals)
    L0 = _l_nonpositive_exact(8, vals, 1)                  # exact L(0, chi)
    n = 0
    with ctx.workprec(C.bits(p)):
        # route check: flint's L against the Hurwitz formula
        dmax = 0.0
        for x in ("1/3", "1", "3/2"):
            s = acb(A(x))
            dmax = max(dmax, up((ch.l(s) - _l_hurwitz(8, vals, s)).abs_upper()))
        if a < 0 or (a == 0 and closed):
            # the trivial zeros of an even character: exact
            for k in (1, 3, 5):
                if Q(1 - k) > a or (Q(1 - k) == a and closed):
                    if _l_nonpositive_exact(8, vals, k) == 0:
                        return result(False, 1, witness=dict(sigma=1 - k,
                                      why="L(1-k, chi) = -B_{k,chi}/k = 0 by exact rational arithmetic"))
        if a != 0 or L0 != 0:
            return result(None, 0, notes="this check handles a = 0 for an even character only")
        delta = 0.125
        # (i) L(0) = 0 exactly and L' > 0 on [0, delta]: L > 0 on (0, delta]
        d_lo = math.inf
        # one Taylor model centred at s = 0 exactly (Arb's L is undefined on a ball containing 0,
        # so the circle bounding the remainder has radius 6 * delta and stays away from 0)
        n += 1
        tb = C.taylor_ball(lambda c, k: list(acb_series([c, 1], prec=k).dirichlet_l(ch)),
                           lambda B: up(ch.l(B).abs_upper()), acb(arb(0, delta)), order=10)
        if tb is None or not (tb[1].real > 0):
            return result(None, n, notes="derivative not enclosed away from 0 near 0")
        d_lo = lo(tb[1].real)
        # (ii) [delta, 2] by sign enclosure
        m = math.inf
        stack = C.grid(delta, 2.0, 64)
        while stack:
            x0, x1 = stack.pop()
            n += 1
            tb = C.taylor_ball(lambda c, k: list(acb_series([c, 1], prec=k).dirichlet_l(ch)),
                               lambda B: up(ch.l(B).abs_upper()), acb(ball(x0, x1)))
            v = ch.l(acb(ball(x0, x1))).real if tb is None else tb[0].real
            if v > 0:
                m = min(m, lo(v))
            elif x1 - x0 < 1e-9:
                return result(None, n, notes=f"undecided near {x0}")
            else:
                mid = 0.5 * (x0 + x1)
                stack += [(x0, mid), (mid, x1)]
        # (iii) sigma >= 2: |L - 1| <= zeta(2) - 1 < 1
        tail = arb(2).zeta() - 1
        ok_tail = bool(tail < 1)
    return result(True if ok_tail else None, n, margin=0.0, tightest=dict(sigma="-> 0+"),
                  inf_on_delta_2=m, derivative_lower_near_0=d_lo, route_defect=dmax,
                  notes="L(0, chi) = 0 exactly, so inf |L| over sigma > 0 is 0 and the hypothesis "
                        "0 < sigma is sharp; L' > 0 on [0, 1/8], sign enclosure on [1/8, 2], "
                        "|L - 1| <= zeta(2) - 1 beyond")


def l_point_nonzero(p):
    """L(s0, (d/.)) != 0 for a real character mod q at an integer point s0 <= 1."""
    q, d, s0 = int(p["q"]), int(p["d"]), int(p["s"])
    ch, vals = _real_char(q, d)
    if s0 <= 0:
        v = _l_nonpositive_exact(q, vals, 1 - s0)
        return result(v != 0, 1, margin=abs(float(v)), exact_value=str(v),
                      witness=None if v != 0 else dict(s=s0, why="L(1-k, chi) = -B_{k,chi}/k = 0 exactly"))
    with ctx.workprec(C.bits(p, 128)):
        s = acb(s0)
        v1 = ch.l(s)
        v2 = -sum(x * (arb(a) / q).digamma() for a, x in vals.items()) / q if s0 == 1 else _l_hurwitz(q, vals, s)
        v3 = arb.pi() / arb(-d).sqrt() if (s0 == 1 and d == -7) else None     # class number formula, h = 1, w = 2
        agree = v1.real.overlaps(v2 if isinstance(v2, arb) else v2.real) and (v3 is None or v1.real.overlaps(v3))
        nz = bool(v1.abs_lower() > 0)
    return result(True if (nz and agree) else None, 3, margin=lo(v1.abs_lower()),
                  value=float(v1.real.mid()), routes_agree=agree,
                  notes="three routes: Arb's Dirichlet L, the digamma formula, the class number formula")


def _cyclotomic(n):
    """Phi_n as an integer coefficient list (low degree first), by exact division."""
    def divide(num, den):
        num = num[:]
        out = [0] * (len(num) - len(den) + 1)
        for i in range(len(out) - 1, -1, -1):
            out[i] = num[i + len(den) - 1] // den[-1]
            for j, dj in enumerate(den):
                num[i + j] -= out[i] * dj
        assert not any(num), "inexact division"
        return out
    poly = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            poly = divide(poly, _cyclotomic_cached(d))
    return poly


_CYC = {}


def _cyclotomic_cached(n):
    if n not in _CYC:
        _CYC[n] = _cyclotomic(n)
    return _CYC[n]


def _vanishes_at_root_of_unity(coeffs, E):
    """Is sum_k coeffs[k] zeta_E^k = 0 exactly?  Reduce modulo Phi_E over the integers."""
    phi = _cyclotomic_cached(E)
    num = list(coeffs) + [0] * max(0, len(phi) - len(coeffs))
    for i in range(len(num) - len(phi), -1, -1):
        c = num[i + len(phi) - 1]
        if c:
            for j, dj in enumerate(phi):
                num[i + j] -= c * dj
    return not any(num)


def l_zero_at_origin(p):
    """Primitive chi != 1 of the stated parity mod N <= N_max: L(0,chi) = 0 with order exactly 1."""
    parity = {"even": 0, "odd": 1}[p["parity"]]
    n, min_d, where, bad = 0, math.inf, None, None
    with ctx.workprec(C.bits(p)):
        for N in range(2, int(p["N_max"]) + 1):
            E = dirichlet_group(N).exponent()
            for a in range(1, N):
                if math.gcd(a, N) != 1:
                    continue
                ch = dirichlet_char(N, a)
                if ch.is_principal() or not ch.is_primitive() or ch.parity() != parity:
                    continue
                n += 1
                # L(0, chi) = -(1/N) sum_b chi(b) b, exactly, in Z[zeta_E]
                coeffs = [0] * E
                for b in range(1, N):
                    e = ch.chi_exponent(b)
                    if e is not None:
                        coeffs[e] += b
                zero = _vanishes_at_root_of_unity(coeffs, E)
                ser = acb_series([acb(0), 1], prec=2).dirichlet_l(ch)
                if not zero:
                    if bad is None:
                        bad = dict(N=N, conrey=a, L0=[float(ser[0].real.mid()), float(ser[0].imag.mid())],
                                   why="sum chi(b) b is nonzero in Z[zeta], exact reduction mod the cyclotomic polynomial")
                    continue
                if not ser[0].contains(0):
                    return result(None, n, notes=f"routes disagree at N={N}, n={a}")
                d = lo(ser[1].abs_lower())
                if d <= 0:
                    return result(None, n, notes=f"derivative not separated from 0 at N={N}, n={a}")
                if d < min_d:
                    min_d, where = d, dict(N=N, conrey=a)
    if bad is not None:
        return result(False, n, witness=bad)
    return result(True, n, margin=min_d, tightest=where, min_abs_derivative=min_d,
                  notes="L(0,chi) = 0 by exact arithmetic in the cyclotomic integers; order exactly 1 "
                        "because the Arb enclosure of L'(0,chi) excludes 0")


# ---------------------------------------------------------------------------
# Z09  zeta(-(2m + off)) != 0
# ---------------------------------------------------------------------------

def _bernoulli_own(nmax):
    B = [Fraction(1)]
    for m in range(1, nmax + 1):
        B.append(-sum(Fraction(math.comb(m + 1, k)) * B[k] for k in range(m)) / (m + 1))
    return B


def zeta_neg_integers(p):
    off, M = int(p["off"]), int(p["M"])
    own = _bernoulli_own(60)
    min_abs, where = None, None
    with ctx.workprec(C.bits(p)):
        for m in range(M + 1):
            n = 2 * m + off
            b = fmpq.bernoulli(n + 1)
            if n + 1 <= 60:
                assert Fraction(int(b.p), int(b.q)) == own[n + 1], "Bernoulli routes disagree"
            val = Fraction(int(b.p), int(b.q)) * (-1) ** n / (n + 1)       # zeta(-n) = (-1)^n B_{n+1}/(n+1)
            if val == 0:
                return result(False, m + 1, witness=dict(m=m, point=-n, why="zeta(-n) = (-1)^n B_{n+1}/(n+1) = 0 exactly"))
            if m <= min(M, 60):
                z = acb(-n).zeta()
                assert z.real.overlaps(arb(fmpq(val.numerator, val.denominator))), "Arb and Bernoulli disagree"
            if min_abs is None or abs(val) < min_abs:
                min_abs, where = abs(val), dict(m=m, value=str(val))
    return result(True, M + 1, margin=float(min_abs), tightest=where,
                  tested_range=f"0 <= m <= {M}",
                  notes="exact Bernoulli numbers (FLINT, checked against an own recurrence to index 60 "
                        "and against Arb's zeta at the first points)")


# ---------------------------------------------------------------------------
# Z10 / A15  zeta(2k) = pi^(2k) / D
# ---------------------------------------------------------------------------

def zeta_even_value(p):
    k, D, N = int(p["k"]), Q(p["D"]), int(p["N"])
    own = _bernoulli_own(2 * k)
    coeff = (-1) ** (k + 1) * own[2 * k] * 2 ** (2 * k - 1) / math.factorial(2 * k)   # Euler
    exact = coeff == 1 / D
    with ctx.workprec(C.bits(p, 128)):
        S = arb(0)
        for n in range(N, 0, -1):
            S += 1 / arb(n) ** (2 * k)
        lo_b = S + 1 / ((2 * k - 1) * arb(N + 1) ** (2 * k - 1))
        hi_b = S + 1 / ((2 * k - 1) * arb(N) ** (2 * k - 1))
        claim = arb.pi() ** (2 * k) / A(D)
        inside = bool(lo_b < claim) and bool(claim < hi_b)
        outside = bool(claim < lo_b) or bool(claim > hi_b)
        width = up(hi_b - lo_b)
        arb_ok = arb(2 * k).zeta().overlaps(claim)
    if outside:
        return result(False, N, witness=dict(why="the claimed value lies outside the partial-sum bracket",
                                             bracket_width=width, exact_coefficient=str(coeff)))
    return result(True if (exact and inside and arb_ok) else None, N, margin=0.0, bracket_width=width,
                  exact_coefficient=str(coeff), sharp=str(1 / coeff), slack=1.0,
                  notes="an identity: the rational coefficient is exact under Euler's formula for zeta(2k); "
                        "independently the value lies in a partial-sum bracket of the stated width")


def zeta_logderiv_limit(p):
    """zeta'/zeta(s) + 1/(s-1) -> L as s -> 1, L = sign * Euler's constant: measured on shrinking radii."""
    sign = int(p.get("sign", 1))
    out = []
    with ctx.workprec(C.bits(p, 256)):
        target = sign * arb.const_euler()
        for k in (2, 4, 8, 12, 16):
            eps = Fraction(1, 10 ** k)
            worst = 0.0
            for th in (0, Fraction(1, 3), Fraction(1, 2), Fraction(7, 5)):
                s = 1 + A(eps) * acb(arb.cos_pi_fmpq(fmpq(Q(th).numerator, Q(th).denominator)),
                                     arb.sin_pi_fmpq(fmpq(Q(th).numerator, Q(th).denominator)))
                z = acb_series([s, 1], prec=2).zeta()
                g = z[1] / z[0] + 1 / (s - 1)
                worst = max(worst, up((g - target).abs_upper()))
                low = lo((g - target).abs_lower())
            out.append((k, worst, low))
    # consistent with the limit: error at radius 10^-k at most 2 * 10^-k
    ok = all(w <= 2 * 10.0 ** -k for k, w, _ in out)
    refuted = out[-1][2] > 1e-3
    return result(False if refuted else (True if ok else None), len(out) * 4, margin=out[-1][1],
                  errors_by_radius={f"1e-{k}": w for k, w, _ in out},
                  witness=dict(why="at radius 1e-16 the value stays at distance > 1e-3 from the claimed limit",
                               distance_lower=out[-1][2]) if refuted else None,
                  tested_range="radii 1e-2 .. 1e-16, four directions",
                  notes="a limit is measured, not enclosed: the distance to the claimed limit shrinks "
                        "linearly with the radius")


# ---------------------------------------------------------------------------
# Gamma on the line 1/2 and on a strip
# ---------------------------------------------------------------------------

def gamma_half_identity(p):
    cosh_scale = p.get("cosh_scale", "pi")
    worst = 0.0
    with ctx.workprec(C.bits(p, 256)):
        for t in ("0", "1/7", "1/2", "1", "2", "5", "10", "30", "60"):
            tt = A(t)
            lhs = acb(arb(1) / 2, tt).gamma().abs_upper() ** 2
            lhs_lo = acb(arb(1) / 2, tt).gamma().abs_lower() ** 2
            arg = arb.pi() * tt if cosh_scale == "pi" else tt
            rhs = arb.pi() / arg.cosh()
            if bool(lhs < rhs) or bool(lhs_lo > rhs):
                return result(False, 1, witness=dict(t=t, lhs=float(lhs.mid()), rhs=float(rhs.mid()),
                                                     why="the two enclosures are disjoint"))
            worst = max(worst, up((lhs - lhs_lo) / rhs))
    return result(True, 9, margin=0.0, slack=1.0, sharp="identity", max_relative_width=worst,
                  tested_range="nine values of t in [0, 60]",
                  notes="an identity cannot be decided by enclosures; both sides agree to the stated "
                        "relative width at every sample (it is the reflection formula at s = 1/2 + it)")


def gamma_half_line(p):
    K, T = Q(p["K"]), p["T"]
    with ctx.workprec(C.bits(p)):
        def f(box):
            t = ball(*box[0])
            c = arb(0.5 * (box[0][0] + box[0][1]))
            g = acb(arb(1) / 2, c).lgamma().real + arb.pi() * c / 2
            if not _is_point(box):       # mean value form: d/dt = pi/2 - Im psi(1/2 + it)
                g = g + (arb.pi() / 2 - acb(arb(1) / 2, t).digamma().imag) * (t - c)
            return g.exp() / A(K)
        res = sup_bnb(f, [(b,) for b in C.grid(0.0, T, int(4 * T))], tol=p.get("tol", 1e-4), stop_above=1.0)
        closed_sup = (2 * arb.pi()).sqrt()                 # sup over all t of sqrt(2 pi/(1 + e^(-2 pi t)))
        closed_ok = bool(closed_sup < A(K))
    v = verdict_from_sup(res)
    if v is False:
        return result(False, res["boxes"], witness=dict(t=res["argmax"][0], ratio_lower=res["lo"]))
    return result(True if (v and closed_ok) else None, res["boxes"], margin=1 - float(closed_sup.mid()) / float(K),
                  tightest=dict(t="-> infinity"), sharp=float(closed_sup.mid()),
                  slack=float(K) / float(closed_sup.mid()), sup_ratio_on_range=[res["lo"], res["hi"]],
                  tested_range=f"direct Gamma cover |t| <= {T}; every t by the closed form",
                  notes="|Gamma(1/2+it)|^2 e^(pi|t|) = 2 pi/(1 + e^(-2 pi |t|)) < 2 pi (reflection formula), "
                        "so the supremum sqrt(2 pi) is approached and not attained")


def gamma_decay(p):
    K, s0, s1, E, T = Q(p["K"]), Q(p["sigma_lo"]), Q(p["sigma_hi"]), int(p["E"]), p["T"]
    with ctx.workprec(C.bits(p)):
        lk = A(K).log()

        def logrho(w):
            return w.lgamma().real + arb.pi() * w.imag / 2 - lk - E * _abs_ball(w + 1).log()

        def f(box):
            if _is_point(box):
                return logrho(acb(arb(box[0][0]), arb(box[1][0]))).exp()
            W = cball(box)
            c = acb(arb(0.5 * (box[0][0] + box[0][1])), arb(0.5 * (box[1][0] + box[1][1])))
            psi = W.digamma(); inv = 1 / (W + 1)
            d_sigma = psi.real - E * inv.real
            d_t = -psi.imag + arb.pi() / 2 + E * inv.imag
            v = logrho(c) + d_sigma * (W.real - c.real) + d_t * (W.imag - c.imag)   # mean value form
            return v.exp()
        boxes = C.boxes2((float(s0), float(s1)), (0.0, T), 8, max(4, int(2 * T)))
        res = sup_bnb(f, boxes, tol=p.get("tol", 1e-3), stop_above=1.0, max_boxes=p.get("max_boxes", 400000))
        lim = (2 * arb.pi()).sqrt() / A(K)
    v = verdict_from_sup(res)
    return result(v, res["boxes"], margin=None if v is False else 1 - res["hi"],
                  tightest=dict(w=res["argmax"]), sharp=_sharp(res, K) if v else None,
                  slack=[1 / res["hi"], 1 / res["lo"]] if v else None, sup_ratio=[res["lo"], res["hi"]],
                  tight=res["tight"], limit_ratio_at_edge=float(lim.mid()),
                  witness=dict(w=res["argmax"], ratio_lower=res["lo"]) if v is False else None,
                  tested_range=f"{float(s0)} <= Re w <= {float(s1)}, |Im w| <= {T} (Im < 0 by conjugation)",
                  notes="complete cover of the rectangle in mean value form; on Re w = sigma_hi the ratio "
                        "tends to sqrt(2 pi)/K as Im w grows when sigma_hi - 1/2 = E")


# ---------------------------------------------------------------------------
# L01  1/(K (q+1)) <= L(1, chi) for real non-principal chi mod q
# ---------------------------------------------------------------------------

def _l1_digamma(d):
    f = abs(d)
    return -sum(C.kronecker(d, a) * (arb(a) / f).digamma() for a in range(1, f) if math.gcd(a, f) == 1) / f


def l_one_lower(p):
    K, Qmax = Q(p["K"]), int(p["Q"])
    worst, where, n = math.inf, None, 0
    with ctx.workprec(C.bits(p)):
        # transcription control: real characters mod q are the Kronecker symbols of the
        # fundamental discriminants d != 1 with |d| dividing q
        for q in range(1, min(Qmax, int(p.get("enum_q", 48))) + 1):
            real = []
            for a in range(1, q + 1):
                if math.gcd(a, q) == 1:
                    ch = dirichlet_char(q, a)
                    if ch.is_real() and not ch.is_principal():
                        real.append(ch)
            ds = [d for d in range(-q, q + 1) if d not in (0, 1) and q % abs(d) == 0 and C.is_fundamental(d)]
            assert len(real) == len(ds), (q, len(real), ds)
            for d in ds:
                ch, vals = _real_char(q, d)
                euler = math.prod(1 - Fraction(C.kronecker(d, pp), pp) for pp in C.factorint(q)) if q > 1 else 1
                v = _l1_digamma(d) * A(Fraction(euler))
                assert ch.l(acb(1)).real.overlaps(v), (q, d)
        for d in range(-Qmax, Qmax + 1):
            if d in (0, 1) or not C.is_fundamental(d):
                continue
            f = abs(d)
            L = _l1_digamma(d)
            for q in range(f, Qmax + 1, f):
                n += 1
                euler = math.prod(1 - Fraction(C.kronecker(d, pp), pp) for pp in C.factorint(q))
                val = A(K) * (q + 1) * L * A(Fraction(euler))          # the statement is val >= 1
                if val < 1:
                    return result(False, n, witness=dict(q=q, d=d, K_times_qplus1_times_L=float(val.mid())))
                if not (val >= 1):
                    return result(None, n, notes=f"undecided at q={q}, d={d}")
                if lo(val) < worst:
                    worst, where = lo(val), dict(q=q, d=d, L=float((L * A(Fraction(euler))).mid()))
    return result(True, n, margin=worst - 1, tightest=where, sharp=float(K) / worst, slack=worst,
                  tested_range=f"every real non-principal character mod q for 3 <= q <= {Qmax}",
                  notes="L(1,chi) by the digamma formula for the primitive character times exact Euler "
                        "factors; the enumeration and the values agree with Arb's Dirichlet characters "
                        "for small q")


# ---------------------------------------------------------------------------
# L02  1 <= K |L(sigma + it, psi)|
# ---------------------------------------------------------------------------

def l_inverse_line(p):
    K, sg, Mmax, T = Q(p["K"]), Q(p["sigma"]), int(p["M_max"]), p["T"]
    worst, where, n = 0.0, None, 0
    with ctx.workprec(C.bits(p)):
        for M in range(1, Mmax + 1):
            for a in range(1, M + 1):
                if math.gcd(a, M) != 1:
                    continue
                ch = dirichlet_char(M, a)

                poles = ((1.0, 0.0),) if ch.is_principal() else ()

                def f(box, ch=ch, poles=poles):
                    S = acb(A(sg), ball(*box[0]))
                    if _is_point(box):
                        z = ch.l(S)
                    else:
                        tb = C.taylor_ball(lambda c, n: list(acb_series([c, 1], prec=n).dirichlet_l(ch)),
                                           lambda B: up(ch.l(B).abs_upper()), S, poles=poles)
                        if tb is None:
                            return _inf_ball()
                        z = tb[0]
                    if not (z.abs_lower() > 0):
                        return _inf_ball()
                    return 1 / (A(K) * _abs_ball(z))
                res = sup_bnb(f, [(b,) for b in C.grid(0.0, T, int(2 * T))], tol=p.get("tol", 5e-3), stop_above=1.0)
                n += res["boxes"]
                if res["lo"] > 1:
                    return result(False, n, witness=dict(M=M, conrey=a, t=res["argmax"][0], ratio_lower=res["lo"]))
                if res["hi"] > 1:
                    return result(None, n, notes=f"undecided at M={M}, n={a}")
                if res["hi"] > worst:
                    worst, where = res["hi"], dict(M=M, conrey=a, t=res["argmax"][0], lo=res["lo"])
        theory = A(sg).zeta() / (2 * A(sg)).zeta() if sg > 1 else None
    return result(True, n, margin=1 - worst, tightest=where, sharp=float(K) * worst, slack=1 / worst,
                  theoretical_sharp=None if theory is None else float(theory.mid()),
                  tested_range=f"every character mod M <= {Mmax}, 0 <= t <= {T} (t < 0 via the conjugate character)",
                  notes="the infimum over all characters and t is zeta(2 sigma)/zeta(sigma) (Euler product), "
                        "approached only when chi(p) p^-it is near -1 for many primes at once; no finite "
                        "search of this size comes near it")


# ---------------------------------------------------------------------------
# L03  |L(1-w, chi)| <= K N^a |w+1|^E |L(w, chi^-1)| for primitive chi mod N
# ---------------------------------------------------------------------------

def l_one_sub(p):
    K, eN, E, Nmax = Q(p["K"]), int(p["expN"]), int(p["E"]), int(p["N_max"])
    pts = [(Fraction(1, 2), Fraction(0)), (Fraction(1, 2), Fraction(7, 3)), (Fraction(1), Fraction(0)),
           (Fraction(1), Fraction(1, 3)), (Fraction(2), Fraction(2)), (Fraction(7, 2), Fraction(10)),
           (Fraction(5), Fraction(0)), (Fraction(5), Fraction(10)), (Fraction(5), Fraction(30))]
    worst, where, n = 0.0, None, 0
    with ctx.workprec(C.bits(p)):
        for N in range(1, Nmax + 1):
            for a in range(1, N + 1):
                if math.gcd(a, N) != 1:
                    continue
                ch = dirichlet_char(N, a)
                if not ch.is_primitive():
                    continue
                inv = dirichlet_char(N, pow(a, -1, N) if N > 1 else 1)
                for sg, t in pts:
                    if N == 1 and sg == 1 and t == 0:
                        continue                         # the hypothesis chi 0 = 0 or w != 1
                    w = acb(A(sg), A(t))
                    lhs = ch.l(1 - w); rhs = A(K) * arb(N) ** eN * (w + 1).abs_lower() ** E * inv.l(w).abs_lower()
                    n += 1
                    if lhs.abs_lower() > A(K) * arb(N) ** eN * (w + 1).abs_upper() ** E * inv.l(w).abs_upper():
                        return result(False, n, witness=dict(N=N, conrey=a, w=[float(sg), float(t)],
                                                             lhs=lo(lhs.abs_lower()), rhs=up(rhs)))
                    if not (lhs.abs_upper() <= rhs):
                        return result(None, n, notes=f"undecided at N={N}, n={a}, w={sg}+{t}i")
                    r = up(lhs.abs_upper() / rhs)
                    if r > worst:
                        worst, where = r, dict(N=N, conrey=a, w=[float(sg), float(t)])
    return result(True, n, margin=1 - worst, tightest=where, sharp=float(K) * worst, slack=1 / worst,
                  tested_range=f"every primitive character of conductor <= {Nmax} at nine sample points",
                  notes="samples only, both sides evaluated directly; no functional equation assumed")


# ---------------------------------------------------------------------------
# A01  1 + z + c z^2 <= exp z for |z| <= R
# ---------------------------------------------------------------------------

def exp_ge_quad(p):
    c, R = Q(p["c"]), Q(p["R"])
    a = 0.25
    with ctx.workprec(C.bits(p)):
        def g(z):
            return z.exp() - 1 - z - A(c) * z * z
        # counterexamples are looked for at points first
        for x in [-float(R), float(R)] + [-float(R) * k / 64 for k in range(1, 64)] + [float(R) * k / 64 for k in range(1, 64)]:
            v = g(arb(x))
            if v < 0:
                return result(False, 1, witness=dict(z=x, value_upper=up(v)))
        # near 0: g(0) = g'(0) = 0 exactly and g'' = exp z - 2c > 0 on [-a, a], so g >= 0 there
        gpp = ball(-a, a).exp() - 2 * A(c)
        if not (gpp > 0):
            return result(None, 1, notes="convexity near 0 not established")
        n, m, where = 0, math.inf, None
        stack = [(-float(R), -a), (a, float(R))]
        while stack:
            x0, x1 = stack.pop()
            n += 1
            v = g(ball(x0, x1))
            if v > 0:
                if lo(v) < m:
                    m, where = lo(v), [x0, x1]
                continue
            if x1 - x0 < 1e-12:
                return result(None, n, notes=f"undecided near {x0}")
            mid = 0.5 * (x0 + x1)
            stack += [(x0, mid), (mid, x1)]
        zR = -A(R)                                        # (e^z - 1 - z)/z^2 increases in z: least at z = -R
        sharp = (zR.exp() - 1 - zR) / (zR * zR)
    return result(True, n, margin=0.0, tightest=dict(z=0, kind="double zero"), sharp=float(sharp.mid()),
                  slack=float(sharp.mid()) / float(c), min_away_from_0=m,
                  notes="complete: convexity on [-1/4, 1/4] with g(0) = g'(0) = 0, sign enclosure elsewhere; "
                        "the largest admissible coefficient is (e^-R - 1 + R)/R^2")


# ---------------------------------------------------------------------------
# A10a / A18b  exp(-t) <= K / t^E for t > 0   (t = c sqrt(log x) in A10a)
# ---------------------------------------------------------------------------

def exp_power(p):
    K, E = Q(p["K"]), int(p["E"])
    T = max(4.0 * E, 16.0)
    with ctx.workprec(C.bits(p)):
        def f(box):
            t = ball(*box[0])
            return t ** E * (-t).exp() / A(K)
        res = sup_bnb(f, [(b,) for b in C.grid(0.0, T, 256)], tol=1e-6, stop_above=1.0)
        peak = arb(E) ** E * arb(-E).exp()                  # max of t^E e^-t at t = E
        # literal form of A10a at sample (c, x): exp(-c sqrt(log x)) <= K / c^4 / (log x)^2
        lit_ok, n = True, 0
        if p.get("literal") == "sqrt_log":
            for c in ("1/100", "1", "4", "50"):
                for x in ("1000001/1000000", "2", "2718281828/1000000000", "1000", "1" + "0" * 40):
                    cc, lx = A(c), A(x).log()
                    lhs = (-cc * lx.sqrt()).exp(); rhs = A(K) / cc ** 4 / lx ** 2
                    n += 1
                    if lhs > rhs:
                        return result(False, n, witness=dict(c=c, x=x))
                    lit_ok = lit_ok and bool(lhs <= rhs)
    v = verdict_from_sup(res)
    if v is False:
        return result(False, res["boxes"], witness=dict(t=res["argmax"][0], ratio_lower=res["lo"]))
    return result(True if (v and lit_ok) else None, res["boxes"] + n, margin=1 - res["hi"],
                  tightest=dict(t=res["argmax"][0]), sharp=float(peak.mid()), slack=float(K) / float(peak.mid()),
                  sup_ratio=[res["lo"], res["hi"]],
                  notes="complete: cover of [0, T] and t^E e^-t is decreasing beyond t = E <= T; "
                        "the smallest admissible constant is (E/e)^E")


# ---------------------------------------------------------------------------
# A03  thin_ptw
# ---------------------------------------------------------------------------

def thin_ptw(p):
    K, el, er = Q(p["K"]), Q(p["e_lam"]), Q(p["e_rhs"])
    # exact reduction: for all c > 0  <=>  (v+lam)^2 <= K v^2  and  lam + sqrt v <= 2 v^(1-e_rhs)
    # on v >= 1, 0 < lam <= v^e_lam; worst case lam = v^e_lam; exponents compared as rationals
    red = bool(K >= 4 and el <= 1 and max(el, Fraction(1, 2)) <= 1 - er)
    n, worst = 0, None
    with ctx.workprec(C.bits(p, 128)):
        for c in ("1/1000", "1", "1000"):
            for lv in ("0", "1/1000000", "1", "7", "30", "100", "400"):          # v = exp(lv)
                for lam_kind in ("top", "half", "tiny"):
                    cc = A(c); v = A(lv).exp()
                    lam = v ** A(el) if lam_kind == "top" else (v ** A(el) / 2 if lam_kind == "half" else arb(1) / 1000)
                    n += 1
                    if lv == "0" and lam_kind == "top":
                        # v = lam = 1: both exponentials are exp(-c/2); the inequality is 4 <= K, exactly
                        if K < 4:
                            return result(False, n, witness=dict(c=c, v=1, lam=1, why="4 exp(-c/2) > K exp(-c/2), exact"))
                        continue
                    # log RHS - log LHS
                    D = (A(K).log() + 2 * v.log() - (cc / 2) * v ** A(er)
                         - 2 * (v + lam).log() + cc * v / (lam + v.sqrt()))
                    if D < 0:
                        return result(False, n, witness=dict(c=c, log_v=lv, lam=lam_kind, log_rhs_over_lhs=up(D)))
                    if not (D >= 0):
                        return result(None, n, notes=f"undecided at c={c}, log v={lv}, lam={lam_kind}")
                    if worst is None or lo(D) < worst[0]:
                        worst = (lo(D), dict(c=c, log_v=lv, lam=lam_kind))
    return result(True if red else None, n, margin=0.0, tightest=dict(v=1, lam=1, c="any", kind="equality"),
                  sharp=4.0, slack=float(K) / 4.0, reduction_holds=red,
                  least_positive_margin_on_grid=worst,
                  notes="exact reduction: the statement for every c > 0 is equivalent to K >= 4 and "
                        "e_lam <= 1 - e_rhs (with e_lam >= 1/2), compared as rationals; the literal "
                        "inequality is evaluated in Arb on a grid reaching v = e^400")
