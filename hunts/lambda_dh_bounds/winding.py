"""WP1, route 1: a decided argument-principle winding count for H_t.

Goal: decide that H_t (the backward-heat deformation of Xi_DH, in the
normalisation of MISSION.md and instrument.py) has a zero STRICTLY inside
the open upper half-plane at t1 = 23/400 = 0.0575 (stretch t2 = 36/625 =
0.0576), by counting zeros inside a rectangle R with 0 < y_lo <= Im z <=
y_hi, centred from data on the pair-5 site.  Every step that carries the
conclusion is an Arb ball with exact rational inputs; the float locating
pass steers box placement only and is labelled measured.

The count
---------

H_t is entire in z: the integrand e^{t u^2} Phi_DH(u) cos(zu) is entire in
z for every u >= 0, and the integral over [0, inf) converges locally
uniformly in z (the instrument's u-tail bound 4 e^{-cV}/(cV) is finite and
shrinking for every fixed t >= 0 and every bound on |Im z|), so Morera plus
Fubini give analyticity on every disc.  For a positively oriented rectangle
on which H_t never vanishes, the argument principle gives

    N = (1/2pi) * (total continuous variation of arg H_t around the boundary),

with N the number of zeros inside, counted with multiplicity.

Per boundary subsegment [z_a, z_b] (half-length h, midpoint on an
axis-parallel edge) two facts are decided, and together they make the
subsegment's contribution exact; this is the ``zeta.rigor._segment_delta``
pattern with the no-zero step adapted to the scale of H (see below):

1. **The image of the subsegment misses 0 and lies in an open half-plane.**
   Let g(d) = H_t(z(d)) along the segment, d in [-h, h], and let p(d) be
   the affine interpolant through the endpoint values.  Twice-integrated
   Taylor remainder: |g(d) - p(d)| <= (M2/2)(h-d)(h+d) <= M2 h^2 / 2,
   where M2 is a decided uniform bound for |H_t''| on the closed box
   (derivation below).  So the image lies in the convex tube
   {chord between endpoint values} + disc(M2 h^2 / 2).  A decided
   dist(0, chord) > M2 h^2 / 2 therefore puts the whole image in a convex
   set missing 0; a convex set missing 0 lies in an open half-plane through
   0 (separating hyperplane), so the continuous variation of arg along the
   subsegment obeys |Delta| < pi.
2. **The endpoint quotient pins Delta exactly.**  With
   q = H(z_b)/H(z_a), Delta == Arg q (mod 2pi).  A decided Re q > 0 gives
   |Arg q| < pi/2, and with |Delta| < pi from step 1 the congruence forces
   Delta = Arg q exactly (the alternatives differ by 2pi and would exceed
   pi in absolute value).

Undecidable subsegments are halved (each new endpoint is an exact dyadic,
evaluations cached), down to a budget; on exhaustion the routine returns
status "undecided" naming the failing segment, never an integer.  The sum
of the per-segment Arg q balls, divided by 2pi, must be a ball deciding a
single integer; the run demands that integer be 1.

The uniform second-derivative bound M2 (the analytic step)
----------------------------------------------------------

Direct ball evaluation of H_t'' over a whole segment is useless here: at
Re z ~ 240 the true |H_t| ~ 5e-83 while the integrand is O(1), so a ball
carrying the segment's width w has radius ~ w and can never exclude 0.
The bound is instead taken from a shifted u-contour, where the smallness
is pointwise and no cancellation is needed.

Write cos(zu) = (e^{izu} + e^{-izu})/2, G(u) = e^{t u^2} Phi_DH(u), so

    H_t^{(k)}(z) = (1/2) [ int_0^inf G(u) (iu)^k e^{izu} du
                         + int_0^inf G(u) (-iu)^k e^{-izu} du ].

G is holomorphic on the strip |Im u| < pi/4 (Phi_DH(u) = 4 e^{3u/2}
omega(e^{2u}) and the omega series converges locally uniformly where
Re e^{2u} = e^{2 Re u} cos(2 Im u) > 0) and G is even (n a_n e^{-pi n^2
e^{2u}/5} is even in u termwise).  Fix v in (0, pi/4).  Shift the first
integral to the contour 0 -> iv -> iv + inf and the second to
0 -> -iv -> -iv + inf; the far sides vanish (double-exponential decay of
G beats every other factor, cos(2 sigma) >= cos(2v) > 0 on the way).  The
two vertical legs cancel exactly for every k: at u = +/- i s the factor
(+/- iu)^k equals (-s)^k in both, G(+/- is) agree by evenness, both carry
e^{-zs}, and the orientations give +i ds and -i ds.  What remains is the
two horizontal rays, and for z = x + iy with x >= x_lo, |y| <= y_hi:

    |H_t^{(k)}(z)| <= e^{-x_lo v - t v^2} *
        int_0^inf (s^2 + v^2)^{k/2} e^{t s^2} |Phi_DH(s + iv)| cosh(y_hi s) ds

using |e^{iz(s+iv)}| = e^{-xv - ys}, |e^{-iz(s-iv)}| = e^{-xv + ys},
|e^{t(s +/- iv)^2}| = e^{t(s^2 - v^2)}, and |Phi(s - iv)| = |Phi(s + iv)|
(Phi is real on the real axis, kappa's ball decides it real, so Schwarz
reflection applies).  Inside the integral,

    |Phi_DH(s + iv)| <= 4 e^{3s/2} * Omega(e^{2s} cos 2v),

where Omega(rho) is any decided upper bound for sum_{n>=1} n e^{-pi n^2
rho / 5} (|a_n| <= 1 since kappa's ball decides 0 < kappa < 1).  Two such
bounds are computed and the smaller kept:

  * unimodal comparison: for f(x) = x e^{-a x^2}, a = pi rho / 5,
    sum_{n>=1} f(n) <= int_0^inf f(x) dx + 2 max f = 1/(2a) + 2 e^{-1/2} /
    sqrt(2a)  (each term except at most the two straddling the peak is
    dominated by a disjoint unit integral of f);
  * geometric domination: e^{-a n^2} <= e^{-a n} for n >= 1, so the sum is
    <= q/(1-q)^2 with q = e^{-a}, when q < 1.

The s-integral is bounded by interval-evaluation panel sums on [0, S]
(each panel's integrand evaluated on the arb hull of the panel, upper
bound times width, summed) plus a closed-form tail for s >= S copied from
the instrument's ``_u_tail`` algebra: with beta = 3/2 + y_hi + k and
(s + v)^k <= e^{k(s+v)}, cosh(y_hi s) <= e^{y_hi s}, Omega <= 2 q_s
(decided q_s <= 29/100 at s = S), the integrand is <= 8 e^{2v} e^{E(s)},
E(s) = t s^2 + beta s - (pi/5) cos(2v) e^{2s} <= -c e^{2s} with
c = (pi/5) cos 2v - (t S^2 + beta S) e^{-2S}, decided c > 0, and

    tail <= 8 e^{2v} int_S^inf e^{-c e^{2s}} ds <= 4 e^{2v} e^{-cV} / (cV),
    V = e^{2S}.

The contour height v = pi/4 - eps is chosen by trying a few exact dyadic
eps and keeping the smallest bound; the choice steers tightness only,
every candidate bound is decided.  At x_lo ~ 240.1 this yields M2 ~ 1e-78
against a measured |H_t''| scale ~ 1e-81: three digits of slack, which the
h^2 in the tube radius absorbs at subsegment half-lengths ~ 1e-3.

Mirror rectangle (the safety complement)
----------------------------------------

H_t(conj z) = conj(H_t(z)): the integrand has real coefficients (kappa's
ball decides kappa real) and H_t is real on the real axis, so zeros come
in conjugate pairs and the mirror rectangle in the lower half-plane
carries the same count N = 1 by symmetry; no compute is spent on it.  The
statement is recorded in the results file.

Vocabulary per MISSION.md: decided quantities are Arb enclosures with
backend and precision stated; the mpmath locating pass is measured.
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

from instrument import H_ball, _exact_q, _prec_guard, _q_to_arb  # noqa: E402

RESULTS_PATH = os.path.join(HERE, "winding_results.json")
BACKEND = "python-flint 0.9.0 (Arb)"

DEN = 1024  # all box coordinates are multiples of 1/1024 (exact dyadics)


def _dy(x: float) -> Fraction:
    """Nearest multiple of 1/DEN (an exact dyadic rational)."""
    return Fraction(round(x * DEN), DEN)


def _fr_str(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


# ---------------------------------------------------------------------------
# the measured locating pass (float grade, steers box placement only)
# ---------------------------------------------------------------------------


def locate_pair(ts: list[str], dps: int = 112) -> dict:
    """Newton-polish the pair-5 zero of H_t at each t (measured, mpmath).

    Reuses flow_repair's DHFlow quadrature (dps 112 >= the ~107 digits the
    height-240 cancellation costs; flow_repair used dps 107 for pair 5).
    Also scans the real axis near the site for sign changes of H_t, which
    is real there; an empty list means the box edges are clear of real
    zeros at float grade.  Nothing here is decided; the winding count does
    not depend on this pass being right, only the box placement does.
    """
    sys.path.insert(0, FLOW_REPAIR)
    from mpmath import mp
    from probe import DHFlow

    t0 = time.time()
    mp.dps = dps
    flow = DHFlow(dps=dps, z_scale=242.0)
    out: dict = {"dps": dps, "evaluator": "flow_repair DHFlow (measured)"}
    seed = mp.mpc("240.4165", "0.02")
    for t in ts:
        tq = mp.mpf(t)
        z = mp.mpc(seed)
        step = mp.mpf(1)
        for _ in range(40):
            h, dh = flow.H_and_dH(z, tq)
            step = h / dh
            z = z - step
            if abs(step) < mp.mpf(10) ** (-40):
                break
        h, dh = flow.H_and_dH(z, tq)
        sign_changes = []
        xs = [z.real + mp.mpf("0.1") * (k - 7) for k in range(15)]
        vals = [flow.H(x, tq).real for x in xs]
        for a, b, va, vb in zip(xs, xs[1:], vals, vals[1:]):
            if va * vb < 0:
                sign_changes.append([float(a), float(b)])
        out[t] = {
            "zstar_re": float(z.real),
            "zstar_im": float(z.imag),
            "newton_residual": float(abs(step)),
            "abs_dH_measured": float(abs(dh)),
            "real_axis_sign_changes_pm_0.7": sign_changes,
        }
        seed = z  # warm start for the next t
    out["seconds"] = round(time.time() - t0, 1)
    return out


# ---------------------------------------------------------------------------
# the decided uniform bound for |H_t''| on a half-strip
# ---------------------------------------------------------------------------


def _omega_sum_upper(rho: arb) -> arb | None:
    """A ball whose upper bound dominates sum_{n>=1} n e^{-pi n^2 rho / 5}.

    Valid for decided rho > 0.  Two routes (derivations in the module
    docstring): unimodal integral-plus-two-maxima, and geometric
    domination; the one with the smaller upper bound is returned.
    """
    a = arb.pi() * rho / 5
    if not (a > 0):
        return None
    b1 = 1 / (2 * a) + 2 * (arb(-1) / 2).exp() / (2 * a).sqrt()
    q = (-a).exp()
    one_minus = 1 - q
    if one_minus > 0:
        b2 = q / (one_minus * one_minus)
        if b2 < b1:
            return b2
    return b1


def second_derivative_bound(
    x_lo: Fraction,
    y_hi: Fraction,
    t: Fraction,
    prec: int = 300,
    S: Fraction = Fraction(5),
    n_panels: int = 800,
    eps_list: tuple[Fraction, ...] = (
        Fraction(1, 128),
        Fraction(1, 256),
        Fraction(1, 512),
        Fraction(1, 1024),
    ),
) -> dict:
    """A decided upper bound M2 >= sup |H_t''(z)| over Re z >= x_lo, |Im z| <= y_hi.

    Shifted-contour derivation in the module docstring (k = 2 case).  All
    arithmetic is Arb balls at ``prec``; panel sums evaluate the bounding
    integrand on the arb hull of each panel, so the sum dominates the
    integral on [0, S]; the closed-form tail handles [S, inf) with decided
    hypotheses (c > 0, q_S <= 29/100).  Returns the best (smallest) bound
    over the eps candidates; the candidate choice steers tightness only.
    """
    t0 = time.time()
    best: dict | None = None
    with _prec_guard(prec):
        t_b = _q_to_arb(_exact_q(t))
        x_b = _q_to_arb(_exact_q(x_lo))
        y_b = _q_to_arb(_exact_q(y_hi))
        S_b = _q_to_arb(_exact_q(S))
        for eps in eps_list:
            eps_b = _q_to_arb(_exact_q(eps))
            v = arb.pi() / 4 - eps_b
            cos2v = (2 * v).cos()
            if not (v > 0) or not (cos2v > 0):
                continue  # candidate outside the valid strip; skip
            # main range [0, S] by interval-evaluation panels
            h = S_b / n_panels
            total = arb(0)
            ok = True
            for j in range(n_panels):
                s = (h * j).union(h * (j + 1))
                om = _omega_sum_upper((2 * s).exp() * cos2v)
                if om is None:
                    ok = False
                    break
                val = (
                    (s * s + v * v)
                    * (t_b * s * s).exp()
                    * 4
                    * (3 * s / 2).exp()
                    * om
                    * (y_b * s).cosh()
                )
                total = total + arb(val.abs_upper()) * h
            if not ok:
                continue
            # tail beyond S (instrument _u_tail algebra, k = 2)
            V = (2 * S_b).exp()
            q_S = (-arb.pi() / 5 * V * cos2v).exp()
            beta = arb(3) / 2 + y_b + 2
            c = arb.pi() / 5 * cos2v - (t_b * S_b * S_b + beta * S_b) / V
            if not (c > 0) or not (q_S < arb(fmpq(29, 100))):
                continue
            tail = 4 * (2 * v).exp() * (-c * V).exp() / (c * V)
            J = total + tail
            M2 = (-x_b * v - t_b * v * v).exp() * J
            M2_up = arb(M2.abs_upper())
            if best is None or M2_up < arb(best["M2"].abs_upper()):
                best = {
                    "M2": M2_up,
                    "eps": eps,
                    "J_upper": float(J.abs_upper()),
                    "tail_upper": float(tail.abs_upper()),
                }
    if best is None:
        raise ValueError("no eps candidate satisfied the decided hypotheses")
    return {
        "M2": best["M2"],
        "M2_upper_float": float(best["M2"].abs_upper()),
        "v": f"pi/4 - {_fr_str(best['eps'])}",
        "eps": _fr_str(best["eps"]),
        "prec_bits": prec,
        "S": _fr_str(S),
        "n_panels": n_panels,
        "J_upper_float": best["J_upper"],
        "tail_upper_float": best["tail_upper"],
        "scope": f"decided upper bound for sup |H_t''| on Re z >= {_fr_str(x_lo)},"
                 f" |Im z| <= {_fr_str(y_hi)}",
        "backend": BACKEND,
        "seconds": round(time.time() - t0, 2),
    }


# ---------------------------------------------------------------------------
# the winding count
# ---------------------------------------------------------------------------


def _chord_clearance(A: acb, B: acb) -> arb:
    """A ball b with b.lower() <= dist(0, chord between the true values).

    A and B are balls containing the true endpoint values H(z_a), H(z_b).
    Cases on the foot of the perpendicular from 0 onto the chord's line,
    each decided over the balls (an undecided case falls through to bounds
    valid unconditionally):

      * foot before A (decided): distance is |A|;
      * foot beyond B (decided): distance is |B|;
      * otherwise: both the line distance |Im(conj(D) A)| / |D| (a lower
        bound for the segment distance always) and the triangle bound
        |A| - |D| (any chord point is A + tau D, tau in [0,1]) are valid;
        the one with the larger lower bound is returned.
    """
    D = B - A
    p = (D.conjugate() * (-A)).real
    d2 = (D.conjugate() * D).real
    if p < 0:
        return abs(A)
    if p > d2:
        return abs(B)
    cands = [abs(A) - abs(D)]
    if d2 > 0:
        cands.append(abs((D.conjugate() * A).imag) / d2.sqrt())
    best = cands[0]
    for c in cands[1:]:
        if c.lower() > best.lower():
            best = c
    return best


def winding_rectangle(
    box: tuple[Fraction, Fraction, Fraction, Fraction],
    t: Fraction,
    prec: int,
    m2_info: dict,
    max_segments: int = 6000,
    min_halflen: Fraction = Fraction(1, 2 ** 22),
    max_wall: float = 1200.0,
) -> dict:
    """The decided winding count of H_t around the rectangle ``box``.

    box = (x_lo, x_hi, y_lo, y_hi), all exact rationals, traversed
    counterclockwise (positively oriented), so the count is the number of
    zeros inside, with multiplicity.  Method and soundness argument are in
    the module docstring.  Returns a dict with status "decided" and the
    integer N, or status "undecided" naming the failing segment; never a
    guessed integer.
    """
    t0 = time.time()
    x_lo, x_hi, y_lo, y_hi = box
    if not (0 < y_lo < y_hi):
        raise ValueError("box must lie strictly inside the open upper half-plane")
    M2 = m2_info["M2"]

    corners = [(x_lo, y_lo), (x_hi, y_lo), (x_hi, y_hi), (x_lo, y_hi)]
    edges = [(corners[i], corners[(i + 1) % 4]) for i in range(4)]

    cache: dict[tuple, acb] = {}
    n_evals = [0]

    def Hval(zq: tuple[Fraction, Fraction]) -> acb:
        got = cache.get(zq)
        if got is None:
            got = H_ball(zq, t, prec)
            cache[zq] = got
            n_evals[0] += 1
        return got

    segments: list[dict] = []
    args: list[arb] = []
    min_chord_margin = math.inf
    min_ball_margin = math.inf
    fail: dict | None = None

    with _prec_guard(prec):
        half = arb(1) / 2
        for a, b in edges:
            stack = [(a, b)]
            while stack:
                if len(segments) + len(stack) > max_segments or (
                    time.time() - t0 > max_wall
                ):
                    fail = {
                        "reason": "budget exhausted",
                        "segment": {
                            "a": [_fr_str(stack[-1][0][0]), _fr_str(stack[-1][0][1])],
                            "b": [_fr_str(stack[-1][1][0]), _fr_str(stack[-1][1][1])],
                        },
                        "n_segments_done": len(segments),
                    }
                    break
                za, zb = stack.pop()
                halflen = (abs(zb[0] - za[0]) + abs(zb[1] - za[1])) / 2
                A = Hval(za)
                B = Hval(zb)
                hh = _q_to_arb(halflen)
                tube = M2 * hh * hh * half
                d = _chord_clearance(A, B)
                q = B / A
                decided = bool(d > tube) and bool(q.real > 0)
                if not decided:
                    if halflen / 2 < min_halflen:
                        fail = {
                            "reason": "min_halflen reached",
                            "segment": {
                                "a": [_fr_str(za[0]), _fr_str(za[1])],
                                "b": [_fr_str(zb[0]), _fr_str(zb[1])],
                            },
                            "n_segments_done": len(segments),
                        }
                        break
                    mid = ((za[0] + zb[0]) / 2, (za[1] + zb[1]) / 2)
                    stack.append((mid, zb))
                    stack.append((za, mid))
                    continue
                arg = q.arg()
                args.append(arg)
                d_lo = float(d.lower())
                tube_up = float(tube.upper())
                margin = math.log10(d_lo / tube_up) if tube_up > 0 else math.inf
                absA_lo = float(abs(A).lower())
                absB_lo = float(abs(B).lower())
                radA = max(
                    float((A.real.upper() - A.real.lower()) / 2),
                    float((A.imag.upper() - A.imag.lower()) / 2),
                )
                ball_margin = (
                    math.log10(min(absA_lo, absB_lo) / radA) if radA > 0 else math.inf
                )
                min_chord_margin = min(min_chord_margin, margin)
                min_ball_margin = min(min_ball_margin, ball_margin)
                segments.append(
                    {
                        "a": [_fr_str(za[0]), _fr_str(za[1])],
                        "b": [_fr_str(zb[0]), _fr_str(zb[1])],
                        "absH_lower": min(absA_lo, absB_lo),
                        "chord_dist_lower": d_lo,
                        "tube_radius_upper": tube_up,
                        "margin_digits": round(margin, 2),
                    }
                )
            if fail is not None:
                break

        result: dict = {
            "t": _fr_str(t),
            "t_float": float(t),
            "box": {
                "re_lo": _fr_str(x_lo),
                "re_hi": _fr_str(x_hi),
                "im_lo": _fr_str(y_lo),
                "im_hi": _fr_str(y_hi),
                "floats": [float(x_lo), float(x_hi), float(y_lo), float(y_hi)],
            },
            "prec_bits": prec,
            "backend": BACKEND,
            "M2_bound": {k: v for k, v in m2_info.items() if k != "M2"},
            "n_segments": len(segments),
            "n_H_evals": n_evals[0],
            "wall_seconds": round(time.time() - t0, 1),
        }
        if fail is not None:
            result["status"] = "undecided"
            result["failure"] = fail
            return result

        W = arb(0)
        for g in args:
            W = W + g
        N_ball = W / (2 * arb.pi())
        decided_one = bool(abs(N_ball - 1) < half)
        result["winding_sum_over_2pi"] = {
            "lower": float(N_ball.lower()),
            "upper": float(N_ball.upper()),
            # width computed here, inside the precision guard, because the
            # float lower/upper above cannot resolve a ~1e-38 ball around 1.0
            "width": float(N_ball.upper() - N_ball.lower()),
        }
        if decided_one:
            result["status"] = "decided"
            result["N"] = 1
        else:
            lo = math.ceil(float(N_ball.lower()))
            hi = math.floor(float(N_ball.upper()))
            ints = list(range(lo, hi + 1))
            if len(ints) == 1:
                result["status"] = "decided"
                result["N"] = ints[0]
            else:
                result["status"] = "undecided"
                result["failure"] = {
                    "reason": "winding ball does not decide a single integer",
                    "integers_in_ball": ints,
                }
        result["min_chord_margin_digits"] = round(min_chord_margin, 2)
        result["min_ball_margin_digits"] = round(min_ball_margin, 2)
        result["segments"] = segments
        return result


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def make_box(cy_locate: dict, re_half: float, y_hi_cap: float) -> tuple:
    """Exact dyadic box around the measured zero (placement is steering)."""
    cx = cy_locate["zstar_re"]
    cy = cy_locate["zstar_im"]
    x_lo = _dy(cx - re_half)
    x_hi = _dy(cx + re_half)
    y_lo = _dy(max(cy / 3, 0.003))
    y_hi = _dy(min(3.4 * cy, y_hi_cap))
    if not (0 < y_lo < Fraction(_exact_q(cy)) < y_hi):
        raise ValueError("box does not bracket the measured zero off-axis")
    return (x_lo, x_hi, y_lo, y_hi)


def main() -> None:
    t_all = time.time()
    t1 = Fraction("0.0575")   # 23/400, exact
    t2 = Fraction("0.0576")   # 36/625, exact
    prec = 420

    print("locating pass (measured, mpmath) ...", flush=True)
    loc = locate_pair(["0.0575", "0.0576"])
    print(json.dumps({k: v for k, v in loc.items() if k != "evaluator"}), flush=True)

    out: dict = {
        "hunt": "lambda_dh_bounds",
        "route": "WP1 route 1: segment-argument winding count",
        "backend": BACKEND,
        "locating_pass_measured": loc,
        "symmetry_note": (
            "H_t(conj z) = conj(H_t(z)): kappa's ball decides kappa real, the "
            "integrand has real coefficients and H_t is real on the real axis, "
            "so zeros come in conjugate pairs; the mirror rectangle in the "
            "lower half-plane therefore carries the same decided count N = 1 "
            "with no further computation."
        ),
    }

    runs = []
    for t, key, re_half, cap in [
        (t1, "0.0575", 0.25, 0.06),
        (t2, "0.0576", 0.20, 0.04),
    ]:
        box = make_box(loc[key], re_half, cap)
        print(f"t = {t}: box {[str(q) for q in box]}", flush=True)
        m2 = second_derivative_bound(box[0], box[3], t, prec=300)
        print(f"  M2 upper = {m2['M2_upper_float']:.3e}  (v = {m2['v']}, "
              f"{m2['seconds']} s)", flush=True)
        res = winding_rectangle(box, t, prec, m2)
        print(f"  status = {res['status']}  N = {res.get('N')}  "
              f"segments = {res['n_segments']}  evals = {res['n_H_evals']}  "
              f"wall = {res['wall_seconds']} s", flush=True)
        runs.append(res)

    out["t1_run"] = runs[0]
    out["t2_stretch_run"] = runs[1]

    floor = None
    if runs[0].get("N") == 1 and runs[0]["status"] == "decided":
        floor = "23/400"
    if runs[1].get("N") == 1 and runs[1]["status"] == "decided":
        floor = "36/625"
    out["decided_floor_t"] = floor
    out["headline"] = (
        None
        if floor is None
        else (
            f"decided: H_t has a zero strictly inside the open upper half-plane "
            f"at t = {floor}; with Dobner's half-line structure (Theorem 1, "
            f"arXiv:2005.05142) this gives Lambda_DH > {floor}.  Composite "
            f"grade: decided modulo that cited theorem."
        )
    )
    out["wall_seconds_total"] = round(time.time() - t_all, 1)

    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=1)
    print(f"wrote {RESULTS_PATH} ({out['wall_seconds_total']} s total)", flush=True)


if __name__ == "__main__":
    main()
