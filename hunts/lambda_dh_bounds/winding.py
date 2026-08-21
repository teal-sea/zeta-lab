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
Re e^{2u} = e^{2 Re u} cos(2 Im u) > 0), and G is even (derived in the
section "Why G is even" below; this is the step that cancels the vertical
legs and is what makes M2 a bound at all).  Fix v in (0, pi/4).  Shift the first
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
every candidate bound is decided.

How much slack M2 actually has (corrected 2026-08-16)
-----------------------------------------------------

At x_lo ~ 240.1 the bound is M2 = 1.1887e-78, against a directly measured
sup |H_t''| of 2.1357e-80 on the t1 box.  That is a factor of 55.7, i.e.
1.75 digits of slack.  The measurement is a 41 x 9 grid over the box plus
a 65-point sweep of the left edge at |Im z| <= y_hi, mpmath dps 140, by
direct quadrature of -int_0^inf e^{t u^2} Phi_DH(u) u^2 cos(zu) du on
flow_repair's Gauss-Legendre rule, which shares no code with the
shifted-contour bound; it is float grade, so *measured*.  The sup sits on
the box's top edge near Re z = 240.16, and |H_t''| falls off to the right
(9.7e-81 at x_lo + 1, 1.5e-83 at x_lo + 8), which is why the half-strip
scope Re z >= x_lo is not costing anything.

  CORRECTION (gate closure item b).  The superseded sentence read: "At
  x_lo ~ 240.1 this yields M2 ~ 1e-78 against a measured |H_t''| scale ~
  1e-81: three digits of slack, which the h^2 in the tube radius absorbs
  at subsegment half-lengths ~ 1e-3."  The scale was wrong by a factor of
  about 20 and the slack is 1.75 digits, not three.

The correction costs the count nothing: the tube radius is M2 h^2 / 2 and
the subdivision halves h until a segment decides, so a factor of 55.7 in
M2 is about three extra halvings in the worst case, not a lost decision.
What the slack does NOT buy is any margin against the derivation itself
being wrong, and that is the exposure: see control 5 in ``controls.py``,
where deflating M2 by 100 makes this routine return the WRONG integer
N = 0 with status "decided" and no complaint.  ``measured_h2_guard``
below is the cheap necessary check that lesion motivated.

Why G is even (the step that cancels the vertical legs)
-------------------------------------------------------

e^{t u^2} is even in u, so the whole content of the claim is

    Phi_DH(-u) = Phi_DH(u),   equivalently, with x = e^{2u},
    omega(1/x) = x^{3/2} omega(x),   omega(x) = sum_{n>=1} n a_n e^{-pi n^2 x/5}.

This is the theta transformation attached to the Davenport-Heilbronn
functional equation F(s) = F(1-s), and it is precisely what the constant
kappa is chosen to produce.  (The theta below is the theta of a Dirichlet
character; it is none of the three thetas in the repo's naming trap.)

(i) *From Hecke's transformation.*  Let chi be an odd primitive character
    mod 5 and theta_chi(x) = sum_{n>=1} n chi(n) e^{-pi n^2 x/5}.
    Classically (Hecke; Davenport, *Multiplicative Number Theory*, ch. 9;
    Iwaniec-Kowalski ch. 4),

        theta_chi(1/x) = -i tau(chi) 5^{-1/2} x^{3/2} theta_{conj chi}(x),
        tau(chi) = sum_{n mod 5} chi(n) e^{2 pi i n/5},  |tau(chi)| = 5^{1/2}.

    The period-5 pattern a = (1, kappa, -kappa, -1, 0) is real and
    supported off 5, so it is a real combination of the two odd characters
    mod 5: a_n = alpha chi(n) + conj(alpha) conj(chi)(n) with
    2 Re alpha = a_1 = 1 and Im alpha fixed by kappa, hence
    omega = alpha theta_chi + conj(alpha) theta_{conj chi}.  Applying the
    transformation to each half and matching the two independent theta
    terms, omega(1/x) = x^{3/2} omega(x) holds if and only if

        alpha = conj(alpha) * (-i tau(conj chi) 5^{-1/2}),

    one real condition on the one real unknown in alpha, hence on kappa
    (the two matched equations are conjugates of each other, using
    conj(tau(conj chi)) = chi(-1) tau(chi) = -tau(chi)).  That condition
    is the functional equation: it is the same equation
    ``instrument.kappa_ball`` solves as a linear solve on the completed
    L-functions at one point, and the same one ``zeta.epstein`` solves.
    So the evenness of Phi_DH is not an accident of the series; it is
    F(s) = F(1-s), transported.

(ii) *The Mellin transport, showing (i) and F(s) = F(1-s) are one fact.*
    omega(x) = O(1/x) as x -> 0+ (crudely, sum n e^{-pi n^2 x/5} <=
    5/(2 pi x) + O(x^{-1/2})) and O(e^{-pi x/5}) as x -> inf, so for
    Re w > 1 the Mellin transform converges absolutely and may be summed
    term by term:

        M(w) := int_0^inf omega(x) x^w dx/x
              = Gamma(w) (pi/5)^{-w} sum_{n>=1} a_n n^{1-2w}.

    With s = 2w - 1 this is M((s+1)/2) = (pi/5)^{-(s+1)/2}
    Gamma((s+1)/2) L(s) = F(s), the completed Davenport-Heilbronn
    function.  Substituting x -> 1/x,

        int_0^inf [x^{-3/2} omega(1/x)] x^w dx/x = M(3/2 - w)
                                                 = F(2 - 2w) = F(1 - s),

    so omega(1/x) = x^{3/2} omega(x) is exactly the statement that turns
    F(s) into F(1-s) under the transform.  The derivation is written in
    the direction Hecke -> functional equation, which is the sound one:
    the two Mellin integrals converge on the disjoint strips Re w > 1 and
    Re w < 1/2, so running the implication backwards would need an
    inversion argument in a strip they do not share.  F(s) = F(1-s) is in
    any case carried by this hunt as a cited classical fact (GATE.md,
    known assumption 5), and (i) puts the evenness at exactly the same
    standing rather than at a weaker one.

(iii) *Complex u, which is what the vertical legs need.*  (i) and (ii)
    give Phi_DH(-u) = Phi_DH(u) for real u.  Phi_DH is holomorphic on the
    strip |Im u| < pi/4 (same convergence statement as above), the strip
    is connected and symmetric under u -> -u, and Phi_DH(-u) - Phi_DH(u)
    is holomorphic there and vanishes on the real axis; by the identity
    theorem it vanishes on the whole strip.  That is what G(+i s) =
    G(-i s) requires at u = +/- i s, and the superseded justification did
    not reach it at all.

*Measured* (dps 260, both sides evaluated directly from the series with no
evenness fold, so the check is not circular): the relative defect
|Phi_DH(u) - Phi_DH(-u)| / |Phi_DH(u)| at real u reads

    u    = 0.05      0.1      0.25   0.5      1     1.5      2       2.5    3
    defect 1.8e-261  5.4e-261 0      2.6e-261 0     2.5e-257 1.6e-248 8.5e-225 2.4e-154

and at the complex points u = 0.5 + 0.5i, 1 + 0.7i, 1.5 - 0.6i,
2 + 0.75i inside the strip it is at or below 4.9e-260.  The growth with u
is the arithmetic, not the identity: at u the reflected evaluation runs
the series at the small argument e^{-2u}, where it is a cancellation
about (pi/5) e^{2u} / ln 10 digits deep, which is about 110 digits at
u = 3 and accounts for the whole of the 2.4e-154 there.  The gate
measured the same identity independently at relative 1.0e-34.

  CORRECTION (gate closure item b).  Until 2026-08-16 the evenness of G
  was justified, in full, by the parenthesis: "(n a_n e^{-pi n^2
  e^{2u}/5} is even in u termwise)".  That is false.  The individual term
  n a_n e^{-pi n^2 e^{2u}/5} carries e^{2u} at u and e^{-2u} at -u and is
  not even; neither is omega(e^{2u}).  The evenness lives in the product
  with the prefactor 4 e^{3u/2} and comes from the functional equation, as
  above.  The conclusion was and is true, so no decided number in
  ``winding_results.json`` moves: this repaired only the justification,
  and the re-run after the repair reproduced every decided value.

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


_FLOW_CACHE: dict[tuple, object] = {}


def _dhflow(dps: int, z_scale: float):
    """flow_repair's DHFlow quadrature, built once per (dps, z_scale).

    Measured, mpmath, float grade.  Two callers share it (the locating
    pass and ``measured_h2_guard``), so the Gauss-Legendre rule and its
    memoised Phi_DH node values are paid for once; construction arguments
    are unchanged from the original inline call, so the locating pass
    returns exactly what it returned before the cache existed.
    """
    key = (int(dps), float(z_scale))
    got = _FLOW_CACHE.get(key)
    if got is None:
        if FLOW_REPAIR not in sys.path:
            sys.path.insert(0, FLOW_REPAIR)
        from probe import DHFlow

        got = DHFlow(dps=int(dps), z_scale=float(z_scale))
        _FLOW_CACHE[key] = got
    return got


def locate_pair(ts: list[str], dps: int = 112) -> dict:
    """Newton-polish the pair-5 zero of H_t at each t (measured, mpmath).

    Reuses flow_repair's DHFlow quadrature (dps 112 >= the ~107 digits the
    height-240 cancellation costs; flow_repair used dps 107 for pair 5).
    Also scans the real axis near the site for sign changes of H_t, which
    is real there; an empty list means the box edges are clear of real
    zeros at float grade.  Nothing here is decided; the winding count does
    not depend on this pass being right, only the box placement does.
    """
    from mpmath import mp

    t0 = time.time()
    mp.dps = dps
    flow = _dhflow(dps, 242.0)
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
# the cheap necessary check on M2 (gate closure item b, control 5's countermeasure)
# ---------------------------------------------------------------------------


def measured_h2_guard(
    m2_info: dict,
    box: tuple[Fraction, Fraction, Fraction, Fraction],
    t: Fraction,
    dps: int = 112,
    n_re: int = 9,
    n_im: int = 3,
) -> dict:
    """Check that M2 dominates a DIRECTLY MEASURED sample of |H_t''| on the box.

    Why this exists.  M2 is the one load-bearing analytic step in the
    route whose derivation is prose (GATE.md known assumption 6), and the
    M2 lesion recorded as control 5 in ``controls.py`` shows what a wrong
    M2 buys: deflate it by 100 and ``winding_rectangle`` returns status
    "decided" with the wrong integer N = 0, while its own health metric
    ``min_chord_margin_digits`` improves from 0.02 to 0.11.  The health
    metric moves the WRONG way under the lesion, so it cannot be used as a
    guard; this can.

    What it is, stated at its true strength.  This is a NECESSARY, NOT
    SUFFICIENT check, and it is *measured* (mpmath floats, no enclosure):
    -int_0^inf e^{t u^2} Phi_DH(u) u^2 cos(zu) du is evaluated on
    flow_repair's Gauss-Legendre rule at ``n_re * n_im`` points of the
    closed box, and the largest modulus found must not exceed M2's decided
    upper bound.  Passing it does not make M2 right; failing it proves M2
    wrong.  It shares no code with the shifted-contour derivation, which
    is the whole point: the two routes to |H_t''| are the derivation under
    test and a direct quadrature of the definition.

    Scope.  M2's scope is the half-strip Re z >= x_lo, |Im z| <= y_hi;
    the sample covers the box only, and |Im z| >= 0 only, the latter with
    no loss because H_t(conj z) = conj(H_t(z)) gives
    |H_t''(conj z)| = |H_t''(z)|.  Measured decay to the right of the box
    (a factor ~1e-3 by Re z = x_lo + 8) is why sampling the box rather
    than the half-strip is not the weak part; the weak part is that a
    finite grid can miss a peak between its nodes, which is exactly why
    this is necessary and not sufficient.
    """
    from mpmath import mp

    t0 = time.time()
    x_lo, x_hi, y_lo, y_hi = box
    flow = _dhflow(dps, 242.0)
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
                v = abs(h2(x, y))
                if v > best:
                    best = v
                    best_at = (float(x), float(y))
        sup_measured = float(best)

    M2_up = m2_info["M2_upper_float"]
    passed = bool(M2_up >= sup_measured)
    out = {
        "check": "M2 >= directly measured sup |H_t''| on a grid over the box",
        "strength": (
            "NECESSARY, NOT SUFFICIENT: passing does not make M2 right, "
            "failing proves M2 wrong"
        ),
        "grade": f"measured (mpmath dps {dps}, float); M2 itself is decided",
        "evaluator": (
            "direct quadrature of -int_0^inf e^{t u^2} Phi_DH(u) u^2 cos(zu) du "
            "on flow_repair's DHFlow rule; shares no code with the "
            "shifted-contour derivation of M2"
        ),
        "grid": {"n_re": n_re, "n_im": n_im, "box_floats": [
            float(x_lo), float(x_hi), float(y_lo), float(y_hi)]},
        "measured_sup_absH2": sup_measured,
        "measured_sup_at": best_at,
        "M2_upper_float": M2_up,
        "ratio_M2_over_measured": M2_up / sup_measured if sup_measured > 0 else None,
        "im_negative_note": (
            "|Im z| < 0 is not sampled: H_t(conj z) = conj(H_t(z)) makes "
            "|H_t''| symmetric in Im z"
        ),
        "verdict": "PASS" if passed else "FAIL",
    }
    out["seconds"] = round(time.time() - t0, 1)
    return out


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
        guard = measured_h2_guard(m2, box, t)
        print(f"  M2 guard = {guard['verdict']}: measured sup |H''| = "
              f"{guard['measured_sup_absH2']:.4e}, M2 / measured = "
              f"{guard['ratio_M2_over_measured']:.1f}  "
              f"({guard['seconds']} s)", flush=True)
        res = winding_rectangle(box, t, prec, m2)
        res["m2_measured_guard"] = guard
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
    guard_failures = [
        r["t"] for r in runs if r["m2_measured_guard"]["verdict"] != "PASS"
    ]
    if guard_failures:
        # the necessary check on M2 failed, so M2 is wrong and every
        # segment decision that used it is void; refuse rather than report
        floor = None
        out["m2_guard_refusal"] = (
            "measured_h2_guard FAILED at t in "
            f"{guard_failures}: M2 does not dominate a directly measured "
            "sample of |H_t''| on the box, so M2 is not an upper bound and "
            "no segment decision that used it stands.  Floor refused."
        )
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
