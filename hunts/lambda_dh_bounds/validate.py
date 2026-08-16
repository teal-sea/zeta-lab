"""Validation runner for the lambda_dh_bounds ball instrument.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/validate.py

Writes ``validation.json`` next to this file.  Six checks.

Two of them were repaired on 2026-08-16 under GATE.md closure item (e),
which named the gaps; the superseded text of each is kept at its check.
The gaps were both of the same kind, a check pointed somewhere the claim
does not live:

* check 5 exercised ``instrument.phi_ball``, which **no decision path
  calls**, because ``_H_core`` carries its own copy of the series.  A fault
  in that copy was invisible to the second backend.  It now exercises
  ``instrument._truncated_integrand``, the callable ``_H_core`` hands to
  the integrator, and the iv leg sums the series directly rather than by
  the theta recurrence, so a recurrence fault has somewhere to show.
* the two hand-derived tail bounds had no check at all with any purchase:
  at every point in this file they sit 36 to 41 orders of magnitude below
  the delivered ball radius, so containment cannot see them.  Check 6
  compares each bound against a high-precision computation of the TRUE
  remainder it bounds, and records the domination ratio.

The six checks:

1. Containment: at 11 points (real and complex z, heights 10 to 420, t in
   {0, 0.03, 0.0575}) the ``instrument.H_ball`` enclosure must contain the
   value of the independent mpmath float route (``hunts/flow_repair``'s
   composite Gauss-Legendre quadrature evaluator, imported from its
   ``probe.py``), and at t = 0 also ``zeta.epstein.completed_dh(1/2 + iz)``
   (the Hurwitz-zeta route, no integral).  The float routes run at working
   precisions whose absolute error sits far below the ball radii, so a
   containment failure would mark the instrument, not the reference.
2. kappa: the ``kappa_ball`` enclosure (backend python-flint, prec 500 bits)
   must lie inside KAPPA_REF +/- 1e-39, where KAPPA_REF is the 40-digit
   decimal pinned in ``zeta/epstein.py``.  (The decimal string is itself a
   40-digit rounding, so containment runs ball-inside-decimal-interval; the
   ball's radius ~1.5e-148 makes the direction immaterial in practice.)
3. Evenness: Phi_DH is even (the functional equation in disguise); the
   ``phi_ball`` enclosures at u and -u must overlap for several u.
4. Precision response: at a fixed hard point (z = 240.4165 + 0.02i exactly,
   t = 23/400), the H_ball radii at prec 320/420/520 must strictly shrink.
5. mpmath.iv cross-leg on the DECISION PATH's series: the truncated
   integrand ``instrument._truncated_integrand(z, t, N, kappa, deriv)``,
   the exact callable ``_H_core`` hands to ``acb.integral``, evaluated at
   rational u entirely in mpmath's directed-rounding interval context and
   required to overlap the Arb value.  The iv leg sums
   sum_{n<=N} n a_n exp(-pi n^2 e^{2u}/5) term by term; the Arb leg walks
   the theta recurrence q^{n^2} <- q^{(n-1)^2} q^{2n-1}, so the two differ
   in the arithmetic under test.  Both real and complex z, both the cosine
   and the sine (deriv) branch.  The kappa interval for the iv leg is
   KAPPA_REF +/- 1e-39, which check (2) establishes as an enclosure; iv has
   no Hurwitz zeta, so this leg cross-checks the series and exponential
   arithmetic, not the kappa solve.  The quadrature step itself is
   single-backend: mpmath.iv has no rigorous integrator, and the in-tree
   precedent (zeta.rigor.enclose_weil_functional) is flint-only and says so.

   SUPERSEDED TEXT (2026-08-16, GATE.md closure item (e)).  This check read:
   "mpmath.iv cross-leg: Phi_DH at rational u evaluated entirely in
   mpmath's directed-rounding interval context (finite sum to N plus the
   same geometric tail bound, as an iv interval) must overlap the Arb
   phi_ball."  Everything in that sentence was true and it checked the
   wrong function: no decision path calls ``phi_ball``.
6. Tail-bound domination (the standing check with purchase): each of the
   instrument's two hand-derived error bounds compared against a
   high-precision mpmath computation of the true remainder it bounds, at
   several (U, t, z, N) points, including a stress regime with |Im z| up to
   50 where the bounds' e^{y U} factors are what has to hold.  Reported as
   domination ratios bound/true; every ratio must be >= 1.  Necessary, not
   sufficient: this is measured (mpmath floats), and passing it does not
   make a bound right, while failing it proves one wrong.

All decided/enclosure statements below carry backend python-flint (Arb) and
an explicit bit precision.  Float-route values are labeled measured.
"""

from __future__ import annotations

import importlib.util
import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for p in (REPO, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)

import flint  # noqa: E402
from flint import acb, arb, ctx, fmpq  # noqa: E402
from mpmath import iv, mp  # noqa: E402

import instrument as ins  # noqa: E402
from zeta.epstein import KAPPA_REF, completed_dh  # noqa: E402

OUT = os.path.join(HERE, "validation.json")
CHECK_PREC = 800  # working precision for exact conversions inside checks


def _load_flow_probe():
    spec = importlib.util.spec_from_file_location(
        "flow_repair_probe", os.path.join(REPO, "hunts", "flow_repair", "probe.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def mpf_to_arb(x) -> arb:
    """Bit-exact mpf -> arb at the ambient ctx.prec (via Fraction)."""
    q = ins._exact_q(x)
    return arb(fmpq(q.numerator, q.denominator))


def _iv_endpoints(x) -> tuple[Fraction, Fraction]:
    """Exact rational endpoints of an mpmath.iv interval (via its ``_mpi_``
    tuple representation, bit-exact)."""
    (lo_t, hi_t) = x._mpi_

    def q(t: tuple) -> Fraction:
        sign, man, exp, _bc = t
        if man == 0:
            return Fraction(0)
        out = Fraction(int(man)) * Fraction(2) ** int(exp)
        return -out if sign else out

    return q(lo_t), q(hi_t)


def _ball_row(b: acb) -> dict:
    return {
        "re_mid": float(b.real.mid()), "re_rad": float(b.real.rad()),
        "im_mid": float(b.imag.mid()), "im_rad": float(b.imag.rad()),
    }


# ---------------------------------------------------------------------------
# 1. containment against the independent float routes
# ---------------------------------------------------------------------------


def check_containment(fp) -> dict:
    # One quadrature evaluator per (dps, height class).  dps is chosen so the
    # float route's absolute error sits orders of magnitude below the ball
    # radius at the Arb prec used for that height (radius ~1.5e-124 at prec
    # 420, ~1e-178 at prec 600).
    t0 = time.perf_counter()
    flowA = fp.DHFlow(150, z_scale=90.0)    # heights <= 86
    flowB = fp.DHFlow(150, z_scale=243.0)   # height ~240
    flowC = fp.DHFlow(205, z_scale=423.0)   # height ~420
    init_s = time.perf_counter() - t0

    # (re, im, t, flow, arb_prec, also_completed_dh)
    points = [
        ("10", "0", "0", flowA, 420, True),
        ("10", "0.5", "0.03", flowA, 420, False),
        ("85.6993", "0", "0", flowA, 420, True),
        ("85.6993", "0.3085", "0.03", flowA, 420, False),
        ("85.6993", "0.3085", "0.0575", flowA, 420, False),
        ("240.4165", "0", "0", flowB, 420, True),
        ("240.4165", "0.02", "0.0575", flowB, 420, False),
        ("240.4165", "0.25", "0.03", flowB, 420, False),
        ("420.0625", "0", "0", flowC, 600, True),
        ("420.0625", "0.02", "0.03", flowC, 600, False),
        ("420.0625", "0.02", "0.0575", flowC, 600, False),
    ]

    rows = []
    h_ball_times_420 = []
    all_ok = True
    for re_s, im_s, t_s, flow, prec, do_cdh in points:
        z_q = (Fraction(re_s), Fraction(im_s))
        tb0 = time.perf_counter()
        H = ins.H_ball(z_q, Fraction(t_s), prec)
        t_ball = time.perf_counter() - tb0
        if prec == 420:
            h_ball_times_420.append(t_ball)

        tf0 = time.perf_counter()
        with mp.workdps(flow.dps + 5):
            z_mp = mp.mpc(mp.mpf(re_s), mp.mpf(im_s))
            ref = flow.H(z_mp, mp.mpf(t_s))
        t_float = time.perf_counter() - tf0

        # The float route carries its own round-off (absolute scale
        # ~10^-(dps-15); visible e.g. as a ~1e-154 spurious imaginary part
        # at real z, where the ball's imaginary radius is far tighter).
        # The containment claim is therefore: the float value lies inside
        # the enclosure widened by the float route's own error allowance.
        # The allowance sits orders of magnitude BELOW the ball radius on
        # every component whose value is nonzero, so it never props up a
        # failing check; it only stops the float route's junk digits from
        # failing a component the ball resolves more tightly than the
        # reference can.
        eps_q = Fraction(1, 10 ** (flow.dps - 15))
        with ins._prec_guard(CHECK_PREC):
            eps = arb(0, arb(fmpq(eps_q.numerator, eps_q.denominator)))
            H_widened = H + acb(eps, eps)
            ok_re = bool(H_widened.real.contains(mpf_to_arb(ref.real)))
            ok_im = bool(H_widened.imag.contains(mpf_to_arb(ref.imag)))
        row = {
            "z": f"{re_s} + {im_s}i", "t": t_s,
            "backend": "python-flint", "prec_bits": prec,
            "ball": _ball_row(H),
            "float_route": "flow_repair DHFlow quadrature (measured), "
                           f"dps={flow.dps}",
            "float_value": mp.nstr(ref, 30),
            "float_error_allowance": f"1e-{flow.dps - 15}",
            "contains_float": bool(ok_re and ok_im),
            "seconds_ball": round(t_ball, 3),
            "seconds_float": round(t_float, 3),
        }
        all_ok = all_ok and row["contains_float"]

        if do_cdh:
            with mp.workdps(flow.dps + 30):
                s_ref = (mp.mpf(1) / 2
                         + mp.mpc(0, 1) * mp.mpc(mp.mpf(re_s), mp.mpf(im_s)))
                cdh = completed_dh(s_ref, dps=flow.dps + 20)
            with ins._prec_guard(CHECK_PREC):
                eps = arb(0, arb(fmpq(eps_q.numerator, eps_q.denominator)))
                H_w = H + acb(eps, eps)
                ok2 = bool(H_w.real.contains(mpf_to_arb(cdh.real))
                           and H_w.imag.contains(mpf_to_arb(cdh.imag)))
            row["completed_dh_value"] = mp.nstr(cdh, 30)
            row["contains_completed_dh"] = ok2
            all_ok = all_ok and ok2
        rows.append(row)
        print(f"  z={row['z']:>22s} t={t_s:>7s} prec={prec} "
              f"contains_float={row['contains_float']}"
              + (f" contains_completed_dh={row.get('contains_completed_dh')}"
                 if do_cdh else ""), flush=True)

    return {
        "all_contained": all_ok,
        "n_points": len(rows),
        "flow_init_seconds": round(init_s, 1),
        "h_ball_seconds_prec420": [round(x, 3) for x in h_ball_times_420],
        "rows": rows,
    }


# ---------------------------------------------------------------------------
# 2. kappa against the pinned 40-digit reference
# ---------------------------------------------------------------------------


def check_kappa() -> dict:
    prec = 500
    k = ins.kappa_ball(prec)
    with ins._prec_guard(CHECK_PREC):
        ref_q = Fraction(KAPPA_REF)
        ref = arb(fmpq(ref_q.numerator, ref_q.denominator))
        ref_interval = ref + arb(0, arb(fmpq(1, 10 ** 39)))
        contained = bool(ref_interval.contains(k))
        diff = float((k - ref).abs_upper())
    row = {
        "backend": "python-flint",
        "prec_bits": prec,
        "kappa_mid": float(k.mid()),
        "kappa_rad": float(k.rad()),
        "kappa_ref_40_digits": KAPPA_REF,
        "ball_inside_ref_pm_1e-39": contained,
        "abs_mid_minus_ref_upper": diff,
        "note": "KAPPA_REF is a 40-digit decimal rounding, so the enclosure "
                "check runs ball-inside-decimal-interval; the ball radius "
                "~1.5e-148 makes the direction immaterial.",
    }
    print(f"  kappa ball rad {row['kappa_rad']:.3e}, inside REF+/-1e-39: "
          f"{contained}, |mid-REF| <= {diff:.3e}", flush=True)
    return row


# ---------------------------------------------------------------------------
# 3. evenness of Phi_DH
# ---------------------------------------------------------------------------


def check_evenness() -> dict:
    prec = 420
    rows = []
    all_ok = True
    for u_s in ("1/10", "1/4", "1/2", "3/4"):
        u = Fraction(u_s)
        p_pos = ins.phi_ball(u, prec)
        p_neg = ins.phi_ball(-u, prec)
        ok = bool(p_pos.overlaps(p_neg))
        all_ok = all_ok and ok
        rows.append({
            "u": u_s, "backend": "python-flint", "prec_bits": prec,
            "phi_pos": _ball_row(p_pos), "phi_neg": _ball_row(p_neg),
            "overlap": ok,
        })
        print(f"  u={u_s:>4s}: phi(u) and phi(-u) overlap: {ok}", flush=True)
    return {"all_overlap": all_ok, "rows": rows}


# ---------------------------------------------------------------------------
# 4. precision response at the hard point
# ---------------------------------------------------------------------------


def check_precision_response() -> dict:
    z_q = (Fraction("240.4165"), Fraction("0.02"))
    t_q = Fraction("0.0575")
    rows = []
    radii = []
    for prec in (320, 420, 520):
        t0 = time.perf_counter()
        H = ins.H_ball(z_q, t_q, prec)
        r = max(float(H.real.rad()), float(H.imag.rad()))
        radii.append(r)
        rows.append({"prec_bits": prec, "backend": "python-flint",
                     "radius": r, "seconds": round(time.perf_counter() - t0, 3)})
        print(f"  prec {prec}: radius {r:.3e}", flush=True)
    shrinks = bool(radii[0] > radii[1] > radii[2])
    return {"point": "z = 240.4165 + 0.02i, t = 23/400",
            "strictly_shrinking": shrinks, "rows": rows}


# ---------------------------------------------------------------------------
# 5. mpmath.iv cross-leg, pointed at the series the decision path runs
# ---------------------------------------------------------------------------


def _frac_iv(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _integrand_iv(u_q: Fraction, z_q: tuple[Fraction, Fraction],
                  t_q: Fraction, N: int, kap_iv, deriv: bool):
    """``instrument._truncated_integrand``'s value at u, in mpmath.iv.

    The same finite expression, written the other way round on purpose:

        4 exp(t u^2 + 3u/2) * sum_{n=1}^{N} n a_n exp(-pi n^2 e^{2u} / 5)
                            * cos(z u)                       (deriv False)
       -4 exp(t u^2 + 3u/2) * (same sum) * u * sin(z u)       (deriv True)

    The Arb leg reaches the sum by the theta recurrence
    q^{n^2} = q^{(n-1)^2} * q^{2n-1}, three multiplications per term and no
    exponential; this leg calls exp once per term.  That is the whole point
    of the cross-leg: an off-by-one or a mis-seeded recurrence changes the
    Arb value and cannot change this one.  Interval arithmetic throughout,
    so the returned box encloses the exact value of the finite expression.
    """
    u = _frac_iv(u_q)
    x = iv.exp(2 * u)
    z = iv.mpc(_frac_iv(z_q[0]), _frac_iv(z_q[1]))
    t = _frac_iv(t_q)
    a_pat = {1: iv.mpf(1), 2: kap_iv, 3: -kap_iv, 4: iv.mpf(-1), 0: None}
    S = iv.mpf(0)
    for n in range(1, N + 1):
        a = a_pat[n % 5]
        if a is not None:
            S += n * a * iv.exp(-iv.pi * n * n * x / 5)
    pref = 4 * iv.exp(t * u * u + 3 * u / 2)
    if deriv:
        return -(pref * S) * u * iv.sin(z * u)
    return (pref * S) * iv.cos(z * u)


def _iv_hull_arb(x_iv) -> arb:
    """The arb hull of an mpmath.iv real interval, exactly."""
    lo_q, hi_q = _iv_endpoints(x_iv)
    lo = arb(fmpq(lo_q.numerator, lo_q.denominator))
    hi = arb(fmpq(hi_q.numerator, hi_q.denominator))
    return lo.union(hi)


def check_iv_cross_leg() -> dict:
    """Check 5, repaired 2026-08-16 (GATE.md closure item (e)).

    SUPERSEDED IMPLEMENTATION.  This function used to build Phi_DH(u) in
    mpmath.iv (finite sum plus the geometric tail bound) and compare it
    against ``instrument.phi_ball``.  The comparison passed and bounded
    nothing that carries the count: ``phi_ball`` is called by no decision
    path, because ``_H_core`` carries its own copy of the series.  The old
    leg is not merely narrower than advertised, it pointed at a different
    implementation of the same mathematics.  It is replaced, not kept
    alongside, because a check that names the wrong target is worse than no
    check: it reads in ``validation.json`` as coverage.
    """
    iv.dps = 60
    kap_iv = (_frac_iv(Fraction(KAPPA_REF))
              + _frac_iv(Fraction(1, 10 ** 39)) * iv.mpf([-1, 1]))
    N = 48
    prec = 420

    # (u, z_re, z_im, t, deriv) -- real and complex z, both branches, and
    # one point on the t1 winding box boundary.
    points = [
        ("1/10", "0", "0", "0", False),
        ("1/4", "10", "0", "23/400", False),
        ("1/2", "240.4165", "0.02", "23/400", False),
        ("1/2", "240.4165", "0.02", "23/400", True),
        ("3/2", "122929/512", "3/512", "23/400", False),
        ("3/2", "122929/512", "3/512", "23/400", True),
        ("5/2", "240.4165", "3/100", "36/625", False),
    ]

    rows = []
    all_ok = True
    for u_s, zr, zi, t_s, deriv in points:
        u_q = Fraction(u_s)
        z_q = (Fraction(zr), Fraction(zi))
        t_q = Fraction(t_s)
        val_iv = _integrand_iv(u_q, z_q, t_q, N, kap_iv, deriv)
        with ins._prec_guard(prec):
            kap = ins.kappa_ball(max(prec + 40, 300))
            t_b = ins._q_to_arb(t_q)
            z_b = ins._as_acb(z_q)
            f = ins._truncated_integrand(z_b, t_b, N, kap, deriv)
            val_arb = f(ins._as_acb(u_q), True)
        with ins._prec_guard(CHECK_PREC):
            ok_re = bool(_iv_hull_arb(val_iv.real).overlaps(val_arb.real))
            ok_im = bool(_iv_hull_arb(val_iv.imag).overlaps(val_arb.imag))
        ok = bool(ok_re and ok_im)
        all_ok = all_ok and ok
        rows.append({
            "u": u_s, "z": f"{zr} + {zi}i", "t": t_s, "deriv": deriv,
            "N": N,
            "iv_backend": "mpmath.iv, dps=60 (directed rounding), direct "
                          "term-by-term sum",
            "arb_target": "instrument._truncated_integrand (the callable "
                          "_H_core hands to acb.integral), theta recurrence",
            "iv_re": [float(q) for q in _iv_endpoints(val_iv.real)],
            "iv_im": [float(q) for q in _iv_endpoints(val_iv.imag)],
            "arb_ball": _ball_row(val_arb),
            "overlap": ok,
        })
        print(f"  u={u_s:>5s} z={zr} + {zi}i t={t_s:>8s} deriv={int(deriv)}: "
              f"iv overlaps the decision-path integrand: {ok}", flush=True)

    return {
        "all_overlap": all_ok,
        "target": "instrument._truncated_integrand",
        "target_note": "the exact callable instrument._H_core hands to "
                       "acb.integral; the decision path runs this code and "
                       "no other copy of the series",
        "repaired": "2026-08-16, GATE.md closure item (e): this leg used to "
                    "exercise instrument.phi_ball, which no decision path "
                    "calls",
        "kappa_interval_source": "KAPPA_REF +/- 1e-39 (an enclosure per "
                                 "check 2; iv has no Hurwitz zeta)",
        "planted_fault_measured_2026_08_16": (
            "seeding the theta recurrence with w = q^2 instead of q^3 (so "
            "every term carries the wrong power of q) is caught at 6 of these "
            "7 points.  The point that misses is u = 5/2, where "
            "exp(-pi e^{2u}/5) is about e^{-93} and the truncated sum is its "
            "own first term to well below the interval width; a check at "
            "large u sees only n = 1, which is the blind spot to know about."
        ),
        "what_this_leg_does_not_cover": (
            "the kappa solve (iv has no Hurwitz zeta), the two tail bounds "
            "(check 6), and the quadrature itself, which is single-backend: "
            "mpmath.iv has no rigorous integrator and the in-tree precedent "
            "zeta.rigor.enclose_weil_functional is flint-only and says so"
        ),
        "rows": rows,
    }


# ---------------------------------------------------------------------------
# 6. tail-bound domination: the standing check that has purchase
# ---------------------------------------------------------------------------


def _kappa_mp(dps: int):
    from zeta.epstein import kappa as kappa_mp

    with mp.workdps(dps + 20):
        return +kappa_mp(dps=dps + 15)


def _omega_mp(x, N: int, kap):
    """sum_{n=1}^{N} n a_n exp(-pi n^2 x / 5) at the ambient mpmath dps."""
    a_pat = (mp.mpf(1), kap, -kap, mp.mpf(-1), mp.mpf(0))
    total = mp.mpf(0)
    for n in range(1, N + 1):
        a = a_pat[n % 5]
        if a == 0:
            continue
        total += n * a * mp.exp(-mp.pi * n * n * x / 5)
    return total


def _hunt_series_tail(N: int, U_q: Fraction, t_q: Fraction, y_q: Fraction,
                      deriv: bool, prec: int = 600):
    with ins._prec_guard(prec):
        v = ins._series_tail_finite(N, ins._q_to_arb(U_q), ins._q_to_arb(t_q),
                                    ins._q_to_arb(y_q), deriv)
        return None if v is None else mp.mpf(str(v.str(30, radius=False)))


def _hunt_u_tail(U_q: Fraction, t_q: Fraction, y_q: Fraction, deriv: bool,
                 prec: int = 600):
    with ins._prec_guard(prec):
        v = ins._u_tail(ins._q_to_arb(U_q), ins._q_to_arb(t_q),
                        ins._q_to_arb(y_q), deriv)
        return None if v is None else mp.mpf(str(v.str(30, radius=False)))


def check_tail_domination() -> dict:
    """Check 6, added 2026-08-16 (GATE.md closure item (e)).

    Why it exists.  The instrument adds two hand-derived error balls to
    every H value: ``_series_tail_finite`` (the series truncated at N on
    [0, U]) and ``_u_tail`` (the integral discarded beyond U).  Both were
    re-derived and found valid by an adversary, and neither had a check
    with any purchase in this file: at every containment point above they
    sit 36 to 41 orders of magnitude below the delivered ball radius, so a
    bound could be wrong by thirty orders and every containment row would
    still read True.

    What this does instead: computes the TRUE remainder each bound bounds,
    by high-precision mpmath quadrature of the exact discarded quantity,
    and reports the ratio bound/true.  Domination is demanded at every
    point.  The stress block pushes |Im z| to 50, where both bounds lean on
    a factor e^{y U} that grows with the |cos(zu)| <= cosh(y u) step: if
    that step were wrong, this is where it fails first.

    Grade: MEASURED (mpmath floats; the true remainders are not enclosed).
    Necessary, not sufficient, exactly like ``winding.measured_h2_guard``:
    passing does not make a bound right, failing proves one wrong.
    """
    t0 = time.perf_counter()
    kap = _kappa_mp(90)

    # --- part A: series truncation on [0, U] ------------------------------
    # (U, t, Re z, Im z, N, deriv, label)
    # Working precision is chosen per row, and it is the whole difficulty of
    # this check: at the instrument's working N = 27 the true series
    # remainder is about 1e-214 and at the working U = 51/16 the true
    # discarded integral is about 1e-160, so mpmath at dps 90 returns
    # exactly 0 for both and the comparison is vacuous.  Every row below
    # states a dps at which the true remainder is resolved, and each row
    # records the quadrature's own error estimate so a reader can see that
    # it was.
    #
    # (U, t, Re z, Im z, N, deriv, dps, label)
    series_cases = [
        ("51/16", "0", "10", "0", 27, False, 300, "working N = 27, t = 0"),
        ("51/16", "23/400", "240.4165", "1/50", 27, False, 300,
         "working N = 27, the t1 box point"),
        ("51/16", "23/400", "240.4165", "1/50", 27, True, 300,
         "working N = 27, the t1 box point, H'"),
        ("51/16", "23/400", "240.4165", "1", 8, False, 90, "N = 8, |Im z| = 1"),
        ("7/2", "23/400", "240.4165", "5", 12, False, 120,
         "|Im z| = 5, stress"),
        ("4", "1/10", "0", "20", 12, False, 140, "|Im z| = 20, stress"),
        ("4", "1/10", "0", "50", 12, True, 160, "|Im z| = 50, stress, H'"),
        ("2", "0", "5", "3", 3, True, 60, "tiny N = 3, H'"),
    ]
    series_rows = []
    series_ok = True
    for U_s, t_s, zr, zi, N, deriv, dps, label in series_cases:
        U_q, t_q = Fraction(U_s), Fraction(t_s)
        y_q = abs(Fraction(zi))
        with mp.workdps(dps):
            U = mp.mpf(U_q.numerator) / U_q.denominator
            t = mp.mpf(t_q.numerator) / t_q.denominator
            z = mp.mpc(mp.mpf(Fraction(zr).numerator) / Fraction(zr).denominator,
                       mp.mpf(Fraction(zi).numerator) / Fraction(zi).denominator)

            def g(u, _N=N, _t=t, _z=z, _deriv=deriv):
                x = mp.exp(2 * u)
                d = _omega_mp(x, _N + 40, kap) - _omega_mp(x, _N, kap)
                pre = mp.exp(_t * u * u) * 4 * mp.exp(3 * u / 2) * d
                if _deriv:
                    return -pre * u * mp.sin(_z * u)
                return pre * mp.cos(_z * u)

            val, qerr = mp.quad(g, [0, U], maxdegree=9, error=True)
            true = abs(val)
            rel_qerr = float(qerr / true) if true > 0 else None
        bound = _hunt_series_tail(N, U_q, t_q, y_q, deriv)
        ok = bool(bound is not None and true > 0 and bound >= true)
        series_ok = series_ok and ok
        ratio = float(bound / true) if (bound is not None and true > 0) else None
        series_rows.append({
            "label": label, "U": U_s, "t": t_s, "z": f"{zr} + {zi}i",
            "N": N, "deriv": deriv, "mpmath_dps": dps,
            "true_remainder": float(true),
            "quad_relative_error_estimate": rel_qerr,
            "claimed_bound": None if bound is None else float(bound),
            "domination_ratio_bound_over_true": ratio,
            "dominates": ok,
        })
        print(f"  series tail  {label:<34s} true {float(true):.3e}  bound "
              f"{(float(bound) if bound is not None else float('nan')):.3e}  "
              f"ratio {ratio if ratio is None else round(ratio, 4)}  ok={ok}",
              flush=True)

    # --- part B: the discarded integral beyond U --------------------------
    # (U, t, Re z, Im z, deriv, dps, label).  "auto" means the U the
    # instrument itself would pick, ins.default_U(t, |Im z|, 420); the two
    # deliberately-too-small rows below it are there to show what the bound
    # does when its hypothesis c > 0 fails, which is refuse.
    u_cases = [
        ("51/16", "0", "10", "0", False, 250, "working U = 51/16, t = 0"),
        ("51/16", "23/400", "240.4165", "1/50", False, 250,
         "working U = 51/16, the t1 box point"),
        ("51/16", "23/400", "240.4165", "1/50", True, 250,
         "working U = 51/16, the t1 box point, H'"),
        ("51/16", "23/400", "240.4165", "5", False, 250,
         "working U, |Im z| = 5, stress"),
        ("5/2", "23/400", "0", "20", False, 90, "|Im z| = 20, stress"),
        ("auto", "1/10", "0", "20", False, 250,
         "|Im z| = 20 at the instrument's own U, stress"),
        ("auto", "1/10", "0", "50", True, 250,
         "|Im z| = 50 at the instrument's own U, stress, H'"),
        ("5/2", "1/10", "0", "50", True, 90,
         "|Im z| = 50 at U = 5/2, deliberately too small"),
        ("3/2", "1/2", "0", "3", False, 60, "small U, large t"),
        ("1", "0", "0", "0", False, 60, "U at its floor"),
    ]
    u_rows = []
    u_ok = True
    u_refusals = []
    for U_s, t_s, zr, zi, deriv, dps, label in u_cases:
        t_q = Fraction(t_s)
        y_q = abs(Fraction(zi))
        U_q = (ins.default_U(t_q, float(y_q), 420) if U_s == "auto"
               else Fraction(U_s))
        with mp.workdps(dps):
            U = mp.mpf(U_q.numerator) / U_q.denominator
            t = mp.mpf(t_q.numerator) / t_q.denominator
            z = mp.mpc(mp.mpf(Fraction(zr).numerator) / Fraction(zr).denominator,
                       mp.mpf(Fraction(zi).numerator) / Fraction(zi).denominator)

            def g2(u, _t=t, _z=z, _deriv=deriv):
                x = mp.exp(2 * u)
                pre = mp.exp(_t * u * u) * 4 * mp.exp(3 * u / 2) \
                    * _omega_mp(x, 30, kap)
                if _deriv:
                    return -pre * u * mp.sin(_z * u)
                return pre * mp.cos(_z * u)

            # the integrand is doubly-exponentially dead by U + 3
            val, qerr = mp.quad(g2, [U, U + mp.mpf(1), U + 3], maxdegree=9,
                                error=True)
            true = abs(val)
            rel_qerr = float(qerr / true) if true > 0 else None
        bound = _hunt_u_tail(U_q, t_q, y_q, deriv)
        if bound is None:
            # NOT a failure: _u_tail returns None exactly when its own
            # hypothesis c = pi/5 - (t U^2 + (3/2+y) U) e^{-2U} > 0 cannot be
            # decided, and _H_core then raises "tail bound not established
            # ... raise U" rather than integrating.  The row is recorded as a
            # refusal, and the companion "auto" row at the same (t, z) shows
            # the bound at the U the instrument would actually choose.
            status = "refused (hypothesis c > 0 fails; _H_core raises and "
            status += "demands a larger U)"
            ok = None
            ratio = None
            u_refusals.append(label)
        else:
            status = "bound returned"
            ok = bool(true > 0 and bound >= true)
            ratio = float(bound / true) if true > 0 else None
            u_ok = u_ok and ok
        u_rows.append({
            "label": label, "U": str(U_q), "U_source": U_s,
            "t": t_s, "z": f"{zr} + {zi}i",
            "deriv": deriv, "mpmath_dps": dps,
            "true_remainder": float(true),
            "quad_relative_error_estimate": rel_qerr,
            "claimed_bound": None if bound is None else float(bound),
            "domination_ratio_bound_over_true": ratio,
            "status": status,
            "dominates": ok,
        })
        print(f"  u tail       {label:<48s} true {float(true):.3e}  bound "
              f"{(float(bound) if bound is not None else float('nan')):.3e}  "
              f"ratio {ratio if ratio is None else round(ratio, 4)}  ok={ok}",
              flush=True)

    ratios = [r["domination_ratio_bound_over_true"]
              for r in series_rows + u_rows
              if r["domination_ratio_bound_over_true"] is not None]
    stress = [r for r in series_rows + u_rows if "stress" in r["label"]]
    return {
        "all_dominate": bool(series_ok and u_ok),
        "grade": "measured (mpmath, floats); the true remainders are not "
                 "enclosed",
        "strength": "NECESSARY, NOT SUFFICIENT: passing does not make a "
                    "bound right, failing proves one wrong",
        "why_this_replaces_nothing": (
            "the containment check (1) has no purchase on these bounds: at "
            "every point there they sit 36 to 41 orders of magnitude below "
            "the delivered ball radius, so a bound could be wrong by thirty "
            "orders and every containment row would still read True"
        ),
        "min_domination_ratio": min(ratios) if ratios else None,
        "max_domination_ratio": max(ratios) if ratios else None,
        "blindness_factor": {
            "value": min(ratios) if ratios else None,
            "meaning": (
                "the smallest domination ratio over all rows, so a bound "
                "deflated by MORE than this factor is caught at one of these "
                "points and a bound deflated by less is not.  Reported "
                "because docs/25's standing consequence is that a lesion "
                "threshold without a blindness radius is half a measurement."
            ),
        },
        "n_stress_points_large_im_z": len(stress),
        "min_stress_domination_ratio": min(
            (r["domination_ratio_bound_over_true"] for r in stress
             if r["domination_ratio_bound_over_true"] is not None),
            default=None),
        "series_truncation_tail": {
            "bound": "instrument._series_tail_finite",
            "true_quantity": "int_0^U e^{t u^2} 4 e^{3u/2} "
                             "(omega - omega_N)(e^{2u}) cos(zu) du "
                             "(-u sin(zu) for the H' branch)",
            "rows": series_rows,
        },
        "u_tail": {
            "bound": "instrument._u_tail",
            "true_quantity": "int_U^inf e^{t u^2} Phi_DH(u) cos(zu) du "
                             "(-u sin(zu) for the H' branch)",
            "refusals": u_refusals,
            "refusal_note": (
                "a refusal is the bound declining to bound, not a domination "
                "failure: _u_tail returns None when its hypothesis c > 0 "
                "fails and _H_core then raises rather than integrating.  Each "
                "refusal row has a companion row at the U the instrument "
                "itself would pick, where the bound exists and dominates."
            ),
            "rows": u_rows,
        },
        "seconds": round(time.perf_counter() - t0, 1),
    }


# ---------------------------------------------------------------------------


def main() -> None:
    t_start = time.perf_counter()
    print("python-flint", flint.__version__, flush=True)
    fp = _load_flow_probe()

    print("[1/6] containment against independent float routes", flush=True)
    containment = check_containment(fp)
    print("[2/6] kappa vs 40-digit pinned reference", flush=True)
    kap = check_kappa()
    print("[3/6] Phi_DH evenness", flush=True)
    even = check_evenness()
    print("[4/6] precision response", flush=True)
    presp = check_precision_response()
    print("[5/6] mpmath.iv cross-leg on the decision path's series", flush=True)
    ivleg = check_iv_cross_leg()
    print("[6/6] tail-bound domination against true remainders", flush=True)
    tails = check_tail_domination()

    all_pass = bool(
        containment["all_contained"]
        and kap["ball_inside_ref_pm_1e-39"]
        and even["all_overlap"]
        and presp["strictly_shrinking"]
        and ivleg["all_overlap"]
        and tails["all_dominate"]
    )
    out = {
        "instrument": "hunts/lambda_dh_bounds/instrument.py",
        "backend": f"python-flint {flint.__version__} (Arb)",
        "vocabulary": "enclosure/decided per MISSION.md; float routes are "
                      "measured",
        "repairs": (
            "2026-08-16, GATE.md closure item (e): check 5 repointed from "
            "instrument.phi_ball (called by no decision path) to "
            "instrument._truncated_integrand (the callable _H_core hands to "
            "the integrator); check 6 added, because containment has no "
            "purchase on the two hand-derived tail bounds"
        ),
        "containment": containment,
        "kappa": kap,
        "evenness": even,
        "precision_response": presp,
        "iv_cross_leg": ivleg,
        "tail_domination": tails,
        "all_pass": all_pass,
        "seconds_total": round(time.perf_counter() - t_start, 1),
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(f"\nall_pass = {all_pass}  ({out['seconds_total']}s)  -> {OUT}",
          flush=True)
    if not all_pass:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
