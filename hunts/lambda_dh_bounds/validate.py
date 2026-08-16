"""Validation runner for the lambda_dh_bounds ball instrument.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/validate.py

Writes ``validation.json`` next to this file.  Five checks:

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
5. mpmath.iv cross-leg: Phi_DH at rational u evaluated entirely in mpmath's
   directed-rounding interval context (finite sum to N plus the same
   geometric tail bound, as an iv interval) must overlap the Arb phi_ball.
   The kappa interval for this leg is KAPPA_REF +/- 1e-39, which check (2)
   establishes as an enclosure; iv has no Hurwitz zeta, so the iv leg
   cross-checks the series and exponential arithmetic, not the kappa solve.
   The quadrature step itself is single-backend: mpmath.iv has no rigorous
   integrator, and the in-tree precedent (zeta.rigor.enclose_weil_functional)
   is flint-only and says so.

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
# 5. mpmath.iv cross-leg for Phi_DH
# ---------------------------------------------------------------------------


def _frac_iv(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _phi_iv(u_q: Fraction, kap_iv, N: int = 48):
    """Phi_DH(u) as an mpmath.iv interval: finite sum to N plus the same
    geometric tail bound as the Arb leg, all in directed-rounding interval
    arithmetic.  Valid for u_q with e^{2u} > 0 (real u: always)."""
    u = _frac_iv(u_q)
    x = iv.exp(2 * u)
    a_pat = {1: iv.mpf(1), 2: kap_iv, 3: -kap_iv, 4: iv.mpf(-1), 0: None}
    S = iv.mpf(0)
    for n in range(1, N + 1):
        a = a_pat[n % 5]
        if a is not None:
            S += n * a * iv.exp(-iv.pi * n * n * x / 5)
    # tail: |a_n| <= 1, n^2 >= n(N+1) for n > N, so the omega tail is
    # <= (N+1) r^{N+1} / (1-r)^2 with r = exp(-pi (N+1) x / 5) evaluated on
    # the interval x (the expression is monotone in r, so the interval
    # evaluation's upper endpoint is a valid bound).
    r = iv.exp(-iv.pi * (N + 1) * x / 5)
    tail1 = (N + 1) * r ** (N + 1) / (1 - r) ** 2
    pref = 4 * iv.exp(3 * u / 2)
    return pref * S + iv.mpf([-1, 1]) * (pref * tail1)


def check_iv_cross_leg() -> dict:
    # kappa interval: KAPPA_REF +/- 1e-39, an enclosure by check (2).
    # NOTE: the quadrature step of H_ball is single-backend (python-flint
    # only): mpmath.iv has no rigorous integrator, and the in-tree precedent
    # (zeta.rigor.enclose_weil_functional) is flint-only and says so.  This
    # leg cross-checks the Phi_DH series arithmetic on the second backend.
    iv.dps = 60
    kap_iv = (_frac_iv(Fraction(KAPPA_REF))
              + _frac_iv(Fraction(1, 10 ** 39)) * iv.mpf([-1, 1]))
    rows = []
    all_ok = True
    for u_s in ("1/10", "1/4", "1/2"):
        u_q = Fraction(u_s)
        p_iv = _phi_iv(u_q, kap_iv)
        p_arb = ins.phi_ball(u_q, 420)
        lo_q, hi_q = _iv_endpoints(p_iv)
        with ins._prec_guard(CHECK_PREC):
            lo = arb(fmpq(lo_q.numerator, lo_q.denominator))
            hi = arb(fmpq(hi_q.numerator, hi_q.denominator))
            hull = lo.union(hi)
            ok = bool(hull.overlaps(p_arb.real))
        all_ok = all_ok and ok
        rows.append({
            "u": u_s,
            "iv_backend": "mpmath.iv, dps=60 (directed rounding)",
            "iv_interval": [float(lo_q), float(hi_q)],
            "arb_ball": _ball_row(p_arb),
            "overlap": ok,
        })
        print(f"  u={u_s:>4s}: iv interval overlaps Arb phi ball: {ok}",
              flush=True)
    return {
        "all_overlap": all_ok,
        "kappa_interval_source": "KAPPA_REF +/- 1e-39 (an enclosure per "
                                 "check 2; iv has no Hurwitz zeta)",
        "quadrature_note": "the H_t quadrature itself is single-backend "
                           "(python-flint acb.integral); precedent: "
                           "zeta.rigor.enclose_weil_functional is flint-only "
                           "and says so",
        "rows": rows,
    }


# ---------------------------------------------------------------------------


def main() -> None:
    t_start = time.perf_counter()
    print("python-flint", flint.__version__, flush=True)
    fp = _load_flow_probe()

    print("[1/5] containment against independent float routes", flush=True)
    containment = check_containment(fp)
    print("[2/5] kappa vs 40-digit pinned reference", flush=True)
    kap = check_kappa()
    print("[3/5] Phi_DH evenness", flush=True)
    even = check_evenness()
    print("[4/5] precision response", flush=True)
    presp = check_precision_response()
    print("[5/5] mpmath.iv cross-leg", flush=True)
    ivleg = check_iv_cross_leg()

    all_pass = bool(
        containment["all_contained"]
        and kap["ball_inside_ref_pm_1e-39"]
        and even["all_overlap"]
        and presp["strictly_shrinking"]
        and ivleg["all_overlap"]
    )
    out = {
        "instrument": "hunts/lambda_dh_bounds/instrument.py",
        "backend": f"python-flint {flint.__version__} (Arb)",
        "vocabulary": "enclosure/decided per MISSION.md; float routes are "
                      "measured",
        "containment": containment,
        "kappa": kap,
        "evenness": even,
        "precision_response": presp,
        "iv_cross_leg": ivleg,
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
