"""Hunt #122: how far the tracked pair can push the second-DH lower endpoint.

`hunts/dh_minus_heat/` left `217/200 < Lambda_minus <= 567009/320000` (narrow
frame, `s = 1/2 + iz`) and named, as its first door, a later rational heat time
for the same conjugate pair. This probe measures the landing (collision) time
`t_c` of that pair by two independent routes, then climbs a ladder of rational
heat times below `t_c` with the hunt's own Arb Taylor/Rouche disk instrument
(`hunts/dh_minus_heat/odd_ball.py`, imported, never modified).

Nothing here is a result; `hunts/README.md` classifies it. Every number in
`results.json` is pinned by `test_dh_minus_landing.py`. Vocabulary: a disk
decision is *enclosure-carrying* (Arb balls with every tail charged, exact
rational endpoint comparison); a landing time is *measured* (float routes),
*hardened* where two independent routes agree.

Routes for the landing time:

* **Route A** (mpmath, adaptive tanh-sinh quadrature, analytic Jacobian): the
  double-zero system `H_t(x) = 0`, `(d/dx) H_t(x) = 0` in the real unknowns
  `(x, t)`, solved by Newton at two working precisions.
* **Route B** (float64, fixed Gauss-Legendre grid, contour moments): the pair
  discriminant `Delta(t) = 2 q_2 - q_1^2 = (z_1 - z_2)^2` from contour
  integrals of `z^k H'/H`, with the winding number required to be exactly 2,
  and `t_c` the root of `Delta` (docs/37, "Contour-moment pair tracker in the
  collision-safe discriminant variable").

The two routes share the kernel formula (coefficients, theta sum, heat
multiplier) and nothing else: different integrators, different root
characterisations. The shared layer is controlled separately by the zero-time
Hurwitz identity `H_0(z) = -i F(1/2 + iz)`, which uses no theta integral, and
a planted kernel fault shows which control carries that weight.

Run from the repository root:

    .venv/bin/python hunts/dh_minus_landing/probe.py
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import mpmath as mp  # noqa: E402
import numpy as np  # noqa: E402
from scipy.optimize import brentq, root  # noqa: E402

from hunts.dh_minus_heat import odd_ball, pilot  # noqa: E402

FRAME = "narrow s=1/2+iz"
RECORDED_LOWER = Fraction(217, 200)
RECORDED_UPPER = Fraction(567009, 320000)
RECORDED_DISK_CENTRE = ("7.543145542463", "0.072646330251")
RADIUS = Fraction(1, 10**7)
DISK_CONFIGS = [(96, 24, "4"), (128, 24, "4"), (160, 28, "4"), (128, 26, "7/2")]

# Pilot zeros of D_minus(s) from hunts/dh_minus_heat/pilot.json (dps 40, measured).
PILOT_ZEROS = {
    "pair1": ("2.308622947043362464668474531338293", "8.9183552921135375897304020319429105"),
    "pair2": ("1.9437413807034388245161449051459879", "18.899390659174843919800253427568499"),
}

# The rational heat-time ladder below the measured landing time. Each is a
# candidate strict lower bound for Lambda_minus; the probe keeps only those
# whose disk is decided on every configuration.
LADDER = [Fraction(87, 80), Fraction(2719, 2500), Fraction(108763, 100000),
          Fraction(217527, 200000), Fraction(10876359, 10000000)]


# ---------------------------------------------------------------------------
# kernels
# ---------------------------------------------------------------------------


def coefficient_pattern(tau, lesion_factor=1.0):
    """Period-five pattern (0, 1, tau, -tau, -1); the lesion scales residue 2."""
    return [0 * tau, 1 + 0 * tau, lesion_factor * tau, -tau, -1 + 0 * tau]


def float_grid(order=480, nmax=14, lesion_factor=1.0):
    """Float64 Gauss-Legendre evaluator of the sine heat flow and its derivatives.

    H(z, t, k) returns the k-th z-derivative of
    4 int_0^4 exp(t u^2 + 3u/2) omega(u) sin(zu) du, k = 0, 1, 2.
    The grid is the pilot's (`pilot.heat_grid`) with the derivative orders
    added; it is a scout, never an enclosure.
    """
    nodes, weights = np.polynomial.legendre.leggauss(order)
    u = 2 * (nodes + 1)
    w = 2 * weights
    with mp.workdps(30):
        tau = float(pilot.parameter())
    a = coefficient_pattern(tau, lesion_factor)
    omega = sum(n * a[n % 5] * np.exp(-np.pi * n * n * np.exp(2 * u) / 5)
                for n in range(1, nmax + 1))
    base = 4 * w * np.exp(1.5 * u) * omega
    waves = [np.sin, np.cos, lambda x: -np.sin(x)]

    def evaluate(z, t, k=0):
        return np.sum(base * np.exp(t * u * u) * u**k * waves[k](z * u))

    return evaluate


def heat_mp(x, t, k=0, m=0, nmax=24, upper=4, lesion_factor=1):
    """mpmath quadrature of 4 int exp(tu^2+3u/2) omega(u) u^(k+m) sin^(k)(xu) du.

    k is the z-derivative order (0..3), m an extra power of u (m = 2 gives the
    t-derivative, since d/dt brings down u^2). Uses the caller's mp.dps.
    """
    tau = pilot.parameter()
    lf = Fraction(lesion_factor)
    a = coefficient_pattern(tau, mp.mpf(lf.numerator) / lf.denominator)
    coeff = [(n, n * a[n % 5]) for n in range(1, nmax + 1) if a[n % 5] != 0]
    waves = [mp.sin, mp.cos, lambda v: -mp.sin(v), lambda v: -mp.cos(v)]

    def integrand(u):
        q = mp.exp(-mp.pi * mp.exp(2 * u) / 5)
        omega = mp.fsum(c * q**(n * n) for n, c in coeff)
        return 4 * mp.exp(t * u * u + 3 * u / 2) * omega * u**(k + m) * waves[k](x * u)

    return mp.quad(integrand, [0, mp.mpf("0.5"), 1, 2, upper])


# ---------------------------------------------------------------------------
# route B: contour moments in the discriminant variable
# ---------------------------------------------------------------------------


class WindingError(ValueError):
    """The contour does not enclose exactly two zeros; the tracker refuses."""


def contour_moments(evaluate, t, centre, radius, nodes=128):
    """(q0, q1, q2): winding number and the first two power sums of the zeros inside."""
    theta = 2 * np.pi * (np.arange(nodes) + 0.5) / nodes
    z = centre + radius * np.exp(1j * theta)
    dz = 1j * radius * np.exp(1j * theta)
    h = 2 * np.pi / nodes
    logdiff = np.array([evaluate(zz, t, 1) / evaluate(zz, t, 0) for zz in z])
    q0 = np.sum(logdiff * dz) * h / (2j * np.pi)
    q1 = np.sum(z * logdiff * dz) * h / (2j * np.pi)
    q2 = np.sum(z * z * logdiff * dz) * h / (2j * np.pi)
    return q0, q1, q2


def discriminant(evaluate, t, centre, radius, nodes=128, winding_tol=1e-6):
    """Delta(t) = 2 q2 - q1^2 = (z1 - z2)^2 for the pair inside; refuses otherwise."""
    q0, q1, q2 = contour_moments(evaluate, t, centre, radius, nodes)
    if abs(q0 - 2) > winding_tol:
        raise WindingError(f"winding {complex(q0).real:.3e}{complex(q0).imag:+.3e}j at t={t}, centre={centre}, radius={radius}")
    delta = 2 * q2 - q1 * q1
    if abs(delta.imag) > 1e-7 * max(1.0, abs(delta.real)):
        raise WindingError(f"discriminant not real: {delta!r}")
    return float(delta.real), float(q1.real / 2)


def pair_root(evaluate, z, t):
    """Float Newton (scipy) for a complex zero of H_t near z."""
    def objective(v):
        value = evaluate(complex(*v), t)
        return [value.real, value.imag]
    answer = root(objective, [z.real, z.imag], tol=1e-13)
    return complex(*answer.x), bool(answer.success)


def landing_time_route_b(evaluate, t_lo, t_hi, centre, radius, nodes=128):
    """Root of Delta(t) on [t_lo, t_hi] by Brent; the contour is fixed."""
    def delta_only(t):
        return discriminant(evaluate, t, centre, radius, nodes)[0]
    t_c = brentq(delta_only, t_lo, t_hi, xtol=1e-14, rtol=4 * np.finfo(float).eps)
    _, x_c = discriminant(evaluate, t_c, centre, radius, nodes)
    return t_c, x_c


# ---------------------------------------------------------------------------
# route A: the double-zero system
# ---------------------------------------------------------------------------


def landing_time_route_a(x0, t0, dps, lesion_factor=1):
    """Newton on (H_t(x), H_t'(x)) = 0 in the real unknowns (x, t) at mp.dps = dps."""
    with mp.workdps(dps):
        def system(x, t):
            return [heat_mp(x, t, 0, lesion_factor=lesion_factor),
                    heat_mp(x, t, 1, lesion_factor=lesion_factor)]

        def jacobian(x, t):
            return mp.matrix([
                [heat_mp(x, t, 1, lesion_factor=lesion_factor), heat_mp(x, t, 0, 2, lesion_factor=lesion_factor)],
                [heat_mp(x, t, 2, lesion_factor=lesion_factor), heat_mp(x, t, 1, 2, lesion_factor=lesion_factor)],
            ])

        solution = mp.findroot(system, (mp.mpf(x0), mp.mpf(t0)), J=jacobian,
                               tol=mp.mpf(10)**(-dps + 5))
        x_c, t_c = solution[0], solution[1]
        residual = [abs(v) for v in system(x_c, t_c)]
        curvature = heat_mp(x_c, t_c, 2, lesion_factor=lesion_factor)
        return {"dps": dps, "x_c": mp.nstr(x_c, dps - 4), "t_c": mp.nstr(t_c, dps - 4),
                "residual_H": mp.nstr(residual[0], 5), "residual_Hprime": mp.nstr(residual[1], 5),
                "second_derivative_at_double_zero": mp.nstr(curvature, 12)}


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def known_value_controls():
    """Ground truth from CLAUDE.md through the libraries this probe uses."""
    out = {}
    with mp.workdps(30):
        z2 = mp.zeta(2)
        out["zeta2_minus_pi2_over_6"] = mp.nstr(abs(z2 - mp.pi**2 / 6), 5)
        g1 = mp.zetazero(1).imag
        out["gamma1_minus_reference"] = mp.nstr(abs(g1 - mp.mpf("14.134725141734694")), 5)
    from zeta.core import Xi
    xi0 = Xi(0, dps=20)
    out["Xi0_minus_reference"] = mp.nstr(abs(mp.mpf(xi0) - mp.mpf("0.4971207781")), 5)
    return out


def recorded_disk_reproduced():
    """The dh_minus_heat 217/200 disk, rerun at 128 bits with its coarse bounds."""
    row = odd_ball.rouche(RECORDED_DISK_CENTRE, RADIUS, t=str(RECORDED_LOWER), prec=128)
    coarse = {
        "H_abs_below_1e-14": Fraction(row["H_abs_upper"]["upper"]) < Fraction("1e-14"),
        "Hprime_abs_above_28_over_10000": Fraction(row["Hprime_abs_lower"]["lower"]) > Fraction(28, 10000),
        "M2_below_19_over_10": Fraction(row["M2_upper"]["upper"]) < Fraction(19, 10),
        "written_margin": str(Fraction(559961, 2000000000000000)),
    }
    return {"decided": row["decided"], "margin": row["margin"], "coarse": coarse}


def zero_time_gate(evaluate):
    """The t=0 admissibility gate: the tracker must reproduce the pilot zeros."""
    rows = {}
    for label, (s_re, s_im) in PILOT_ZEROS.items():
        z = complex(float(s_im), float(s_re) - 0.5)
        found, ok = pair_root(evaluate, z, 0.0)
        rows[label] = {"pilot_z": [z.real, z.imag], "tracker_z": [found.real, found.imag],
                       "converged": ok, "abs_difference": abs(found - z)}
    with mp.workdps(30):
        z = mp.mpc("2", "0.4")
        value = heat_mp(z, mp.mpf(0))
        reference = -1j * pilot.completed(mp.mpf("0.5") + 1j * z)
        rows["hurwitz_identity_defect_dps30"] = mp.nstr(abs(value - reference), 5)
    return rows


def tracker_known_value_controls():
    """The discriminant tracker on exact polynomial heat flows with closed-form landings."""
    def polynomial_evaluator(coefficients_at):
        def evaluate(z, t, k=0):
            p = np.polynomial.polynomial.Polynomial(coefficients_at(t))
            return p(z) if k == 0 else p.deriv()(z)
        return evaluate

    # p_t = exp(-t d^2/dz^2) p_0 is the backward flow the sine integral obeys
    # (d/dt H = -H''), so p_0 = (z-x)^2 + y0^2 gives p_t = (z-x)^2 + y0^2 - 2t.
    x0, y0 = 0.3, 0.6
    isolated = polynomial_evaluator(lambda t: [x0 * x0 + y0 * y0 - 2 * t, -2 * x0, 1.0])
    t_iso = brentq(lambda t: discriminant(isolated, t, x0, 1.0)[0], 0.05, 0.3, xtol=1e-15)
    # (z^2-a^2)(z^2+Y^2): p_t = z^4 + (Y^2-a^2-12t) z^2 - a^2 Y^2 - 2t(Y^2-a^2) + 12 t^2,
    # landing of the pair at +-iY at t_+ = [(Y^2-a^2) + sqrt((Y^2-a^2)^2 + 12 a^2 Y^2)]/12
    # (docs/37, four-root control). Y < a so a radius between them isolates the pair.
    a, Y = 1.2, 0.5
    quartic = polynomial_evaluator(lambda t: [-a * a * Y * Y - 2 * t * (Y * Y - a * a) + 12 * t * t,
                                              0.0, Y * Y - a * a - 12 * t, 0.0, 1.0])
    t_plus = ((Y * Y - a * a) + np.sqrt((Y * Y - a * a)**2 + 12 * a * a * Y * Y)) / 12
    t_quartic = brentq(lambda t: discriminant(quartic, t, 0.0, 0.9)[0], 0.5 * t_plus, 1.5 * t_plus, xtol=1e-15)
    return {
        "isolated_pair": {"x0": x0, "y0": y0, "measured": t_iso, "expected_y0sq_over_2": y0 * y0 / 2,
                          "abs_error": abs(t_iso - y0 * y0 / 2)},
        "quartic": {"a": a, "Y": Y, "measured": t_quartic, "expected_closed_form": t_plus,
                    "abs_error": abs(t_quartic - t_plus)},
    }


def lesions(evaluate):
    """Planted faults, each of which a named check must catch."""
    out = {}
    # 1. clipped contour: a radius smaller than the pair's depth at t = 1.08
    try:
        discriminant(evaluate, 1.08, 7.549, 0.05)
        out["clipped_contour"] = {"refused": False}
    except WindingError as exc:
        out["clipped_contour"] = {"refused": True, "message": str(exc)[:80]}
    # 2. displaced centre (1e-4, a thousand radii): the disk must not decide
    displaced = odd_ball.rouche(("7.543245542463", RECORDED_DISK_CENTRE[1]), RADIUS,
                                t=str(RECORDED_LOWER), prec=128)
    out["displaced_centre"] = {"decided": displaced["decided"]}
    # 3. underresolved theta series: nmax = 2 must not decide
    under = odd_ball.rouche(RECORDED_DISK_CENTRE, RADIUS, t=str(RECORDED_LOWER), prec=128, nmax=2)
    out["underresolved_series"] = {"decided": under["decided"]}
    return out


def track_pair(evaluate, z0, step=0.05, max_steps=60):
    """Continue a conjugate zero in t from z0 at t = 0 until it reaches the axis.

    Returns (track, last_off) where last_off = (t, z) is the last time the
    float root solve returned an off-axis zero. Measured only.
    """
    track, last_off, z = [], None, z0
    for k in range(1, max_steps + 1):
        t = round(step * k, 10)
        z, ok = pair_root(evaluate, z, t)
        track.append({"t": t, "z_re": z.real, "z_im": z.imag, "converged": ok})
        if not ok or abs(z.imag) < 1e-6:
            break
        last_off = (t, z)
    return track, last_off


def land(evaluate, last_off, radius=0.4, dps=30, lesion_factor=1):
    """Landing time from the last off-axis point: route B bracket, then route A."""
    t_lo, z_lo = last_off
    centre = z_lo.real
    t_hi = t_lo
    while True:
        t_hi = round(t_hi + 0.01, 10)
        if discriminant(evaluate, t_hi, centre, radius)[0] > 0:
            break
    t_b, x_b = landing_time_route_b(evaluate, t_lo, t_hi, centre, radius)
    a = landing_time_route_a(x_b, t_b, dps, lesion_factor=lesion_factor)
    return {"route_b": {"t_c": t_b, "x_c": x_b, "contour": [centre, radius], "bracket": [t_lo, t_hi]},
            f"route_a_dps{dps}": a, "routes_abs_difference": abs(float(a["t_c"]) - t_b)}


def shared_layer_lesion(t_c_true, factor=1.01):
    """Scale the residue-2 coefficient by `factor` in BOTH routes.

    The two tracking routes share the kernel, so they must still agree with
    each other on the wrong function's landing time; only the zero-time
    Hurwitz identity, which shares no theta integral, can see the fault.
    This is docs/37's independence-by-mutation control, run rather than cited.
    """
    lesioned = float_grid(lesion_factor=factor)
    z0 = complex(float(PILOT_ZEROS["pair1"][1]), float(PILOT_ZEROS["pair1"][0]) - 0.5)
    track, last_off = track_pair(lesioned, z0, step=0.025)
    if last_off is None:
        return {"pair_found": False}
    landed = land(lesioned, last_off, lesion_factor=Fraction(101, 100))
    with mp.workdps(30):
        z = mp.mpc("2", "0.4")
        bad = heat_mp(z, mp.mpf(0), lesion_factor=Fraction(101, 100))
        reference = -1j * pilot.completed(mp.mpf("0.5") + 1j * z)
        identity_defect = mp.nstr(abs(bad - reference), 5)
        shift = mp.nstr(abs(mp.mpf(landed["route_a_dps30"]["t_c"]) - mp.mpf(t_c_true)), 5)
    return {"pair_found": True, "factor": factor, "landing": landed,
            "routes_abs_difference": landed["routes_abs_difference"],
            "shift_from_true_t_c": shift, "hurwitz_identity_defect": identity_defect,
            "reading": "the two routes agree on the wrong function; only the Hurwitz identity sees the fault"}


# ---------------------------------------------------------------------------
# the ladder
# ---------------------------------------------------------------------------


def centre_at(evaluate, t_q: Fraction):
    """Polish the pair's upper zero at rational time t_q to 14 significant digits."""
    with mp.workdps(30):
        t = mp.mpf(t_q.numerator) / t_q.denominator
        z_float, ok = pair_root(evaluate, complex(7.54, 0.01), float(t))
        if not ok or abs(z_float.imag) < 1e-9:
            raise ValueError(f"no off-axis float zero at t={t_q}")
        w = mp.findroot(lambda v: pilot.heat_mp(v, t, nmax=24),
                        mp.mpc(z_float.real, abs(z_float.imag)), tol=mp.mpf("1e-26"))
        return (mp.nstr(w.real, 14), mp.nstr(abs(w.imag), 14))


def disk_ladder(evaluate, t_c_text):
    rows = []
    t_c = Fraction(t_c_text)
    for t_q in LADDER:
        if t_q >= t_c:
            rows.append({"t": str(t_q), "skipped": "at or above the measured landing time"})
            continue
        centre = centre_at(evaluate, t_q)
        configs = []
        for prec, nmax, upper in DISK_CONFIGS:
            row = odd_ball.rouche(centre, RADIUS, t=str(t_q), prec=prec, nmax=nmax, upper=upper)
            configs.append({"prec": prec, "nmax": nmax, "upper": upper, "decided": row["decided"],
                            "margin": row["margin"], "H_abs_upper": row["H_abs_upper"]["upper"],
                            "Hprime_abs_lower": row["Hprime_abs_lower"]["lower"],
                            "M2_upper": row["M2_upper"]["upper"]})
        decided_all = all(c["decided"] for c in configs)
        # Coarse rational bounds in the safe direction, as dh_minus_heat section 2 states them.
        h_up = max(Fraction(c["H_abs_upper"]) for c in configs)
        hp_lo = min(Fraction(c["Hprime_abs_lower"]) for c in configs)
        m2_up = max(Fraction(c["M2_upper"]) for c in configs)
        coarse = {"H_abs_below": _round_up(h_up), "Hprime_abs_above": _round_down(hp_lo),
                  "M2_below": _round_up(m2_up)}
        written = (RADIUS * Fraction(coarse["Hprime_abs_above"]) - Fraction(coarse["H_abs_below"])
                   - RADIUS * RADIUS * Fraction(coarse["M2_below"]) / 2)
        rows.append({"t": str(t_q), "t_float": float(t_q), "delta_to_t_c": float(t_c - t_q),
                     "centre": list(centre), "radius": str(RADIUS), "configs": configs,
                     "decided_all_configs": decided_all, "coarse": coarse,
                     "written_margin": str(written), "written_margin_positive": written > 0})
    return rows


def _round_up(q: Fraction, digits=2) -> str:
    """Smallest 2-significant-digit decimal >= q."""
    if q <= 0:
        return "0"
    e = 0
    while q >= 10**(digits):
        q /= 10
        e += 1
    while q < 10**(digits - 1):
        q *= 10
        e -= 1
    m = -(-q.numerator // q.denominator)  # ceiling
    return str(Fraction(m) * Fraction(10)**e)


def _round_down(q: Fraction, digits=2) -> str:
    """Largest 2-significant-digit decimal <= q."""
    if q <= 0:
        return "0"
    e = 0
    while q >= 10**(digits):
        q /= 10
        e += 1
    while q < 10**(digits - 1):
        q *= 10
        e -= 1
    m = q.numerator // q.denominator  # floor
    return str(Fraction(m) * Fraction(10)**e)


# ---------------------------------------------------------------------------
# the second pilot pair, as a scout
# ---------------------------------------------------------------------------


def second_pair(evaluate, fine):
    """Landing time of the pilot's second zero (height 18.9), both routes, measured only."""
    z0 = complex(float(PILOT_ZEROS["pair2"][1]), float(PILOT_ZEROS["pair2"][0]) - 0.5)
    track, last_off = track_pair(evaluate, z0)
    landed = land(evaluate, last_off)
    t_lo, t_hi = landed["route_b"]["bracket"]
    centre, radius = landed["route_b"]["contour"]
    t_b2, x_b2 = landing_time_route_b(fine, t_lo, t_hi, centre, radius, nodes=256)
    landed["route_b_grid960_nodes256"] = {"t_c": t_b2, "x_c": x_b2}
    landed["resolution_response"] = abs(t_b2 - landed["route_b"]["t_c"])
    return {"grade": "measured", "track": track, **landed}


def after_landing(evaluate, t_c, x_c):
    """Measured: the two real zeros separate after t_c and keep separating."""
    rows = []
    for t in [t_c + 1e-3, t_c + 1e-2, 1.1, 1.12, 1.15]:
        delta, x = discriminant(evaluate, t, x_c, 0.6)
        rows.append({"t": t, "discriminant": delta, "separation": float(np.sqrt(max(delta, 0.0))), "mean": x})
    return rows


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def run():
    started = time.monotonic()
    result = {"hunt": "dh_minus_landing", "frame": FRAME,
              "timestamp": datetime.now(timezone.utc).isoformat(),
              "recorded_bracket_narrow": {"strict_lower": str(RECORDED_LOWER), "upper": str(RECORDED_UPPER)}}
    stage = time.monotonic()
    result["known_value_controls"] = known_value_controls()
    result["recorded_disk_reproduced"] = recorded_disk_reproduced()
    evaluate = float_grid(480)
    result["zero_time_gate"] = zero_time_gate(evaluate)
    result["tracker_known_value_controls"] = tracker_known_value_controls()
    result["timing"] = {"controls_s": time.monotonic() - stage}

    stage = time.monotonic()
    scout = []
    for t in [1.08, 1.085, 1.0875, 1.0876, 1.0877, 1.09]:
        delta, x = discriminant(evaluate, t, 7.545, 0.3)
        scout.append({"t": t, "discriminant": delta, "depth": float(np.sqrt(-delta / 4)) if delta < 0 else None, "mean": x})
    t_b, x_b = landing_time_route_b(evaluate, 1.085, 1.09, 7.545, 0.3)
    fine = float_grid(960)
    t_b2, x_b2 = landing_time_route_b(fine, 1.085, 1.09, 7.545, 0.3, nodes=256)
    result["route_b"] = {"grade": "measured", "scout_rows": scout,
                         "grid480_nodes128": {"t_c": t_b, "x_c": x_b},
                         "grid960_nodes256": {"t_c": t_b2, "x_c": x_b2},
                         "resolution_response": abs(t_b - t_b2)}
    result["timing"]["route_b_s"] = time.monotonic() - stage

    stage = time.monotonic()
    a30 = landing_time_route_a(x_b, t_b, 30)
    a50 = landing_time_route_a(x_b, t_b, 50)
    with mp.workdps(60):
        precision_response = mp.nstr(abs(mp.mpf(a30["t_c"]) - mp.mpf(a50["t_c"])), 5)
        cross_route = mp.nstr(abs(mp.mpf(a50["t_c"]) - mp.mpf(t_b)), 5)
    result["route_a"] = {"grade": "measured", "dps30": a30, "dps50": a50,
                         "precision_response_t_c": precision_response}
    result["agreement"] = {"route_a_dps50_vs_route_b_grid480": cross_route,
                           "grade_of_t_c": "hardened: two independent float routes agree; no enclosure"}
    result["timing"]["route_a_s"] = time.monotonic() - stage

    stage = time.monotonic()
    result["after_landing"] = after_landing(evaluate, t_b, x_b)
    result["disk_ladder"] = disk_ladder(evaluate, a50["t_c"])
    decided = [r for r in result["disk_ladder"] if r.get("decided_all_configs")]
    best = max(decided, key=lambda r: Fraction(r["t"])) if decided else None
    result["timing"]["ladder_s"] = time.monotonic() - stage

    stage = time.monotonic()
    result["second_pair"] = second_pair(evaluate, fine)
    result["lesions"] = lesions(evaluate)
    result["lesions"]["shared_layer_kernel_fault"] = shared_layer_lesion(a50["t_c"])
    result["timing"]["second_pair_and_lesions_s"] = time.monotonic() - stage

    t_c = Fraction(a50["t_c"])
    result["bracket_after"] = {
        "frame": FRAME,
        "strict_lower_rational": best["t"] if best else str(RECORDED_LOWER),
        "strict_lower_float": float(Fraction(best["t"])) if best else float(RECORDED_LOWER),
        "upper_unchanged": str(RECORDED_UPPER),
        "wide_frame_strict_lower": str(4 * Fraction(best["t"])) if best else str(4 * RECORDED_LOWER),
        "door_value_for_this_pair": float(t_c - RECORDED_LOWER),
        "remaining_below_t_c": float(t_c - Fraction(best["t"])) if best else None,
        "fraction_of_recorded_gap": float((t_c - RECORDED_LOWER) / (RECORDED_UPPER - RECORDED_LOWER)),
        "grade": "lower endpoint enclosure-carrying at the numerical step (Arb disks, exact rational margins); the surrounding argument is hunts/dh_minus_heat RESULTS section 5, ordinary and model-reviewed only",
    }
    result["kill_conditions"] = {
        "routes_disagree_above_1e-10": float(mp.mpf(cross_route)) > 1e-10,
        "t_c_moves_under_refinement_above_1e-20": float(mp.mpf(precision_response)) > 1e-20,
        "zero_time_gate_fails": any(not v["converged"] or v["abs_difference"] > 1e-8
                                    for k, v in result["zero_time_gate"].items() if k.startswith("pair")),
        "no_rational_time_above_217_over_200_decided": best is None,
        "second_pair_lands_later": result["second_pair"]["route_b"]["t_c"] > float(t_c),
    }
    result["seconds"] = time.monotonic() - started
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "results.json")
    args = parser.parse_args()
    data = run()
    args.output.write_text(json.dumps(data, indent=2, default=str) + "\n")
    summary = {k: data[k] for k in ("agreement", "bracket_after", "kill_conditions", "seconds")}
    summary["t_c_route_a_dps50"] = data["route_a"]["dps50"]["t_c"]
    summary["t_c_route_b"] = data["route_b"]["grid480_nodes128"]["t_c"]
    summary["second_pair_t_c"] = data["second_pair"]["route_b"]["t_c"]
    print(json.dumps(summary, indent=2, default=str))


if __name__ == "__main__":
    main()
