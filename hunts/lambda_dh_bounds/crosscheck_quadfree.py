"""A quadrature-free ball route to H_t(z), written from the definitions.

Provenance: written by adversary 4 and re-run by the gate adjudication of
2026-08-16 as ``a4_indep.py`` plus ``a4_box.py`` in a scratch directory, and
landed here under GATE.md closure item (e).  The mathematics and the numbers
are unchanged; the two scratch files are merged, the absolute paths are
gone, and the run writes a json.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/crosscheck_quadfree.py

It writes ``crosscheck_quadfree_results.json``.  Wall time is about two
minutes.

Why this route exists
---------------------

``instrument.py`` reaches H_t(z) by Arb's rigorous adaptive integrator over
the u axis, and BOTH winding routes call it (``INDEPENDENCE.md``: they share
nine of twelve declared layers, the whole evaluator).  This route reaches
the same number with no quadrature anywhere, and with a different equation
for kappa:

  kappa   from the Gauss sum of the odd primitive character chi mod 5.
          chi = (1, i, -i, -1) on n = 1..4, and a_n = (1, kappa, -kappa, -1)
          = A chi + B chibar with A = (1 - i kappa)/2, B = (1 + i kappa)/2.
          The completed L-functions satisfy
          Lambda(1-s, chibar) = (i sqrt5 / tau(chi)) Lambda(s, chi), so
          F(s) = F(1-s) forces A/B = w := i sqrt5 / tau(chi), hence
          kappa = (1 - w) / (i (1 + w)), with
          tau(chi) = sum_{n=1}^{4} chi(n) e^{2 pi i n / 5} an exact ball.
          This is a DIFFERENT equation from instrument.kappa_ball's
          numerical self-duality solve at s0 = 3/4 + 3i/2, and it is the one
          layer the DHFlow route (crosscheck_dhflow_winding.py) does not
          supply, since that route's kappa is the same solve in mpmath.

  H_0(z)  = F(1/2 + iz) with f(s) = 5^{-s} sum_j a_j zeta(s, j/5), by
          Hurwitz zeta.  No series in u, no quadrature.

  H_t(z)  = sum_{k>=0} t^k / k! * F^{(2k)}(1/2 + iz), from dH/dt =
          -d^2H/dz^2 and H_0(z) = F(1/2 + iz).  Taylor coefficients from
          ``acb_series`` (Hurwitz zeta series and Gamma series), with the
          truncation remainder bounded explicitly in ``taylor_remainder``.
          No quadrature anywhere.

Grade: enclosure-carrying (Arb balls with an explicit remainder), so the
agreements below are ball overlaps, not float comparisons.  What it shares
with the instrument is the ball arithmetic backend and nothing else; that
shared layer is reconvergent, and agreement here cannot see a fault in
python-flint itself.

The three parts
---------------

1. kappa: the Gauss-sum ball against ``instrument.kappa_ball`` at three
   precisions.
2. t = 0: the Hurwitz-zeta ball against ``instrument.H_ball`` at six points
   spanning heights 10 to 420.
3. t > 0: the Taylor-in-t ball against ``instrument.H_ball``, at five
   assorted points and then at all eight distinguished points of the
   boundary of the t1 = 23/400 winding box, at K = 100 and 900 bits, where
   the route's own remainder ball is smaller than the instrument's radius.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import acb, acb_series, arb, ctx, fmpq  # noqa: E402

import instrument as ins  # noqa: E402

OUT = os.path.join(HERE, "crosscheck_quadfree_results.json")

# the t1 winding box, from winding_results.json (t1_run)
RE_LO, RE_HI = Fraction(122929, 512), Fraction(123185, 512)
IM_LO, IM_HI = Fraction(3, 512), Fraction(61, 1024)
T1 = Fraction(23, 400)


class prec_guard:
    """Set ``ctx.prec`` for a block (this route's own, not the instrument's)."""

    def __init__(self, p: int):
        self.p = p

    def __enter__(self):
        self.old = ctx.prec
        ctx.prec = self.p
        return self

    def __exit__(self, *a):
        ctx.prec = self.old
        return False


def q(x) -> arb:
    """arb of an exact rational, at the ambient precision."""
    f = Fraction(x)
    return arb(fmpq(f.numerator, f.denominator))


# ---------------------------------------------------------------------------
# kappa, from the Gauss sum (an independent equation)
# ---------------------------------------------------------------------------


def kappa_gauss(prec: int) -> arb:
    """kappa = (1 - w) / (i (1 + w)), w = i sqrt5 / tau(chi).

    Derivation in the module docstring.  The imaginary part of the quotient
    must contain 0 or the routine raises; the real ball is returned.
    """
    with prec_guard(prec):
        chi = {1: acb(0, 1) ** 0, 2: acb(0, 1), 3: acb(0, -1), 4: acb(-1)}
        two_pi_i_over_5 = acb(0, 1) * 2 * arb.pi() / 5
        tau = acb(0)
        for n in range(1, 5):
            tau += chi[n] * (two_pi_i_over_5 * n).exp()
        w = acb(0, 1) * acb(arb(5).sqrt()) / tau
        k = (1 - w) / (acb(0, 1) * (1 + w))
        if not k.imag.contains(arb(0)):
            raise ValueError("kappa_gauss: imaginary part does not contain 0")
        return k.real


# ---------------------------------------------------------------------------
# F(s) by Hurwitz zeta, and H_0(z) = F(1/2 + iz)
# ---------------------------------------------------------------------------


def F_ball(s, kap: arb, prec: int) -> acb:
    """F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) 5^{-s} sum_j a_j zeta(s, j/5)."""
    with prec_guard(prec):
        s = acb(s)
        a = [None, arb(1), kap, -kap, arb(-1)]
        tot = acb(0)
        for j in range(1, 5):
            tot += acb(a[j]) * s.zeta(acb(fmpq(j, 5)))
        f = acb(5) ** (-s) * tot
        gam = ((acb(arb.pi() / 5)) ** (-(s + 1) / 2)) * ((s + 1) / 2).gamma()
        return gam * f


def H0_hurwitz(z, kap: arb, prec: int) -> acb:
    with prec_guard(prec):
        zb = z if isinstance(z, acb) else acb(q(z[0]), q(z[1]))
        return F_ball(acb(arb(fmpq(1, 2))) + acb(0, 1) * zb, kap, prec)


# ---------------------------------------------------------------------------
# H_t by the Taylor-in-t series, with a rigorous truncation remainder
# ---------------------------------------------------------------------------


def F_taylor(s0: acb, kap: arb, order: int, prec: int) -> list:
    """Taylor coefficients c_m of F about s0: F(s0 + h) = sum c_m h^m."""
    old_cap = ctx.cap
    ctx.cap = order          # python-flint series truncation is GLOBAL
    try:
        with prec_guard(prec):
            s = acb_series([s0, 1])
            a = [None, arb(1), kap, -kap, arb(-1)]
            tot = acb_series([0])
            for j in range(1, 5):
                tot = tot + acb_series([acb(a[j])]) * s.zeta(acb(fmpq(j, 5)))
            five_pow = (s * (-acb(5).log())).exp()
            f = five_pow * tot
            half = (s + 1) / 2
            gam = ((half * (-acb(arb.pi() / 5).log())).exp()) * half.gamma()
            out = (gam * f).coeffs()
            if len(out) < order:
                raise ValueError(f"series cap failed: got {len(out)} < {order}")
            return out
    finally:
        ctx.cap = old_cap


def W0_upper(prec: int) -> arb:
    """Upper bound for W(0) = sum_{n>=1} n exp(-pi n^2 / 5)."""
    with prec_guard(prec):
        s = arb(0)
        for n in range(1, 40):
            s += n * (-arb.pi() * n * n / 5).exp()
        # the tail beyond n = 40 is under 1e-200; add a crude cushion
        return (s + arb(fmpq(1, 10 ** 200))).abs_upper()


def taylor_remainder(K: int, t_q, y_q, U0_q, prec: int) -> arb:
    """Upper bound for |sum_{k>=K} t^k/k! M_k|, M_k = int u^{2k} Phi cos(zu) du.

    |M_k| <= int_0^inf u^{2k} |Phi(u)| cosh(yu) du and
    sum_{k>=K} x^k/k! <= x^K e^x / K!, so with x = t u^2,

      R_K <= (1/K!) int_0^inf 4 (t u^2)^K e^{t u^2} e^{(3/2+y)u} W(u) du,
      W(u) = sum_{n>=1} n e^{-pi n^2 e^{2u}/5}   (so |Phi| <= 4 e^{3u/2} W).

    On [0, U0]: W(u) <= W(0) and the rest is increasing, so the integral is
      <= U0 * 4 (t U0^2)^K e^{t U0^2} e^{(3/2+y)U0} W(0).
    On [U0, inf): W(u) <= 2 e^{-pi e^{2u}/5} (valid once e^{-pi e^{2u}/5}
    <= 0.29, i.e. e^{2u} >= 1.97), and u^{2K} <= e^{2Ku} (since log u <= u),
    so the integrand is <= 8 t^K e^{t u^2 + (3/2 + y + 2K) u - (pi/5) e^{2u}}
    and the same algebra as elsewhere (u and u^2 <= U0 and U0^2 times
    e^{-2U0} e^{2u} for u >= U0 >= 1) gives
      <= 4 t^K e^{-cV} / (cV),  V = e^{2U0},
      c = pi/5 - (t U0^2 + (3/2 + y + 2K) U0) e^{-2U0} > 0 (checked).
    """
    with prec_guard(prec):
        t = q(t_q)
        y = q(y_q)
        U0 = q(U0_q)
        if not (U0 >= 1):
            raise ValueError("need U0 >= 1")
        lgK = sum(arb(i).log() for i in range(2, K + 1))
        x0 = t * U0 * U0
        head = (U0 * 4 * (x0 ** K) * x0.exp()
                * ((arb(3) / 2 + y) * U0).exp() * arb(W0_upper(prec)))
        V = (2 * U0).exp()
        r = (-arb.pi() * V / 5).exp()
        if not (r.abs_upper() < arb(fmpq(29, 100))):
            raise ValueError("U0 too small for the |omega| <= 2r step")
        beta = arb(3) / 2 + y + 2 * K
        c = arb.pi() / 5 - (t * U0 * U0 + beta * U0) / V
        if not (c.lower() > 0):
            raise ValueError(f"c <= 0 at K={K}, U0={U0_q}: raise U0")
        tail = 4 * (t ** K) * (-c * V).exp() / (c * V)
        total = (head + tail) / lgK.exp()
        return total.abs_upper()


def H_taylor(z_re, z_im, t_q, K: int, U0_q, prec: int, order: int | None = None):
    """H_t(z) = sum_{k<K} t^k/k! F^{(2k)}(1/2 + iz) plus a remainder ball."""
    order = order or (2 * K + 2)
    with prec_guard(prec):
        s0 = acb(arb(fmpq(1, 2)) - q(z_im), q(z_re))   # 1/2 + i z
        kap = kappa_gauss(prec + 60)
        cs = F_taylor(s0, kap, order, prec)
        t = q(t_q)
        tot = acb(0)
        for k in range(K):
            m = 2 * k
            if m >= len(cs):
                break
            # F^{(m)}(s0) = m! c_m, so the term is t^k/k! * F^{(2k)}
            coef = arb(math.factorial(m)) / arb(math.factorial(k))
            tot += acb(coef * (t ** k)) * cs[m]
        rem = taylor_remainder(K, t_q, abs(Fraction(z_im)), U0_q, prec)
        e = arb(0, rem)
        return tot + acb(e, e), rem


# ---------------------------------------------------------------------------
# the three parts
# ---------------------------------------------------------------------------


def _ball_row(b) -> dict:
    return {"re_mid": float(b.real.mid()), "re_rad": float(b.real.rad()),
            "im_mid": float(b.imag.mid()), "im_rad": float(b.imag.rad())}


def _agreement_digits(a: acb, b: acb) -> float:
    """Measured relative agreement of two balls, in decimal digits.

    An upper bound for |a - b| divided by a lower bound for |b|, negated
    log10.  Reported because the gate's summary said the two routes agree
    "to about 22 digits", which was the width of the printed comparison
    rather than a measurement; this is the measurement.
    """
    with prec_guard(1200):
        num = float((a - b).abs_upper())
        den = float(b.abs_lower())
        if den <= 0:
            return float("nan")
        if num <= 0:
            return float("inf")
        return -math.log10(num / den)


def part_kappa() -> dict:
    rows = []
    all_ok = True
    for prec in (200, 400, 600):
        kg = kappa_gauss(prec)
        ki = ins.kappa_ball(prec)
        with prec_guard(900):
            ov = bool(kg.overlaps(ki))
        all_ok = all_ok and ov
        rows.append({"prec_bits": prec, "gauss": kg.str(35),
                     "instrument": ki.str(35), "overlap": ov})
        print(f"  prec {prec}: overlap {ov}   gauss {kg.str(30)}", flush=True)
    return {"all_overlap": all_ok,
            "equation": "kappa = (1 - w)/(i(1 + w)), w = i sqrt5 / tau(chi)",
            "instrument_equation": "self-duality linear solve at "
                                   "s0 = 3/4 + 3i/2",
            "rows": rows}


def part_t0() -> dict:
    kap = kappa_gauss(700)
    rows = []
    all_ok = True
    cases = [("10", "0", 420), ("10", "1/2", 420),
             ("240.4165", "0", 420), ("240.4165", "0.02", 420),
             ("240.4165", "0.02", 600), ("420.0625", "0", 600)]
    for zr, zi, prec in cases:
        H1 = H0_hurwitz((zr, zi), kap, prec)
        H2 = ins.H_ball((Fraction(zr), Fraction(zi)), 0, prec)
        with prec_guard(900):
            ov = bool(H1.overlaps(H2))
        all_ok = all_ok and ov
        rows.append({"z": f"{zr} + {zi}i", "prec_bits": prec,
                     "hurwitz": _ball_row(H1), "instrument": _ball_row(H2),
                     "overlap": ov})
        print(f"  z = {zr} + {zi}i, prec {prec}: overlap {ov}", flush=True)
    return {"all_overlap": all_ok,
            "route": "F(1/2 + iz) by Hurwitz zeta, no quadrature",
            "rows": rows}


def part_t_positive() -> dict:
    rows = []
    all_ok = True
    cases = [
        ("10", "0", "23/400", 30, "4", 500),
        ("240.4165", "0.02", "23/400", 40, "4", 600),
        ("240.4165", "0.02", "23/400", 60, "4", 700),
        ("240.4165", "3/100", "36/625", 60, "4", 700),
        ("85.6993", "0.3085", "3/100", 50, "4", 600),
    ]
    for zr, zi, ts, K, U0, prec in cases:
        HT, rem = H_taylor(zr, zi, ts, K, U0, prec)
        HI = ins.H_ball((Fraction(zr), Fraction(zi)), Fraction(ts), prec)
        with prec_guard(900):
            ov = bool(HT.overlaps(HI))
        all_ok = all_ok and ov
        rows.append({"z": f"{zr} + {zi}i", "t": ts, "K": K,
                     "prec_bits": prec,
                     "taylor_remainder_bound": float(rem),
                     "taylor": _ball_row(HT), "instrument": _ball_row(HI),
                     "overlap": ov})
        print(f"  z = {zr} + {zi}i, t = {ts}, K = {K}: overlap {ov}  "
              f"(remainder {float(rem):.2e})", flush=True)
    return {"all_overlap": all_ok,
            "route": "H_t = sum t^k/k! F^{(2k)}(1/2+iz), acb_series "
                     "coefficients, explicit remainder; no quadrature",
            "rows": rows}


def part_box_boundary() -> dict:
    """The eight distinguished boundary points of the t1 winding box."""
    pts = [
        (RE_LO, IM_LO), (RE_HI, IM_LO), (RE_LO, IM_HI), (RE_HI, IM_HI),
        ((RE_LO + RE_HI) / 2, IM_LO), ((RE_LO + RE_HI) / 2, IM_HI),
        (RE_LO, (IM_LO + IM_HI) / 2), (RE_HI, (IM_LO + IM_HI) / 2),
    ]
    K, PREC, U0 = 100, 900, "4"
    rows = []
    all_ok = True
    n_bad = 0
    for zr, zi in pts:
        HT, rem = H_taylor(str(zr), str(zi), str(T1), K, U0, PREC,
                           order=2 * K + 2)
        HI = ins.H_ball((zr, zi), T1, 420)
        with prec_guard(1200):
            ov = bool(HT.overlaps(HI))
        if not ov:
            n_bad += 1
        all_ok = all_ok and ov
        dig = _agreement_digits(HT, HI)
        rows.append({
            "z": f"{float(zr):.9f} + {float(zi):.9f}i",
            "z_exact": [str(zr), str(zi)],
            "taylor": HT.str(22), "instrument": HI.str(22),
            "taylor_remainder_bound": float(rem),
            "instrument_radius": float(HI.real.rad()),
            "measured_agreement_digits": dig,
            "overlap": ov,
        })
        print(f"  z = {float(zr):.9f} + {float(zi):.9f}i: overlap {ov}  "
              f"agreement {dig:.1f} digits  (remainder {float(rem):.2e} vs "
              f"instrument radius {float(HI.real.rad()):.2e})", flush=True)
    digits = [r["measured_agreement_digits"] for r in rows]
    return {"all_overlap": all_ok, "mismatches": n_bad,
            "min_measured_agreement_digits": min(digits),
            "agreement_digits_note": (
                "the gate's summary reported agreement 'to about 22 digits'; "
                "that was the width of the printed comparison, not a "
                "measurement.  The measured relative agreement, an upper "
                "bound for |taylor - instrument| over a lower bound for "
                "|instrument|, is reported per row."
            ),
            "box": {"re_lo": str(RE_LO), "re_hi": str(RE_HI),
                    "im_lo": str(IM_LO), "im_hi": str(IM_HI)},
            "t": str(T1), "K": K, "prec_bits": PREC,
            "note": "at K = 100 and 900 bits the route's own remainder ball "
                    "is smaller than the instrument's radius, so the overlap "
                    "is a real agreement and not a wide ball swallowing a "
                    "narrow one",
            "rows": rows}


def main() -> None:
    t_start = time.time()
    print("1. kappa: Gauss-sum equation vs instrument.kappa_ball", flush=True)
    kap = part_kappa()
    print("2. t = 0: quadrature-free Hurwitz ball vs instrument.H_ball",
          flush=True)
    t0 = part_t0()
    print("3. t > 0: Taylor-in-t (no quadrature) vs instrument.H_ball",
          flush=True)
    tp = part_t_positive()
    print("4. the eight boundary points of the t1 winding box", flush=True)
    box = part_box_boundary()

    all_ok = bool(kap["all_overlap"] and t0["all_overlap"]
                  and tp["all_overlap"] and box["all_overlap"])
    out = {
        "hunt": "lambda_dh_bounds",
        "route": "route 4: quadrature-free ball evaluator (Gauss-sum kappa, "
                 "Hurwitz-zeta H_0, acb_series Taylor in t with an explicit "
                 "remainder)",
        "provenance": "written by adversary 4 and re-run by the gate "
                      "adjudication of 2026-08-16 as a4_indep.py and "
                      "a4_box.py; landed here unchanged in mathematics under "
                      "GATE.md closure item (e)",
        "grade": "enclosure-carrying (Arb balls with an explicit remainder); "
                 "the agreements are ball overlaps",
        "independence": "shares exactly one declared layer with route 1, the "
                        "python-flint ball arithmetic backend, and that "
                        "layer is reconvergent.  Radius 0.  See "
                        "INDEPENDENCE.md and independence_decl.py.",
        "kappa": kap,
        "t_zero": t0,
        "t_positive": tp,
        "box_boundary": box,
        "all_pass": all_ok,
        "seconds_total": round(time.time() - t_start, 1),
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(f"\nall_pass = {all_ok}  ({out['seconds_total']} s)  -> {OUT}",
          flush=True)
    if not all_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
