"""Decide the hunt's constants on both backends and write decided.json.

Run from the repo root:

    .venv/bin/python hunts/prime_zeta_rightmost/decide.py

Constants decided (see instrument.py for every tail-bound derivation):

  x_star  : the root in (1,2) of zeta(x) = 2 (OEIS A107311).
  sigma_c : the root in (1,2) of h(s) = P(s) - 2^(1-s) = 0, the balance
            2^(-s) = sum_{p>=3} p^(-s) governing the rightmost zeros of
            the prime zeta function.
  sigma_3 : the root of u(s) = P(s) - 2^(-s) - 2*3^(-s) = 0, the same
            balance for the subset S = {p >= 3}: 3^(-s) = sum_{p>=5} p^(-s).

Sign decisions on top of them:

  separation : sigma_c - x_star > 1/20   (exact rational endpoint compare)
  margin     : P(x_star) - 2^(1-x_star) > 1/60  (h over the x_star enclosure)
  guards     : h' < 0 on [1.7, 1.9] and u' < 0 on [1.8, 1.85], deciding
               uniqueness of each root in its bracket; zeta is strictly
               decreasing on (1,2) termwise-exactly, no numerics needed.

Every decided number carries backend and precision. All intervals in
decided.json are outward-rounded decimal strings [lo, hi]. The iv leg is
the honest weaker leg: mpmath 1.3.0's iv.zeta raises on call, so it uses
the finite-sum + Euler-Maclaurin enclosure from instrument.py and reaches
smaller depth; what it could and could not carry is recorded in
backend_story.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from math import ceil, log10

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import flint
import mpmath

from instrument import (
    Timer,
    arb_endpoints,
    arb_from_fraction,
    arb_interval,
    bisect_decreasing,
    h_arb,
    h_iv,
    h_prime_upper_arb,
    h_prime_upper_iv,
    iv_endpoints,
    iv_from_fraction,
    mobius_sieve,
    outward_decimal,
    u_arb,
    u_iv,
    u_prime_upper_arb,
    u_prime_upper_iv,
    zeta_iv,
)

arb = flint.arb
fctx = flint.ctx
iv = mpmath.iv

FLINT_PREC_BITS = 350
IV_DPS = 40
K_FLINT = 120
K_IV = 40
N_IV_XSTAR = 4000
GUARD_PRIME_CUTOFF = 1000

# Transcribed from the OEIS A107311 JSON (revision 55, fetched 2026-08-15;
# scratchpad copy A107311.json), data field joined, offset 1: one digit
# before the decimal point, 102 digits total.
OEIS_DIGITS = (
    "172864723899818361813510301029769146423410984933503573232128590842317"
    "859653571008677274608108898264401"
)
assert len(OEIS_DIGITS) == 102
OEIS_LO = Fraction(int(OEIS_DIGITS), 10 ** 101)
OEIS_HI = OEIS_LO + Fraction(1, 10 ** 101)


def digits_for_width(width: Fraction) -> int:
    """Decimal places so outward rounding widens the interval only slightly."""
    if width <= 0:
        return 40
    return min(40, ceil(-log10(float(width))) + 2)


def interval_record(lo: Fraction, hi: Fraction, backend: str, precision: str,
                    method: str, seconds: float, extra: dict | None = None) -> dict:
    width = hi - lo
    d = digits_for_width(width)
    dlo, dhi = outward_decimal(lo, hi, d)
    rec = {
        "interval": [dlo, dhi],
        "width": f"{float(width):.3e}",
        "backend": backend,
        "precision": precision,
        "method": method,
        "time_s": round(seconds, 3),
    }
    if extra:
        rec.update(extra)
    return rec


def fr_str(x: Fraction, digits: int = 33) -> str:
    lo, hi = outward_decimal(x, x, digits) if x > 0 else (None, None)
    return lo if lo is not None else str(float(x))


def main() -> None:
    fctx.prec = FLINT_PREC_BITS
    iv.dps = IV_DPS
    mu = mobius_sieve(K_FLINT + 1)

    out: dict = {
        "hunt": "prime_zeta_rightmost",
        "task": "WP2 + WP4 decided constants, both backends",
        "date": "2026-08-16",
        "versions": {
            "python-flint": getattr(flint, "__version__", "unknown"),
            "mpmath": mpmath.__version__,
        },
        "vocabulary": "decided = interval/ball enclosure with exact endpoint sign logic; measured = one float route",
    }

    constants: dict = {}
    decisions: dict = {}
    notes: dict = {}

    # ------------------------------------------------------------------
    # x* on flint: zeta(x) = 2, bisection with arb zeta
    # ------------------------------------------------------------------
    def f_xstar_arb(q: Fraction):
        return arb_endpoints(arb.zeta(arb_from_fraction(q)) - 2)

    with Timer() as t:
        r = bisect_decreasing(f_xstar_arb, Fraction(17, 10), Fraction(18, 10),
                              Fraction(1, 10 ** 31))
    xs_flint = (r["lo"], r["hi"])
    constants.setdefault("x_star", {})["flint"] = interval_record(
        *xs_flint, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        "bisection on zeta(x)-2 with arb zeta; bracket [1.7, 1.8]",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"]})

    # ------------------------------------------------------------------
    # x* on mpmath.iv: finite Dirichlet sum + Euler-Maclaurin tail
    # ------------------------------------------------------------------
    def f_xstar_iv(q: Fraction):
        return iv_endpoints(zeta_iv(iv_from_fraction(q), N_IV_XSTAR) - 2)

    with Timer() as t:
        r = bisect_decreasing(f_xstar_iv, Fraction(17, 10), Fraction(18, 10),
                              Fraction(1, 10 ** 16))
    xs_iv = (r["lo"], r["hi"])
    constants["x_star"]["mpmath_iv"] = interval_record(
        *xs_iv, "mpmath.iv", f"dps {IV_DPS}",
        f"bisection; zeta by Dirichlet sum N={N_IV_XSTAR} plus Euler-Maclaurin "
        "tail with decided remainder (instrument.py docstring 2); iv.zeta "
        "raises on call in mpmath 1.3.0 so it was not used",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "dirichlet_N": N_IV_XSTAR})

    # OEIS containment cross-check
    oeis_in_flint = xs_flint[0] <= OEIS_LO and OEIS_HI <= xs_flint[1]
    oeis_in_iv = xs_iv[0] <= OEIS_LO and OEIS_HI <= xs_iv[1]
    constants["x_star"]["cross_checks"] = {
        "oeis_a107311_digits": OEIS_DIGITS[0] + "." + OEIS_DIGITS[1:],
        "oeis_value_interval_inside_flint_interval": oeis_in_flint,
        "oeis_value_interval_inside_iv_interval": oeis_in_iv,
        "backends_intersect": max(xs_flint[0], xs_iv[0]) <= min(xs_flint[1], xs_iv[1]),
        "flint_interval_inside_iv_interval": xs_iv[0] <= xs_flint[0] and xs_flint[1] <= xs_iv[1],
    }

    # ------------------------------------------------------------------
    # sigma_c on flint: h(s) = P(s) - 2^(1-s) via Moebius series
    # ------------------------------------------------------------------
    def f_h_arb(q: Fraction):
        return arb_endpoints(h_arb(arb_from_fraction(q), K_FLINT, mu))

    with Timer() as t:
        r = bisect_decreasing(f_h_arb, Fraction(17, 10), Fraction(19, 10),
                              Fraction(1, 10 ** 31))
    sc_flint = (r["lo"], r["hi"])
    constants.setdefault("sigma_c", {})["flint"] = interval_record(
        *sc_flint, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        f"bisection on P(s)-2^(1-s); P by Moebius series K={K_FLINT} with "
        "tail |sum_{k>K}| <= 3*2^(-(K+1)s)/((K+1)(1-2^(-s))) from "
        "0 < log zeta(y) <= 3*2^(-y) for y >= 2 (instrument.py docstring 1); "
        "bracket [1.7, 1.9]",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_FLINT})

    # ------------------------------------------------------------------
    # sigma_c on mpmath.iv: same Moebius series, iv zeta enclosure per term
    # ------------------------------------------------------------------
    def f_h_iv(q: Fraction):
        return iv_endpoints(h_iv(iv_from_fraction(q), K_IV, mu))

    with Timer() as t:
        r = bisect_decreasing(f_h_iv, Fraction(17, 10), Fraction(19, 10),
                              Fraction(1, 10 ** 13))
    sc_iv = (r["lo"], r["hi"])
    constants["sigma_c"]["mpmath_iv"] = interval_record(
        *sc_iv, "mpmath.iv", f"dps {IV_DPS}",
        f"bisection; Moebius series K={K_IV}, each zeta(k s) enclosed by "
        "finite sum + Euler-Maclaurin tail (N: 2000/400/100/30 by k), same "
        "Moebius tail bound as the flint leg",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_IV})
    constants["sigma_c"]["cross_checks"] = {
        "backends_intersect": max(sc_flint[0], sc_iv[0]) <= min(sc_flint[1], sc_iv[1]),
        "flint_interval_inside_iv_interval": sc_iv[0] <= sc_flint[0] and sc_flint[1] <= sc_iv[1],
    }

    # ------------------------------------------------------------------
    # sigma_3 on both backends: u(s) = P(s) - 2^(-s) - 2*3^(-s)
    # ------------------------------------------------------------------
    def f_u_arb(q: Fraction):
        return arb_endpoints(u_arb(arb_from_fraction(q), K_FLINT, mu))

    with Timer() as t:
        r = bisect_decreasing(f_u_arb, Fraction(9, 5), Fraction(37, 20),
                              Fraction(1, 10 ** 31))
    s3_flint = (r["lo"], r["hi"])
    constants.setdefault("sigma_3", {})["flint"] = interval_record(
        *s3_flint, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
        "bisection on u(s) = P(s) - 2^(-s) - 2*3^(-s), the {p>=3} subset "
        "balance 3^(-s) = sum_{p>=5} p^(-s); same Moebius machinery as "
        "sigma_c; bracket [1.80, 1.85]",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_FLINT})

    def f_u_iv(q: Fraction):
        return iv_endpoints(u_iv(iv_from_fraction(q), K_IV, mu))

    with Timer() as t:
        r = bisect_decreasing(f_u_iv, Fraction(9, 5), Fraction(37, 20),
                              Fraction(1, 10 ** 10))
    s3_iv = (r["lo"], r["hi"])
    constants["sigma_3"]["mpmath_iv"] = interval_record(
        *s3_iv, "mpmath.iv", f"dps {IV_DPS}",
        "bisection, same iv machinery as sigma_c, deliberately shallower "
        "target width (the weaker leg confirms, the flint leg decides depth)",
        t.seconds, {"iterations": r["iterations"], "sign_stalled": r["sign_stalled"],
                    "moebius_K": K_IV})
    constants["sigma_3"]["cross_checks"] = {
        "backends_intersect": max(s3_flint[0], s3_iv[0]) <= min(s3_flint[1], s3_iv[1]),
        "flint_interval_inside_iv_interval": s3_iv[0] <= s3_flint[0] and s3_flint[1] <= s3_iv[1],
    }

    # ------------------------------------------------------------------
    # Decision 3: separation sigma_c - x_star > 1/20 (exact rational compare)
    # ------------------------------------------------------------------
    sep_lo_flint = sc_flint[0] - xs_flint[1]
    sep_lo_iv = sc_iv[0] - xs_iv[1]
    decisions["separation_sigma_c_minus_x_star_gt_1_over_20"] = {
        "statement": "sigma_c - x_star > 1/20",
        "flint": {
            "decided": bool(sep_lo_flint > Fraction(1, 20)),
            "lower_bound_of_difference": fr_str(sep_lo_flint, 33),
            "compare": "exact rational: lo(sigma_c) - hi(x_star) vs 1/20",
        },
        "mpmath_iv": {
            "decided": bool(sep_lo_iv > Fraction(1, 20)),
            "lower_bound_of_difference": fr_str(sep_lo_iv, 14),
        },
    }

    # ------------------------------------------------------------------
    # Decision 4: margin P(x_star) - 2^(1-x_star) > 1/60
    # h evaluated over the whole x_star enclosure, so the decision holds for
    # the true x_star wherever it sits in the interval.
    # ------------------------------------------------------------------
    with Timer() as t:
        hx = h_arb(arb_interval(*xs_flint), K_FLINT, mu)
        hx_lo, hx_hi = arb_endpoints(hx)
    decisions["margin_P_at_x_star_minus_2_pow_1_minus_x_star_gt_1_over_60"] = {
        "statement": "P(x_star) - 2^(1-x_star) > 1/60",
        "flint": {
            "decided": bool(hx_lo > Fraction(1, 60)),
            "h_enclosure": list(outward_decimal(hx_lo, hx_hi, 33)),
            "compare": "exact rational: lower endpoint vs 1/60",
            "time_s": round(t.seconds, 3),
        },
    }
    with Timer() as t:
        hx_iv = h_iv(iv.mpf([iv_from_fraction(xs_iv[0]).a, iv_from_fraction(xs_iv[1]).b]),
                     K_IV, mu)
        hxi_lo, hxi_hi = iv_endpoints(hx_iv)
    decisions["margin_P_at_x_star_minus_2_pow_1_minus_x_star_gt_1_over_60"]["mpmath_iv"] = {
        "decided": bool(hxi_lo > Fraction(1, 60)),
        "h_enclosure": list(outward_decimal(hxi_lo, hxi_hi, 14)),
        "time_s": round(t.seconds, 3),
    }

    # ------------------------------------------------------------------
    # Decision 6: monotonicity guards (uniqueness of each root)
    # ------------------------------------------------------------------
    with Timer() as t:
        hp_lo, hp_hi = h_prime_upper_arb(Fraction(17, 10), Fraction(19, 10), GUARD_PRIME_CUTOFF)
    decisions["h_prime_negative_on_1p7_1p9"] = {
        "statement": "h'(s) < 0 for all s in [1.7, 1.9], so the sigma_c root is unique there",
        "bound": "h'(s) <= log2*2^(-s) - sum_{3<=p<=1000} log p * p^(-s); dropping the positive prime tail only raises the value",
        "flint": {
            "decided": bool(hp_hi < 0),
            "upper_bound_enclosure_upper_endpoint": str(float(hp_hi)),
            "prime_cutoff": GUARD_PRIME_CUTOFF,
            "time_s": round(t.seconds, 3),
        },
    }
    with Timer() as t:
        hpi_lo, hpi_hi = h_prime_upper_iv(Fraction(17, 10), Fraction(19, 10), GUARD_PRIME_CUTOFF)
    decisions["h_prime_negative_on_1p7_1p9"]["mpmath_iv"] = {
        "decided": bool(hpi_hi < 0),
        "upper_bound_enclosure_upper_endpoint": str(float(hpi_hi)),
        "prime_cutoff": GUARD_PRIME_CUTOFF,
        "time_s": round(t.seconds, 3),
    }

    with Timer() as t:
        up_lo, up_hi = u_prime_upper_arb(Fraction(9, 5), Fraction(37, 20), GUARD_PRIME_CUTOFF)
    decisions["u_prime_negative_on_1p80_1p85"] = {
        "statement": "u'(s) < 0 for all s in [1.80, 1.85], so the sigma_3 root is unique there",
        "bound": "u'(s) <= log2*2^(-s) + 2 log3*3^(-s) - sum_{p<=1000} log p * p^(-s)",
        "flint": {
            "decided": bool(up_hi < 0),
            "upper_bound_enclosure_upper_endpoint": str(float(up_hi)),
            "prime_cutoff": GUARD_PRIME_CUTOFF,
            "time_s": round(t.seconds, 3),
        },
    }
    with Timer() as t:
        upi_lo, upi_hi = u_prime_upper_iv(Fraction(9, 5), Fraction(37, 20), GUARD_PRIME_CUTOFF)
    decisions["u_prime_negative_on_1p80_1p85"]["mpmath_iv"] = {
        "decided": bool(upi_hi < 0),
        "upper_bound_enclosure_upper_endpoint": str(float(upi_hi)),
        "prime_cutoff": GUARD_PRIME_CUTOFF,
        "time_s": round(t.seconds, 3),
    }

    decisions["zeta_strictly_decreasing_on_1_2"] = {
        "statement": "zeta'(x) = -sum_{n>=2} log n * n^(-x) < 0 termwise for x > 1; "
                     "exact, no numerics needed; the x_star root is unique in (1,2)",
        "decided": True,
        "kind": "termwise-exact, both backends unnecessary",
    }

    decisions["bracket_endpoint_signs"] = {
        "note": "each bisection first decided the bracket endpoint signs "
                "(f(lo) > 0, f(hi) < 0) on its own backend; a bracket with "
                "undecided endpoints raises and no such raise occurred",
        "brackets": {
            "x_star": "[1.7, 1.8]", "sigma_c": "[1.7, 1.9]", "sigma_3": "[1.80, 1.85]",
        },
    }

    # ------------------------------------------------------------------
    # pre-registered prediction checks (MISSION.md P1, P3)
    # ------------------------------------------------------------------
    p1_sigma = Fraction(177954465, 10**8) <= sc_flint[0] and sc_flint[1] <= Fraction(177954466, 10**8)
    p1_x = Fraction(172864723, 10**8) <= xs_flint[0] and xs_flint[1] <= Fraction(172864724, 10**8)
    p3 = Fraction(182522, 10**5) <= s3_flint[0] and s3_flint[1] <= Fraction(182523, 10**5)
    out["preregistered_checks"] = {
        "P1_sigma_c_in_[1.77954465,1.77954466]": bool(p1_sigma),
        "P1_x_star_in_[1.72864723,1.72864724]": bool(p1_x),
        "P1_separation_gt_1_over_20": bool(sep_lo_flint > Fraction(1, 20)),
        "P3_sigma_3_in_[1.82522,1.82523]": bool(p3),
    }

    notes["backend_story"] = (
        "flint (arb, 350 bits) carries everything to width < 1e-30: arb.zeta "
        "directly for x_star, the Moebius series with K=120 and the decided "
        "2^(-(K+1)s) tail for P. mpmath.iv (dps 40) is the weaker leg by "
        "construction: iv.zeta exists as an attribute in mpmath 1.3.0 but "
        "raises AttributeError('bernoulli') on call, so the iv leg carries a "
        "finite Dirichlet sum plus an Euler-Maclaurin tail whose remainder is "
        "bounded by y(y+1)(y+2)a^(-y-3)/720 and added as an interval. That "
        "enclosure decides x_star to ~1e-16, sigma_c to ~1e-13 and sigma_3 to "
        "~1e-10, and it independently confirms every sign decision the flint "
        "leg makes (separation, margin, both derivative guards). What iv "
        "could not carry: 30-digit widths (the per-term Euler-Maclaurin "
        "remainder floor and iv arithmetic cost cap the useful depth), and "
        "any use of a library zeta. All bracket bookkeeping is exact "
        "Fractions on both legs, so backend rounding can widen but never "
        "misplace an interval."
    )
    notes["uniqueness_argument"] = (
        "Each constant is the unique root of a strictly decreasing function "
        "on its bracket: zeta on (1,2) termwise-exactly; h and u by the "
        "decided derivative guards above. Bisection preserves decided "
        "opposite signs at the bracket ends, so each reported interval "
        "contains the root."
    )
    notes["moebius_tail_bound"] = (
        "|sum_{k>K} mu(k)/k log zeta(ks)| <= 3*2^(-(K+1)s)/((K+1)(1-2^(-s))) "
        "for s >= 1, K >= 1, from 0 < log zeta(y) <= zeta(y)-1 <= 3*2^(-y) "
        "for y >= 2; full derivation in instrument.py."
    )

    out["constants"] = constants
    out["decisions"] = decisions
    out["notes"] = notes

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "decided.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
        f.write("\n")

    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
