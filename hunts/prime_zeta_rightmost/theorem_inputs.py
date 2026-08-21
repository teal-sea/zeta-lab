"""Decide the demonstration inputs quoted by THEOREM.md, on both backends.

Run from the repo root:

    .venv/bin/python hunts/prime_zeta_rightmost/theorem_inputs.py

THEOREM.md (WP3, WP4) is written so that its general statements need no
numerics beyond decided.json: the wall constants are exact roots of exactly
monotone functions, and every glue step is proved in the text. What remains
numeric is the small set of demonstration inequalities that pin the concrete
refuting instances, decided here with the instrument.py machinery:

  D1  h(7/4) > 1/128            ring margin at sigma_1 = 7/4 for Theorem B's
                                 concrete instance (h(s) = P(s) - 2^(1-s));
                                 second, independent route to h(7/4) > 0,
                                 which also follows from 7/4 < sigma_c.
  D2  u(9/5) > 1/256            ring margin at sigma_1 = 9/5 for the subset
                                 {p >= 3} (u(s) = P(s) - 2^(-s) - 2*3^(-s));
                                 independent route to u(9/5) > 0.
  D3  log2(69/(5 log 23)) > 17/8  the Theorem C tail instance k = 9,
                                 p_9 = 23: the Rosser-Schoenfeld count
                                 3x/(5 log x) at x = 23 forces the {p >= 23}
                                 wall above 17/8 = 2.125.

Exact-rational window comparisons against decided.json endpoints (no backend
arithmetic; Fraction compares of outward-rounded decimal endpoints, which is
conservative in the safe direction because outward rounding only widens):

  W1  hi(x_star)  < 173/100     so every zero with Re s >= 1.73 beats x*.
  W2  lo(sigma_c) > 7/4         so 7/4 is inside (1, sigma_c).
  W3  lo(sigma_c) > 177/100     so the window (1.73, 1.77) sits inside
                                 (1, sigma_c).
  W4  hi(sigma_c) < 89/50       so the window (1.78, 1.82) sits entirely to
                                 the right of sigma_c.
  W5  lo(sigma_3) > 91/50       so the window (1.78, 1.82) sits inside
                                 (1, sigma_3).

Every decided value carries backend and precision. All output intervals are
outward-rounded decimal strings.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import flint
import mpmath

from instrument import (
    Timer,
    arb_endpoints,
    arb_from_fraction,
    h_arb,
    h_iv,
    iv_endpoints,
    iv_from_fraction,
    mobius_sieve,
    outward_decimal,
    u_arb,
    u_iv,
)

arb = flint.arb
fctx = flint.ctx
iv = mpmath.iv

FLINT_PREC_BITS = 350
IV_DPS = 40
K_FLINT = 120
K_IV = 40

HERE = os.path.dirname(os.path.abspath(__file__))


def record(lo: Fraction, hi: Fraction, digits: int, backend: str, precision: str,
           method: str, seconds: float) -> dict:
    dlo, dhi = outward_decimal(lo, hi, digits)
    return {
        "interval": [dlo, dhi],
        "width": f"{float(hi - lo):.3e}",
        "backend": backend,
        "precision": precision,
        "method": method,
        "time_s": round(seconds, 3),
    }


def main() -> None:
    fctx.prec = FLINT_PREC_BITS
    iv.dps = IV_DPS
    mu = mobius_sieve(K_FLINT + 1)

    out: dict = {
        "hunt": "prime_zeta_rightmost",
        "task": "WP3 demonstration inputs for THEOREM.md, both backends",
        "date": "2026-08-16",
        "versions": {
            "python-flint": getattr(flint, "__version__", "unknown"),
            "mpmath": mpmath.__version__,
        },
        "vocabulary": "decided = interval/ball enclosure with exact endpoint sign logic",
    }

    dec: dict = {}

    # D1: h(7/4) > 1/128 on both backends.
    q = Fraction(7, 4)
    thr = Fraction(1, 128)
    with Timer() as t:
        lo, hi = arb_endpoints(h_arb(arb_from_fraction(q), K_FLINT, mu))
    dec["D1_h_at_7_over_4_gt_1_over_128"] = {
        "statement": "h(7/4) = P(7/4) - 2^(-3/4) > 1/128",
        "flint": dict(record(lo, hi, 33, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
                             f"Moebius series K={K_FLINT} with decided tail "
                             "(instrument.py docstring 1); exact rational compare of "
                             "the lower endpoint against 1/128", t.seconds),
                      decided=bool(lo > thr)),
    }
    with Timer() as t:
        lo_i, hi_i = iv_endpoints(h_iv(iv_from_fraction(q), K_IV, mu))
    dec["D1_h_at_7_over_4_gt_1_over_128"]["mpmath_iv"] = dict(
        record(lo_i, hi_i, 14, "mpmath.iv", f"dps {IV_DPS}",
               f"Moebius series K={K_IV}, per-term finite-sum zeta enclosures "
               "(instrument.py docstring 2), same tail bound", t.seconds),
        decided=bool(lo_i > thr))

    # D2: u(9/5) > 1/256 on both backends.
    q = Fraction(9, 5)
    thr = Fraction(1, 256)
    with Timer() as t:
        lo, hi = arb_endpoints(u_arb(arb_from_fraction(q), K_FLINT, mu))
    dec["D2_u_at_9_over_5_gt_1_over_256"] = {
        "statement": "u(9/5) = sum_{p>=5} p^(-9/5) - 3^(-9/5) > 1/256",
        "flint": dict(record(lo, hi, 33, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
                             f"Moebius series K={K_FLINT}; exact rational compare of "
                             "the lower endpoint against 1/256", t.seconds),
                      decided=bool(lo > thr)),
    }
    with Timer() as t:
        lo_i, hi_i = iv_endpoints(u_iv(iv_from_fraction(q), K_IV, mu))
    dec["D2_u_at_9_over_5_gt_1_over_256"]["mpmath_iv"] = dict(
        record(lo_i, hi_i, 14, "mpmath.iv", f"dps {IV_DPS}", "same machinery", t.seconds),
        decided=bool(lo_i > thr))

    # D3: log2(69 / (5 log 23)) > 17/8, the p_9 = 23 tail-wall instance.
    thr = Fraction(17, 8)
    with Timer() as t:
        val = (arb(69) / (5 * arb(23).log())).log() / arb(2).log()
        lo, hi = arb_endpoints(val)
    dec["D3_log2_69_over_5log23_gt_17_over_8"] = {
        "statement": "log2(69/(5*log 23)) > 17/8, so the {p >= 23} wall exceeds 2.125",
        "flint": dict(record(lo, hi, 30, "python-flint (arb)", f"{FLINT_PREC_BITS} bits",
                             "direct ball arithmetic; exact rational compare of the "
                             "lower endpoint against 17/8", t.seconds),
                      decided=bool(lo > thr)),
    }
    with Timer() as t:
        val_i = iv.log(iv.mpf(69) / (5 * iv.log(iv.mpf(23)))) / iv.log(iv.mpf(2))
        lo_i, hi_i = iv_endpoints(val_i)
    dec["D3_log2_69_over_5log23_gt_17_over_8"]["mpmath_iv"] = dict(
        record(lo_i, hi_i, 30, "mpmath.iv", f"dps {IV_DPS}", "direct interval arithmetic",
               t.seconds),
        decided=bool(lo_i > thr))

    # Window comparisons: exact Fraction compares against decided.json endpoints.
    with open(os.path.join(HERE, "decided.json")) as f:
        decided = json.load(f)

    def ep(name: str, leg: str, which: int) -> Fraction:
        return Fraction(decided["constants"][name][leg]["interval"][which])

    windows = {
        "W1_x_star_hi_lt_173_over_100": {
            "statement": "hi(x_star) < 173/100 on both backends, so Re s >= 1.73 implies Re s > x_star",
            "flint": bool(ep("x_star", "flint", 1) < Fraction(173, 100)),
            "mpmath_iv": bool(ep("x_star", "mpmath_iv", 1) < Fraction(173, 100)),
        },
        "W2_sigma_c_lo_gt_7_over_4": {
            "statement": "lo(sigma_c) > 7/4 on both backends, so 7/4 lies in (1, sigma_c)",
            "flint": bool(ep("sigma_c", "flint", 0) > Fraction(7, 4)),
            "mpmath_iv": bool(ep("sigma_c", "mpmath_iv", 0) > Fraction(7, 4)),
        },
        "W3_sigma_c_lo_gt_177_over_100": {
            "statement": "lo(sigma_c) > 177/100 on both backends, so (1.73, 1.77) lies inside (1, sigma_c)",
            "flint": bool(ep("sigma_c", "flint", 0) > Fraction(177, 100)),
            "mpmath_iv": bool(ep("sigma_c", "mpmath_iv", 0) > Fraction(177, 100)),
        },
        "W4_sigma_c_hi_lt_89_over_50": {
            "statement": "hi(sigma_c) < 89/50 on both backends, so Re s >= 1.78 implies Re s > sigma_c",
            "flint": bool(ep("sigma_c", "flint", 1) < Fraction(89, 50)),
            "mpmath_iv": bool(ep("sigma_c", "mpmath_iv", 1) < Fraction(89, 50)),
        },
        "W5_sigma_3_lo_gt_91_over_50": {
            "statement": "lo(sigma_3) > 91/50 on both backends, so (1.78, 1.82) lies inside (1, sigma_3)",
            "flint": bool(ep("sigma_3", "flint", 0) > Fraction(91, 50)),
            "mpmath_iv": bool(ep("sigma_3", "mpmath_iv", 0) > Fraction(91, 50)),
        },
    }
    windows["note"] = (
        "exact Fraction comparisons of the outward-rounded decimal endpoints "
        "recorded in decided.json; outward rounding only widens an interval, so "
        "a comparison that succeeds against the rounded endpoint also holds for "
        "the underlying enclosure"
    )

    out["decisions"] = dec
    out["window_comparisons"] = windows
    out["notes"] = {
        "instrument_defect_found_by_D3": (
            "the first run of D3 produced disjoint enclosures on the two "
            "backends (iv leg collapsed to a 53-bit point value); traced to "
            "iv_endpoints converting through the global mp context (dps 15) "
            "instead of reading the raw _mpi_ endpoints. Sign decisions were "
            "never at risk (nearest rounding at relative precision cannot "
            "cross zero), value enclosures were; fixed in instrument.py, "
            "decide.py re-run afterwards reproduced decided.json identically "
            "except timings. The cross-backend disjointness check did exactly "
            "what MISSION.md kill condition 3 says it is for: it marked the "
            "instrument as the artifact."
        ),
    }

    all_ok = all(
        dec[k][leg]["decided"] for k in dec for leg in ("flint", "mpmath_iv")
    ) and all(
        windows[k][leg] for k in windows if k != "note" for leg in ("flint", "mpmath_iv")
    )
    out["all_decided"] = bool(all_ok)

    path = os.path.join(HERE, "theorem_inputs.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
