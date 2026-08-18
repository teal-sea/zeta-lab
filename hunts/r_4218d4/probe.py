#!/usr/bin/env python3
"""Hunt R-4218D4 — the arithmetic of the Mertens constant propagation.

This script is not a proof of anything. Every inequality it evaluates is
also carried, symbolically and with zero sorrys, by the three Lean files
this hunt edited:

    lean/ZetaLean/Mertensstheorems.lean       (Mertens I, both forms)
    lean/ZetaLean/MertensSecond.lean          (Mertens II)
    lean/ZetaLean/HardyRamanujantheorem.lean  (Turan's variance bound)

What the script is for is the bookkeeping: which slack step feeds which
constant, what each step gives before and after, and how far each landed
constant sits from the value the same argument would give with no
rounding at all. Run it to reproduce every number in RESULTS.md.

    python3 hunts/r_4218d4/probe.py            # table to stdout
    python3 hunts/r_4218d4/probe.py --json     # results.json to stdout

No dependencies beyond the standard library: the whole computation is
elementary arithmetic on floats, and nothing here needs mpmath.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict

E = math.e
LOG2 = math.log(2.0)
LOG4 = math.log(4.0)


# --------------------------------------------------------------------------
# Step 1. The Chebyshev remainder: psi x <= x log 4 + 2 sqrt(x) log x.
# --------------------------------------------------------------------------
#
# Mathlib proves `Chebyshev.psi_le` in exactly that shape and then packages
# `psi_le_const_mul_self : psi x <= (log 4 + 4) x` by bounding the remainder
# 2 sqrt(x) log x by 4x, i.e. by using log x / sqrt x <= 2.
#
# The true supremum of log x / sqrt x is 2/e, attained at x = e^2. Writing
# log x = 2 log sqrt x and applying log t <= t/e to t = sqrt x gives
# 2 sqrt(x) log x <= (4/e) x, so the packaged 4 can be replaced by 4/e.

def chebyshev_remainder_constant() -> tuple[float, float, float]:
    """(Mathlib's packaged constant, the sharp one, the value we state)."""
    return 4.0, 4.0 / E, 1.5


# --------------------------------------------------------------------------
# Step 2. B(N) = sum_{n <= N} (log n) / n^2.
# --------------------------------------------------------------------------
#
# Old route: log n <= 2 sqrt n, then sum_{n <= N} n^{-3/2} <= 3 - 2/sqrt N
# <= 3, giving B <= 6.
#
# New route: two independent tightenings of the same telescope.
#   (a) log n <= (2/e) sqrt n instead of log n <= 2 sqrt n.
#   (b) the n = 1 term of B vanishes, so the telescope may start at n = 2,
#       where sum_{2 <= n <= N} n^{-3/2} <= 2 - 2/sqrt N <= 2 rather than 3.
# Together (2/e) * 2 = 4/e.
#
# The limit of B is -zeta'(2) = 0.93754825431584375...

MINUS_ZETA_PRIME_2 = 0.9375482543158437

def sum_log_over_sq_bounds() -> dict[str, float]:
    return {
        "old_majorant_constant": 2.0,            # log n <= 2 sqrt n
        "new_majorant_constant": 2.0 / E,        # log n <= (2/e) sqrt n
        "old_telescope_from_1": 3.0,             # sum_{n<=N} n^{-3/2} <= 3
        "new_telescope_from_2": 2.0,             # sum_{2<=n<=N} n^{-3/2} <= 2
        "old_bound": 2.0 * 3.0,                  # = 6
        "new_bound_sharp": (2.0 / E) * 2.0,      # = 4/e
        "new_bound_stated": 1.5,                 # what Lean carries
        "limit": MINUS_ZETA_PRIME_2,
    }


def sum_log_over_sq_direct(n_max: int) -> float:
    """Direct evaluation, as a sanity check on the majorant chain."""
    return sum(math.log(n) / (n * n) for n in range(1, n_max + 1))


def telescope_direct(n_max: int, start: int) -> float:
    return sum(1.0 / (n * math.sqrt(n)) for n in range(start, n_max + 1))


# --------------------------------------------------------------------------
# Step 3. The prime-power correction in Mertens I.
# --------------------------------------------------------------------------
#
# The tail is sum_{k >= 2} sum_{p <= N^{1/k}} (log p) / p^k. The layer bound
# is (log p)/p^k <= ((log p)/p^2) * 2^{-(k-2)}, so the tail is at most
# B * sum_{k >= 2} 2^{-(k-2)} = 2 B.
#
# Its limit is sum over prime powers p^k, k >= 2, of (log p)/p^k, which is
# 0.7553666108..., the constant usually written as -sum_p log p/(p(p-1))
# plus the prime sum; we just evaluate it.

def prime_power_tail_limit(p_max: int = 200000) -> float:
    """sum_{p} sum_{k>=2} (log p)/p^k = sum_p (log p) / (p (p-1))."""
    sieve = bytearray([1]) * (p_max + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(p_max**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return sum(math.log(p) / (p * (p - 1)) for p in range(2, p_max + 1) if sieve[p])


def tail_bounds(b_old: float, b_new: float) -> dict[str, float]:
    return {
        "layer_geometric_factor": 2.0,
        "old_bound": 2.0 * b_old,        # 2 * 6 = 12
        "new_bound_sharp": 2.0 * b_new,  # 2 * (4/e) = 2.943
        "new_bound_stated": 3.0,
    }


# --------------------------------------------------------------------------
# Step 4. Mertens I, both forms.
# --------------------------------------------------------------------------
#
# von Mangoldt form: |sum_{n<=N} Lambda(n)/n - log N| <= max(1, c_psi),
# where the lower loss is 1 (from N log N - N + 1 <= sum log n <= N log N)
# and the upper loss is the Chebyshev constant c_psi.
#
# Prime form: the two sides take different routes.
#   upper  prime sum <= vonMangoldt sum       -> loss c_psi
#   lower  prime sum >= vonMangoldt sum - tail -> loss 1 + tail
# so the band is max(c_psi, 1 + tail). Passing through the *symmetric* von
# Mangoldt band instead would cost c_psi + tail, which is what the original
# proof did; splitting the halves is worth about 1.5 here.

@dataclass(frozen=True)
class MertensOne:
    vm_upper: float          # c_psi = log 4 + remainder constant
    vm_lower: float          # 1
    tail: float
    band_symmetric: float    # what a symmetric vM band would force
    band_split: float        # what the one-sided lower half gives
    stated: float            # what Lean carries


def mertens_one(remainder_const: float, tail: float, stated: float) -> MertensOne:
    c_psi = LOG4 + remainder_const
    return MertensOne(
        vm_upper=c_psi,
        vm_lower=1.0,
        tail=tail,
        band_symmetric=max(c_psi, 1.0) + tail,
        band_split=max(c_psi, 1.0 + tail),
        stated=stated,
    )


# --------------------------------------------------------------------------
# Step 5. Mertens II from Mertens I.
# --------------------------------------------------------------------------
#
# The Abel-summation assembly gives, with c the Mertens I band as actually
# rounded in Lean and r an upper bound on 1/log 2:
#
#   upper <=  c*r + 1 + |log log 2| + c*r
#   lower >= -c*r + 1 - g            - c*r        (g = the sum_{n} 1/n^2 gap)
#
# so the band is max(2 c r + 1 + |log log 2|, 2 c r + g - 1). With g = 4 the
# lower side dominates. The old proof used r < 2; the true 1/log 2 is
# 1.442695..., and r = 1.443 is as cheap to prove.

LOGLOG2 = math.log(math.log(2.0))   # = -0.3665129205816643

@dataclass(frozen=True)
class MertensTwo:
    band_c: float
    r: float
    gap: float
    upper: float
    lower: float
    required: float
    stated: float


def mertens_two(band_c: float, r: float, gap: float, stated: float) -> MertensTwo:
    cr = band_c * r
    upper = cr + 1.0 + abs(LOGLOG2) + cr
    lower = cr + gap - 1.0 + cr
    return MertensTwo(
        band_c=band_c, r=r, gap=gap,
        upper=upper, lower=lower,
        required=max(upper, lower), stated=stated,
    )


# --------------------------------------------------------------------------
# Step 6. Turan's variance constant.
# --------------------------------------------------------------------------
#
# Variance <= N (S-L)^2 + N S + 2 L N <= N m^2 + N (L + m) + 2 N L
#          <= (m^2 + m) N + 3 N L <= (m^2 + m + 3) N L   when L >= 1.

def variance_constant(m: float) -> float:
    return m * m + m + 3.0


# --------------------------------------------------------------------------

def build_results() -> dict:
    packaged, sharp_rem, stated_rem = chebyshev_remainder_constant()
    b = sum_log_over_sq_bounds()
    tails_old = tail_bounds(b["old_bound"], b["new_bound_sharp"])

    m1_old = mertens_one(remainder_const=packaged, tail=12.0, stated=LOG4 + 16.0)
    m1_new = mertens_one(remainder_const=stated_rem, tail=3.0, stated=LOG4 + 3.0)

    m2_old = mertens_two(band_c=17.4, r=2.0, gap=4.0, stated=76.0)
    m2_new = mertens_two(band_c=4.4, r=1.443, gap=4.0, stated=16.0)

    hr_old = variance_constant(76.0)
    hr_new = variance_constant(16.0)

    return {
        "hunt": "r_4218d4",
        "question": "Tighten the variance constant 5855",
        "chebyshev_remainder": {
            "mathlib_packaged": packaged,
            "sharp_4_over_e": sharp_rem,
            "stated_in_lean": stated_rem,
            "note": "2 sqrt(x) log x <= (4/e) x, since sup log t / sqrt t = 2/e",
        },
        "sum_log_over_sq": b,
        "sum_log_over_sq_direct_N": {
            "N": 200000,
            "value": sum_log_over_sq_direct(200000),
            "limit_minus_zeta_prime_2": MINUS_ZETA_PRIME_2,
        },
        "telescope_direct_N": {
            "N": 200000,
            "from_1": telescope_direct(200000, 1),
            "from_2": telescope_direct(200000, 2),
            "bound_from_1": 3.0,
            "bound_from_2": 2.0,
        },
        "prime_power_tail": {
            **tails_old,
            "limit": prime_power_tail_limit(),
        },
        "mertens_first": {"before": asdict(m1_old), "after": asdict(m1_new)},
        "mertens_second": {"before": asdict(m2_old), "after": asdict(m2_new)},
        "variance_constant": {
            "before": {"mertens_band": 76.0, "value": hr_old, "stated": 5855.0},
            "after": {"mertens_band": 16.0, "value": hr_new, "stated": 275.0},
            "decomposition": "m^2 + m + 3",
        },
        "headline": {
            "mertens_first_before": LOG4 + 16.0,
            "mertens_first_after": LOG4 + 3.0,
            "mertens_second_before": 76.0,
            "mertens_second_after": 16.0,
            "variance_before": 5855.0,
            "variance_after": 275.0,
            "variance_factor": 5855.0 / 275.0,
        },
    }


def render_table(r: dict) -> str:
    h = r["headline"]
    rows = [
        ("Chebyshev remainder constant (psi <= x log4 + c x)",
         "4", f"{r['chebyshev_remainder']['stated_in_lean']:g}",
         f"sharp {r['chebyshev_remainder']['sharp_4_over_e']:.4f} = 4/e"),
        ("sum_{n<=N} (log n)/n^2",
         "6", f"{r['sum_log_over_sq']['new_bound_stated']:g}",
         f"sharp {r['sum_log_over_sq']['new_bound_sharp']:.4f}, "
         f"limit {r['sum_log_over_sq']['limit']:.4f}"),
        ("prime-power tail in Mertens I",
         "12", f"{r['prime_power_tail']['new_bound_stated']:g}",
         f"sharp {r['prime_power_tail']['new_bound_sharp']:.4f}, "
         f"limit {r['prime_power_tail']['limit']:.4f}"),
        ("Mertens I band (prime form)",
         f"log4+16 = {h['mertens_first_before']:.4f}",
         f"log4+3 = {h['mertens_first_after']:.4f}",
         "classical 2"),
        ("Mertens II band",
         f"{h['mertens_second_before']:g}", f"{h['mertens_second_after']:g}",
         f"needs {r['mertens_second']['after']['required']:.3f}; classical 4"),
        ("Turan variance constant",
         f"{h['variance_before']:g}", f"{h['variance_after']:g}",
         "m^2 + m + 3"),
    ]
    w = [max(len(str(row[i])) for row in rows) for i in range(4)]
    hdr = ("quantity", "before", "after", "reference")
    w = [max(w[i], len(hdr[i])) for i in range(4)]
    out = ["| " + " | ".join(hdr[i].ljust(w[i]) for i in range(4)) + " |",
           "|" + "|".join("-" * (w[i] + 2) for i in range(4)) + "|"]
    for row in rows:
        out.append("| " + " | ".join(str(row[i]).ljust(w[i]) for i in range(4)) + " |")
    out.append("")
    out.append(f"variance constant improved by a factor of {h['variance_factor']:.2f}")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="emit results.json to stdout")
    args = ap.parse_args()
    r = build_results()
    if args.json:
        print(json.dumps(r, indent=2))
    else:
        print(render_table(r))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
