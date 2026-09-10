"""Section 8: the Davenport-Heilbronn battery for POSITIVITY_ENERGY.md.

POSITIVITY_ENERGY.md's mean/central-mode scale consumes exactly one
arithmetic fact: Lambda(n) >= 0, i.e. the coefficients of log(zeta) are
non-negative -- the Euler-product input to the classical zero-free region.
This script runs the identical claim against the Davenport-Heilbronn
function (real coefficients, a genuine Riemann-type functional equation,
a zero off the critical line), reusing zeta/epstein.py and
zeta/factorization.py by path, never reimplementing the Dirichlet-coefficient
data or the log-derivative recursion itself.

Two things are done:

1. Reverify, independently of the docstring numbers already recorded in
   zeta/epstein.py, that claim_multiplicativity and
   claim_euler_product_positivity both fail for the Davenport-Heilbronn
   interface (zeta.epstein.battery, unmodified).

2. Compute Lambda_F(n), the DH log-derivative coefficients, out to a much
   larger n_max than zeta/epstein.py's or zeta/factorization.py's O(n^2)
   Python loops reach in the repository's 60-second diagnostic convention,
   using an independently written O(n_max log n_max) divisor-sieve
   recursion of the *same* defining identity (see log_derivative_fast
   below); cross-check it against zeta.epstein.log_derivative_coefficients
   (mpmath) at n_max = 200, where the docstring's own reference value
   Lambda_F(3) = -6.78 lives. Then track the running maximum of
   |sum_{n<=t} Lambda_F(n)| out to the larger n_max and fit its growth
   exponent by log-log regression, to compare against:
     - the decay POSITIVITY_ENERGY.md's mean-mode bound would predict if
       (invalidly) ported to DH: subpolynomial, in fact exponentially
       small relative to any fixed power of t;
     - the growth the pinned off-line zero rho = 0.808517... + 85.699...i
       predicts on the standard Landau/Perron explicit-formula grounds
       (see POSITIVITY_ENERGY.md Section 5): Omega(t^Re(rho)) up to o(1)
       in the exponent.

This is supporting numerical evidence for a fixed exponent range, not a
proof of the asymptotic Omega statement (that is a citation to standard
theory in POSITIVITY_ENERGY.md, not re-derived here).

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/s8_positivity_battery.py
Writes hunts/prime_pair_error/results_s8_positivity_battery.json
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
sys.path.insert(0, str(REPO_ROOT))

from zeta.epstein import (  # noqa: E402
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    battery,
    claim_euler_product_positivity,
    claim_multiplicativity,
    dh_coefficient,
    dh_interface,
    kappa,
    log_derivative_coefficients as epstein_log_derivative_coefficients,
)

OFFLINE_ZERO_RE_FLOAT = float(OFFLINE_ZERO_RE)
OFFLINE_ZERO_IM_FLOAT = float(OFFLINE_ZERO_IM)


def log_derivative_fast(a: np.ndarray, n_max: int) -> np.ndarray:
    """Lambda_F(n) for n <= n_max, from a's own defining recursion

        a_n log(n) = sum_{d | n} Lambda_F(d) a_{n/d},    a_1 = 1,

    solved by an O(n_max log n_max) divisor sieve rather than the O(n_max^2)
    Python loop in zeta.factorization.log_derivative_coefficients or
    zeta.epstein.log_derivative_coefficients. Independently written so the
    n_max = 200 cross-check below is a real check, not a call to the same
    code twice.
    """
    n_max = int(n_max)
    if a[1] == 0:
        raise ValueError("a_1 must be nonzero")
    divisors: list[list[int]] = [[] for _ in range(n_max + 1)]
    for d in range(1, n_max + 1):
        for k in range(d, n_max + 1, d):
            divisors[k].append(d)
    b = np.zeros(n_max + 1)
    log_n = np.log(np.arange(n_max + 1))
    a1 = a[1]
    for n in range(1, n_max + 1):
        s = a[n] * log_n[n]
        for d in divisors[n]:
            if d == n:
                continue
            s -= b[d] * a[n // d]
        b[n] = s / a1
    return b


def dh_period(dps: int = 30) -> list[float]:
    """a_1..a_5 for the DH sequence, kappa re-derived (never hardcoded) via
    zeta.epstein.kappa, matching dh_coefficient's own convention."""
    k = float(kappa(dps))
    return [1.0, k, -k, -1.0, 0.0]


def periodic_extend(period: list[float], n_max: int) -> np.ndarray:
    q = len(period)
    a = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        a[n] = period[(n - 1) % q]
    return a


def fit_growth_exponent(t: np.ndarray, running_max: np.ndarray, frac: float = 0.5):
    """log-log linear fit of running_max against t over the top `frac` of the
    range (the part least contaminated by small-t transients)."""
    n = len(t)
    lo = int(n * (1 - frac))
    lt = np.log(t[lo:])
    lm = np.log(np.maximum(running_max[lo:], 1e-300))
    slope, intercept = np.polyfit(lt, lm, 1)
    return float(slope), float(intercept)


def main() -> int:
    t0 = time.time()
    out: dict = {}

    # --- Part 1: reverify the two claims the mean-mode construction needs ---
    mult = battery(claim_multiplicativity)
    epp = battery(claim_euler_product_positivity)
    out["claim_multiplicativity"] = mult
    out["claim_euler_product_positivity"] = epp
    assert mult["riemann_zeta"] is True
    assert mult["davenport_heilbronn"] is False
    assert epp["riemann_zeta"] is True
    assert epp["davenport_heilbronn"] is False

    iface = dh_interface(dps=30)
    lam_ref = epstein_log_derivative_coefficients(iface["coefficient"], 200, dps=25)
    lam3_ref = float(lam_ref[3])
    out["lambda_F_3_reference_epstein_module"] = lam3_ref

    # --- Part 2: build the fast divisor-sieve version, cross-check it ---
    period = dh_period(dps=30)
    out["dh_period_a1_a5"] = period

    a_small = periodic_extend(period, 200)
    lam_fast_small = log_derivative_fast(a_small, 200)
    diffs = [
        abs(float(lam_fast_small[n]) - float(lam_ref[n])) for n in range(2, 201)
    ]
    out["cross_check_n_max_200"] = {
        "max_abs_diff_vs_epstein_module": max(diffs),
        "lambda_F_3_fast": float(lam_fast_small[3]),
    }

    # --- Part 3: run the fast version out to a much larger n_max ---
    N_MAX = 200_000
    a_big = periodic_extend(period, N_MAX)
    lam_big = log_derivative_fast(a_big, N_MAX)
    partial = np.cumsum(lam_big)
    abs_partial = np.abs(partial[1:])
    t = np.arange(1, N_MAX + 1, dtype=float)
    running_max = np.maximum.accumulate(abs_partial)

    checkpoints = [200, 1000, 5000, 20000, 50000, 100000, 200000]
    table = []
    for cp in checkpoints:
        idx = cp - 1
        table.append(
            {
                "t": cp,
                "running_max_abs_partial_sum": float(running_max[idx]),
                "t_pow_offline_re": cp ** OFFLINE_ZERO_RE_FLOAT,
                "t_exp_neg_c_sqrt_log_t": cp * math.exp(-1.0 * math.sqrt(math.log(cp))),
            }
        )
    out["partial_sum_growth_checkpoints"] = table

    slope, intercept = fit_growth_exponent(t, running_max, frac=0.5)
    out["fitted_growth_exponent_top_half"] = slope
    slope_q, intercept_q = fit_growth_exponent(t, running_max, frac=0.25)
    out["fitted_growth_exponent_top_quarter"] = slope_q

    # A robust (non-asymptotic-sensitive) check, distinct from the partial-sum
    # growth fit above: Lambda(n) <= log(n) always, for the primes. Is
    # Lambda_F(n) also O(log n)? Track max|Lambda_F| in successive windows
    # against log(n) at the window's right edge.
    lam_abs = np.abs(lam_big[1:])  # index 0 <-> n=1
    n_idx = np.arange(1, N_MAX + 1)
    windows = [(2, 2000), (2000, 20000), (20000, 200000)]
    magnitude_table = []
    for lo, hi in windows:
        mask = (n_idx >= lo) & (n_idx < hi)
        m = float(lam_abs[mask].max())
        magnitude_table.append(
            {
                "window": [lo, hi],
                "max_abs_lambda_F": m,
                "log_hi": math.log(hi),
                "ratio_to_log_hi": m / math.log(hi),
            }
        )
    out["lambda_F_magnitude_vs_log_n"] = magnitude_table

    out["offline_zero_re"] = OFFLINE_ZERO_RE_FLOAT
    out["offline_zero_im"] = OFFLINE_ZERO_IM_FLOAT
    out["n_max"] = N_MAX
    out["elapsed_seconds"] = time.time() - t0

    dest = HERE / "results_s8_positivity_battery.json"
    dest.write_text(json.dumps(out, indent=2))
    print(json.dumps({k: v for k, v in out.items() if k != "partial_sum_growth_checkpoints"}, indent=2))
    print("checkpoints:")
    for row in table:
        print(row)
    return 0


if __name__ == "__main__":
    sys.exit(main())
