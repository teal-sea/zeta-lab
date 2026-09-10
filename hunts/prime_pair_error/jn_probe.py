"""Control instrument for RESULTS.md Section 19, 'What is additional'.

Section 19 ties the whole of Theorem A/(T) to a single unmeasured estimate:

    J(N) = sum_{m <= N} Lambda(m) chi(m) (psi(m) - m) = O(N^{1+eps})

with Lambda the von Mangoldt function, chi the non-principal Dirichlet
character mod 3, and psi Chebyshev's function. Nothing elsewhere in this
hunt computes J(N); this script does, exactly, at a ladder of cutoffs.

Definitions used here:

    Lambda(m)   von Mangoldt function, from an exact integer sieve (a sieve
                of Eratosthenes plus explicit prime-power enumeration, so
                which m are prime powers is never a floating-point question)
    chi(m)      the non-principal character mod 3: 0 if 3 | m, +1 if
                m = 1 (mod 3), -1 if m = 2 (mod 3)
    psi(m)      Chebyshev's psi(m), read from zeta.explicit.psi_staircase
                (the repo's own vectorised psi) rather than re-derived here,
                and cross-checked at every ladder cutoff against the repo's
                scalar reference zeta.explicit.psi_true
    J(N)        sum_{m <= N} Lambda(m) chi(m) (psi(m) - m), accumulated with
                mpmath (mp.dps = 50) via mp.fsum over the raw float64 terms,
                so the accumulation itself does not add rounding drift on
                top of whatever float64 already carries in each term

This measures J(N) at seven cutoffs up to 8,000,000; it does not bound it.
A finite ladder is a measurement, not an asymptotic statement, and the
growth exponent below is an observed log-log slope over seven points, not
a proved rate. See "what_this_measures" in the written JSON for the full
statement of what that is and is not good for.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/jn_probe.py
Writes hunts/prime_pair_error/results_jn.json
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from mpmath import mp

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from zeta.explicit import psi_staircase, psi_true  # repo's own psi, not re-derived

# Geometric-ish ladder, 1e5 to 8e6 in seven steps. Chosen so the sieve, the
# vectorised psi_staircase over the whole grid, and the mpmath summation
# together run in well under 60 seconds (measured at ~20s on this machine).
LADDER = [100_000, 250_000, 500_000, 1_000_000, 2_000_000, 4_000_000, 8_000_000]


def von_mangoldt_sieve(n_max: int) -> np.ndarray:
    """Lambda(m) for 0 <= m <= n_max.

    Exact: a sieve of Eratosthenes gives the primes as integers, and every
    prime power p^k <= n_max is then written explicitly. Both steps are
    integer arithmetic, so there is no floating-point ambiguity about which
    m carry a nonzero Lambda; only the value log(p) assigned to them is a
    float."""
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(n_max ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    primes = np.nonzero(sieve)[0]
    lam = np.zeros(n_max + 1, dtype=np.float64)
    lam[primes] = np.log(primes.astype(np.float64))
    small_primes = primes[primes.astype(np.int64) ** 2 <= n_max]
    for p in small_primes:
        p = int(p)
        lp = math.log(p)
        pk = p * p
        while pk <= n_max:
            lam[pk] = lp
            pk *= p
    return lam


def chi_mod3(n_max: int) -> np.ndarray:
    """The non-principal Dirichlet character mod 3, on 0 <= m <= n_max."""
    m = np.arange(n_max + 1)
    chi = np.zeros(n_max + 1, dtype=np.float64)
    chi[m % 3 == 1] = 1.0
    chi[m % 3 == 2] = -1.0
    return chi


def main() -> int:
    mp.dps = 50
    t0 = time.time()
    n_max = LADDER[-1]

    lam = von_mangoldt_sieve(n_max)
    chi = chi_mod3(n_max)
    grid = np.arange(0, n_max + 1, dtype=np.float64)
    psi_vals = psi_staircase(grid)  # zeta.explicit's own psi, used as-is

    # Cross-check the vectorised psi against the repo's scalar reference at
    # every ladder cutoff, exactly, before trusting it in the sum below.
    psi_checks = []
    for N in LADDER:
        exact = psi_true(N)
        vec = float(psi_vals[N])
        psi_checks.append(
            {"N": N, "psi_true": exact, "psi_staircase": vec, "absdiff": abs(exact - vec)}
        )
    max_psi_diff = max(c["absdiff"] for c in psi_checks)

    terms = lam * chi * (psi_vals - grid)

    rows = []
    running = mp.mpf(0)
    prev_cut = 0
    for N in LADDER:
        seg = terms[prev_cut + 1 : N + 1].tolist()  # m in (prev_cut, N]
        running = running + mp.fsum(seg)
        prev_cut = N
        rows.append(
            {
                "N": N,
                "J_N": float(running),
                "J_N_over_N": float(running / N),
            }
        )

    Ns = np.array([r["N"] for r in rows], dtype=np.float64)
    absJ = np.maximum(np.array([abs(r["J_N"]) for r in rows], dtype=np.float64), 1e-12)
    slope, intercept = np.polyfit(np.log(Ns), np.log(absJ), 1)

    elapsed = time.time() - t0

    out = {
        "definitions": {
            "Lambda": (
                "von Mangoldt function, from an exact integer sieve of "
                "Eratosthenes plus explicit prime-power enumeration"
            ),
            "chi": (
                "the non-principal Dirichlet character mod 3: 0 at multiples "
                "of 3, +1 at m = 1 (mod 3), -1 at m = 2 (mod 3)"
            ),
            "psi": (
                "Chebyshev's psi(m), read from zeta.explicit.psi_staircase "
                "(the repo's own vectorised psi) rather than re-derived here, "
                "and cross-checked against zeta.explicit.psi_true at every "
                "ladder cutoff"
            ),
            "J_N": (
                "sum_{m <= N} Lambda(m) chi(m) (psi(m) - m), accumulated with "
                "mpmath (mp.dps = 50) via mp.fsum over the raw float64 terms "
                "so the accumulation step adds no rounding drift of its own"
            ),
        },
        "ladder": LADDER,
        "ladder_note": (
            "geometric-ish ladder from 1e5 to 8e6 in seven steps, chosen so "
            "the sieve, the vectorised psi_staircase call over the full grid, "
            "and the mpmath summation together run in well under 60 seconds"
        ),
        "psi_cross_check_vs_psi_true": psi_checks,
        "max_abs_diff_psi_staircase_vs_psi_true": max_psi_diff,
        "rows": rows,
        "growth_exponent_loglog_leastsquares": float(slope),
        "growth_exponent_loglog_intercept": float(intercept),
        "what_this_measures": (
            "This is a measurement of J(N) at a finite ladder of seven "
            "cutoffs, not an asymptotic statement. A finite ladder bounds "
            "nothing outside the range it covers: it cannot rule out that "
            "the growth changes shape past N = 8,000,000, and it cannot by "
            "itself tell an O(N^{1+eps}) rate apart from a power that only "
            "looks flatter over this particular range. The least-squares "
            "exponent above is an observed slope of log|J(N)| against "
            "log(N) over these seven points, not a proved rate, and it "
            "carries no error bar beyond what a seven-point fit can give. "
            "Nothing here bears on RH."
        ),
        "seconds_total": elapsed,
    }
    out_path = HERE / "results_jn.json"
    out_path.write_text(json.dumps(out, indent=1))

    print(f"psi_staircase vs psi_true, max abs diff over ladder: {max_psi_diff:.2e}")
    for r in rows:
        print(f"N={r['N']:>9}  J(N)={r['J_N']:>16.4f}  J(N)/N={r['J_N_over_N']:.6f}")
    print(f"observed growth exponent (log-log least squares): {slope:.4f}")
    print(f"wrote {out_path} ({elapsed:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
