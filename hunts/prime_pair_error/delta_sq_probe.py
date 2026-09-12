"""Control instrument for RESULTS.md 'The doors', rank 1 constraint.

The doors section ranks the mixed moment at q = 1 (UPPER_BOUND.md (23), the
term 32 U_1) as the constraint that binds hardest, and names exactly what
would close it: UPPER_BOUND.md (31),

    sum_{t <= N} Delta(t)^2 << _eps N^{2+eps},   Delta(t) = psi(t) - t.

Nothing elsewhere in this hunt measures that sum. This script does, exactly,
at a ladder of cutoffs, the same way jn_probe.py measures J(N) for Section 19.

Definitions used here:

    psi(t)      Chebyshev's psi(t), read from zeta.explicit.psi_staircase
                (the repo's own vectorised psi) rather than re-derived here,
                and cross-checked at every ladder cutoff against the repo's
                scalar reference zeta.explicit.psi_true
    Delta(t)    psi(t) - t, UPPER_BOUND.md Section 7's notation exactly
    S(N)        sum_{t=1}^N Delta(t)^2, accumulated with mpmath (mp.dps = 50)
                via mp.fsum over the raw float64 terms, so the accumulation
                itself does not add rounding drift on top of whatever
                float64 already carries in each term

This measures S(N) at a ladder of cutoffs up to 10,000,000; it does not bound
it. A finite ladder is a measurement, not an asymptotic statement, and the
growth exponent below is an observed log-log slope over these points, not a
proved rate. See "what_this_measures" in the written JSON for the full
statement of what that is and is not good for.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/delta_sq_probe.py
Writes hunts/prime_pair_error/results_delta_sq.json
"""
from __future__ import annotations

import json
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

# Geometric-ish ladder, 1e5 to 1e7 in eight steps. Chosen so the sieve inside
# psi_staircase, the vectorised call over the whole grid, and the mpmath
# summation together run in well under 60 seconds (measured below).
LADDER = [
    100_000,
    250_000,
    500_000,
    1_000_000,
    2_000_000,
    4_000_000,
    7_000_000,
    10_000_000,
]


def main() -> int:
    mp.dps = 50
    t0 = time.time()
    n_max = LADDER[-1]

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

    delta = psi_vals - grid  # Delta(t) = psi(t) - t, for t = 0 .. n_max
    delta_sq_terms = delta * delta

    rows = []
    running = mp.mpf(0)
    prev_cut = 0
    for N in LADDER:
        seg = delta_sq_terms[prev_cut + 1 : N + 1].tolist()  # t in (prev_cut, N]
        running = running + mp.fsum(seg)
        prev_cut = N
        rows.append(
            {
                "N": N,
                "S_N": float(running),
                "S_N_over_N2": float(running / (mp.mpf(N) ** 2)),
            }
        )

    Ns = np.array([r["N"] for r in rows], dtype=np.float64)
    S_vals = np.array([r["S_N"] for r in rows], dtype=np.float64)
    slope, intercept = np.polyfit(np.log(Ns), np.log(S_vals), 1)

    elapsed = time.time() - t0

    target_note = (
        "The observed log-log exponent above is {:.4f}. UPPER_BOUND.md (31) "
        "needs S(N) << _eps N^{{2+eps}} for every eps > 0, i.e. an exponent "
        "approaching 2 from above in that asymptotic sense, not measured "
        "here. A finite ladder does not settle whether the true rate sits "
        "at, above, or below 2: it only reports where the fitted slope over "
        "this particular range of N happens to land, which is not the same "
        "quantity as the eps-indexed asymptotic rate (31) requires."
    ).format(slope)

    out = {
        "definitions": {
            "psi": (
                "Chebyshev's psi(t), read from zeta.explicit.psi_staircase "
                "(the repo's own vectorised psi) rather than re-derived here, "
                "and cross-checked against zeta.explicit.psi_true at every "
                "ladder cutoff"
            ),
            "Delta": "Delta(t) = psi(t) - t, UPPER_BOUND.md Section 7's notation exactly",
            "S_N": (
                "sum_{t=1}^N Delta(t)^2, accumulated with mpmath (mp.dps = 50) "
                "via mp.fsum over the raw float64 terms so the accumulation "
                "step adds no rounding drift of its own"
            ),
        },
        "ladder": LADDER,
        "ladder_note": (
            "geometric-ish ladder from 1e5 to 1e7 in eight steps, chosen so "
            "the sieve inside psi_staircase, the vectorised call over the "
            "full grid, and the mpmath summation together run in well under "
            "60 seconds"
        ),
        "psi_cross_check_vs_psi_true": psi_checks,
        "max_abs_diff_psi_staircase_vs_psi_true": max_psi_diff,
        "rows": rows,
        "growth_exponent_loglog_leastsquares": float(slope),
        "growth_exponent_loglog_intercept": float(intercept),
        "exponent_vs_target_note": target_note,
        "what_this_measures": (
            "This is a measurement of S(N) = sum_{t<=N} Delta(t)^2 at a "
            "finite ladder of eight cutoffs, not an asymptotic statement. A "
            "finite ladder bounds nothing outside the range it covers: it "
            "cannot rule out that the growth changes shape past "
            "N = 10,000,000, and it cannot by itself tell an "
            "O_eps(N^{2+eps}) rate apart from a power that only looks "
            "flatter, or steeper, over this particular range. The "
            "least-squares exponent above is an observed slope of "
            "log(S(N)) against log(N) over these eight points, not a "
            "proved rate, and it carries no error bar beyond what an "
            "eight-point fit can give. Nothing here bears on RH."
        ),
        "seconds_total": elapsed,
    }
    out_path = HERE / "results_delta_sq.json"
    out_path.write_text(json.dumps(out, indent=1))

    print(f"psi_staircase vs psi_true, max abs diff over ladder: {max_psi_diff:.2e}")
    for r in rows:
        print(f"N={r['N']:>9}  S(N)={r['S_N']:>18.4f}  S(N)/N^2={r['S_N_over_N2']:.6f}")
    print(f"observed growth exponent (log-log least squares): {slope:.4f}")
    print(f"wrote {out_path} ({elapsed:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
