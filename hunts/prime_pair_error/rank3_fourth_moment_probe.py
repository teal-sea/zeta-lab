"""Measures the full-circle analogue of UPPER_BOUND.md's fourth residual
moment Z_(q),

    Z*_(q) = sum_{a mod q}^* integral_T |R_{q,a}(beta)|^4 dbeta,
    R_{q,a}(beta) = F_N(a/q+beta) - P_{q,a}(beta),
    P_{q,a}(beta) = (mu(q)/phi(q)) K_N(beta),

directly from the true von Mangoldt function, exactly (not sampled), by
Discrete Fourier Transform. R_{q,a} is a trigonometric polynomial with
one-sided frequency support n=1..N (its Fourier coefficient at n is
Lambda(n)*e(n*a/q) - mu(q)/phi(q)), so |R_{q,a}|^4 has frequency support
confined to [-(2N-2), 2N-2]; sampling it at M >= 4N equally spaced points
and averaging |R_{q,a}|^4 there computes integral_T |R_{q,a}|^4 dbeta
exactly (up to floating-point error), via the standard band-limited
quadrature identity behind the DFT. This is the same full-circle-analogue
object RANK3_ROUTE_D.md Section 7 works with throughout (it never reaches
the literal arc-restricted Z_(q) either, for the same structural reason:
no arc-transfer argument is available for the fourth moment).

This script is a numerical companion to RANK3_QUARTIC_TOOLS.md, which asks
whether any unconditional, q-averaged tool could bound
sum_{2<=q<=R_0} Z_(q). It measures two things Vaughan's bound (V) and the
trivial bound already price analytically (RANK3_SCOPE.md Section 2):
whether Z*_(q) shows any q-dependent saving at small q that neither (V)
nor (LS) capture, and how it grows with N at fixed small q. It also
verifies directly, by measurement, the structural claim (provable from the
definitions alone, and checked here rather than just asserted) that
Z_(q) does NOT vanish on non-squarefree q -- unlike U_(q), which
RANK3_ROUTE_D.md Section 4 shows is identically zero there -- because
mu(q)=0 forces P_{q,a} = 0 identically, so R_{q,a} = F_N with no bias
subtracted at all.

Lambda(n) is computed by direct enumeration of prime powers <= N (exact,
no sampling). mu(q), phi(q) via sympy.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_fourth_moment_probe.py
Writes hunts/prime_pair_error/results_rank3_fourth_moment_probe.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from sympy import mobius, primerange, totient

HERE = Path(__file__).resolve().parent


def von_mangoldt(n_max: int) -> np.ndarray:
    """Lambda(1..n_max), 1-indexed (index 0 unused)."""
    lam = np.zeros(n_max + 1, dtype=np.float64)
    for p in primerange(2, n_max + 1):
        logp = math.log(p)
        pk = p
        while pk <= n_max:
            lam[pk] = logp
            pk *= p
    return lam


def fft_size(n_val: int) -> int:
    """Smallest power of two >= 4*n_val (safe margin for exact quartic quadrature)."""
    target = 4 * n_val + 8
    m = 1
    while m < target:
        m *= 2
    return m


def reduced_residues(q: int) -> list[int]:
    return [a for a in range(1, q + 1) if math.gcd(a, q) == 1]


def z_star(lam: np.ndarray, n_val: int, q: int, m: int) -> dict:
    """Returns Z*_(q) = sum_a^* integral_T |R_{q,a}|^4, plus diagnostics."""
    mu_q = int(mobius(q))
    phi_q = int(totient(q))
    residues = reduced_residues(q)
    n_arr = np.arange(1, n_val + 1)
    z_total = 0.0
    per_a = []
    for a in residues:
        coeff = np.zeros(m, dtype=np.complex128)
        phase = np.exp(2j * np.pi * a * n_arr / q)
        coeff[1 : n_val + 1] = lam[1 : n_val + 1] * phase - (mu_q / phi_q)
        vals = np.fft.ifft(coeff) * m
        z_a = float(np.mean(np.abs(vals) ** 4).real)
        per_a.append(z_a)
        z_total += z_a
    return {
        "q": q,
        "mu_q": mu_q,
        "phi_q": phi_q,
        "squarefree": mu_q != 0,
        "Z_star_q": z_total,
        "Z_star_per_a_mean": z_total / len(residues) if residues else 0.0,
    }


def main() -> int:
    # Experiment 1: fixed N, Z*_(q) across small q (mix of squarefree and not).
    N1 = 20000
    Q_LIST = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 18, 20, 25, 30]
    m1 = fft_size(N1)
    lam1 = von_mangoldt(N1)
    rows1 = []
    for q in Q_LIST:
        row = z_star(lam1, N1, q, m1)
        row["Z_star_over_N3"] = row["Z_star_q"] / N1**3
        row["Z_star_over_phi_q_N3"] = row["Z_star_q"] / (row["phi_q"] * N1**3)
        rows1.append(row)

    sq_ratios = [r["Z_star_over_phi_q_N3"] for r in rows1 if r["squarefree"]]
    nonsq_ratios = [r["Z_star_over_phi_q_N3"] for r in rows1 if not r["squarefree"]]

    # Experiment 2: fixed q=2 (the single worst dyadic block per
    # RANK3_ROUTE_D.md Section 6), Z*_(2) as N grows -- isolates the N-power.
    Q2 = 2
    N_SWEEP = [2000, 4000, 8000, 16000, 32000, 64000]
    rows2 = []
    for n_val in N_SWEEP:
        m = fft_size(n_val)
        lam = von_mangoldt(n_val)
        row = z_star(lam, n_val, Q2, m)
        row["N"] = n_val
        row["Z_star_over_N3"] = row["Z_star_q"] / n_val**3
        row["Z_star_over_N3_logN"] = row["Z_star_q"] / (n_val**3 * math.log(n_val))
        rows2.append(row)

    out = {
        "definition": (
            "Z*_(q) = sum_{a mod q, gcd(a,q)=1} integral_T |R_{q,a}(beta)|^4 dbeta, "
            "R_{q,a} = F_N(a/q+beta) - (mu(q)/phi(q)) K_N(beta), computed exactly "
            "via DFT quadrature (frequency-exact, no sampling error beyond float64). "
            "This is the full-circle analogue of UPPER_BOUND.md Section 6's Z_(q), "
            "the same object RANK3_ROUTE_D.md Section 7 works with (no arc-transfer "
            "argument is available for the fourth moment, so the literal arc-"
            "restricted Z_(q) is not computed here, matching that document's own "
            "scope)."
        ),
        "context": (
            "Numerical companion to RANK3_QUARTIC_TOOLS.md's search for an "
            "unconditional, q-averaged tool bounding sum_{2<=q<=R_0} Z_(q). "
            "Trivial full-circle order per residue is O(N^3 log N) (sup|R|~N times "
            "integral|R|^2~N log N); Vaughan's (V) gives no saving at small q "
            "(RANK3_SCOPE.md Section 2)."
        ),
        "experiment_1_fixed_N_varying_q": {
            "N": N1,
            "rows": rows1,
            "squarefree_Z_over_phi_N3_range": [min(sq_ratios), max(sq_ratios)] if sq_ratios else None,
            "nonsquarefree_Z_over_phi_N3_range": [min(nonsq_ratios), max(nonsq_ratios)] if nonsq_ratios else None,
            "reading": (
                "Z_star_over_phi_q_N3 (Z*_(q) divided by phi(q)*N^3, the natural "
                "per-residue trivial-order normalization) is checked separately for "
                "squarefree and non-squarefree q. If mu(q)=0 collapses P_{q,a} to 0 "
                "identically (as the definitions force), R_{q,a}=F_N exactly for "
                "every a at non-squarefree q, so Z_(q) there carries no "
                "bias-subtraction at all, unlike U_(q) which vanishes identically "
                "on the same q (RANK3_ROUTE_D.md Section 4)."
            ),
        },
        "experiment_2_fixed_q2_varying_N": {
            "q": Q2,
            "rows": rows2,
            "reading": (
                "Isolates the N-power of Z*_(2) (mu(2)=-1, squarefree, phi(2)=1, "
                "the single worst dyadic block RANK3_ROUTE_D.md Section 6 prices "
                "at O(N^3) once summed over q). Z_star_over_N3 is reported to see "
                "whether it is bounded (no unconditional saving beyond trivial "
                "order, consistent with Section 2's analytic finding that (V) and "
                "(LS) both fail to save at this q) or shrinks with N (which would "
                "be a positive, previously unrecorded lead worth flagging)."
            ),
        },
    }

    out_path = HERE / "results_rank3_fourth_moment_probe.json"
    out_path.write_text(json.dumps(out, indent=1))

    print(f"Experiment 1: N={N1}, q varying")
    print(f"{'q':>4} {'sqfree':>7} {'Z*_(q)':>14} {'Z*/N^3':>12} {'Z*/(phi(q)N^3)':>16}")
    for r in rows1:
        print(
            f"{r['q']:>4} {str(r['squarefree']):>7} {r['Z_star_q']:>14.4e} "
            f"{r['Z_star_over_N3']:>12.6f} {r['Z_star_over_phi_q_N3']:>16.6f}"
        )
    print()
    print(f"Experiment 2: q={Q2}, N varying")
    print(f"{'N':>8} {'Z*_(2)':>14} {'Z*/N^3':>12} {'Z*/(N^3 logN)':>14}")
    for r in rows2:
        print(
            f"{r['N']:>8} {r['Z_star_q']:>14.4e} {r['Z_star_over_N3']:>12.6f} "
            f"{r['Z_star_over_N3_logN']:>14.6f}"
        )
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
