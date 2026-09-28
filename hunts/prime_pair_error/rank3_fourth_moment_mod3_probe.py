"""Follow-up to rank3_fourth_moment_probe.py / RANK3_QUARTIC_TOOLS.md Section 2.

That probe's own output (results_rank3_fourth_moment_probe.json,
experiment_1_fixed_N_varying_q, N=20000) shows Z*_(q)/(phi(q)N^3) is NOT a
single constant across squarefree q>=3 as RANK3_QUARTIC_TOOLS.md Section 2
claims ("matching q=3,5,6,7,10 etc. to at least four digits"): q=3 and q=6
(both 3 | q) land at ~1.4846, while q=5,7,10,15,30 (3 does not divide q,
except 15 and 30 which ARE divisible by 3 -- see below) land at ~1.5226-
1.5259, and non-squarefree q all land at 1.525934 to six digits. This script
checks whether the 3|q vs 3 nmid q split is a real, N-growing effect or a
finite-N artifact of N=20000 specifically (which is coprime to 3), by
sweeping N at fixed q in {3,5,6,10} and by re-running the original q-list at
a second, independent N.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_fourth_moment_mod3_probe.py
Writes hunts/prime_pair_error/results_rank3_fourth_moment_mod3_probe.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from sympy import mobius, primerange, totient

HERE = Path(__file__).resolve().parent


def von_mangoldt(n_max: int) -> np.ndarray:
    lam = np.zeros(n_max + 1, dtype=np.float64)
    for p in primerange(2, n_max + 1):
        logp = math.log(p)
        pk = p
        while pk <= n_max:
            lam[pk] = logp
            pk *= p
    return lam


def fft_size(n_val: int) -> int:
    target = 4 * n_val + 8
    m = 1
    while m < target:
        m *= 2
    return m


def reduced_residues(q: int) -> list[int]:
    return [a for a in range(1, q + 1) if math.gcd(a, q) == 1]


def z_star(lam: np.ndarray, n_val: int, q: int, m: int) -> dict:
    mu_q = int(mobius(q))
    phi_q = int(totient(q))
    residues = reduced_residues(q)
    n_arr = np.arange(1, n_val + 1)
    z_total = 0.0
    for a in residues:
        coeff = np.zeros(m, dtype=np.complex128)
        phase = np.exp(2j * np.pi * a * n_arr / q)
        coeff[1 : n_val + 1] = lam[1 : n_val + 1] * phase - (mu_q / phi_q)
        vals = np.fft.ifft(coeff) * m
        z_total += float(np.mean(np.abs(vals) ** 4).real)
    return {
        "q": q,
        "mu_q": mu_q,
        "phi_q": phi_q,
        "div3": q % 3 == 0,
        "Z_star_q": z_total,
        "Z_star_over_phi_q_N3": z_total / (phi_q * n_val**3),
    }


def main() -> int:
    # Experiment A: N sweep at fixed q, contrasting 3|q vs 3 nmid q, all squarefree.
    Q_LIST = [3, 5, 6, 10]  # 3|3, 3 nmid 5, 3|6, 3 nmid 10
    N_SWEEP = [4000, 8000, 16000, 32000, 64000, 128000]
    rowsA = []
    for n_val in N_SWEEP:
        m = fft_size(n_val)
        lam = von_mangoldt(n_val)
        for q in Q_LIST:
            row = z_star(lam, n_val, q, m)
            row["N"] = n_val
            rowsA.append(row)

    # Experiment B: same q-list as the original probe, at a second N not
    # coprime to 3 (N=21000 = 2^3*3*5^3*7), to see if the split persists,
    # shrinks, or is an artifact tied to N=20000's own factorization.
    Q_LIST_B = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 18, 20, 25, 30]
    N_B = 21000
    m_b = fft_size(N_B)
    lam_b = von_mangoldt(N_B)
    rowsB = [z_star(lam_b, N_B, q, m_b) for q in Q_LIST_B]

    out = {
        "context": (
            "Checks whether the 3|q vs 3-nmid-q split visible in "
            "results_rank3_fourth_moment_probe.json (N=20000, q=3,6 give "
            "Z*_(q)/(phi(q)N^3)~1.4846 vs q=5,7,10 etc ~1.523-1.526) is a "
            "finite-N artifact of N=20000=2^5*5^4 (coprime to 3) or persists "
            "as N grows / at N not coprime to 3. RANK3_QUARTIC_TOOLS.md "
            "Section 2's claim that all squarefree q>=3 match "
            "'to at least four digits' is not correct as stated for q=3,6 "
            "at N=20000; this script checks whether it is approximately "
            "correct in the N->infinity limit (a genuine single constant, "
            "slow to converge for q|3) or whether 3|q is a permanently "
            "distinct case."
        ),
        "experiment_A_N_sweep_3div_vs_not": {
            "Q_LIST": Q_LIST,
            "N_SWEEP": N_SWEEP,
            "rows": rowsA,
        },
        "experiment_B_second_N_full_qlist": {
            "N": N_B,
            "rows": rowsB,
        },
    }

    out_path = HERE / "results_rank3_fourth_moment_mod3_probe.json"
    out_path.write_text(json.dumps(out, indent=1))

    print(f"Experiment A: N sweep, q in {Q_LIST}")
    print(f"{'N':>8} {'q':>4} {'div3':>6} {'Z*/(phi(q)N^3)':>16}")
    for r in rowsA:
        print(f"{r['N']:>8} {r['q']:>4} {str(r['div3']):>6} {r['Z_star_over_phi_q_N3']:>16.6f}")
    print()
    print(f"Experiment B: N={N_B}")
    print(f"{'q':>4} {'div3':>6} {'Z*/(phi(q)N^3)':>16}")
    for r in rowsB:
        print(f"{r['q']:>4} {str(r['div3']):>6} {r['Z_star_over_phi_q_N3']:>16.6f}")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
