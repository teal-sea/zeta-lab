"""Section 8 candidate energy: an exact dyadic multiscale decomposition of

    E_corr(N) = 2 sum_{h=1}^N |r_N(h) - C_N(h)|^2               (CORRECTED_RH_BRIDGE.md eq 1)

and the proof that the resulting Energy(N) equals E_corr(N) exactly, term
by term, for every N. See CANDIDATE_ENERGY.md for the definition and the
domination proof; this script only evaluates both sides and the per-scale
breakdown.

No exceptional zero is asserted to exist, so (CORRECTED_RH_BRIDGE.md
Section 1) C_N(h) = 0 identically, and r_N(h) - C_N(h) = r_N(h) = the
original CHHL residual e(N, h) that probe.py already computes. E_corr(N)
therefore coincides numerically with probe.py's E(N); this script reuses
probe.py's von_mangoldt, singular_series, psi2_fft and E_of_N routines
rather than recomputing psi_2 or the singular series from scratch.

The multiscale decomposition: pad the residual vector x_h (1 <= h <= N) to
length M = 2^K (the least power of 2 that is >= N) by zeros, and form the
nested block-average (orthogonal-projection) telescoping identity of
CANDIDATE_ENERGY.md Section 2:

    sum_{h=1}^M x_h^2 = M * mu(N)^2 + sum_{k=0}^{K-1} Delta_k(N),

where mu(N) is the global mean of x and Delta_k(N) = ||P_k x - P_{k+1} x||^2
is the (nonnegative) energy of the scale-k block-average detail, P_k being
orthogonal projection onto vectors constant on blocks of length 2^k. Energy(N)
is twice the right side; per_scale reports each of its K+1 nonnegative terms.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/s8_candidate_energy.py
Writes hunts/prime_pair_error/results_s8_candidate_energy.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

from probe import E_of_N, singular_series, von_mangoldt, psi2_fft

HERE = Path(__file__).resolve().parent

NS = [2000, 5000, 10000, 30000, 100000]


def residual_vector(N: int, lam: np.ndarray, S: np.ndarray) -> np.ndarray:
    """x_h = r_N(h) - C_N(h) for 1 <= h <= N.  No exceptional zero is
    asserted to exist, so C_N == 0 and x_h = r_N(h) = psi_2(N,h) - (N-h)S(h),
    the exact sharp-endpoint residual of CORRECTED_RH_BRIDGE.md eq (4)/(1)."""
    psi2 = psi2_fft(lam, N)
    h = np.arange(1, N + 1)
    return psi2[1 : N + 1] - S[1 : N + 1] * (N - h)


def multiscale_decompose(x: np.ndarray) -> tuple[float, list[float], int, int]:
    """Exact telescoping identity sum x_h^2 = M*mu^2 + sum_k Delta_k(N).
    Returns (mean_term, [Delta_0, ..., Delta_{K-1}], M, K)."""
    N = x.shape[0]
    K = max(1, math.ceil(math.log2(N))) if N > 1 else 0
    M = 1 << K
    xp = np.zeros(M, dtype=np.float64)
    xp[:N] = x

    sums = xp.copy()  # block sums at level 0 (block length 1)
    level_energies: list[float] = []
    for k in range(K):
        pairs = sums.reshape(-1, 2)
        combined = pairs.sum(axis=1)  # block sums at level k+1
        a1 = pairs[:, 0] / (2 ** k)
        a2 = pairs[:, 1] / (2 ** k)
        b = combined / (2 ** (k + 1))
        d1 = a1 - b
        d2 = a2 - b
        energy_k = float((2 ** k) * np.sum(d1 * d1 + d2 * d2))
        level_energies.append(energy_k)
        sums = combined

    mu = float(sums[0]) / M
    mean_term = M * mu * mu
    return mean_term, level_energies, M, K


def run_one(N: int, lam: np.ndarray, S: np.ndarray) -> dict:
    x = residual_vector(N, lam, S)
    E_corr = 2.0 * float(np.dot(x, x))
    E_corr_probe = E_of_N(psi2_fft(lam, N), S, N)

    mean_term, level_energies, M, K = multiscale_decompose(x)
    per_scale = {"mean": 2.0 * mean_term}
    for k, dk in enumerate(level_energies):
        per_scale[f"scale_{k}_blocklen_{2 ** k}"] = 2.0 * dk
    Energy = 2.0 * (mean_term + sum(level_energies))

    rel_err = abs(Energy - E_corr) / max(E_corr, 1.0)
    rel_err_probe = abs(E_corr - E_corr_probe) / max(E_corr_probe, 1.0)

    return {
        "N": N,
        "M_padded": M,
        "K_scales": K,
        "E_corr": E_corr,
        "E_corr_from_probe_E_of_N": E_corr_probe,
        "Energy": Energy,
        "dominates": bool(Energy >= E_corr - 1e-6 * max(E_corr, 1.0)),
        "relative_gap_Energy_minus_Ecorr": (Energy - E_corr) / max(E_corr, 1.0),
        "check_matches_probe_E_of_N_relerr": rel_err_probe,
        "per_scale": per_scale,
        "per_scale_share": {k: v / Energy for k, v in per_scale.items()} if Energy > 0 else {},
    }


def main() -> int:
    rows = []
    Nmax = max(NS)
    lam, _lam_p = von_mangoldt(Nmax)
    S = singular_series(Nmax)
    for N in NS:
        row = run_one(N, lam, S)
        rows.append(row)
        print(f"N={N:>7}  E_corr={row['E_corr']:.6e}  Energy={row['Energy']:.6e}  "
              f"dominates={row['dominates']}  rel_gap={row['relative_gap_Energy_minus_Ecorr']:.2e}  "
              f"K={row['K_scales']}")

    out = {"definition": "CANDIDATE_ENERGY.md", "rows": rows,
           "all_dominate": all(r["dominates"] for r in rows),
           "max_abs_relative_gap": max(abs(r["relative_gap_Energy_minus_Ecorr"]) for r in rows)}
    out_path = HERE / "results_s8_candidate_energy.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
