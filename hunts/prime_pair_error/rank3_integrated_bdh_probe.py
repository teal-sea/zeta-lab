"""Measures the *integrated-in-t* Barban-Davenport-Halberstam-type quantity

    Sigma(N, Q) = sum_{q=2}^{Q} sum_{a mod q, gcd(a,q)=1} sum_{t=1}^{N}
                  (psi(t;q,a) - t/phi(q))^2

directly, from the true von Mangoldt function, for a ladder of fixed small Q
and a sweep of N. This is the exact quantity named in this task and in
RANK3_MEAN_VALUE_TOOLS.md Section 5 / RANK3_ROUTE_D.md's T(q,b) summed over
q,b: the object an "integrated" Barban-Davenport-Halberstam theorem would
have to bound at order Q*N^{1+epsilon}, as opposed to the classical
single-endpoint theorem's D(N,Q) << Q N log N (measured separately in
rank3_bdh_probe.py / results_rank3_bdh_probe.json).

This script does not touch U_(q), Z_(q), or any arc/transfer quantity; it
measures Sigma(N,Q) itself against three reference shapes:

  - Q N^{1+eps} for a few small fixed eps (the target order this task asks
    whether an integrated theorem could reach);
  - Q N^2 log N (the order reached by summing the classical single-endpoint
    theorem crudely over N values of t, RANK3_MEAN_VALUE_TOOLS.md's (E1));
  - the trivial per-(q,a,t) bound 4t^2 summed, of order Q^2 N^3.

Lambda(n) is computed by direct enumeration of prime powers <= N (reusing
rank3_bdh_probe.py's von_mangoldt, cross-checked already against sympy's
totient for phi(q) there). psi(t;q,a) for every t is the exact cumulative
sum (numpy cumsum) of Lambda restricted to n = a (mod q); no sampling.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_integrated_bdh_probe.py
Writes hunts/prime_pair_error/results_rank3_integrated_bdh_probe.json
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from sympy import totient

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import rank3_bdh_probe as bdh  # noqa: E402  (reuses von_mangoldt)

Q_LADDER = [5, 10, 20, 30]
N_SWEEP = [10000, 20000, 40000, 80000, 160000, 320000]
EPS_LADDER = [0.05, 0.1, 0.2, 0.3]


def Sigma(n_val: int, q_max: int) -> float:
    """Sigma(n_val, q_max) = sum_{q=2}^{q_max} sum_a^* sum_{t=1}^{n_val} Delta(t;q,a)^2,

    computed exactly (no sampling) via cumulative sums of the true von Mangoldt
    function restricted to each residue class."""
    lam = bdh.von_mangoldt(n_val)[1:]  # lam[i] = Lambda(i+1), i=0..n_val-1
    t_arr = np.arange(1, n_val + 1, dtype=np.float64)
    n_idx = np.arange(1, n_val + 1)
    total = 0.0
    for q in range(2, q_max + 1):
        phi_q = int(totient(q))
        residues = [a for a in range(q) if math.gcd(a, q) == 1]
        n_mod_q = n_idx % q
        for a in residues:
            mask = (n_mod_q == a).astype(np.float64)
            psi_t = np.cumsum(mask * lam)
            delta_t = psi_t - t_arr / phi_q
            total += float(np.sum(delta_t * delta_t))
    return total


def main() -> int:
    rows = []
    for q_max in Q_LADDER:
        for n_val in N_SWEEP:
            sig = Sigma(n_val, q_max)
            L = math.log(n_val)
            row = {
                "Q": q_max,
                "N": n_val,
                "Sigma_measured": sig,
                "Sigma_over_Q_N2_logN": sig / (q_max * n_val * n_val * L),
                "trivial_bound_order_Q2N3": q_max * q_max * n_val ** 3 * 4.0,
                "ratio_measured_over_trivial": sig / (q_max * q_max * n_val ** 3 * 4.0),
            }
            for eps in EPS_LADDER:
                row[f"Sigma_over_Q_N1p{int(eps*100):02d}"] = sig / (
                    q_max * n_val ** (1.0 + eps)
                )
            rows.append(row)
            print(
                f"Q={q_max:>3} N={n_val:>7} Sigma={sig:>16.5e} "
                f"Sigma/(QN^2 logN)={row['Sigma_over_Q_N2_logN']:>10.5f} "
                f"Sigma/(QN^1.2)={row['Sigma_over_Q_N1p20']:>14.5e}"
            )

    out = {
        "definition": (
            "Sigma(N,Q) = sum_{q=2}^{Q} sum_{a mod q, gcd(a,q)=1} sum_{t=1}^{N} "
            "(psi(t;q,a) - t/phi(q))^2, psi(t;q,a) = sum_{n<=t, n=a (q)} Lambda(n). "
            "This is the exact t-integrated quantity this task's target theorem "
            "(order Q N^{1+eps}) would have to bound."
        ),
        "Q_ladder": Q_LADDER,
        "N_sweep": N_SWEEP,
        "eps_ladder": EPS_LADDER,
        "rows": rows,
        "reading": (
            "For fixed Q, Sigma_over_Q_N2_logN (the ratio to Q*N^2*log(N), the "
            "order reached by summing the classical single-endpoint BDH theorem "
            "crudely over t=1..N) is checked for stability across the N sweep: "
            "stability supports Sigma(N,Q) genuinely scaling like N^2 log N, not "
            "like N^{1+eps} for any fixed eps in EPS_LADDER. For contrast, "
            "Sigma_over_Q_N1p05 .. Sigma_over_Q_N1p30 are also reported at each "
            "(Q,N): if Sigma(N,Q) were really of order Q*N^{1+eps}, one of these "
            "columns would stabilize instead; growth of all of them across the N "
            "sweep is evidence against any such eps, however small, working "
            "uniformly, over exactly the N range measured here."
        ),
    }
    out_path = HERE / "results_rank3_integrated_bdh_probe.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
