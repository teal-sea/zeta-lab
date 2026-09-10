"""Measures RANK3_SCOPE.md's Route A quantity itself, directly.

RANK3_ARC_TRANSFER.md (T6) reduces rank 3's U-side, unconditionally and
without any Delta(t;q,b) estimate, to exactly

    S(N) := sum_{q=2}^{R_0} mu(q)^2 sum_{b mod q, gcd(b,q)=1} T(q,b),
    T(q,b) = sum_{t=1}^N Delta(t;q,b)^2
             + sum_{t=1}^{N-1} [Delta(N;q,b) - Delta(t;q,b)]^2,
    Delta(t;q,b) = psi(t;q,b) - t/phi(q),

with R_0 = floor(Q/L), Q = floor(sqrt(N)/3), L = log N (RANK3_ROUTE_D.md
(D5); UPPER_BOUND.md Section 6). RANK3_MEAN_VALUE_TOOLS.md Section 5 prices
the best unconditional tool found for this quantity (Barban-Davenport-
Halberstam, summed crudely over t) at O(N^{5/2}), one full power of N^{1/2}
short of the target O(N^{2+eps}); RANK3_BDH_VERIFY.md confirms no stronger
citable theorem closes that gap. Neither document computes S(N) itself --
they price named tools against it. This script computes S(N) directly from
the true von Mangoldt function (prime-power enumeration, no model, no
sampling), to see what growth rate the actual arithmetic exhibits, as an
independent empirical data point against the analytic bounds already on
record. It does not attempt to prove or disprove the O(N^{2+eps}) target;
a finite measurement cannot settle an asymptotic question either way.

Two experiments, matching rank3_bdh_probe.py's structure:

  1. S(N) at the *actual* R_0(N) (the quantity rank 3 needs), across a
     ladder of N -- checked against N^2 (target order), N^{5/2} (best
     unconditional bound on record), and the explicit crude bound
     R_0 * N^2 * log(N) that RANK3_MEAN_VALUE_TOOLS.md (E1)-(E2) derives.
  2. Fixed Q, varying N (isolates the N-power of S at one modulus range)
     and fixed N, varying Q (isolates the Q-power), the same decomposition
     rank3_bdh_probe.py uses for D(N,Q).

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_route_a_measure.py
Writes hunts/prime_pair_error/results_rank3_route_a_measure.json
"""
from __future__ import annotations

import json
import math
import time
from pathlib import Path

import numpy as np
from sympy import mobius, totient

HERE = Path(__file__).resolve().parent


def von_mangoldt(n_max: int) -> np.ndarray:
    """Lambda(1..n_max), Lambda(n) at index n-1, by direct prime-power enumeration."""
    is_prime = np.ones(n_max + 1, dtype=bool)
    is_prime[:2] = False
    for i in range(2, int(n_max**0.5) + 1):
        if is_prime[i]:
            is_prime[i * i :: i] = False
    lam = np.zeros(n_max, dtype=np.float64)
    for p in np.nonzero(is_prime)[0]:
        logp = math.log(p)
        pk = int(p)
        while pk <= n_max:
            lam[pk - 1] = logp
            pk *= p
    return lam


def R0_of(n_val: int) -> int:
    Q = int(math.sqrt(n_val)) // 3
    L = math.log(n_val)
    return int(Q // L)


def T_qb(lam_n: np.ndarray, q: int, b: int, phi_q: int) -> float:
    """T(q,b) exactly, from Delta(t;q,b) for every t=1..N, N=len(lam_n)."""
    n_val = lam_n.shape[0]
    contrib = np.zeros(n_val, dtype=np.float64)
    contrib[b - 1 :: q] = lam_n[b - 1 :: q]
    psi_arr = np.cumsum(contrib)
    t_arr = np.arange(1, n_val + 1, dtype=np.float64)
    delta = psi_arr - t_arr / phi_q
    return float(np.sum(delta * delta) + np.sum((delta[-1] - delta[:-1]) ** 2))


def S_running(lam_n: np.ndarray, q_max: int) -> dict[int, float]:
    """{q: S(N, q_max=q)} running cumulative sum, one pass over q=2..q_max."""
    running = 0.0
    out: dict[int, float] = {}
    for q in range(2, q_max + 1):
        mu_q = int(mobius(q))
        if mu_q != 0:
            phi_q = int(totient(q))
            s_q = 0.0
            for b in range(1, q + 1):
                if math.gcd(b, q) == 1:
                    s_q += T_qb(lam_n, q, b, phi_q)
            running += (mu_q**2) * s_q
        out[q] = running
    return out


def main() -> int:
    t_start = time.time()

    # ---- Experiment 1: S(N) at the true R_0(N), across a ladder of N. ----
    N_LADDER = [20000, 60000, 150000, 400000, 1000000, 2000000]
    n_max = max(N_LADDER)
    lam_full = von_mangoldt(n_max)

    rows_r0 = []
    prev = None
    for n_val in N_LADDER:
        r0 = R0_of(n_val)
        if r0 < 2:
            rows_r0.append({"N": n_val, "R0": r0, "skipped": "R0<2"})
            continue
        s_val = S_running(lam_full[:n_val], r0)[r0]
        L = math.log(n_val)
        crude_bound = r0 * (n_val**2) * L  # RANK3_MEAN_VALUE_TOOLS.md (E1)
        row = {
            "N": n_val,
            "R0": r0,
            "S_measured": s_val,
            "S_over_N2": s_val / n_val**2,
            "S_over_N2p5": s_val / n_val**2.5,
            "S_over_N3": s_val / n_val**3,
            "S_over_crude_E1_bound": s_val / crude_bound,
        }
        if prev is not None:
            row["empirical_local_exponent_vs_prev_N"] = math.log(
                s_val / prev[0]
            ) / math.log(n_val / prev[1])
        rows_r0.append(row)
        prev = (s_val, n_val)
        print(
            f"[{time.time()-t_start:7.1f}s] N={n_val:>9} R0={r0:>3} "
            f"S={s_val:.4e} S/N^2={row['S_over_N2']:.4e} "
            f"S/N^2.5={row['S_over_N2p5']:.4e} S/crude={row['S_over_crude_E1_bound']:.3e}"
        )

    # ---- Experiment 2a: fixed Q, varying N (isolates the N-power). ----
    Q_FIXED = 8
    N_SWEEP = [20000, 60000, 150000, 400000, 1000000, 2000000]
    rows_fixedQ = []
    prev2 = None
    for n_val in N_SWEEP:
        s_val = S_running(lam_full[:n_val], Q_FIXED)[Q_FIXED]
        row = {"N": n_val, "S_measured": s_val, "S_over_N2": s_val / n_val**2}
        if prev2 is not None:
            row["empirical_local_exponent_vs_prev_N"] = math.log(
                s_val / prev2[0]
            ) / math.log(n_val / prev2[1])
        rows_fixedQ.append(row)
        prev2 = (s_val, n_val)
        print(f"[{time.time()-t_start:7.1f}s] fixedQ={Q_FIXED} N={n_val:>9} S={s_val:.4e}")

    # ---- Experiment 2b: fixed N, varying Q (isolates the Q-power). ----
    N_FIXED = 400000
    Q_CHECKPOINTS = [4, 8, 12, 16, 20, 25, 30]
    s_by_q = S_running(lam_full[:N_FIXED], Q_CHECKPOINTS[-1])
    rows_fixedN = []
    prev3 = None
    for q in Q_CHECKPOINTS:
        s_val = s_by_q[q]
        row = {"Q": q, "S_measured": s_val}
        if prev3 is not None and prev3[0] > 0:
            row["empirical_local_exponent_vs_prev_Q"] = math.log(
                s_val / prev3[0]
            ) / math.log(q / prev3[1])
        rows_fixedN.append(row)
        prev3 = (s_val, q)
        print(f"[{time.time()-t_start:7.1f}s] fixedN={N_FIXED} Q={q:>3} S={s_val:.4e}")

    out = {
        "definition": (
            "S(N) = sum_{q=2}^{R0} mu(q)^2 sum_{b mod q, gcd(b,q)=1} T(q,b), "
            "T(q,b) = sum_{t=1}^N Delta(t;q,b)^2 "
            "+ sum_{t=1}^{N-1}[Delta(N;q,b)-Delta(t;q,b)]^2, "
            "Delta(t;q,b) = psi(t;q,b) - t/phi(q); R0 = floor(floor(sqrt(N)/3)/log(N))."
        ),
        "context": (
            "RANK3_ARC_TRANSFER.md (T6) reduces rank 3's U-side, unconditionally, "
            "to exactly S(N); the target is S(N) = O_eps(N^{2+eps}). "
            "RANK3_MEAN_VALUE_TOOLS.md Section 5 prices the best unconditional tool "
            "found (Barban-Davenport-Halberstam, summed crudely over t) at O(N^{5/2}); "
            "RANK3_BDH_VERIFY.md confirms no stronger citable theorem closes the "
            "remaining N^{1/2} gap. This script measures S(N) itself, from the true "
            "von Mangoldt function; it does not prove or disprove the target."
        ),
        "experiment_1_true_R0": {
            "N_ladder": N_LADDER,
            "rows": rows_r0,
        },
        "experiment_2a_fixed_Q_varying_N": {
            "Q": Q_FIXED,
            "N_sweep": N_SWEEP,
            "rows": rows_fixedQ,
        },
        "experiment_2b_fixed_N_varying_Q": {
            "N": N_FIXED,
            "Q_checkpoints": Q_CHECKPOINTS,
            "rows": rows_fixedN,
        },
        "runtime_seconds": time.time() - t_start,
    }

    out_path = HERE / "results_rank3_route_a_measure.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"wrote {out_path} in {out['runtime_seconds']:.1f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
