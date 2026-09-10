"""Numerically checks the specific claim RANK3_POLYRANGE_TINT_CHECK.md sources
from classical (BDH) via partial summation in q, rather than from any named
"t-integrated" theorem:

    S(N,B) = sum_{q=floor(L^B)+1}^{R_0} (mu(q)^2/phi(q)^2)
             sum_{a mod q, gcd(a,q)=1} sum_{t=1}^{N} (psi(t;q,a)-t/phi(q))^2

(discrete sum in t, in place of the integral -- Delta(t;q,a) is constant on
each unit interval [t,t+1), so integral_1^N Delta(t;q,a)^2 dt and
sum_{t=1}^N Delta(t;q,a)^2 agree up to an O(1)-per-t discretization effect
that does not change the order being checked here; this script measures the
same discrete quantity the rest of this hunt's probes use, e.g.
rank3_bdh_probe.py's D(N,Q)).

This is a sanity check on an elementary partial-summation argument (see
RANK3_POLYRANGE_TINT_CHECK.md Section 3), not a proof by itself: it measures
S(N,B) directly from the true von Mangoldt function at the one N,B pair that
is affordable here (R_0 must exceed floor(L^B) with enough margin for the
range to be non-empty at reachable N; this needs N of order 10^6-10^7 for
B=1, and is unreachable at this compute budget for B=2, since that needs
N > 9L^4 ~ 4*10^5 only nominally but R_0-A margin is thin near that
threshold -- see the printed diagnostics for the exact N chosen).

For each q, this computes, per coprime residue b mod q, psi(t;q,b) on the
grid t = b+1, b+1+q, b+1+2q, ... (vectorized via strided slicing + cumsum),
then sums Delta(t;q,b)^2 over each length-q interval between grid points in
closed form (sum_{j=0}^{m-1}(c-j/phi(q))^2 has an elementary closed form),
instead of an O(N) per-t Python loop. This is exact (not sampled), just
algebraically reorganized for speed.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/polyrange_weighted_bdh_check.py
Writes hunts/prime_pair_error/results_polyrange_weighted_bdh_check.json
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
from sympy import primerange, totient, mobius

HERE = Path(__file__).resolve().parent


def von_mangoldt(n_max: int) -> np.ndarray:
    """lam[n-1] = Lambda(n) for n = 1..n_max."""
    lam = np.zeros(n_max, dtype=np.float64)
    for p in primerange(2, n_max + 1):
        logp = math.log(p)
        pk = p
        while pk <= n_max:
            lam[pk - 1] = logp
            pk *= p
    return lam


def sum_delta_sq_for_q(lam: np.ndarray, n_max: int, q: int, phi_q: int) -> float:
    """sum_{a mod q, gcd(a,q)=1} sum_{t=1}^{n_max} (psi(t;q,a)-t/phi_q)^2, exact."""
    total = 0.0
    inv_phi = 1.0 / phi_q
    # closed form for sum_{j=0}^{m-1} (c - j*inv_phi)^2
    for b in range(q):
        # column b holds n = b+1, b+1+q, b+1+2q, ...; residue of n mod q is (b+1) mod q
        residue = (b + 1) % q
        if math.gcd(residue, q) != 1:
            continue

        # initial segment t = 1..min(b, n_max) (before the first possible
        # occurrence of this residue class, n=b+1): psi=0 there, so
        # Delta(t)=-t/phi_q. Capped at n_max for q > n_max edge cases.
        b_eff = min(b, n_max)
        if b_eff > 0:
            total += inv_phi**2 * (b_eff * (b_eff + 1) * (2 * b_eff + 1) / 6.0)

        seq = lam[b::q]  # Lambda at n = b+1, b+1+q, ...
        if seq.size == 0:
            # no occurrence of this residue class at all in [1,n_max]:
            # psi(t)=0 for every t, so Delta(t)=-t/phi_q throughout.
            m = n_max - b  # t = b+1, ..., n_max
            if m > 0:
                s1, s2, s3 = m, m * (m - 1) / 2.0, (m - 1) * m * (2 * m - 1) / 6.0
                # c=0 here (psi=0), t offset from b+1: reuse closed form with c=0
                total += inv_phi**2 * s3
            continue
        psi_grid = np.cumsum(seq)  # psi(t;q,residue) at t = b+1+i*q
        t_grid = (b + 1) + q * np.arange(seq.size)
        c = psi_grid - t_grid * inv_phi  # Delta(t;q,residue) exactly at grid points

        # full-length-q intervals: all but the last grid point contribute a
        # full interval [t_grid[i], t_grid[i]+q); the last grid point's
        # interval is truncated to n_max.
        if seq.size > 1:
            c_full = c[:-1]
            m = q
            s1 = m  # sum_{j=0}^{m-1} 1
            s2 = m * (m - 1) / 2.0  # sum j
            s3 = (m - 1) * m * (2 * m - 1) / 6.0  # sum j^2
            interval_sums = c_full**2 * s1 - 2 * inv_phi * c_full * s2 + inv_phi**2 * s3
            total += float(interval_sums.sum())

        # last (possibly truncated) interval
        t_last = int(t_grid[-1])
        m_last = min(q, n_max - t_last + 1)
        if m_last > 0:
            c_last = c[-1]
            s1 = m_last
            s2 = m_last * (m_last - 1) / 2.0
            s3 = (m_last - 1) * m_last * (2 * m_last - 1) / 6.0
            total += c_last**2 * s1 - 2 * inv_phi * c_last * s2 + inv_phi**2 * s3
    return total


def measure(n_val: int, b_exponents: list[float]) -> dict:
    L = math.log(n_val)
    Q = int(math.floor(math.sqrt(n_val) / 3))
    R0 = int(math.floor(Q / L))
    lam = von_mangoldt(n_val)

    rows = []
    for B in b_exponents:
        A = int(math.floor(L**B))
        q_lo, q_hi = A + 1, R0
        if q_lo > q_hi:
            rows.append(
                {
                    "B": B,
                    "A_floor_LB": A,
                    "R0": R0,
                    "q_range": None,
                    "note": "empty range (A+1 > R0) at this N",
                }
            )
            continue
        S = 0.0
        per_q = []
        for q in range(q_lo, q_hi + 1):
            mu_q = int(mobius(q))
            if mu_q == 0:
                continue  # weight is exactly 0 for non-squarefree q
            phi_q = int(totient(q))
            f_q = sum_delta_sq_for_q(lam, n_val, q, phi_q)
            weight = (mu_q * mu_q) / (phi_q * phi_q)
            contrib = weight * f_q
            S += contrib
            per_q.append({"q": q, "f_q": f_q, "weight": weight, "contrib": contrib})
        rows.append(
            {
                "B": B,
                "A_floor_LB": A,
                "R0": R0,
                "q_range": [q_lo, q_hi],
                "S_measured": S,
                "S_over_N2": S / n_val**2,
                "S_over_N2_over_L": S * L / n_val**2,
                "per_q": per_q,
            }
        )
    return {"N": n_val, "L": L, "Q": Q, "R0": R0, "rows": rows}


def main() -> int:
    # N chosen so that R_0 = floor(sqrt(N)/3)/L comfortably exceeds floor(L^1),
    # i.e. the B=1 range is non-empty with margin; B=2 needs N far larger
    # (R_0 > L^2 needs N of order (3 L^2 * L)^2 ~ 10^8+), unaffordable here
    # and reported as such rather than silently skipped.
    n_sweep = [500_000, 2_000_000]
    b_exponents = [1.0, 2.0]

    results = [measure(n, b_exponents) for n in n_sweep]

    out = {
        "definition": (
            "S(N,B) = sum_{q=floor(L^B)+1}^{R0} (mu(q)^2/phi(q)^2) "
            "sum_{a mod q, gcd(a,q)=1} sum_{t=1}^{N} (psi(t;q,a)-t/phi(q))^2, "
            "L=log N, Q=floor(sqrt(N)/3), R0=floor(Q/L). Discrete-t version "
            "of RANK3_POLYRANGE_TINT_CHECK.md Section 1's t-integrated claim."
        ),
        "claim_checked_is_derived_not_cited": (
            "RANK3_POLYRANGE_TINT_CHECK.md Section 3 derives S(N,B) = "
            "O(N^2 (log N)^{max(1-B,0)+o(1)}) from classical (BDH), "
            "D(t,Q) << Qt log t for every Q,t (Barban 1966; Davenport-"
            "Halberstam 1966), via partial summation over q against the "
            "decaying weight mu(q)^2/phi(q)^2 -- NOT from a named "
            "t-integrated theorem found in the literature search that "
            "document reports. This script checks that derived prediction "
            "against the true, exactly-computed S(N,B) (full von Mangoldt "
            "enumeration, no sampling)."
        ),
        "results": results,
    }
    out_path = HERE / "results_polyrange_weighted_bdh_check.json"
    out_path.write_text(json.dumps(out, indent=1))

    for res in results:
        print(f"N={res['N']} L={res['L']:.3f} Q={res['Q']} R0={res['R0']}")
        for row in res["rows"]:
            if row.get("q_range") is None:
                print(f"  B={row['B']}: {row['note']} (A={row['A_floor_LB']}, R0={row['R0']})")
                continue
            print(
                f"  B={row['B']}: q in {row['q_range']}, "
                f"S={row['S_measured']:.6e}, S/N^2={row['S_over_N2']:.6e}, "
                f"S*L/N^2={row['S_over_N2_over_L']:.6e}"
            )
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
