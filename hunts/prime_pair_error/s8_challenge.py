"""Section 8 independent challenge against CANDIDATE_ENERGY.md's claimed exact
domination identity

    E_corr(N) <= Energy(N)      (in fact CANDIDATE_ENERGY.md claims equality)

See CHALLENGE.md for the verdict. Three required attacks:

  1. Search N <= 1e5 for a violation of the domination, from a from-scratch
     reimplementation of E_corr(N) and Energy(N) (this file never imports
     s8_candidate_energy.py). Cross-checked against
     results_s8_candidate_energy.json at N = 2000, and the FFT-based psi_2
     used here is itself cross-checked against a direct O(N^2) pair sum and
     against probe.py's own published Table 1 ratio at N = 100000.

  2. The Davenport-Heilbronn battery (zeta/epstein.py): build the identical
     x_h -> Energy(N) construction on a real, period-5 sequence coming from a
     function with a Riemann-type functional equation and a zero off the
     critical line, and check whether the same identity holds there too.

  3. A structural reading of CANDIDATE_ENERGY.md Section 3's proof is
     recorded in CHALLENGE.md, not here; this script only supplies the
     numbers that reading refers to.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/s8_challenge.py
Writes hunts/prime_pair_error/results_s8_challenge.json
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

from zeta.epstein import dh_coefficient  # noqa: E402  (independent DH battery input)

C2_REF = 0.6601618158468695739278121100145  # twin-prime constant, quoted (Wrench 1961)


# ---------------------------------------------------------------------------
# Fresh implementation of Lambda, S, psi_2 -- no import of probe.py or
# s8_candidate_energy.py. Definitions are exactly CORRECTED_RH_BRIDGE.md
# Section 1 / CHHL: Lambda includes proper prime powers, S(k) is the full
# singular series, endpoint is the sharp N - h.
# ---------------------------------------------------------------------------

def sieve_primes(nmax: int) -> np.ndarray:
    is_p = np.ones(nmax + 1, dtype=bool)
    is_p[:2] = False
    for i in range(2, int(nmax ** 0.5) + 1):
        if is_p[i]:
            is_p[i * i :: i] = False
    return np.nonzero(is_p)[0]


def von_mangoldt(nmax: int, primes: np.ndarray) -> np.ndarray:
    """Lambda(n), 0 <= n <= nmax, proper prime powers included."""
    lam = np.zeros(nmax + 1, dtype=np.float64)
    for p in primes:
        logp = math.log(int(p))
        pk = int(p)
        while pk <= nmax:
            lam[pk] = logp
            pk *= int(p)
    return lam


def singular_series(nmax: int, primes: np.ndarray) -> np.ndarray:
    """S(k), 0 <= k <= nmax: S(k) = 2*C2 * prod_{p|k, p>2} (p-1)/(p-2) for
    even k, 0 for odd k (CHHL / CORRECTED_RH_BRIDGE.md eq 4)."""
    S = np.full(nmax + 1, 2.0 * C2_REF, dtype=np.float64)
    for p in primes:
        p = int(p)
        if p == 2:
            continue
        S[p :: p] *= (p - 1.0) / (p - 2.0)
    S[1::2] = 0.0
    S[0] = 0.0
    return S


def autocorr_fft(a: np.ndarray, N: int) -> np.ndarray:
    """sum_{n=1}^{N-h} a(n) a(n+h) for 0 <= h <= N, via FFT, for a real
    sequence a indexed 0..N (a[0] may be anything; it is never used since the
    correlation sums start at n=1)."""
    v = a[: N + 1].copy()
    v[0] = 0.0
    L = 1
    while L < 2 * (N + 1):
        L *= 2
    F = np.fft.rfft(v, n=L)
    ac = np.fft.irfft(F * np.conj(F), n=L)[: N + 1]
    return ac


def autocorr_direct(a: np.ndarray, N: int) -> np.ndarray:
    """O(N^2) pair sum, for cross-checking autocorr_fft at small N."""
    v = a[: N + 1].copy()
    v[0] = 0.0
    out = np.zeros(N + 1, dtype=np.float64)
    for h in range(N + 1):
        if h == 0:
            out[0] = float(np.dot(v, v))
        else:
            out[h] = float(np.dot(v[1 : N + 1 - h], v[1 + h : N + 1]))
    return out


def multiscale_energy(x: np.ndarray) -> tuple[float, list[float], int, int]:
    """CANDIDATE_ENERGY.md Section 2/3's identity, coded fresh: pad x to
    M = 2^K >= len(x) with zeros, then repeatedly halve by averaging pairs,
    accumulating the scale-k detail energy Delta_k = 2^(k-1) * sum(a1-a2)^2
    over the length-2^(k+1) blocks (a1, a2 the two length-2^k sub-block
    averages). Returns (M*mu^2, [Delta_0, ..., Delta_{K-1}], M, K)."""
    N = x.shape[0]
    K = 0
    M = 1
    while M < N:
        M *= 2
        K += 1
    xp = np.zeros(M, dtype=np.float64)
    xp[:N] = x
    level = xp
    deltas: list[float] = []
    blocklen = 1
    while blocklen < M:
        pairs = level.reshape(-1, 2)
        a1, a2 = pairs[:, 0], pairs[:, 1]
        diff = a1 - a2
        deltas.append(blocklen * float(np.sum(diff * diff)) / 2.0)
        level = (a1 + a2) / 2.0
        blocklen *= 2
    mu = float(level[0]) if level.size else 0.0
    mean_term = M * mu * mu
    return mean_term, deltas, M, K


def e_corr_and_energy(x: np.ndarray) -> dict:
    E_corr = 2.0 * float(np.dot(x, x))
    mean_term, deltas, M, K = multiscale_energy(x)
    Energy = 2.0 * (mean_term + sum(deltas))
    denom = max(E_corr, 1.0)
    return {
        "E_corr": E_corr,
        "Energy": Energy,
        "M": M,
        "K": K,
        "dominates": bool(Energy >= E_corr - 1e-8 * denom),
        "relative_gap_Energy_minus_Ecorr": (Energy - E_corr) / denom,
    }


# ---------------------------------------------------------------------------
# Attack 1
# ---------------------------------------------------------------------------

def build_grid(nmax: int) -> list[int]:
    g = set(range(1, 21))
    g |= set(range(25, 201, 25))
    g |= set(range(200, 2001, 100))
    g |= set(range(2000, 20001, 1000))
    g |= set(range(20000, nmax + 1, 5000))
    for k in range(1, 18):
        for v in (1 << k, (1 << k) - 1, (1 << k) + 1):
            if v >= 1:
                g.add(v)
    g |= {2000, 5000, 10000, 30000, 100000}
    return sorted(v for v in g if 1 <= v <= nmax)


def attack1(nmax: int) -> dict:
    t0 = time.time()
    primes = sieve_primes(nmax)
    lam = von_mangoldt(nmax, primes)
    S = singular_series(nmax, primes)

    # Fresh-implementation cross-checks, independent of probe.py/s8_candidate_energy.py
    checks = {}
    N_small = 2000
    psi2_fft_small = autocorr_fft(lam, N_small)
    psi2_direct_small = autocorr_direct(lam, N_small)
    checks["fft_vs_direct_pairsum_N2000_maxabs"] = float(
        np.max(np.abs(psi2_fft_small - psi2_direct_small))
    )
    # probe.py's own published Table 1 value at N=100000: E/(N^2 log^2 N) = 0.16857
    psi2_100k = autocorr_fft(lam, nmax) if nmax == 100000 else autocorr_fft(lam, 100000)
    N100k = 100000
    h100k = np.arange(1, N100k + 1)
    x100k = psi2_100k[1 : N100k + 1] - S[1 : N100k + 1] * (N100k - h100k)
    E100k = 2.0 * float(np.dot(x100k, x100k))
    checks["E_over_N2log2N_at_1e5"] = E100k / (N100k ** 2 * math.log(N100k) ** 2)
    checks["paper_table1_value_at_1e5"] = 0.16857

    grid = build_grid(nmax)
    rows = []
    for N in grid:
        psi2 = autocorr_fft(lam, N)
        h = np.arange(1, N + 1)
        x = psi2[1 : N + 1] - S[1 : N + 1] * (N - h)
        r = e_corr_and_energy(x)
        r["N"] = N
        rows.append(r)

    violations = [r for r in rows if not r["dominates"]]
    max_gap = max(abs(r["relative_gap_Energy_minus_Ecorr"]) for r in rows)

    # cross-check against results_s8_candidate_energy.json at N=2000, without
    # importing s8_candidate_energy.py
    cand_path = HERE / "results_s8_candidate_energy.json"
    cross = {}
    if cand_path.exists():
        cand = json.loads(cand_path.read_text())
        row2000 = next(r for r in cand["rows"] if r["N"] == 2000)
        mine2000 = next(r for r in rows if r["N"] == 2000)
        cross = {
            "candidate_E_corr_N2000": row2000["E_corr"],
            "my_E_corr_N2000": mine2000["E_corr"],
            "relerr_E_corr": abs(mine2000["E_corr"] - row2000["E_corr"])
            / max(row2000["E_corr"], 1.0),
            "candidate_Energy_N2000": row2000["Energy"],
            "my_Energy_N2000": mine2000["Energy"],
            "relerr_Energy": abs(mine2000["Energy"] - row2000["Energy"])
            / max(row2000["Energy"], 1.0),
        }

    return {
        "n_tested": len(grid),
        "n_max": nmax,
        "checks": checks,
        "cross_check_vs_s8_candidate_energy_json_at_N2000": cross,
        "violations_found": [
            {"N": r["N"], "relative_gap": r["relative_gap_Energy_minus_Ecorr"]}
            for r in violations
        ],
        "all_dominate": len(violations) == 0,
        "max_abs_relative_gap": max_gap,
        "rows": rows,
        "seconds": time.time() - t0,
    }


# ---------------------------------------------------------------------------
# Attack 2: the Davenport-Heilbronn battery
# ---------------------------------------------------------------------------

def dh_sequence(nmax: int) -> np.ndarray:
    """a(n) for 0 <= n <= nmax, the real, period-5 Dirichlet coefficients of
    the Davenport-Heilbronn function f (zeta/epstein.py: dh_coefficient),
    a_1..a_5 = 1, kappa, -kappa, -1, 0, tiled (a is exactly periodic mod 5 by
    construction, so 5 evaluations determine it all)."""
    period = [float(dh_coefficient(n, dps=30)) for n in range(1, 6)]
    a = np.zeros(nmax + 1, dtype=np.float64)
    idx = np.arange(0, nmax + 1)
    r = idx % 5  # r=0 corresponds to n=5,10,... i.e. period[4]
    for rr in range(5):
        a[r == rr] = period[(rr - 1) % 5]
    a[0] = 0.0
    return a


def dh_period_rho(a: np.ndarray) -> np.ndarray:
    """rho(h), h = 0..4: the exact period-average of a(n) a(n+h), the
    Davenport-Heilbronn analogue of the singular series S(h). Since a is
    exactly periodic mod 5 (no arithmetic irregularity), rho(h) is the exact
    expected main term of sum a(n) a(n+h), not an approximation."""
    period = a[1:6]  # a(1..5)
    rho = np.zeros(5, dtype=np.float64)
    for h in range(5):
        rho[h] = float(np.mean([period[j] * period[(j + h) % 5] for j in range(5)]))
    return rho


def attack2(nmax: int) -> dict:
    t0 = time.time()
    a = dh_sequence(nmax)
    rho5 = dh_period_rho(a)

    grid = sorted({100, 1000, 2000, 5000, 10000, 30000, 100000,
                   *(1 << k for k in range(4, 18)),
                   *((1 << k) - 1 for k in range(4, 18))})
    grid = [n for n in grid if 1 <= n <= nmax]

    rows = []
    for N in grid:
        psi2_dh = autocorr_fft(a, N)
        h = np.arange(1, N + 1)
        rho_h = rho5[h % 5]
        x = psi2_dh[1 : N + 1] - rho_h * (N - h)
        r = e_corr_and_energy(x)
        r["N"] = N
        rows.append(r)

    violations = [r for r in rows if not r["dominates"]]
    max_gap = max(abs(r["relative_gap_Energy_minus_Ecorr"]) for r in rows)

    return {
        "n_tested": len(grid),
        "rho_h_mod_5": rho5.tolist(),
        "dh_a_1_to_5": a[1:6].tolist(),
        "violations_found": [
            {"N": r["N"], "relative_gap": r["relative_gap_Energy_minus_Ecorr"]}
            for r in violations
        ],
        "all_dominate": len(violations) == 0,
        "max_abs_relative_gap": max_gap,
        "domination_and_equality_hold_for_dh_too": len(violations) == 0 and max_gap < 1e-6,
        "rows": rows,
        "seconds": time.time() - t0,
    }


def main() -> int:
    nmax = 100_000
    print("Attack 1: independent search for a domination violation, N <= 1e5")
    a1 = attack1(nmax)
    print(f"  tested {a1['n_tested']} values of N; all_dominate={a1['all_dominate']}; "
          f"max |relative gap| = {a1['max_abs_relative_gap']:.2e}")
    print(f"  fft-vs-direct pair sum check (N=2000): "
          f"{a1['checks']['fft_vs_direct_pairsum_N2000_maxabs']:.2e}")
    print(f"  E/(N^2 log^2 N) at 1e5 = {a1['checks']['E_over_N2log2N_at_1e5']:.5f} "
          f"(paper table 1: {a1['checks']['paper_table1_value_at_1e5']})")
    cc = a1["cross_check_vs_s8_candidate_energy_json_at_N2000"]
    if cc:
        print(f"  cross-check vs results_s8_candidate_energy.json at N=2000: "
              f"relerr(E_corr)={cc['relerr_E_corr']:.2e}  relerr(Energy)={cc['relerr_Energy']:.2e}")

    print("\nAttack 2: Davenport-Heilbronn battery (zeta/epstein.py)")
    a2 = attack2(nmax)
    print(f"  tested {a2['n_tested']} values of N; all_dominate={a2['all_dominate']}; "
          f"max |relative gap| = {a2['max_abs_relative_gap']:.2e}")
    print(f"  domination (in fact equality) holds for DH too: "
          f"{a2['domination_and_equality_hold_for_dh_too']}")

    out = {
        "attack1_independent_search": a1,
        "attack2_dh_battery": a2,
    }
    out_path = HERE / "results_s8_challenge.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
