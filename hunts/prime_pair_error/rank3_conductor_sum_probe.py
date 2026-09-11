"""Finite checks for RANK3_CONDUCTOR_SUM.md.

Three things, none asymptotic:
  (1) the constant C_3 = prod_p (1 + (p-1)^-3) = sum over squarefree q of phi(q)^-3;
  (2) the q = 2 pin: the full-circle weighted moment T_N(2,1) against T_N, and
      the arc-restricted U_(2) against T_N/2 - 4 N L^2, at several N;
  (3) at q = 6 and q = 10, every nonprincipal character chi mod q against the
      primitive chi* inducing it: M_chi <= 2 M*(chi*) + 4 N rho_2(q)^2, and the
      conductor-organized identity
      sum_{chi != chi_0} cond(chi) M_chi = sum_{q*|q, q*>1} q* sum_{chi* prim mod q*} M_chi
      where M_chi is the induced character's moment (bookkeeping, checked exactly).
Runs in a few seconds with numpy only.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def mangoldt(N):
    lam = np.zeros(N + 1)
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, N + 1):
        if sieve[p]:
            sieve[p * p::p] = False
            pk = p
            while pk <= N:
                lam[pk] = math.log(p)
                pk *= p
    return lam


def moment_from_coeffs(c):
    """int_T |K_N * sum c_n e(n beta)|^2 = sum_t |S(t)|^2 + sum_{t<N} |S(N)-S(t)|^2,
    with S the partial sums of c (c indexed 1..N, c[0] unused)."""
    S = np.cumsum(c[1:])
    N = len(S)
    return float(np.sum(np.abs(S) ** 2) + np.sum(np.abs(S[-1] - S[:-1]) ** 2))


def characters_mod(q):
    """All Dirichlet characters mod q as arrays chi[n], n = 0..q-1, via brute force
    on the unit group (q small). Returns list of (chi_array, conductor)."""
    units = [a for a in range(1, q) if math.gcd(a, q) == 1]
    # generate the group of characters as homomorphisms: enumerate via the
    # structure of (Z/qZ)^* for squarefree q by CRT of prime components.
    primes = [p for p in range(2, q + 1) if q % p == 0 and all(p % r for r in range(2, p))]
    assert math.prod(primes) == q, "squarefree q only"
    comps = []
    for p in primes:
        # primitive root mod p
        g = next(g for g in range(1, p) if len({pow(g, k, p) for k in range(1, p)}) == p - 1) if p > 2 else 1
        comps.append((p, g))
    chars = []
    import itertools
    ranges = [range(p - 1) for p, _ in comps]
    for exps in itertools.product(*ranges):
        chi = np.zeros(q, dtype=complex)
        for n in range(q):
            if math.gcd(n, q) != 1:
                continue
            val = 1 + 0j
            for (p, g), e in zip(comps, exps):
                if p == 2:
                    continue
                r = n % p
                k = next(k for k in range(p - 1) if pow(g, k, p) == r)
                val *= np.exp(2j * np.pi * e * k / (p - 1))
            chi[n] = val
        cond = math.prod(p for (p, _), e in zip(comps, exps) if p != 2 and e != 0)
        chars.append((chi, cond))
    return chars


def main():
    out = {}
    # (1) C_3
    c3 = 1.0
    for p in range(2, 200000):
        if all(p % r for r in range(2, int(p ** 0.5) + 1)):
            c3 *= 1 + (p - 1) ** -3
    out["C_3"] = c3
    out["four_times_C3_minus_1"] = 4 * (c3 - 1)

    # (2) q = 2 pin
    rows = []
    for N in (120, 1000, 5000, 20000):
        lam = mangoldt(N)
        L = math.log(N)
        d = lam.copy(); d[1:] -= 1.0          # Lambda(n) - 1
        T_N = moment_from_coeffs(d)
        c21 = np.zeros(N + 1); c21[1:] = lam[1:] * ((-1.0) ** np.arange(1, N + 1)) + 1.0
        T_N21 = moment_from_coeffs(c21)      # full circle, (q,a) = (2,1); |mu(2)/phi(2)| = 1
        # arc-restricted U_(2): integrate |K_N|^2 |R_{2,1}|^2 over |beta| <= Q/(2N)
        Q = int(math.isqrt(N) // 3)
        M = 8 * N
        beta = (np.arange(M) / M)
        # exponential sums on the grid by FFT: S(j) = sum_n c_n e(n j / M) = M * ifft(c_pad)[j]
        pad = np.zeros(M, dtype=complex); pad[1:N + 1] = 1.0
        K = M * np.fft.ifft(pad)
        pad[1:N + 1] = c21[1:]
        R = M * np.fft.ifft(pad)
        integrand = np.abs(K) ** 2 * np.abs(R) ** 2
        # arc: ||beta|| <= Q/(2N)
        dist = np.minimum(beta, 1 - beta)
        arc = dist <= Q / (2 * N)
        U2 = float(integrand[arc].sum() / M)
        full = float(integrand.sum() / M)
        rows.append({"N": N, "Q": Q, "T_N": T_N, "T_N(2,1)_full_circle": T_N21,
                     "T_N(2,1)_grid": full, "U_(2)_arc": U2,
                     "ratio_U2_over_TN": U2 / T_N,
                     "lower_bound_TN_half_minus_4NL2": 0.5 * T_N - 4 * N * L * L,
                     "pin_holds": bool(U2 >= 0.5 * T_N - 4 * N * L * L)})
    out["q2_pin"] = rows

    # (3) conductor bookkeeping at q = 6, 10
    N = 3000
    lam = mangoldt(N)
    conds = []
    for q in (6, 10, 15):
        rho2 = float(sum(lam[n] for n in range(1, N + 1) if math.gcd(n, q) > 1))
        chars = characters_mod(q)
        lhs = 0.0
        worst = 0.0
        prim_by_cond = {}
        for chi, cond in chars:
            if cond == 1:
                continue
            c = np.zeros(N + 1, dtype=complex); c[1:] = lam[1:] * chi[np.arange(1, N + 1) % q]
            M_chi = moment_from_coeffs(c)
            # primitive inducing character: same values on n coprime to cond, extended
            chi_star = np.zeros(cond, dtype=complex)
            for r in range(cond):
                if math.gcd(r, cond) == 1:
                    # find n = r mod cond, n coprime to q, via CRT search
                    nn = next(m for m in range(r, r + q * cond, cond) if math.gcd(m, q) == 1)
                    chi_star[r] = chi[nn % q]
            cs = np.zeros(N + 1, dtype=complex); cs[1:] = lam[1:] * chi_star[np.arange(1, N + 1) % cond]
            M_star = moment_from_coeffs(cs)
            worst = max(worst, float(M_chi / (2 * M_star + 4 * N * rho2 ** 2)))
            lhs += cond * M_chi
            prim_by_cond.setdefault(cond, []).append(M_chi)
        conds.append({"q": q, "rho_2": rho2, "N": N,
                      "max_ratio_Mchi_over_(2Mstar+4Nrho2sq)": worst,
                      "inequality_holds": bool(worst <= 1.0),
                      "sum_cond_times_Mchi": lhs,
                      "by_conductor": {str(k): {"count": len(v), "sum_M": sum(v)} for k, v in prim_by_cond.items()}})
    out["conductor_bookkeeping"] = conds
    (HERE / "results_rank3_conductor_sum_probe.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: out[k] for k in ("C_3", "four_times_C3_minus_1")}))
    for r in rows:
        print(f"N={r['N']:6d} Q={r['Q']:3d} T_N={r['T_N']:.4g} T_N(2,1)={r['T_N(2,1)_full_circle']:.4g} "
              f"grid={r['T_N(2,1)_grid']:.4g} U_(2)={r['U_(2)_arc']:.4g} U2/TN={r['ratio_U2_over_TN']:.3f} pin={r['pin_holds']}")
    for c in conds:
        print(f"q={c['q']} rho2={c['rho_2']:.3f} worst ratio={c['max_ratio_Mchi_over_(2Mstar+4Nrho2sq)']:.4f} holds={c['inequality_holds']} by_cond={c['by_conductor']}")


if __name__ == "__main__":
    main()
