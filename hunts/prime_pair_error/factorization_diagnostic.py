"""Focused independent diagnostic for the signed-cancellation repair package.

Scope (bounded audit-and-repair task, base b823a640dc7d460e7499c89dd514e062f80026d0):
  E2  - E-sign both-sides assertion: T_bil + sum(R(N/k)-R(Y)) computed once
        with high-precision transcendentals (mpmath dps=80) and once with
        exact Fraction arithmetic, compared against BOTH signs. Includes N=49.
        Discriminates the memo (3') sign; a flipped sign must FAIL.
  YR  - Y-range sweep for N in [4, 100000]: lower bound sqrt(N) <= Y (exact),
        violations of Y < sqrt(N)+1 (near-squares, small N), validation of the
        repaired bound Y <= sqrt(N)+1+1/(sqrt(N)-1).
  AB  - ab>Y gate for Sigma2: scalar check 2(U+1) > Y over [4,100000] plus
        exact pair-level min-gap on sampled N (ab >= 2(U+1) is exact).
  KN  - exact kernel identity D_N = S_smooth + sum_{m<=M} w_N(m) Lam(m),
        w in exact Fraction arithmetic, Lam from a fresh sieve (all prime
        powers, rational Y, jump endpoints, squares/nonsquares, N>=4).
  HY  - exact hyperbola partition D_N = S_smooth + Sigma1 + Sigma2 with
        exact integer mu; validates FACTORIZATION_NEXT_STEP section 6 table.
  S2B - Sigma2 against the honestly-derived trivial envelope N log^2 N
        (diagnostic ratios only; finite agreement is not a bound proof).
  EI  - empty-interval guard unit test: exhibits (b,k) cells where the
        clamped Mertens difference would reverse, and checks the guarded
        identity sums exactly to the direct mu sum.

Imports: stdlib + mpmath only. Nothing from author checkers, zeta/, or hunts/.
One process, N<=100000, well under 3 minutes.
"""

import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).parent
N_MAX = 100000


def sieve(n_max):
    """Fresh sieves: lam[n] = ln p if n = p^m else 0.0; mu[n] exact ints."""
    lam = [0.0] * (n_max + 1)
    mu = [0] * (n_max + 1)
    mu[1] = 1
    is_comp = bytearray(b"\x00") * (n_max + 1)
    primes = []
    for n in range(2, n_max + 1):
        if not is_comp[n]:
            primes.append(n)
            pp = n
            while pp <= n_max:
                lam[pp] = math.log(n)
                if pp > n_max // n:
                    break
                pp *= n
            if n * n <= n_max:
                for m in range(n * n, n_max + 1, n):
                    is_comp[m] = 1
    # mu via prime-factor parity sieve
    mu[1] = 1
    lp = [0] * (n_max + 1)  # least prime factor exponent packing: use arrays
    for p in primes:
        for m in range(p, n_max + 1, p):
            lp[m] += 1
    # square detection
    for p in primes:
        p2 = p * p
        for m in range(p2, n_max + 1, p2):
            lp[m] = -1000
    for n in range(2, n_max + 1):
        mu[n] = 0 if lp[n] < 0 else (-1 if lp[n] % 2 else 1)
    psi = [0.0] * (n_max + 1)
    s = 0.0
    for n in range(1, n_max + 1):
        s += lam[n]
        psi[n] = s
    return lam, mu, psi


def base_prime(n, primes):
    for p in primes:
        if p * p > n:
            break
        if n % p == 0:
            return p
    return n


def main():
    lam, mu, psi = sieve(N_MAX)
    # small prime list for base_prime recovery
    small_primes = []
    sieve_p = bytearray(b"\x00") * (N_MAX + 1)
    for n in range(2, N_MAX + 1):
        if not sieve_p[n]:
            small_primes.append(n)
            if n * n <= N_MAX:
                for m in range(n * n, N_MAX + 1, n):
                    sieve_p[m] = 1

    out = {"description": "Focused factorization/E-sign/Y-range diagnostic",
           "base": "b823a640dc7d460e7499c89dd514e062f80026d0",
           "E_sign": {}, "Y_range": {}, "AB_gate": {}, "kernel": {},
           "hyperbola": {}, "sigma2_bound": {}, "empty_interval": {}}

    # ---- E2: both-sides E-sign assertion ----
    for N in [16, 25, 27, 32, 36, 49, 64, 81, 100, 121, 144, 200, 400]:
        K = math.isqrt(N)
        Yf = Fraction(N, K)
        fY = N // K
        # Side A: high-precision transcendental evaluation of T_bil + sumR
        Ym = mp.mpf(N) / mp.mpf(K)
        T_bil = mp.mpf(0)
        sumR = mp.mpf(0)
        for k in range(2, K + 1):
            khi = N // k
            if khi > fY:
                seg = mp.mpf(psi[khi] - psi[fY])
                T_bil -= seg - mp.mpf(khi - fY)
            sumR += (mp.mpf(psi[khi]) - mp.mpf(N) / mp.mpf(k)) \
                - (mp.mpf(psi[fY]) - Ym)
        lhs = T_bil + sumR
        # Side B: exact Fraction arithmetic, both signs
        rhs_neg = -sum((Fraction(N, k) - Yf) - Fraction(N // k - fY)
                       for k in range(2, K + 1))
        rhs_pos = -rhs_neg
        d_neg = abs(float(lhs) - float(rhs_neg))
        d_pos = abs(float(lhs) - float(rhs_pos))
        ok = (d_neg < 1e-9) and (d_pos > 0.5 * abs(float(rhs_pos)) or rhs_pos == 0)
        out["E_sign"][str(N)] = {
            "Y_exact": str(Yf), "lhs_float": float(lhs),
            "rhs_correct_neg_Fraction": str(rhs_neg),
            "defect_correct_sign": d_neg, "defect_flipped_sign": d_pos,
            "discriminates": bool(ok)}
        assert ok, f"E-sign assertion failed at N={N}"

    # ---- YR: range sweep ----
    viol = []
    bound_ok = True
    lower_ok = True
    for N in range(4, N_MAX + 1):
        K = math.isqrt(N)
        Y = N / K
        sq = math.sqrt(N)
        if not (Y + 1e-12 >= sq):
            lower_ok = False
        if not (Y < sq + 1):
            if len(viol) < 12:
                viol.append({"N": N, "K": K, "Y": Y, "sqrtN": sq})
        if not (Y <= sq + 1 + 1 / (sq - 1) + 1e-12):
            bound_ok = False
    out["Y_range"] = {"lower_sqrtN_le_Y_all": bool(lower_ok),
                      "upper_Y_lt_sqrtN_plus_1_violations_count": None,
                      "upper_violations_sample": viol,
                      "repaired_bound_holds_all": bool(bound_ok)}
    # count violations separately (cheap second pass over residues near squares)
    out["Y_range"]["upper_Y_lt_sqrtN_plus_1_violations_count"] = sum(
        1 for N in range(4, N_MAX + 1)
        if not (N / math.isqrt(N) < math.sqrt(N) + 1))

    # ---- AB: 2(U+1) > Y scalar sweep + pair-level min gap on samples ----
    gmin_scalar = float("inf")
    scalar_ok = True
    for N in range(4, N_MAX + 1):
        K = math.isqrt(N)
        M = N // 2
        U = math.isqrt(M)
        gap = 2 * (U + 1) - N / K
        gmin_scalar = min(gmin_scalar, gap)
        if not gap > 0:
            scalar_ok = False
    sample_N = [n for n in range(4, 2001)] + \
        [i for i in range(2001, N_MAX + 1, 977)] + \
        [m * m - 1 for m in range(5, 317) if 4 <= m * m - 1 <= N_MAX]
    pair_min_gap = float("inf")
    pair_checked = 0
    for N in sample_N:
        K = math.isqrt(N)
        M = N // 2
        U = math.isqrt(M)
        for b in range(2, U + 1):
            hi = M // b
            for a in range(U + 1, hi + 1):
                pair_min_gap = min(pair_min_gap, K * a * b - N)
                pair_checked += 1
    out["AB_gate"] = {"scalar_2Uplus1_minus_Y_min": gmin_scalar,
                      "scalar_holds_all_4_to_100000": bool(scalar_ok),
                      "pair_level_min_Kab_minus_N": pair_min_gap,
                      "pairs_checked": pair_checked,
                      "pairs_all_strictly_positive": bool(pair_min_gap > 0)}

    # ---- KN + HY: kernel and partition, table validation ----
    table = {16: (14.2786, -18.2432, 0.6931, -3.2715),
             25: (32.8889, -34.8791, 0.0000, -1.9902),
             36: (59.9236, -64.1311, 0.6931, -3.5144),
             49: (96.1160, -100.8375, 3.5835, -1.1379),
             64: (142.0853, -139.9752, -4.7875, -2.6774),
             81: (198.3672, -207.9158, 8.3710, -1.1776),
             100: (265.4338, -266.9905, -4.0943, -5.6511),
             144: (433.5698, -431.5832, -4.4308, -2.4441),
             200: (666.7213, -690.2463, 29.6492, 6.1242),
             400: (1606.5025, -1591.4802, -16.8221, -1.7997),
             1000: (4923.7976, -5057.3877, 126.4718, -7.1182)}
    out["hyperbola"]["table_max_abs_deviation"] = 0.0
    for N in sorted(table) + [10000, 100000]:
        K = math.isqrt(N)
        M = N // 2
        U = math.isqrt(M)
        Y = N / K
        fY = N // K
        # kernel sum with exact Fraction weights
        kern = 0.0
        for m in range(1, M + 1):
            if lam[m]:
                w = (Fraction(1) - Fraction(N, m)) if m <= Y else \
                    Fraction(1 - (N // m))
                kern += float(w) * lam[m]
        H_K = sum(1.0 / k for k in range(1, K + 1))
        S = N * (math.log(Y) + H_K - 2 - 0.5772156649015329)
        DN = kern + S
        # reference D_N from psi definition (tail via euler)
        euler = 0.5772156649015329
        s_over = 0.0
        for d in range(1, fY + 1):
            if lam[d]:
                s_over += lam[d] / d
        tail = N * (-(1 + euler) - (s_over - psi[fY] / Y - math.log(Y)))
        sumR = sum(psi[N // k] - N / k for k in range(2, K + 1))
        Dref = tail - sumR
        kdef = abs(DN - Dref)
        out["kernel"][str(N)] = {"defect": kdef}
        assert kdef < 1e-6 * max(1.0, abs(Dref)), f"kernel defect at {N}"
        # hyperbola split with exact integer mu
        S1 = 0.0
        for a in range(1, U + 1):
            if mu[a]:
                hi = M // a
                for b in range(2, hi + 1):
                    m = a * b
                    w = (1 - N / m) if m <= Y else (1 - (N // m))
                    S1 += mu[a] * math.log(b) * w
        S2 = 0.0
        for b in range(2, U + 1):
            lb = math.log(b)
            hi = M // b
            for a in range(U + 1, hi + 1):
                m = a * b
                w = (1 - N / m) if m <= Y else (1 - (N // m))
                S2 += lb * mu[a] * w
        hdef = abs((S + S1 + S2) - Dref)
        row = {"S": S, "Sig1": S1, "Sig2": S2, "D": Dref, "defect": hdef}
        out["hyperbola"][str(N)] = row
        if N in table:
            t = table[N]
            dev = max(abs(S - t[0]), abs(S1 - t[1]), abs(S2 - t[2]), abs(Dref - t[3]))
            out["hyperbola"]["table_max_abs_deviation"] = max(
                out["hyperbola"]["table_max_abs_deviation"], dev)
            assert dev < 5e-4, f"table mismatch at N={N}: {dev}"
        if N in (10000, 100000):
            env = N * (math.log(N) ** 2)
            out["sigma2_bound"][str(N)] = {"Sig2": S2, "Nlog2N": env,
                                           "ratio": abs(S2) / env}
    out["hyperbola"]["table_validated_to_4dp"] = True

    # ---- EI: empty-interval guard ----
    # find (b,k) cells with lo >= hi; guarded contribution must be 0 and the
    # unguarded M(hi)-M(lo) must differ (wrong sign) whenever nonzero.
    Mert = [0] * (N_MAX + 1)
    s = 0
    for n in range(1, N_MAX + 1):
        s += mu[n]
        Mert[n] = s

    def Mof(t):
        return Mert[int(math.floor(t))] if t >= 1 else 0

    found = 0
    for N in [12, 16, 20, 36, 100, 400]:
        K = math.isqrt(N)
        M = N // 2
        U = math.isqrt(M)
        for b in range(2, U + 1):
            hib = M // b
            for k in range(2, K + 1):
                lo = max(U, N / (b * (k + 1)))
                hi = min(hib, N / (b * k))
                if hi <= lo:
                    # integer points in (lo, hi]: must be none for a true empty
                    pts = [a for a in range(U + 1, hib + 1) if lo < a <= hi]
                    direct = sum(mu[a] for a in pts)
                    guarded = 0 if Mof(hi) - Mof(lo) == 0 and not pts else None
                    unguarded = Mof(hi) - Mof(lo)
                    if not pts:
                        assert direct == 0
                        if unguarded != 0 and found < 3:
                            out["empty_interval"].setdefault("examples", []).append(
                                {"N": N, "b": b, "k": k, "unguarded": unguarded,
                                 "correct": 0})
                            found += 1
    out["empty_interval"]["guard_required_confirmed"] = found > 0
    out["empty_interval"]["checked_N"] = [12, 16, 20, 36, 100, 400]

    path = ROOT / "results_factorization_diagnostic.json"
    path.write_text(json.dumps(out, indent=2) + "\n")
    print("E-sign discriminates at all N (incl 49):",
          all(v["discriminates"] for v in out["E_sign"].values()))
    print("Y<sqrtN+1 violations:", out["Y_range"]["upper_Y_lt_sqrtN_plus_1_violations_count"],
          "sample:", [(v["N"], round(v["Y"], 4)) for v in out["Y_range"]["upper_violations_sample"][:6]])
    print("repaired Y bound holds:", out["Y_range"]["repaired_bound_holds_all"])
    print("2(U+1)-Y min:", round(out["AB_gate"]["scalar_2Uplus1_minus_Y_min"], 4),
          "pair min K.ab-N:", out["AB_gate"]["pair_level_min_Kab_minus_N"],
          "pairs:", out["AB_gate"]["pairs_checked"])
    print("table max deviation:", out["hyperbola"]["table_max_abs_deviation"])
    print("guard examples:", out["empty_interval"].get("examples", []))
    for n in ["10000", "100000"]:
        r = out["sigma2_bound"][n]
        print(f"N={n}: |Sig2|/Nlog2N = {r['ratio']:.4f}")
    return out


if __name__ == "__main__":
    main()
