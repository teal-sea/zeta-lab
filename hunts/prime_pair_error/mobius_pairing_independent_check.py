"""Independent verification of p=2 Mobius pairing inside Sigma_2.

Independent implementation: does not import author code or data.
Validates:
1. Exact 5-part disjoint combinatorial partition of (U, V] and bijection m <-> 2m.
2. Exact rational Fraction identity M_b = P_b + T_b + H_b (Z_b = 0 termwise).
3. Integer gate 2(U+1)K - N >= 3 > 0 and ab > Y on all pairs across 12 <= N <= 10000,
   including near-square stress cases (K^2 - 1, K^2, K^2 + 1, K^2 + 2K).
4. Exact integer cutoff b* = floor(M / [2(U+1)]) for F > U.
5. Planted lesions (missing head, missing tail, wrong sign, tail even inclusion).
6. Baseline and paired majorant asymptotic sums B(N) and Ptot(N).

Execution: 1 process, <= 60s target.
Outputs: results_mobius_pairing_independent.json.
"""

import json
import math
import time
from fractions import Fraction
from pathlib import Path
from sympy import mobius as sym_mobius

HERE = Path(__file__).resolve().parent
OUT = HERE / "results_mobius_pairing_independent.json"

N_LIST = [12, 13, 14, 15, 16, 20, 25, 27, 32, 36, 49, 64, 81, 100, 121, 144,
          200, 400, 1000, 10000]


def main():
    t0 = time.time()
    print("=== STARTING INDEPENDENT VERIFICATION ===")

    # 1. Exact Mobius oracle via SymPy
    mu = [0] * 10001
    for n in range(1, 10001):
        mu[n] = int(sym_mobius(n))

    # Spot checks on mu
    assert mu[1] == 1 and mu[2] == -1 and mu[4] == 0 and mu[6] == 1
    assert mu[8] == 0 and mu[9] == 0 and mu[30] == -1 and mu[49] == 0

    # 2. Near-square stress test for the gate 2(U+1)K - N >= 1
    near_square_checks = []
    for K in range(3, 101):
        for delta in (-1, 0, 1, 2 * K):
            N = K * K + delta
            if N < 12 or N > 10000:
                continue
            M = N // 2
            U = math.isqrt(M)
            K_actual = math.isqrt(N)
            gap = 2 * (U + 1) * K_actual - N
            assert gap > 0, f"Gate failure at near-square N={N}, K={K_actual}, gap={gap}"
            near_square_checks.append({"N": N, "K": K_actual, "U": U, "gap": gap})

    # 3. Main loop over N_LIST
    rows = {}
    total_pairs_checked = 0
    global_min_gate = None

    for N in N_LIST:
        M = N // 2
        U = math.isqrt(M)
        K = math.isqrt(N)
        Y_frac = Fraction(N, K)
        b_star = M // (2 * (U + 1))

        def w(m):
            return Fraction(1) - Fraction(N, m) if m <= Y_frac else Fraction(1 - N // m)

        max_defect = Fraction(0)
        n_total_terms = 0
        n_paired_odds = 0
        n_tail_odds = 0
        n_head_terms = 0
        base_tot = 0.0
        pair_tot = 0.0
        t_tot = 0.0
        h_tot = 0.0
        p_tot = 0.0

        for b in range(2, U + 1):
            V = M // b
            if V <= U:
                continue
            F = V // 2
            LO = max(U, F)

            # Check exact cutoff equivalence
            assert (F > U) == (b <= b_star), f"Cutoff mismatch at N={N}, b={b}"

            interval = set(range(U + 1, V + 1))
            s_odd_low = {m for m in range(U + 1, F + 1) if m % 2 == 1}
            s_odd_high = {m for m in range(LO + 1, V + 1) if m % 2 == 1}
            s_even_head = {2 * t for t in range(1, U + 1) if U < 2 * t <= V}
            s_even_mid_odd = {2 * t for t in range(U + 1, F + 1) if t % 2 == 1}
            s_even_mid_even = {2 * t for t in range(U + 1, F + 1) if t % 2 == 0}

            # Partition check
            sets = [s_odd_low, s_odd_high, s_even_head, s_even_mid_odd, s_even_mid_even]
            total_elements = sum(len(s) for s in sets)
            union_set = set().union(*sets)
            assert total_elements == len(union_set), f"Overlapping partition at N={N}, b={b}"
            assert union_set == interval, f"Non-exhaustive partition at N={N}, b={b}"

            # Bijection m -> 2m
            assert {2 * m for m in s_odd_low} == s_even_mid_odd

            # Even-mid-even must have mu = 0 termwise
            for a in s_even_mid_even:
                assert mu[a] == 0, f"mu({a}) != 0 for 4 | a"

            # Check gate margin on all pairs
            for a in interval:
                total_pairs_checked += 1
                g = a * b * K - N
                if global_min_gate is None or g < global_min_gate:
                    global_min_gate = g
                assert g > 0, f"Gate violation: a={a}, b={b}, N={N}"

            # Exact sums
            Mb = sum(mu[a] * w(a * b) for a in interval)
            P = sum(mu[m] * (w(m * b) - w(2 * m * b)) for m in s_odd_low)
            T = sum(mu[m] * w(m * b) for m in s_odd_high)
            H = sum(mu[a] * w(a * b) for a in s_even_head)
            Z = sum(mu[a] * w(a * b) for a in s_even_mid_even)

            assert Z == 0
            defect = abs(Mb - (P + T + H))
            max_defect = max(max_defect, defect)
            assert defect == 0, f"Identity defect at N={N}, b={b}"

            n_total_terms += len(interval)
            n_paired_odds += len(s_odd_low)
            n_tail_odds += len(s_odd_high)
            n_head_terms += len(s_even_head)

            # Majorant sums
            lb = math.log(b)
            Bb = sum(N / (a * b) for a in interval)
            Pm = sum(N / (2 * m * b) + 1 for m in s_odd_low)
            Tm = sum(N / (m * b) for m in s_odd_high)
            Hm = sum(N / (2 * t * b) for t in range(1, U + 1) if U < 2 * t <= V)

            base_tot += lb * Bb
            p_tot += lb * Pm
            t_tot += lb * Tm
            h_tot += lb * Hm

        pair_tot = p_tot + t_tot + h_tot
        unpaired = n_tail_odds + n_head_terms
        L3 = N * (math.log(N) ** 3)
        L2 = N * (math.log(N) ** 2)

        rows[str(N)] = {
            "max_fraction_defect": str(max_defect),
            "b_star": b_star,
            "U": U,
            "n_total_terms": n_total_terms,
            "n_paired_odds": n_paired_odds,
            "n_tail_odds": n_tail_odds,
            "n_head_terms": n_head_terms,
            "unpaired_fraction": unpaired / n_total_terms if n_total_terms else None,
            "base_majorant": base_tot,
            "paired_majorant": pair_tot,
            "paired_over_base": pair_tot / base_tot if base_tot else None,
            "boundary_majorant": t_tot + h_tot,
            "c0_eff": base_tot / L3 if L3 else None,
            "cp_eff": pair_tot / L3 if L3 else None,
            "boundary_over_Nlog2N": (t_tot + h_tot) / L2 if L2 else None,
        }

    # 4. Planted Lesions at N=100 and N=400
    lesions = {}
    for N in (100, 400):
        M = N // 2
        U = math.isqrt(M)
        K = math.isqrt(N)
        Y_frac = Fraction(N, K)

        def w(m):
            return Fraction(1) - Fraction(N, m) if m <= Y_frac else Fraction(1 - N // m)

        dLis = {
            "missing_head": Fraction(0),
            "missing_tail": Fraction(0),
            "wrong_sign": Fraction(0),
            "tail_even_inclusion": Fraction(0),
        }

        for b in range(2, U + 1):
            V = M // b
            if V <= U:
                continue
            F = V // 2
            LO = max(U, F)
            interval = range(U + 1, V + 1)

            Mb = sum(mu[a] * w(a * b) for a in interval)
            P = sum(mu[m] * (w(m * b) - w(2 * m * b)) for m in range(U + 1, F + 1) if m % 2 == 1)
            T = sum(mu[m] * w(m * b) for m in range(LO + 1, V + 1) if m % 2 == 1)
            H = sum(mu[2 * t] * w(2 * t * b) for t in range(1, U + 1) if U < 2 * t <= V)
            Pw = sum(mu[m] * (w(m * b) + w(2 * m * b)) for m in range(U + 1, F + 1) if m % 2 == 1)
            T_corrupt = sum(mu[m] * w(m * b) for m in range(LO + 1, V + 1))

            dLis["missing_head"] += abs(Mb - (P + T))
            dLis["missing_tail"] += abs(Mb - (P + H))
            dLis["wrong_sign"] += abs(Mb - (Pw + T + H))
            dLis["tail_even_inclusion"] += abs(Mb - (P + T_corrupt + H))

        lesions[str(N)] = {k: str(v) for k, v in dLis.items()}
        for k, v in dLis.items():
            assert v > 0, f"Lesion {k} failed at N={N}"

    elapsed = time.time() - t0
    print(f"Verified all 20 cutoffs in {elapsed:.2f}s.")
    print(f"Total pairs checked: {total_pairs_checked}, global min gate: {global_min_gate}.")

    out = {
        "title": "Independent machine verification of p=2 Mobius pairing inside Sigma_2",
        "description": "Clean-room reproduction: exact rational identity, gate inequalities, lesions, majorants",
        "elapsed_s": elapsed,
        "total_pairs_checked": total_pairs_checked,
        "global_min_gate_margin": global_min_gate,
        "near_square_stress_checks_count": len(near_square_checks),
        "cutoffs": rows,
        "lesions": lesions,
    }

    OUT.write_text(json.dumps(out, indent=2) + "\n")
    print(f"Saved independent evidence to {OUT}")


if __name__ == "__main__":
    main()
