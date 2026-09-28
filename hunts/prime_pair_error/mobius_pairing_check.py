"""Exact check of the p=2 Mobius pairing inside Sigma_2 (MOBIUS_PAIRING.md).

Exact rational (Fraction) identity M_b = P_b + T_b + H_b (+ Z_b = 0) per b,
ab > Y gate assertion, mu(2m)=-mu(m) assertions, square/prime-power mu spots,
missing-boundary and wrong-sign lesions, before/after per-b coefficient match,
and baseline-vs-paired majorant totals. Floats only for log weights and ratios
(diagnostics, never proofs). N <= 10000. Estimate: ~20k Fraction terms at the
largest N, predicted < 60 s total.
"""

import json
import math
import time
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "results_mobius_pairing.json"

N_LIST = [12, 13, 14, 15, 16, 20, 25, 27, 32, 36, 49, 64, 81, 100, 121, 144,
          200, 400, 1000, 10000]


def sieve_mu(n_max):
    """Exact integer mu via prime-factor parity + squarefree flag."""
    sign = [1] * (n_max + 1)
    sqfree = [True] * (n_max + 1)
    for p in range(2, n_max + 1):
        is_p_prime = True
        for q in range(2, int(p ** 0.5) + 1):
            if p % q == 0:
                is_p_prime = False
                break
        if is_p_prime:
            for j in range(p, n_max + 1, p):
                sign[j] *= -1
            for j in range(p * p, n_max + 1, p * p):
                sqfree[j] = False
    mu = [0] * (n_max + 1)
    mu[1] = 1
    for i in range(2, n_max + 1):
        mu[i] = 0 if not sqfree[i] else sign[i]
    return mu


def main():
    t0 = time.time()
    mu = sieve_mu(10000)

    # Independent oracle: sympy.mobius over the full range + divisor-sum identity.
    from sympy import mobius as sym_mobius
    for n in range(1, 10001):
        assert mu[n] == int(sym_mobius(n)), n
    for n in range(1, 201):
        s = sum(mu[d] for d in range(1, n + 1) if n % d == 0)
        assert s == (1 if n == 1 else 0), n

    # mu spot checks: squares / prime powers are 0; nonsquares have sign.
    spots = {4: 0, 8: 0, 9: 0, 25: 0, 27: 0, 36: 0, 49: 0, 121: 0,
             6: 1, 30: -1, 2: -1, 3: -1, 5: -1, 7: -1, 10: 1, 15: 1}
    for n, want in spots.items():
        assert mu[n] == want, (n, mu[n], want)

    # sign identity on all in-range m: mu(2m) == -mu(m) for odd m; 0 for even m.
    for m in range(1, 5001, 2):
        if mu[m] != 0:
            assert mu[2 * m] == -mu[m], m
        else:
            assert mu[2 * m] == 0, m
    for m in range(2, 5001, 2):
        assert mu[2 * m] == 0, m  # 4 | 2m

    rows = {}
    lesions = {}
    for N in N_LIST:
        M = N // 2
        U = math.isqrt(M)
        Yf = Fraction(N, math.isqrt(N))

        def w(m):
            return Fraction(1) - Fraction(N, m) if m <= Yf else Fraction(1 - N // m)

        max_defect = Fraction(0)
        gate_min_num = None  # min of (a*b*K - N) over pairs, must be > 0
        K = math.isqrt(N)
        n_tail_terms = 0
        n_head_terms = 0
        n_pair_terms = 0
        n_total_terms = 0
        base_tot = 0.0
        pair_tot = 0.0
        sig2_true = 0.0
        empty_b = 0
        vacuous_pair_b = 0
        for b in range(2, U + 1):
            V = M // b
            if V <= U:
                empty_b += 1
                continue
            F = V // 2
            LO = max(U, F)
            # gate: every pair product exceeds Y
            for a in range(U + 1, V + 1):
                g = a * b * K - N
                gate_min_num = g if gate_min_num is None else min(gate_min_num, g)
            Mb = Fraction(0)
            for a in range(U + 1, V + 1):
                n_total_terms += 1
                Mb += mu[a] * w(a * b)
            P = Fraction(0)
            for m in range(U + 1, F + 1):
                if m % 2 == 1:
                    P += mu[m] * (w(m * b) - w(2 * m * b))
                    n_pair_terms += 1
            T = Fraction(0)
            for m in range(LO + 1, V + 1):
                if m % 2 == 1:
                    T += mu[m] * w(m * b)
                    n_tail_terms += 1
            H = Fraction(0)
            for t in range(1, U + 1):
                if U < 2 * t <= V:
                    H += mu[2 * t] * w(2 * t * b)
                    n_head_terms += 1
            Z = Fraction(0)
            for m in range(U + 1, F + 1):
                if m % 2 == 0 and (m // 2) % 2 == 0:
                    assert mu[m] == 0, m
                    Z += mu[m] * w(m * b)
            assert Z == 0
            d = abs(Mb - (P + T + H))
            max_defect = max(max_defect, d)
            assert d == 0, (N, b, d)
            if F <= U:
                vacuous_pair_b += 1
            lb = math.log(b)
            sig2_true += lb * float(Mb)
            # majorants (floats; diagnostics)
            Bb = sum(N / (a * b) for a in range(U + 1, V + 1))
            Pm = sum(N / (2 * m * b) + 1 for m in range(U + 1, F + 1) if m % 2 == 1)
            Tm = sum(N / (m * b) for m in range(LO + 1, V + 1) if m % 2 == 1)
            Hm = sum(N / (2 * t * b) for t in range(1, U + 1) if U < 2 * t <= V)
            base_tot += lb * Bb
            pair_tot += lb * (Pm + Tm + Hm)
        assert max_defect == 0
        assert gate_min_num is not None and gate_min_num > 0, (N, gate_min_num)
        unpaired = n_tail_terms + n_head_terms
        rows[str(N)] = {
            "max_fraction_defect": str(max_defect),
            "gate_min_abK_minus_N": gate_min_num,
            "sig2_true": sig2_true,
            "baseline_majorant": base_tot,
            "paired_majorant": pair_tot,
            "paired_over_baseline": pair_tot / base_tot if base_tot else None,
            "n_total_terms": n_total_terms,
            "n_paired_odds": n_pair_terms,
            "n_tail_odds": n_tail_terms,
            "n_head_terms": n_head_terms,
            "unpaired_fraction": unpaired / n_total_terms if n_total_terms else None,
            "n_empty_b": empty_b,
            "n_vacuous_pair_b": vacuous_pair_b,
        }

    # Lesions (exact Fraction defects, must be nonzero) at N=400 and N=100.
    for N in (100, 400):
        M = N // 2
        U = math.isqrt(M)
        Yf = Fraction(N, math.isqrt(N))

        def w(m):
            return Fraction(1) - Fraction(N, m) if m <= Yf else Fraction(1 - N // m)

        dLis = {"missing_head": Fraction(0), "missing_tail": Fraction(0),
                "wrong_sign": Fraction(0)}
        for b in range(2, U + 1):
            V = M // b
            if V <= U:
                continue
            F = V // 2
            LO = max(U, F)
            Mb = sum((mu[a] * w(a * b) for a in range(U + 1, V + 1)), Fraction(0))
            P = sum((mu[m] * (w(m * b) - w(2 * m * b))
                     for m in range(U + 1, F + 1) if m % 2 == 1), Fraction(0))
            T = sum((mu[m] * w(m * b)
                     for m in range(LO + 1, V + 1) if m % 2 == 1), Fraction(0))
            H = sum((mu[2 * t] * w(2 * t * b)
                     for t in range(1, U + 1) if U < 2 * t <= V), Fraction(0))
            Pw = sum((mu[m] * (w(m * b) + w(2 * m * b))
                      for m in range(U + 1, F + 1) if m % 2 == 1), Fraction(0))
            dLis["missing_head"] += abs(Mb - (P + T))
            dLis["missing_tail"] += abs(Mb - (P + H))
            dLis["wrong_sign"] += abs(Mb - (Pw + T + H))
        lesions[str(N)] = {k: str(v) for k, v in dLis.items()}
        for k, v in dLis.items():
            assert v != 0, (N, k)

    out = {
        "description": "Exact p=2 Mobius pairing check inside Sigma_2 "
                       "(identity, gate, lesions, majorant comparison)",
        "base": "a626c916a0082e59b2c4c0eca83035e948160d3e",
        "N_list": N_LIST,
        "mu_spots_ok": True,
        "sign_identity_ok": True,
        "rows": rows,
        "lesions_exact_nonzero_defects": lesions,
        "note": "Ratios are finite-N diagnostics only; they prove no asymptotics.",
        "elapsed_s": time.time() - t0,
    }
    OUT.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({n: rows[n] for n in ("100", "1000", "10000")}, indent=2))
    print("lesions:", json.dumps(lesions))
    print("elapsed_s:", out["elapsed_s"])


if __name__ == "__main__":
    main()
