"""Low-rank matrix arm, Erdos #126 support run 99fc686a.

Checks, on the witnesses recorded by hunts/r_186989, the three structural
facts the low-rank reduction rests on:

  R1  M_ij = a_i + a_j has rank exactly 2 over Q (rank 1 only if |A| = 1).
  R2  the Alon-Solymosi *rectangle condition* holds for M, i.e.
      a_jj a_ik != a_jk a_ij  for i < j != k, which is the exact
      nondegeneracy hypothesis their Theorem 9 needs in place of
      "diagonal entries are not in Gamma".
  R3  the two-row reduction: for each ordered pair (a, b) of distinct
      elements of A, every other d in A gives a solution (a+d, b+d) of
      the two-variable S-unit equation X - Y = a - b, and the map
      d -> (a+d, b+d) is injective.  This is what turns rank 2 into a
      single 2-term unit equation, with no nondegeneracy hypothesis at all.

stdlib only.  Writes results.json.
"""

from fractions import Fraction
from itertools import combinations, permutations
import json
import os

# witnesses from hunts/r_186989/RESULTS.md section 3 (lower bounds on g(k))
WITNESSES = {
    1: ([2], [1, 3]),
    2: ([2, 3], [1, 5, 7, 11]),
    3: ([2, 3, 5], [1, 3, 7, 17, 47]),
    4: ([2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
    5: ([2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
    6: ([2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
    7: ([2, 3, 5, 7, 11, 13, 17],
        [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
}


def is_s_unit(n, S):
    """n a positive integer, all of whose prime factors lie in S."""
    if n <= 0:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def rank_over_Q(rows):
    """Exact Gaussian elimination over Fraction."""
    m = [[Fraction(x) for x in r] for r in rows]
    nrows, ncols = len(m), len(m[0])
    rank, piv = 0, 0
    for col in range(ncols):
        p = None
        for r in range(rank, nrows):
            if m[r][col] != 0:
                p = r
                break
        if p is None:
            continue
        m[rank], m[p] = m[p], m[rank]
        inv = m[rank][col]
        m[rank] = [v / inv for v in m[rank]]
        for r in range(nrows):
            if r != rank and m[r][col] != 0:
                f = m[r][col]
                m[r] = [a - f * b for a, b in zip(m[r], m[rank])]
        rank += 1
        piv = col
    return rank


def check_witness(k, S, A):
    out = {"k": k, "S": S, "A": A, "n": len(A)}

    # the hypothesis itself: every off-diagonal sum is an S-unit
    out["hypothesis_holds"] = all(
        is_s_unit(a + b, S) for a, b in combinations(A, 2))

    M = [[a + b for b in A] for a in A]

    # R1
    out["rank"] = rank_over_Q(M)

    # R2  rectangle condition: for i < j != k,  M_jj * M_ik != M_jk * M_ij
    n = len(A)
    viol = []
    for i in range(n):
        for j in range(n):
            for kk in range(n):
                if i < j and j != kk:
                    if M[j][j] * M[i][kk] == M[j][kk] * M[i][j]:
                        viol.append((i, j, kk))
    out["rectangle_condition"] = (len(viol) == 0)
    out["rectangle_violations"] = viol[:5]

    # how many diagonal entries 2a are themselves S-units -- the reason
    # Alon-Solymosi Theorem 1 does not apply and Theorem 9 is needed
    out["diagonal_in_Gamma"] = sum(1 for a in A if is_s_unit(2 * a, S))

    # R3  two-row reduction
    worst = 0
    inj_ok = True
    unit_eq_ok = True
    for a, b in permutations(A, 2):
        sols = set()
        for d in A:
            if d in (a, b):
                continue
            x, y = a + d, b + d
            if not (is_s_unit(x, S) and is_s_unit(y, S)):
                unit_eq_ok = False
            if x - y != a - b:
                unit_eq_ok = False
            sols.add((x, y))
        if len(sols) != len(A) - 2:
            inj_ok = False
        worst = max(worst, len(sols))
    out["two_row_reduction_valid"] = unit_eq_ok
    out["two_row_map_injective"] = inj_ok
    out["max_unit_eq_solutions_forced"] = worst

    # the classical and the S-unit-route bounds, at this k
    out["erdos_turan_bound"] = 3 * 2 ** (k - 1)
    out["evertse_route_bound"] = 2 + 3 * 7 ** (2 * k + 3)
    return out


def main():
    rows = [check_witness(k, S, A) for k, (S, A) in sorted(WITNESSES.items())]
    summary = {
        "all_hypotheses_hold": all(r["hypothesis_holds"] for r in rows),
        "all_rank_2": all(r["rank"] == 2 for r in rows),
        "all_rectangle_condition": all(r["rectangle_condition"] for r in rows),
        "all_two_row_reduction_valid": all(
            r["two_row_reduction_valid"] for r in rows),
        "all_two_row_map_injective": all(
            r["two_row_map_injective"] for r in rows),
    }
    doc = {"witness_checks": rows, "summary": summary}
    for k, v in summary.items():
        print(f"{k}: {v}")
    for r in rows:
        print(f"  k={r['k']} n={r['n']} rank={r['rank']} "
              f"diag_in_Gamma={r['diagonal_in_Gamma']} "
              f"forced_unit_eq_solutions={r['max_unit_eq_solutions_forced']}")
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "probe_out.json"), "w") as fh:
        json.dump(doc, fh, indent=2)
    return doc


if __name__ == "__main__":
    main()
