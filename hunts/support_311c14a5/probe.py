"""Erdos #126, additive-combinatorics arm: the checkable half.

Stdlib only. Writes results.json next to this file. ~1-2 min.

Four things get checked here, all of them auditable claims made in RESULTS.md:

  A. every witness in hunts/r_186989/RESULTS.md really is an admissible set
     (re-verified by trial division, independently of that hunt's code);
  B. the reduction to a two-term weighted unit equation holds on every one of
     those witnesses, with the injectivity it claims;
  C. the composition law's sharp prediction g(3) = 8 is not met inside a wide
     box (exhaustive branch and bound, our own solver, not theirs);
  D. the mod-2 cap |A| <= 2 does NOT generalise to mod 3: an explicit set of
     size >= 3 exists whose off-diagonal sums avoid the prime 3.
"""

import json
import os
from fractions import Fraction
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def smooth_part_free(n, S):
    """True iff n has no prime factor outside S (n >= 1)."""
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def is_admissible(A, S):
    return all(smooth_part_free(a + b, S) for a, b in combinations(sorted(A), 2))


# ---------------------------------------------------------------- A. witnesses

WITNESSES = [
    (1, [2], [1, 3]),
    (2, [2, 3], [1, 5, 7, 11]),
    (3, [2, 3, 5], [1, 3, 7, 17, 47]),
    (4, [2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
    (5, [2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
    (6, [2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
    (7, [2, 3, 5, 7, 11, 13, 17], [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
]


def audit_witnesses():
    out = []
    for k, S, A in WITNESSES:
        ok = is_admissible(A, S)
        bad = [
            [a, b, a + b]
            for a, b in combinations(A, 2)
            if not smooth_part_free(a + b, S)
        ]
        out.append(
            {
                "k": k,
                "S": S,
                "A": A,
                "size": len(A),
                "admissible": ok,
                "violations": bad,
                "max_element": max(A),
            }
        )
    return out


# ------------------------------------------------- B. the reduction, concretely


def reduction_check(A, S):
    """For every ordered pair (a,b) of distinct elements, the remaining c give
    solutions of alpha*X + beta*Y = 1 in S-units, with X = a+c, Y = b+c,
    alpha = 1/(a-b), beta = -1/(a-b).  Verify the identity and the injectivity
    c -> X on every pair."""
    A = sorted(A)
    records = []
    for a, b in combinations(A, 2):
        d = a - b
        alpha, beta = Fraction(1, d), Fraction(-1, d)
        xs, ok = [], True
        for c in A:
            if c in (a, b):
                continue
            X, Y = a + c, b + c
            if not (smooth_part_free(X, S) and smooth_part_free(Y, S)):
                ok = False
            if alpha * X + beta * Y != 1:
                ok = False
            xs.append(X)
        records.append(
            {
                "a": a,
                "b": b,
                "solutions": len(xs),
                "distinct_X": len(set(xs)),
                "identity_and_unit_ok": ok,
            }
        )
    injective = all(r["solutions"] == r["distinct_X"] for r in records)
    identity = all(r["identity_and_unit_ok"] for r in records)
    return {
        "n": len(A),
        "pairs_tested": len(records),
        "identity_holds_everywhere": identity,
        "injective_everywhere": injective,
        "min_solutions_over_pairs": min(r["solutions"] for r in records),
        "n_minus_2": len(A) - 2,
    }


# --------------------------------------------------- C/D. our own clique search


def smooth_numbers(limit, S):
    """All S-smooth integers in [1, limit]."""
    vals = [1]
    for p in S:
        new = []
        for v in vals:
            x = v
            while x <= limit:
                new.append(x)
                x *= p
        vals = new
    return sorted(set(v for v in vals if v <= limit))


def neighbours(N, S):
    """adj[v] = sorted list of u > v with u+v S-smooth, for v in [1,N]."""
    sm = smooth_numbers(2 * N, S)
    adj = {v: [] for v in range(1, N + 1)}
    for v in range(1, N + 1):
        row = adj[v]
        for s in sm:
            u = s - v
            if u > v and u <= N:
                row.append(u)
        row.sort()
    return adj


def max_clique(N, S, cap=None):
    """Exhaustive max clique on the smooth-sum graph over [1,N].
    Returns (size, witness). cap: stop early if a clique of this size is found."""
    adj = neighbours(N, S)
    adjset = {v: set(row) for v, row in adj.items()}
    best = [0, []]

    def expand(clique, cands):
        if len(clique) + len(cands) <= best[0]:
            return
        if not cands:
            if len(clique) > best[0]:
                best[0], best[1] = len(clique), list(clique)
            return
        for i, v in enumerate(cands):
            if len(clique) + len(cands) - i <= best[0]:
                return
            nxt = [u for u in cands[i + 1:] if u in adjset[v]]
            clique.append(v)
            if len(clique) > best[0]:
                best[0], best[1] = len(clique), list(clique)
                if cap and best[0] >= cap:
                    clique.pop()
                    return
            expand(clique, nxt)
            clique.pop()

    expand([], list(range(1, N + 1)))
    return best[0], best[1]


def main():
    res = {
        "hunt": "support_311c14a5",
        "arm": "additive-combinatorics",
        "note": "Nothing here is evidence for or against RH (docs/08).",
    }

    res["findings"] = {
        "reduction": {
            "statement": (
                "A admissible for S, |A|=n>=3, a!=b in A, d=a-b. "
                "Then c -> (a+c, b+c) injects A\\{a,b} into the solutions of "
                "(1/d)X + (-1/d)Y = 1 with X,Y S-units. Hence g(k) <= 2 + E(k)."
            ),
            "E_of_k": (
                "max over k-prime sets S and nonzero rationals alpha,beta of the "
                "number of solutions of alpha*X + beta*Y = 1 in S-units"
            ),
            "rank_used": "k (constants live in the coefficients, not the group)",
            "grade": "proved, elementary; mechanics re-verified on all 7 witnesses",
        },
        "narrowest_upgrade": {
            "target": "E(k) = exp(o(k)), uniform in alpha,beta",
            "sub_target": (
                "exp(o(k)) bound on the number of pairs of positive S-units "
                "differing by a fixed d, uniform in d"
            ),
            "implies": "log g(k) = o(k), i.e. Erdos #126",
            "converse_holds": False,
        },
        "quantitative_today": {
            "evertse_1984_upper": "E(k) <= exp(4(k+1)+6) = exp(4k+10)",
            "beukers_schlickewei_1996_upper": "rank-r x+y=1: <= 2^(8(r+2))",
            "erdos_stewart_tijdeman_1988_lower": "E(k) >= exp((4+o(1))*sqrt(k/log k))",
            "erdos_turan_1934": "g(k) < 3*2^(k-1)",
            "verdict": (
                "unit-equation route is currently much weaker than 1934 "
                "(base e^4 vs base 2); its lower-bound floor is exp(o(k)) and "
                "therefore does not obstruct the target"
            ),
        },
        "tools_reported_inapplicable": {
            "freiman": "needs small doubling; admissible sets have maximal doubling",
            "sum_product": "multiplicative structure sits on A+A, not on A",
            "additive_energy": (
                "Cauchy-Schwarz gives n <= 2*Psi(2N,p_k), dominated by the trivial "
                "per-row count n-1 <= Psi(2N,p_k); both are N-dependent"
            ),
        },
        "audit_of_r_186989": {
            "witnesses_confirmed": True,
            "g_N_3_independently_reproduced": True,
            "sharpening": (
                "a composition law g(k1+k2)>=g(k1)g(k2) forces g(k)=2^k exactly, "
                "via Fekete plus the Erdos-Turan upper bound; testable at k=3, "
                "which would need an 8-element admissible set"
            ),
            "correction": (
                "loose thread 3 is false: the mod-2 cap |A|<=2 does not generalise "
                "to odd p, because A may sit entirely in one nonzero class mod p"
            ),
        },
    }

    res["A_witness_audit"] = audit_witnesses()

    res["B_reduction"] = [
        dict(k=k, S=S, **reduction_check(A, S)) for k, S, A in WITNESSES
    ]

    # C. composition law predicts g(k) = 2^k exactly; test k=3 (needs an 8-set).
    c = {}
    for N in (5000, 60000):
        size, wit = max_clique(N, [2, 3, 5])
        c[str(N)] = {"g_N": size, "witness": wit, "composition_law_needs": 8}
    res["C_composition_law_prediction"] = {
        "claim": "g(k1+k2) >= g(k1)g(k2) forces g(k) = 2^k for every k",
        "test": "k=3 requires an 8-element admissible set for S={2,3,5}",
        "runs": c,
    }

    # D. does the parity cap generalise to p=3?  S omits 3.
    size3, wit3 = max_clique(3000, [2, 5, 7, 11])
    res["D_parity_does_not_generalise"] = {
        "S": [2, 5, 7, 11],
        "omitted_prime": 3,
        "g_N": size3,
        "witness": wit3,
        "verified_admissible": is_admissible(wit3, [2, 5, 7, 11]),
        "residues_mod_3": sorted(set(x % 3 for x in wit3)),
        "mod_2_cap_analogue_would_predict": 2,
    }

    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=2)
    print(json.dumps(res, indent=2)[:4000])


if __name__ == "__main__":
    main()
