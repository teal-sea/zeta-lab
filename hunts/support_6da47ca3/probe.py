"""Arithmetic-graph arm for Erdos #126: audit of hunts/r_186989 plus the
K_{2,m} / S-unit-equation reduction measured inside a bounded universe.

Stdlib only.  Run:  python hunts/support_6da47ca3/probe.py
Writes hunts/support_6da47ca3/results.json.

Nothing here is evidence for or against RH (docs/08).
"""

import json
import os
import time
from itertools import combinations

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def is_smooth(n, S):
    """True iff n > 0 and every prime factor of n lies in S (trial division)."""
    if n <= 0:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def smooth_upto(N, S):
    """All S-smooth integers in [1, N], ascending."""
    out = [1]
    for p in S:
        new = []
        for v in out:
            w = v * p
            while w <= N:
                new.append(w)
                w *= p
        out.extend(new)
    return sorted(out)


# ---------------------------------------------------------------- arm A
# Exhaustive g_N(k): largest A subset of [1,N] with every off-diagonal
# a+b S-smooth.  Independent re-implementation, to audit r_186989's table.

def max_clique(N, S, cap_time=None):
    t0 = time.time()
    smooth = set(smooth_upto(2 * N, S))
    cand = list(range(1, N + 1))
    # adjacency by smooth sums
    adj = {a: set() for a in cand}
    for a in cand:
        for b in cand:
            if b > a and (a + b) in smooth:
                adj[a].add(b)
                adj[b].add(a)
    best = []
    exhaustive = True

    def expand(cur, pool):
        nonlocal best, exhaustive
        if cap_time is not None and time.time() - t0 > cap_time:
            exhaustive = False
            return
        if len(cur) > len(best):
            best = list(cur)
        if len(cur) + len(pool) <= len(best):
            return
        pool = list(pool)
        while pool:
            v = pool.pop(0)
            if len(cur) + 1 + len(pool) <= len(best):
                return
            expand(cur + [v], [w for w in pool if w in adj[v]])

    expand([], cand)
    return best, exhaustive


# ---------------------------------------------------------------- arm B
# The reduction's right-hand side, measured.  For x1 < x2 with c = x2 - x1,
# the y with y-x1 and y-x2 both S-units are exactly the solutions of
# u - v = c in S-units.  N2_N(k) = max over c of that count, inside [1,N].

def n2_measured(N, S):
    sm = smooth_upto(N, S)
    smset = set(sm)
    from collections import defaultdict
    tally = defaultdict(int)
    for u in sm:
        for v in sm:
            if v < u:
                tally[u - v] += 1
    if not tally:
        return 0, None
    c, m = max(tally.items(), key=lambda kv: (kv[1], -kv[0]))
    return m, c


# ---------------------------------------------------------------- arm C
# Refute r_186989's loose thread 3: "|A| <= p-1 when p not in S".

def best_avoiding(N, S, p):
    assert p not in S
    A, _ = max_clique(N, S)
    return A


def main():
    out = {
        "hunt": "support_6da47ca3",
        "question": "bipartite S-unit difference pattern for Erdos #126",
        "nothing_here_is_evidence_about_RH": True,
    }

    # --- audit: re-verify every witness printed by r_186989 -------------
    witnesses = {
        1: ([1, 3], [2]),
        2: ([1, 5, 7, 11], [2, 3]),
        3: ([1, 3, 7, 17, 47], [2, 3, 5]),
        4: ([1, 2, 3, 5, 7, 13], [2, 3, 5, 7]),
        5: ([1, 2, 5, 9, 13, 19, 23, 31], [2, 3, 5, 7, 11]),
        6: ([1, 2, 3, 5, 7, 9, 13, 19, 23, 47], [2, 3, 5, 7, 11, 13]),
        7: ([1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49], [2, 3, 5, 7, 11, 13, 17]),
    }
    audit = {}
    for k, (A, S) in witnesses.items():
        bad = [(a, b, a + b) for a, b in combinations(A, 2) if not is_smooth(a + b, S)]
        audit[k] = {
            "witness": A,
            "S": S,
            "size": len(A),
            "all_sums_S_smooth": not bad,
            "violations": bad,
            "max_element": max(A),
        }
    out["audit_r_186989_witnesses"] = audit

    # --- independent exhaustive g_N(k), small N (the claim is that the
    #     optima live far below the box, so a small box must reproduce them)
    gn = {}
    for k, N in [(1, 200), (2, 200), (3, 200), (4, 120), (5, 90)]:
        S = PRIMES[:k]
        A, ex = max_clique(N, S)
        gn[k] = {"N": N, "S": S, "g_N": len(A), "witness": sorted(A),
                 "exhaustive": ex}
    out["independent_g_N"] = gn

    # --- arm B: N2 measured, the reduction's right-hand side ------------
    n2 = {}
    for k, N in [(1, 10 ** 6), (2, 10 ** 6), (3, 10 ** 6), (4, 10 ** 5), (5, 10 ** 5)]:
        S = PRIMES[:k]
        m, c = n2_measured(N, S)
        n2[k] = {"N": N, "S": S, "N2_measured": m, "argmax_c": c,
                 "reduction_upper_bound_on_g": m + 2}
    out["n2_measured"] = n2

    # --- arm C: refute "|A| <= p-1 when p not in S" ----------------------
    # p = 3 not in S = {2,5}: exhibit |A| = 3, and search for the max.
    ce = []
    for S, p in [([2, 5], 3), ([2, 7], 3), ([2, 5, 7], 3), ([2, 3, 7], 5)]:
        A, ex = max_clique(400 if len(S) < 3 else 200, S)
        ce.append({"S": S, "p_absent": p, "claimed_cap": p - 1,
                   "measured_max": len(A), "witness": sorted(A),
                   "refutes_cap": len(A) > p - 1})
    out["loose_thread_3_test"] = ce

    # --- the K_{2,m} chain on a concrete witness ------------------------
    # For the k=5 witness, show the anchor pair (a1,a2) and the m solutions.
    A, S = witnesses[5]
    a1, a2 = A[0], A[1]
    c = a1 - a2
    sols = [(x + a1, x + a2) for x in A[2:]]
    out["chain_demo"] = {
        "A": A, "S": S, "anchors": [a1, a2], "c": c,
        "solutions_u_minus_v_equals_c": [[u, v] for u, v in sols],
        "all_u_smooth": all(is_smooth(u, S) for u, _ in sols),
        "all_v_smooth": all(is_smooth(v, S) for _, v in sols),
        "differences_all_equal_c": all(u - v == c for u, v in sols),
        "count": len(sols),
    }

    # --- the theorem-level reduction, as data --------------------------
    out["reduction"] = {
        "statement": (
            "g(k) <= N2(k) + 2, where N2(k) = max over |S|=k and c in Q* of "
            "#{(u,v) in (Z_S^*)^2 : u - v = c}."
        ),
        "proof_sketch": (
            "Fix a1 != a2 in A, c = a1 - a2. For every other x in A the pair "
            "(u,v) = (x+a1, x+a2) consists of S-units with u - v = c, and x "
            "is recovered as u - a1, so the map is injective."
        ),
        "uses_only_pattern": "K_{2,m} (two anchors joined to m vertices)",
        "explicit_corollary": {
            "input": "Evertse 1984, Invent. Math. 75: alpha*x + beta*y = 1 in "
                     "S-units of a degree-d field with s places has at most "
                     "3 * 7^(d + 2s) solutions; here d = 1, s = k + 1.",
            "bound_on_g": "g(k) <= 3 * 7^(2k+3) + 2",
            "log_slope": 2.0 * __import__("math").log(7),
            "bound_on_f": "f(n) > k whenever n > 2 + 3*7^(2k+3); i.e. "
                          "f(n) >= (log(n-2) - log 3)/(2 log 7) - 3/2",
        },
        "conditional": (
            "If log N2(k) = o(k) then Erdos #126 holds. The known lower "
            "bounds on S-unit-equation solution counts (Erdos-Stewart-"
            "Tijdeman 1988; Konyagin-Soundararajan 2007, exp(k^(2-sqrt2-o(1)))) "
            "are all exp(k^theta) with theta < 1, so log N2(k) = o(k) is "
            "consistent with everything known and is the expected truth. "
            "Sufficient, not necessary: the reduction is measurably lossy."
        ),
        "improvement_from_within_part_structure": (
            "None in the exponent. The extra sums buy a free nondegeneracy "
            "guarantee for the 4-term relation (a+b)+(c+d)=(a+c)+(b+d), "
            "but routing through it needs 3-term unit equations whose best "
            "uniform bound exp((6n)^(3n)(r+1)) with n=3 is exp(~2e11 * k), "
            "vastly worse than 7^(2k)."
        ),
    }

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
    print(json.dumps(out, indent=2, sort_keys=True)[:4000])


if __name__ == "__main__":
    main()
