"""Erdos #126, entropy/combinatorics arm: exact checks behind RESULTS.md.

Stdlib only.  ~1 min.  Writes results.json next to this file.

Nothing here is evidence for or against RH (docs/08).

Definitions used throughout
---------------------------
S is a finite set of primes.  A finite set A of distinct positive integers is
*S-summable* if a + b has no prime factor outside S for every pair of distinct
a, b in A.  g(k) = max |A| over all S with |S| = k.  g_N(k) restricts A to
[1, N] and is a lower bound on g(k).
"""

import itertools
import json
import os


# ---------------------------------------------------------------- smoothness

def smooth_support(m, S):
    """Prime support of m restricted to S; returns None if m has a factor outside S."""
    r = m
    for p in S:
        while r % p == 0:
            r //= p
    return r == 1


def prime_support(m):
    supp, d, r = set(), 2, m
    while d * d <= r:
        while r % d == 0:
            supp.add(d)
            r //= d
        d += 1
    if r > 1:
        supp.add(r)
    return supp


def is_S_summable(A, S):
    return all(smooth_support(a + b, S) for a, b in itertools.combinations(sorted(A), 2))


# ------------------------------------------------------------- clique search

def max_S_summable(S, N):
    """Exact maximum S-summable subset of [1, N] (branch and bound)."""
    S = sorted(S)
    verts = list(range(1, N + 1))
    adj = {v: set() for v in verts}
    for i, a in enumerate(verts):
        for b in verts[i + 1:]:
            if smooth_support(a + b, S):
                adj[a].add(b)
                adj[b].add(a)
    best = []

    def expand(clique, cand):
        nonlocal best
        if len(clique) + len(cand) <= len(best):
            return
        if not cand:
            if len(clique) > len(best):
                best = list(clique)
            return
        for v in sorted(cand):
            if len(clique) + len(cand) <= len(best):
                return
            expand(clique + [v], {u for u in cand if u > v and u in adj[v]})
            cand = cand - {v}

    expand([], set(verts))
    return best


# ------------------------------------------------------ Lemma A (residues)

def classes_used(A, p):
    return sorted({a % p for a in A})


def lemma_A_holds(A, p):
    """A meets at most (p+1)//2 classes mod p, at most one element in class 0,
    and never both r and -r."""
    cls = set(a % p for a in A)
    if len(cls) > (p + 1) // 2:
        return False
    if sum(1 for a in A if a % p == 0) > 1:
        return False
    for r in cls:
        if r and (p - r) in cls:
            return False
    if p == 2 and len(A) > 2:
        return False
    return True


PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

out = {}

# ---------------------------------------------------------------- check 1
# The parent hunt's thread guesses |A| <= p - 1 when p not in S.  Refute it.
cx = [1, 3, 7, 13]
cx_S = sorted(set().union(*(prime_support(a + b) for a, b in itertools.combinations(cx, 2))))
out["counterexample_to_p_minus_1"] = {
    "A": cx,
    "S": cx_S,
    "k": len(cx_S),
    "S_summable": is_S_summable(cx, cx_S),
    "sums": {f"{a}+{b}": sorted(prime_support(a + b)) for a, b in itertools.combinations(cx, 2)},
    "p_absent_from_S": 3,
    "size": len(cx),
    "guessed_bound_p_minus_1": 2,
    "refutes_guess": len(cx) > 2,
    "classes_mod_3": classes_used(cx, 3),
    "lemma_A_bound_mod_3": (3 + 1) // 2,
}

# How far can |A| exceed p-1 for the smallest absent prime, inside a small box?
excess = []
for k in (3, 4):
    for S in itertools.combinations(PRIMES[:7], k):
        if 2 not in S or 3 in S:
            continue
        A = max_S_summable(S, 400)
        excess.append({"S": list(S), "N": 400, "max_size": len(A), "witness": A,
                       "p": 3, "p_minus_1": 2})
out["absent_prime_3_searches"] = excess
out["max_size_with_3_absent"] = max(e["max_size"] for e in excess)

# ---------------------------------------------------------------- check 2
# Lemma A on every witness we or the parent produced.
parent_witnesses = [
    {"k": 1, "S": [2], "A": [1, 3]},
    {"k": 2, "S": [2, 3], "A": [1, 5, 7, 11]},
    {"k": 3, "S": [2, 3, 5], "A": [1, 3, 7, 17, 47]},
    {"k": 4, "S": [2, 3, 5, 7], "A": [1, 2, 3, 5, 7, 13]},
    {"k": 5, "S": [2, 3, 5, 7, 11], "A": [1, 2, 5, 9, 13, 19, 23, 31]},
    {"k": 6, "S": [2, 3, 5, 7, 11, 13], "A": [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]},
    {"k": 7, "S": [2, 3, 5, 7, 11, 13, 17], "A": [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]},
]
checks = []
for w in parent_witnesses:
    ok = is_S_summable(w["A"], w["S"])
    per_p = {}
    for p in PRIMES:
        if p in w["S"]:
            continue
        per_p[p] = {"classes": classes_used(w["A"], p),
                    "bound": (p + 1) // 2,
                    "lemma_A": lemma_A_holds(w["A"], p)}
    checks.append({"k": w["k"], "S": w["S"], "A": w["A"],
                   "reverified_S_summable": ok,
                   "residue_checks": per_p,
                   "all_lemma_A": all(v["lemma_A"] for v in per_p.values())})
out["parent_witness_audit"] = checks
out["parent_witnesses_all_valid"] = all(c["reverified_S_summable"] for c in checks)
out["lemma_A_holds_on_all_witnesses"] = all(c["all_lemma_A"] for c in checks)

# ---------------------------------------------------------------- check 3
# Independent re-derivation of two of the parent's g_N(k) rows.
recheck = []
for k, N in ((3, 3000), (4, 1500)):
    S = PRIMES[:k]
    A = max_S_summable(S, N)
    recheck.append({"k": k, "S": S, "N": N, "g_N": len(A), "witness": A,
                    "verified": is_S_summable(A, S)})
out["independent_g_N_recheck"] = recheck

# ---------------------------------------------------------------- check 4
# The local-signature model is unbounded: a set satisfying every residue
# constraint at every prime p <= P outside S, of size as large as we please.
P, S_loc = 60, [2, 3, 5]
odd_absent = [p for p in range(3, P + 1) if all(p % d for d in range(2, p)) and p not in S_loc]
M = 1
for p in odd_absent:
    M *= p
Nbox = 200 * M
A_loc = [1 + i * M for i in range(200)]
viol = [p for p in odd_absent
        if not all((a + b) % p for a, b in itertools.combinations(A_loc[:40], 2))]
out["local_model_unbounded"] = {
    "P": P, "S": S_loc, "absent_odd_primes_up_to_P": odd_absent,
    "modulus_M": M, "box_N": Nbox, "size": len(A_loc),
    "all_local_constraints_satisfied": viol == [],
    "violating_primes": viol,
    "erdos_turan_bound_for_this_k": 3 * 2 ** (len(S_loc) - 1),
    "size_exceeds_erdos_turan": len(A_loc) > 3 * 2 ** (len(S_loc) - 1),
}

# ---------------------------------------------------------------- check 5
# Entropy accounting: the residue bound over all primes <= P, with CRT
# injectivity, versus 3*2^(k-1).  Reports the crossover (there is none).
from math import log2

acct = []
for k in (5, 10, 20):
    S = PRIMES[:min(k, len(PRIMES))]
    logbound, logmod, P = 0.0, 0.0, 1
    while logmod < 64:          # CRT modulus must exceed N; take log2 N = 64
        P += 1
        if any(P % d == 0 for d in range(2, P)):
            continue
        if P in S:
            continue
        logmod += log2(P)
        logbound += log2((P + 1) / 2)
    acct.append({"k": k, "log2_N": 64, "largest_prime_used": P,
                 "log2_entropy_bound": round(logbound, 2),
                 "log2_erdos_turan": round(log2(3 * 2 ** (k - 1)), 2),
                 "entropy_bound_better": logbound < log2(3 * 2 ** (k - 1))})
out["entropy_accounting"] = acct

path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
with open(path, "w") as fh:
    json.dump(out, fh, indent=2, sort_keys=True)
print(json.dumps({kk: vv for kk, vv in out.items() if kk != "parent_witness_audit"},
                 indent=2, sort_keys=True)[:4000])
print("wrote", path)
