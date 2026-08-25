"""Independent re-derivation of the finite data in hunts/r_186989.

Written from the problem statement, not from the prior hunt's probe.py.
Stdlib only.  `python3 hunts/support_eccd5f5e/audit.py` (~1-2 min).
"""

import itertools
import json
import sys
from pathlib import Path

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def smooth_set(S, limit):
    """All S-smooth integers in [1, limit], by sieving multiplicatively."""
    out = {1}
    for p in S:
        new = set()
        for v in out:
            w = v * p
            while w <= limit:
                new.add(w)
                w *= p
        out |= new
    return out


def max_clique(S, N):
    """Exact maximum |A|, A subset of [1,N], all pairwise sums S-smooth.

    Bitset branch and bound.  Returns (size, witness).
    """
    sm = smooth_set(S, 2 * N)
    adj = [0] * (N + 1)
    for a in range(1, N + 1):
        for b in range(a + 1, N + 1):
            if a + b in sm:
                adj[a] |= 1 << b
                adj[b] |= 1 << a  # the graph is undirected; an asymmetric
                # adjacency silently caps every clique at 1.

    best = [0, ()]

    def expand(cur, cand):
        if len(cur) > best[0]:
            best[0] = len(cur)
            best[1] = tuple(cur)
        while cand:
            if len(cur) + bin(cand).count("1") <= best[0]:
                return
            v = cand.bit_length() - 1  # take largest first
            cand &= ~(1 << v)
            expand(cur + [v], cand & adj[v])

    full = 0
    for a in range(1, N + 1):
        full |= 1 << a
    expand([], full)
    return best[0], tuple(sorted(best[1]))


def verify(A, S):
    """Re-verify a witness from scratch by trial division."""
    Sset = set(S)
    for a, b in itertools.combinations(A, 2):
        n = a + b
        d = 2
        while d * d <= n:
            if n % d == 0:
                if d not in Sset:
                    return False
                while n % d == 0:
                    n //= d
            d += 1
        if n > 1 and n not in Sset:
            return False
    return True


def main():
    out = {}

    # --- Claim A: reproduce the g_N(k) table for S = first k primes.
    firstk = []
    for k, N in [(1, 2000), (2, 2000), (3, 1200), (4, 800), (5, 600), (6, 400), (7, 300)]:
        S = PRIMES[:k]
        n, A = max_clique(S, N)
        ok = verify(A, S)
        firstk.append({"k": k, "S": S, "N": N, "g_N": n, "witness": list(A), "verified": ok})
        print(f"k={k} S={S} N={N} -> {n}  {A}  verified={ok}", flush=True)
    out["first_k_primes"] = firstk

    # --- Claim B: does optimising S over ALL k-subsets beat the first k primes?
    best_over_S = []
    for k, pool, N in [(2, 8, 800), (3, 8, 600), (4, 8, 400)]:
        rows = []
        for S in itertools.combinations(PRIMES[:pool], k):
            n, A = max_clique(list(S), N)
            rows.append((n, list(S), list(A)))
        rows.sort(reverse=True)
        top = rows[0]
        assert verify(top[2], top[1])
        best_over_S.append(
            {
                "k": k,
                "pool": PRIMES[:pool],
                "N": N,
                "best": top[0],
                "best_S": top[1],
                "witness": top[2],
                "first_k_primes_value": next(r[0] for r in rows if r[1] == PRIMES[:k]),
                "all_ties": [r[1] for r in rows if r[0] == top[0]],
            }
        )
        print(f"k={k} best over all {k}-subsets of {PRIMES[:pool]} at N={N}: "
              f"{top[0]} with S={top[1]} {top[2]}", flush=True)
    out["best_over_S"] = best_over_S

    # --- Claim C: the omitted-prime heuristic |A| <= p-1 for p not in S.
    # Counterexample from the prior hunt's OWN table: S = {2,5,7}, 3 not in S.
    ce = {"S": [2, 5, 7], "A": [1, 3, 7, 13], "omitted_prime": 3}
    ce["all_sums_smooth"] = verify(ce["A"], ce["S"])
    ce["heuristic_bound"] = 2  # p - 1
    ce["actual"] = len(ce["A"])
    ce["refuted"] = ce["all_sums_smooth"] and ce["actual"] > ce["heuristic_bound"]
    print("omitted-prime counterexample:", ce, flush=True)

    # unbounded family with 3 not in S: A = {1, 4, 7, ..., 3m-2}
    fam = []
    for m in range(2, 9):
        A = [3 * i + 1 for i in range(m)]
        sums = {a + b for a, b in itertools.combinations(A, 2)}
        prs = set()
        for n in sums:
            d = 2
            while d * d <= n:
                if n % d == 0:
                    prs.add(d)
                    while n % d == 0:
                        n //= d
                d += 1
            if n > 1:
                prs.add(n)
        fam.append({"m": m, "A": A, "k": len(prs), "S": sorted(prs), "3_in_S": 3 in prs})
    print("AP family (3 never divides a sum):", [(f["m"], f["k"], f["3_in_S"]) for f in fam], flush=True)
    out["omitted_prime"] = {"counterexample": ce, "ap_family": fam}

    # --- Claim D: f and f_0 small values, exhaustive over [0, 40] and [1, 40].
    def prime_support_size(A):
        prs = set()
        for a, b in itertools.combinations(A, 2):
            n = a + b
            d = 2
            while d * d <= n:
                if n % d == 0:
                    prs.add(d)
                    while n % d == 0:
                        n //= d
                d += 1
            if n > 1:
                prs.add(n)
        return len(prs)

    f_tab, f0_tab = {}, {}
    for n in range(1, 6):
        f_tab[n] = min(prime_support_size(A) for A in itertools.combinations(range(1, 31), n))
        f0_tab[n] = min(prime_support_size(A) for A in itertools.combinations(range(0, 31), n))
    print("f  :", f_tab)
    print("f0 :", f0_tab)
    out["f_small"] = {"f": f_tab, "f0": f0_tab, "universe": "[0,30] / [1,30]"}

    Path(__file__).with_name("results_audit.json").write_text(json.dumps(out, indent=2))
    print("wrote results_audit.json")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
