"""Erdos #126, descent arm: numerical support for the claims in RESULTS.md.

Stdlib only. Run from the repo root:

    python hunts/support_7ddfee4b/probe.py

Writes hunts/support_7ddfee4b/results.json.

Definitions used throughout. S is a finite set of primes, A a finite set of
distinct positive integers, and (S, A) is *admissible* when every sum a + b
with a != b in A has all its prime factors in S. A is *primitive* for S when
no element of A is divisible by any prime of S.
"""

from __future__ import annotations

import itertools
import json
import os
import sys
from typing import Iterable

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


def smooth(n: int, S: Iterable[int]) -> bool:
    """True when every prime factor of n lies in S (n >= 1; 1 is smooth)."""
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def prime_support(n: int) -> set[int]:
    out, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1
    if n > 1:
        out.add(n)
    return out


def admissible(A: list[int], S: Iterable[int]) -> bool:
    return all(smooth(a + b, S) for a, b in itertools.combinations(sorted(A), 2))


def max_set(S: list[int], N: int, primitive: bool = False) -> list[int]:
    """Exhaustive branch-and-bound for the largest admissible A inside [1, N]."""
    cand = [a for a in range(1, N + 1)
            if not (primitive and any(a % p == 0 for p in S))]
    idx = {a: i for i, a in enumerate(cand)}
    # neighbour bitsets over the candidate universe
    nbr = [0] * len(cand)
    for i, a in enumerate(cand):
        m = 0
        for j in range(i + 1, len(cand)):
            if smooth(a + cand[j], S):
                m |= 1 << j
        nbr[i] = m
    best: list[int] = []

    def expand(cur: list[int], allowed: int, start: int) -> None:
        nonlocal best
        if len(cur) > len(best):
            best = list(cur)
        # bound: remaining candidates cannot beat the incumbent
        if len(cur) + bin(allowed).count("1") <= len(best):
            return
        j = start
        m = allowed >> start
        while m:
            if m & 1:
                cur.append(cand[j])
                expand(cur, allowed & nbr[j], j + 1)
                cur.pop()
            m >>= 1
            j += 1

    expand([], (1 << len(cand)) - 1, 0)
    assert idx  # silence linters
    return sorted(best)


def omission_counterexample(p: int, m: int) -> dict:
    """A of size m, all elements = 1 mod p, so p divides no pairwise sum."""
    A = [1 + i * p for i in range(m)]
    S = sorted(set().union(*(prime_support(a + b)
                             for a, b in itertools.combinations(A, 2))))
    return {
        "p_omitted": p,
        "A": A,
        "S": S,
        "k": len(S),
        "p_in_S": p in S,
        "admissible": admissible(A, S),
        "size": len(A),
        "claim_bound_p_minus_1": p - 1,
        "refutes_claim": len(A) > p - 1 and p not in S,
    }


def main() -> None:
    out: dict = {}

    # 1. the k = 2 witness that makes 2^k tight there, and its primitivity
    W = [1, 5, 7, 11]
    out["k2_witness"] = {
        "A": W,
        "S": [2, 3],
        "admissible": admissible(W, [2, 3]),
        "primitive": all(a % 2 and a % 3 for a in W),
        "pair_sums": {f"{a}+{b}": a + b
                      for a, b in itertools.combinations(W, 2)},
        "residues_mod_3": {a: a % 3 for a in W},
        "power_of_two_fibres": [[1, 7], [5, 11]],
    }

    # 2. the "omitting a small prime caps |A|" claim
    out["omission"] = [omission_counterexample(p, m)
                       for p, m in [(3, 8), (5, 8), (7, 10), (11, 14)]]

    # 3. per-prime loss, measured: max |A| over all k-subsets of the first 8
    #    primes, general and primitive, inside a bounded universe
    N = int(os.environ.get("PROBE_N", "1200"))
    pool = PRIMES[:8]
    rows = []
    for k in (1, 2, 3):
        bestg, bestp = ([], None), ([], None)
        for S in itertools.combinations(pool, k):
            g = max_set(list(S), N)
            if len(g) > len(bestg[0]):
                bestg = (g, S)
            q = max_set(list(S), N, primitive=True)
            if len(q) > len(bestp[0]):
                bestp = (q, S)
        rows.append({
            "k": k, "N": N,
            "g_N": len(bestg[0]), "g_witness": bestg[0], "g_S": list(bestg[1]),
            "gstar_N": len(bestp[0]), "gstar_witness": bestp[0],
            "gstar_S": list(bestp[1]),
            "two_to_k": 2 ** k,
        })
        print(rows[-1], flush=True)
    out["max_over_subsets"] = rows
    out["measured_loss_ratio"] = [
        {"k": rows[i]["k"], "g_N/g_N(k-1)": rows[i]["g_N"] / rows[i - 1]["g_N"],
         "gstar_N/gstar_N(k-1)": rows[i]["gstar_N"] / rows[i - 1]["gstar_N"]}
        for i in range(1, len(rows))
    ]

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
    print(json.dumps({k: v for k, v in out.items() if k != "omission"},
                     indent=2)[:2000])


if __name__ == "__main__":
    sys.exit(main())
