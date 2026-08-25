"""Erdos #126, exact search arm: g(S) over choices of S.

Definitions.  S is a finite set of primes.  A finite set A of distinct positive
integers is *S-admissible* when every sum a+b with a,b in A, a != b, has all of
its prime factors in S.  g(S) = max |A|; g(k) = max over |S| = k of g(S).

Everything here is a search inside a bounded universe [1, N], so every number it
prints is a LOWER bound on the corresponding g.  Where a claim is exhaustive the
word "exhaustive" is qualified by the box.

stdlib only.  Run: python hunts/support_60982bf6/probe.py
"""

from __future__ import annotations

import itertools
import json
import sys
import time
from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


# --------------------------------------------------------------------------
# smoothness

def smooth_mask(S, limit):
    """Bytearray m with m[x] = 1 iff x >= 1 is S-smooth, for x <= limit."""
    m = bytearray(limit + 1)
    m[1] = 1
    reach = [1]
    seen = {1}
    for p in S:
        new = []
        for v in reach:
            w = v * p
            while w <= limit:
                if w not in seen:
                    seen.add(w)
                    new.append(w)
                w *= p
        reach.extend(new)
    for v in seen:
        m[v] = 1
    return m


def prime_support(n):
    """Full trial-division prime support of n. Independent re-verification."""
    out = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1
    if n > 1:
        out.add(n)
    return out


def verify(A, S):
    A = sorted(A)
    for i in range(len(A)):
        for j in range(i + 1, len(A)):
            if not prime_support(A[i] + A[j]) <= set(S):
                return False
    return True


# --------------------------------------------------------------------------
# exact max clique inside [1, N]

def max_admissible(S, N, lower=0):
    """Exact maximum |A| for A subset of [1,N], plus one witness.

    Branch and bound over the graph a ~ b iff a+b is S-smooth.  Exhaustive
    inside the box; `lower` seeds the incumbent to prune harder.
    """
    # Edges come from the S-smooth sums themselves, not from scanning pairs:
    # for each S-smooth s <= 2N, every split s = a + b with a != b is an edge.
    m = smooth_mask(S, 2 * N)
    smooths = [s for s in range(2, 2 * N + 1) if m[s]]
    nbr = {}
    for s in smooths:
        lo = max(1, s - N)
        for a in range(lo, (s + 1) // 2):
            b = s - a
            nbr.setdefault(a, []).append(b)
            nbr.setdefault(b, []).append(a)
    verts = sorted(nbr)
    idx = {v: i for i, v in enumerate(verts)}
    adj = [0] * len(verts)
    for v in verts:
        msk = 0
        for w in nbr[v]:
            msk |= 1 << idx[w]
        adj[idx[v]] = msk
    best = [lower, []]

    def expand(R, P):
        if not P:
            if len(R) > best[0]:
                best[0], best[1] = len(R), list(R)
            return
        # simple bound: cannot exceed |R| + popcount(P)
        if len(R) + bin(P).count("1") <= best[0]:
            return
        cand = P
        while cand:
            v = cand.bit_length() - 1
            if len(R) + bin(cand).count("1") <= best[0]:
                return
            R.append(v)
            expand(R, cand & adj[v])
            R.pop()
            cand &= ~(1 << v)

    expand([], (1 << len(verts)) - 1)
    return best[0], sorted(verts[i] for i in best[1])


# --------------------------------------------------------------------------

def report(tag, S, N, lower=0):
    t = time.time()
    n, w = max_admissible(S, N, lower)
    ok = verify(w, S) if w else True
    print(f"  {tag:24s} S={list(S)!s:22s} N={N:6d}  g_N={n:3d}  "
          f"{'ok' if ok else 'FAIL'}  {w}   ({time.time()-t:.1f}s)")
    return {"S": list(S), "N": N, "g_N": n, "witness": w, "reverified": ok}


def main():
    out = {"note": "all numbers are lower bounds on g; search box stated per row"}

    # ---- 1. exhaustive over all S of size k inside the first 9 primes
    print("[1] all k-subsets of the first 9 primes, exhaustive in the box")
    per_k = {}
    for k, N in ((1, 2000), (2, 2000), (3, 1200), (4, 800), (5, 600)):
        rows = []
        for S in itertools.combinations(PRIMES[:9], k):
            rows.append(report(f"k={k}", S, N))
        per_k[k] = rows
        print(f"  -- k={k}: max over S = {max(r['g_N'] for r in rows)}")
    out["subsets_by_k"] = per_k

    with open("hunts/support_60982bf6/raw.json", "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote raw.json")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
