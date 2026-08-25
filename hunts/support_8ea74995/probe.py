"""Formulation-arm probe for Erdos #126 (support run 8ea74995).

Stdlib only.  Three jobs, none of which is a search for a big set:

1. re-verify, from scratch, the witnesses hunt r_186989 published;
2. re-derive the small values of f and f_0 independently of that hunt;
3. sweep the choice of S at fixed |S| = k, which is the one frozen constant
   the prior hunt flagged as having genuine trade shape.

Everything it prints about g is a LOWER bound on g(k): the universe is
bounded and, for the sweeps, S ranges over a finite family only.

Run:  python hunts/support_8ea74995/probe.py
"""

from __future__ import annotations

import itertools
import json
import time
from pathlib import Path

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


# --------------------------------------------------------------------------
# smoothness
# --------------------------------------------------------------------------

def prime_support(m: int) -> set[int]:
    """Every prime dividing m, by trial division.  m >= 1."""
    out: set[int] = set()
    d = 2
    while d * d <= m:
        if m % d == 0:
            out.add(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out.add(m)
    return out


def support_of_set(A) -> set[int]:
    """P(A): primes dividing some a+b with a != b in A."""
    out: set[int] = set()
    for a, b in itertools.combinations(sorted(A), 2):
        out |= prime_support(a + b)
    return out


def smooth_upto(S, limit: int) -> list[int]:
    """All S-smooth integers in [1, limit]."""
    vals = [1]
    for p in S:
        nxt = []
        for v in vals:
            w = v
            while w <= limit:
                nxt.append(w)
                w *= p
        vals = nxt
    return sorted(v for v in vals if v <= limit)


# --------------------------------------------------------------------------
# exact maximum clique in the S-smooth pair-sum graph on [1, N]
# --------------------------------------------------------------------------

def _build_adj(S, N: int) -> list[int]:
    adj = [0] * (N + 1)
    for v in smooth_upto(S, 2 * N - 1):
        lo = max(1, v - N)
        for a in range(lo, (v - 1) // 2 + 1):
            b = v - a
            if b <= N and a != b:
                adj[a] |= 1 << b
                adj[b] |= 1 << a
    return adj


def max_clique(S, N: int):
    """Exact max clique on {1..N} with a ~ b iff a+b is S-smooth."""
    adj = _build_adj(S, N)
    alive = 0
    for a in range(1, N + 1):
        if adj[a]:
            alive |= 1 << a

    best = [0, ()]

    def greedy(start: int) -> None:
        R = [start]
        P = adj[start] & alive
        while P:
            v = (P & -P).bit_length() - 1
            R.append(v)
            P &= adj[v]
        if len(R) > best[0]:
            best[0], best[1] = len(R), tuple(sorted(R))

    for a in range(1, min(N, 400) + 1):
        if alive >> a & 1:
            greedy(a)

    # k-core style reduction: nothing of degree < best-1 can be in a bigger clique
    changed = True
    while changed:
        changed = False
        for a in range(1, N + 1):
            if alive >> a & 1:
                if (adj[a] & alive).bit_count() < best[0] - 1:
                    alive &= ~(1 << a)
                    changed = True

    def expand(R: list[int], P: int) -> None:
        while P:
            if len(R) + P.bit_count() <= best[0]:
                return
            v = (P & -P).bit_length() - 1
            P &= ~(1 << v)
            R.append(v)
            if len(R) > best[0]:
                best[0], best[1] = len(R), tuple(sorted(R))
            expand(R, P & adj[v])
            R.pop()

    P0 = alive
    while P0:
        v = (P0 & -P0).bit_length() - 1
        P0 &= ~(1 << v)
        expand([v], adj[v] & P0)
    return best[0], list(best[1])


# --------------------------------------------------------------------------
# f and f_0, exhaustively, in a small universe
# --------------------------------------------------------------------------

def f_small(n: int, universe: int, allow_zero: bool) -> tuple[int, list[int]]:
    lo = 0 if allow_zero else 1
    best = None
    bestA: list[int] = []
    for A in itertools.combinations(range(lo, universe + 1), n):
        s = len(support_of_set(A))
        if best is None or s < best:
            best, bestA = s, list(A)
            if best == 0:
                break
    return best or 0, bestA


def main() -> None:
    t0 = time.time()
    out: dict = {"run_id": "8ea74995-af9e-4053-bedf-c73dbe0ae46b"}

    # 1. independent re-verification of r_186989's published witnesses
    published = {
        1: [1, 3],
        2: [1, 5, 7, 11],
        3: [1, 3, 7, 17, 47],
        4: [1, 2, 3, 5, 7, 13],
        5: [1, 2, 5, 9, 13, 19, 23, 31],
        6: [1, 2, 3, 5, 7, 9, 13, 19, 23, 47],
        7: [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49],
    }
    checks = []
    for k, A in published.items():
        sup = sorted(support_of_set(A))
        checks.append(
            {
                "k": k,
                "A": A,
                "size": len(A),
                "support": sup,
                "support_size": len(sup),
                "ok": len(sup) <= k and len(set(A)) == len(A),
            }
        )
    out["witness_reverification"] = checks
    print("witnesses re-verified:", all(c["ok"] for c in checks))

    # 2. f and f_0 for n <= 5, exhaustive in [0, 30] / [1, 30]
    fs, f0s = {}, {}
    for n in range(1, 6):
        fv, Av = f_small(n, 30, allow_zero=False)
        f0v, A0v = f_small(n, 30, allow_zero=True)
        fs[n] = {"value": fv, "witness": Av}
        f0s[n] = {"value": f0v, "witness": A0v}
    out["f_upper_bounds_universe_30"] = fs
    out["f0_upper_bounds_universe_30"] = f0s
    print("f  <=", {n: fs[n]["value"] for n in fs})
    print("f0 <=", {n: f0s[n]["value"] for n in f0s})

    # 3. the residue lemma, and the counterexample to "p not in S => |A| <= p-1"
    #    A congruent to 1 mod p has every off-diagonal sum = 2 mod p.
    residue_ce = []
    for p in (3, 5, 7):
        A = [1 + p * i for i in range(p + 3)]  # size p+3 > p-1
        sup = support_of_set(A)
        residue_ce.append(
            {
                "p": p,
                "A": A,
                "size": len(A),
                "p_in_support": p in sup,
                "support_size": len(sup),
                "claimed_bound_p_minus_1": p - 1,
            }
        )
    out["residue_counterexamples"] = residue_ce
    print("thread-3 counterexamples (p not in P(A), |A| > p-1):",
          all(not c["p_in_support"] and c["size"] > c["claimed_bound_p_minus_1"]
              for c in residue_ce))

    # 4. S-sweep at fixed k: is "first k primes" optimal?
    sweeps = []
    for k, pool, N in ((3, 8, 4000), (4, 8, 2500)):
        rows = []
        for S in itertools.combinations(PRIMES[:pool], k):
            n, A = max_clique(list(S), N)
            rows.append({"S": list(S), "g_N": n, "witness": A})
        rows.sort(key=lambda r: -r["g_N"])
        first = [r for r in rows if r["S"] == PRIMES[:k]][0]
        sweeps.append(
            {
                "k": k,
                "N": N,
                "pool": PRIMES[:pool],
                "subsets_searched": len(rows),
                "best_g_N": rows[0]["g_N"],
                "first_k_primes_g_N": first["g_N"],
                "first_k_primes_optimal_in_this_family": first["g_N"] == rows[0]["g_N"],
                "top": rows[:6],
                "without_2_max": max(r["g_N"] for r in rows if 2 not in r["S"]),
            }
        )
        print(f"k={k} N={N}: best over {len(rows)} subsets = {rows[0]['g_N']} "
              f"(S={rows[0]['S']}), first-k-primes = {first['g_N']}, "
              f"max without 2 = {sweeps[-1]['without_2_max']}")

    out["S_sweeps"] = sweeps
    out["elapsed_sec"] = round(time.time() - t0, 1)
    Path(__file__).with_name("results.json").write_text(
        json.dumps(out, indent=2), encoding="utf-8"
    )
    print("wrote results.json in", out["elapsed_sec"], "s")


if __name__ == "__main__":
    main()
