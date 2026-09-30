"""Erdos #126, counterexample arm: measurements supporting hunts/support_6cdfd2e3.

Stdlib only. Writes results.json next to this file.

Three things are measured, none of them a proof:

 1. an independent re-verification of the witnesses tabulated by r_186989,
    from scratch by trial division;
 2. exhaustive max-clique inside [1, N] for S = first k primes, k = 1..8,
    to extend the parent's table by one row and to check its rows;
 3. the interval construction A = {1, ..., m}, m = floor((p_{k+1} - 1)/2),
    which is proved admissible in RESULTS.md, evaluated against those rows;
 4. the two composition gadgets the counterexample arm was asked to try:
    dilated union  A u cA,  and the tensor  A . B,  scanned exhaustively over
    the multiplier / factor pairs available in the search box.
"""

import json
import sys
from pathlib import Path

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]


def prime_support(n):
    """Full set of prime factors of n, by trial division. No table lookup."""
    out, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            out.add(d)
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out.add(n)
    return out


def is_smooth(n, S):
    if n <= 0:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def admissible(A, S):
    A = sorted(A)
    for i in range(len(A)):
        for j in range(i + 1, len(A)):
            if not is_smooth(A[i] + A[j], S):
                return False
    return True


# ---------------------------------------------------------------- max clique

def max_clique(N, S):
    """Exhaustive max clique on [1,N] with a~b iff a+b is S-smooth.

    Bitset branch-and-bound with a greedy-colouring bound (Tomita style).
    Returns (size, witness). Exhaustive inside the box; says nothing outside it.
    """
    verts = list(range(1, N + 1))
    idx = {v: i for i, v in enumerate(verts)}
    adj = [0] * len(verts)
    smooth = [is_smooth(n, S) for n in range(0, 2 * N + 2)]
    for i, a in enumerate(verts):
        m = 0
        for b in verts:
            if b != a and smooth[a + b]:
                m |= 1 << idx[b]
        adj[i] = m

    best = [0, []]

    def bits(m):
        while m:
            b = m & -m
            yield b.bit_length() - 1
            m ^= b

    def expand(R, P):
        # greedy colouring of P gives an upper bound on the clique inside it
        order, colour, cls, U = [], [], 0, P
        while U:
            cls += 1
            Q = U
            while Q:
                v = (Q & -Q).bit_length() - 1
                Q &= ~(1 << v)
                U &= ~(1 << v)
                Q &= ~adj[v]
                order.append(v)
                colour.append(cls)
        for i in range(len(order) - 1, -1, -1):
            if len(R) + colour[i] <= best[0]:
                return
            v = order[i]
            R.append(v)
            nxt = P & adj[v]
            if not nxt:
                if len(R) > best[0]:
                    best[0], best[1] = len(R), [verts[u] for u in R]
            else:
                expand(R, nxt)
            R.pop()
            P &= ~(1 << v)

    expand([], (1 << len(verts)) - 1)
    return best[0], sorted(best[1])


# ------------------------------------------------------------ the two gadgets

def dilated_union(A, S, cmax, extra_primes):
    """Best  A u cA  over multipliers c <= cmax, allowing extra primes.

    Reports, for each achievable size, the minimum number of primes outside S
    that the union needs. That number is the 'prime cost of doubling' the
    counterexample arm is really asking about.
    """
    allowed = set(S) | set(extra_primes)
    best = None
    for c in range(2, cmax + 1):
        U = sorted(set(A) | {c * a for a in A})
        if len(U) <= len(A):
            continue
        need = set()
        ok = True
        for i in range(len(U)):
            for j in range(i + 1, len(U)):
                sup = prime_support(U[i] + U[j])
                if not sup <= allowed:
                    ok = False
                    break
                need |= sup - set(S)
            if not ok:
                break
        if ok and (best is None or (len(need), c) < (len(best["extra"]), best["c"])):
            best = {"c": c, "size": len(U), "extra": sorted(need)}
    return best


def tensor(A, SA, B, SB):
    """Is A.B admissible for S_A u S_B?  Report the first mixed pair that fails."""
    C = sorted({a * b for a in A for b in B})
    if len(C) != len(A) * len(B):
        return {"collision": True}
    S = set(SA) | set(SB)
    fails = []
    for i in range(len(C)):
        for j in range(i + 1, len(C)):
            if not is_smooth(C[i] + C[j], S):
                fails.append([C[i], C[j], C[i] + C[j], sorted(prime_support(C[i] + C[j]) - S)])
    return {
        "collision": False,
        "size": len(C),
        "pairs": len(C) * (len(C) - 1) // 2,
        "failures": len(fails),
        "first_failures": fails[:5],
    }


def main():
    out = {}

    # 1. re-verify the parent's witnesses from scratch
    parent = {
        1: ([2], [1, 3]),
        2: ([2, 3], [1, 5, 7, 11]),
        3: ([2, 3, 5], [1, 3, 7, 17, 47]),
        4: ([2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
        5: ([2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
        6: ([2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
        7: ([2, 3, 5, 7, 11, 13, 17], [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
    }
    out["parent_witness_audit"] = {
        str(k): {"witness": A, "size": len(A), "admissible": admissible(A, S)}
        for k, (S, A) in parent.items()
    }

    # 2. exhaustive max clique, k = 1..8
    boxes = {1: 400, 2: 400, 3: 400, 4: 400, 5: 400, 6: 400, 7: 300, 8: 260, 9: 200}
    rows = []
    for k, N in boxes.items():
        S = PRIMES[:k]
        n, W = max_clique(N, S)
        assert admissible(W, S)
        rows.append({"k": k, "S": S, "N": N, "g_N": n, "witness": W,
                     "root": round(n ** (1.0 / k), 4)})
        print(f"k={k} N={N} g_N={n} {W}", flush=True)
    out["clique"] = rows

    # 3. the interval construction
    iv = []
    for k in range(1, 15):
        m = (PRIMES[k] - 1) // 2
        A = list(range(1, m + 1))
        iv.append({"k": k, "m": m, "admissible": admissible(A, PRIMES[:k]) if m >= 2 else True})
    out["interval_construction"] = iv

    # 4a. dilated union on the parent's k=3 optimum and on smaller ones
    du = []
    for k in (2, 3, 4):
        S, A = parent[k]
        b = dilated_union(A, S, cmax=200, extra_primes=PRIMES[:12])
        du.append({"k": k, "S": S, "A": A, "best": b})
        print(f"dilated union k={k}: {b}", flush=True)
    out["dilated_union"] = du

    # 4b. tensor of the two smallest optima
    S1, A1 = parent[1]
    S2, A2 = [3, 5], [1, 2]           # disjoint-support partner, admissible: 1+2=3
    out["tensor"] = [
        {"A": A1, "S_A": S1, "B": A2, "S_B": S2, "result": tensor(A1, S1, A2, S2)},
        {"A": parent[2][1], "S_A": parent[2][0], "B": [1, 4], "S_B": [5],
         "result": tensor(parent[2][1], parent[2][0], [1, 4], [5])},
    ]

    Path(__file__).with_name("results_probe.json").write_text(json.dumps(out, indent=2))
    print("wrote results_probe.json")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
