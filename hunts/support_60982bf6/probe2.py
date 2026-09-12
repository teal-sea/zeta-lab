"""Erdos #126, exact search arm, part 2: normalization, height, and the
refutations.  Run after probe.py.  stdlib only.
"""
from __future__ import annotations

import json
import sys
import time
from math import gcd

sys.path.insert(0, "hunts/support_60982bf6")
from probe import PRIMES, max_admissible, prime_support, verify  # noqa: E402


def is_smooth(n, S):
    return prime_support(n) <= set(S)


def ladder(S, Ns):
    """g_N(S) as N grows; returns list of (N, g_N, witness)."""
    out = []
    best, bw = 0, []
    for N in Ns:
        n, w = max_admissible(S, N, lower=best - 1)
        if n > best or w:
            best, bw = n, w
        out.append((N, best, bw))
    return out


def main():
    res = {}

    # --- A. normalization: gcd(A) is always S-smooth, and A/gcd(A) is admissible.
    # Checked on every witness produced by probe.py.
    raw = json.load(open("hunts/support_60982bf6/raw.json"))["subsets_by_k"]
    checks = {"n": 0, "gcd_smooth": 0, "quotient_admissible": 0}
    for k, rows in raw.items():
        for r in rows:
            A, S = r["witness"], r["S"]
            if len(A) < 2:
                continue
            d = 0
            for a in A:
                d = gcd(d, a)
            checks["n"] += 1
            checks["gcd_smooth"] += is_smooth(d, S)
            checks["quotient_admissible"] += verify([a // d for a in A], S)
    print("[A] normalization checks:", checks)
    res["normalization_checks"] = checks

    # --- B. height ladder: where does g_N saturate?
    print("[B] height ladder")
    Ns = [16, 32, 64, 128, 256, 1024, 4096, 20000]
    targets = [(2,), (2, 3), (2, 3, 5), (2, 3, 11), (2, 3, 7), (2, 3, 5, 7),
               (2, 3, 5, 11), (2, 3, 7, 11), (2, 3, 5, 7, 11),
               (2, 3, 5, 7, 13), (2, 3, 5, 11, 13), (2, 3, 5, 7, 11, 13)]
    lad = {}
    for S in targets:
        k = len(S)
        cap = 20000 if k <= 3 else (4096 if k <= 4 else (2048 if k == 5 else 1024))
        rows = ladder(S, [N for N in Ns if N <= cap])
        lad[str(list(S))] = [{"N": N, "g_N": g, "witness": w} for N, g, w in rows]
        sat = min(N for N, g, w in rows if g == rows[-1][1])
        print(f"  S={list(S)!s:22s} g={rows[-1][1]:2d}  saturates at N={sat:6d}  "
              f"(box {rows[-1][0]})  2^(k+2)={2**(k+2)}")
    res["height_ladder"] = lad

    # (the mod-p refutation moved to probe3.py)

    with open("hunts/support_60982bf6/raw2.json", "w") as fh:
        json.dump(res, fh, indent=1)
    print("wrote raw2.json")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    t = time.time()
    main()
    print("%.1fs" % (time.time() - t))
