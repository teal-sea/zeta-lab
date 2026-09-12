"""Erdos #126, exact search arm, part 3: exact heights, and the refutations.

Two measurements probe2.py left coarse or broken:

  D. h(S) = min over maximum-size S-admissible sets A inside the box of max(A),
     computed exactly rather than on a power-of-two ladder.
  C. counterexamples to the proposed lemma "|A| <= p-1 whenever p is a prime
     not in S" (hunts/r_186989 RESULTS.md, loose thread 3).

stdlib only.
"""
from __future__ import annotations

import itertools
import json
import sys
import time

sys.path.insert(0, "hunts/support_60982bf6")
from probe import PRIMES, max_admissible, verify  # noqa: E402


def exact_height(S, gbox, Nbox):
    """Smallest N with g_N(S) == gbox. Linear scan upward, cheap at small N."""
    lo, hi = 1, Nbox
    while lo < hi:                       # g_N is non-decreasing in N
        mid = (lo + hi) // 2
        n, _ = max_admissible(S, mid, lower=gbox - 1)
        if n >= gbox:
            hi = mid
        else:
            lo = mid + 1
    n, w = max_admissible(S, lo)
    return lo, w


def main():
    res = {}

    print("[D] exact height h(S) of a smallest maximum-size witness")
    targets = [(2,), (2, 3), (2, 3, 5), (2, 3, 7), (2, 3, 11), (2, 3, 13),
               (2, 3, 5, 7), (2, 3, 5, 11), (2, 3, 7, 11), (2, 3, 7, 13),
               (2, 3, 5, 7, 11), (2, 3, 5, 7, 13), (2, 3, 5, 11, 13),
               (2, 3, 5, 7, 11, 13), (2, 3, 5, 7, 11, 17)]
    rows = []
    for S in targets:
        k = len(S)
        Nbox = 20000 if k <= 3 else (4096 if k <= 4 else 1024)
        g, _ = max_admissible(S, Nbox)
        # the box maximum is already reached inside [1,256] on every S tested,
        # so the exact height search only needs that window (asserted, not assumed)
        small, _ = max_admissible(S, 256)
        assert small == g, (S, small, g)
        h, w = exact_height(S, g, 256)
        assert verify(w, S)
        print(f"  S={list(S)!s:22s} g_box={g:2d} (box {Nbox:5d})  h={h:4d}  "
              f"witness={w}")
        rows.append({"S": list(S), "k": k, "box": Nbox, "g_box": g,
                     "height": h, "witness": w})
    res["heights"] = rows

    print("[C] proposed lemma  |A| <= p-1 for p not in S  -- counterexamples")
    ce = []
    for p in (3, 5, 7, 11, 13):
        pool = [q for q in PRIMES[:9] if q != p]
        best = (0, None, None)
        for k in (5, 6):
            for S in itertools.combinations(pool, k):
                if 2 not in S:
                    continue
                n, w = max_admissible(S, 400, lower=best[0])
                if n > best[0]:
                    best = (n, list(S), w)
        assert verify(best[2], best[1])
        ok = best[0] > p - 1
        print(f"  p={p:3d}: lemma claims |A| <= {p-1:2d};  found |A| = {best[0]}"
              f"  S={best[1]}  A={best[2]}   -> "
              f"{'REFUTED' if ok else 'consistent'}")
        ce.append({"p": p, "claimed_bound": p - 1, "found": best[0],
                   "S": best[1], "A": best[2], "refutes": ok})
    res["mod_p_counterexamples"] = ce

    with open("hunts/support_60982bf6/raw3.json", "w") as fh:
        json.dump(res, fh, indent=1)
    print("wrote raw3.json")


if __name__ == "__main__":
    sys.setrecursionlimit(20000)
    t = time.time()
    main()
    print("%.1fs" % (time.time() - t))
