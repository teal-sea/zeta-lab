"""Probe for the size-dichotomy arm of Erdos #126 (support run 95bb5cb7).

Three measurements, stdlib only, ~1 minute:

  A. Audit: re-verify from scratch every witness in hunts/r_186989/RESULTS.md
     table 3, by full trial division of every off-diagonal sum.

  B. Height: for S = {2,3} and S = {2,3,5}, exhaustively enumerate PRIMITIVE
     (gcd = 1) 3-element and 4-element sets whose off-diagonal sums are all
     S-smooth and bounded by a cutoff X, and report max(A) as X grows.
     This decides whether the "controlled interval" horn of the dichotomy has
     any hope of being supplied by a normalisation.

  C. Threshold: the counting horn needs log Psi(2N, S) = o(k). Report, for the
     measured witnesses, where max(A) sits relative to rad(S) = prod_{p in S} p,
     i.e. the exponent eps with max(A) = rad(S)^eps.

Nothing here is evidence for or against RH (docs/08).
"""

from __future__ import annotations

import json
from bisect import bisect_left, bisect_right
from itertools import combinations
from math import gcd, log
from pathlib import Path

# ---------------------------------------------------------------- helpers


def smooth_part_ok(n: int, primes: tuple[int, ...]) -> bool:
    """True iff every prime factor of n lies in `primes`.  Full trial division."""
    if n <= 0:
        return False
    for p in primes:
        while n % p == 0:
            n //= p
    return n == 1


def smooth_upto(primes: tuple[int, ...], limit: int) -> list[int]:
    """All `primes`-smooth integers in [1, limit], sorted."""
    vals = [1]
    for p in primes:
        out = []
        for v in vals:
            w = v
            while w <= limit:
                out.append(w)
                w *= p
        vals = out
    vals.sort()
    return vals


# ---------------------------------------------------------------- A. audit

WITNESSES = {
    1: (2, [1, 3]),
    2: (3, [1, 5, 7, 11]),
    3: (5, [1, 3, 7, 17, 47]),
    4: (7, [1, 2, 3, 5, 7, 13]),
    5: (11, [1, 2, 5, 9, 13, 19, 23, 31]),
    6: (13, [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
    7: (17, [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
}

FIRST_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)


def audit() -> list[dict]:
    rows = []
    for k, (pmax, A) in WITNESSES.items():
        S = FIRST_PRIMES[:k]
        assert S[-1] == pmax, (k, S, pmax)
        bad = [
            (a, b)
            for a, b in combinations(A, 2)
            if not smooth_part_ok(a + b, S)
        ]
        rad = 1
        for p in S:
            rad *= p
        rows.append(
            {
                "k": k,
                "S": list(S),
                "claimed_size": len(A),
                "witness": A,
                "all_sums_S_smooth": not bad,
                "violations": bad,
                "distinct": len(set(A)) == len(A),
                "max_element": max(A),
                "rad_S": rad,
                "eps_max_over_rad": round(log(max(A)) / log(rad), 4) if rad > 1 else None,
            }
        )
    return rows


# ---------------------------------------------------------------- B. height


def primitive_triples(primes: tuple[int, ...], cutoff: int):
    """All {a<b<c} with every pairwise sum `primes`-smooth and <= cutoff.

    Enumerated through the three sums s1<s2<s3, which determine the set:
        a = (s1+s2-s3)/2, b = (s1-s2+s3)/2, c = (-s1+s2+s3)/2.
    Exhaustive inside the cutoff on the SUMS (not on the elements), which is
    the right universe: an element bound would silently truncate.
    """
    Sm = smooth_upto(primes, cutoff)
    nS = len(Sm)
    out = []
    for i in range(nS):
        s1 = Sm[i]
        for j in range(i + 1, nS):
            s2 = Sm[j]
            hi = s1 + s2  # need s3 < s1+s2 for a > 0
            lo = s2
            l = bisect_right(Sm, lo)
            r = bisect_left(Sm, hi)
            for m in range(l, r):
                s3 = Sm[m]
                t = s1 + s2 + s3
                if t & 1:
                    continue
                a = (s1 + s2 - s3) // 2
                b = (s1 - s2 + s3) // 2
                c = (-s1 + s2 + s3) // 2
                if a <= 0 or b <= 0 or c <= 0:
                    continue
                if a == b or b == c or a == c:
                    continue
                if gcd(gcd(a, b), c) != 1:
                    continue
                out.append((a, b, c))
    return out, len(Sm)


def extend_to_four(triples, primes, cutoff, top=None):
    """Try to extend each triple by one more element (sums still <= cutoff).

    `top=None` means every triple is tried (no truncation).  A truncation here
    biases the answer: ranking by max element and keeping the head throws away
    exactly the small sets that extend.
    """
    Sm = smooth_upto(primes, cutoff)
    Sset = set(Sm)
    ranked = sorted(triples, key=lambda t: -max(t))
    if top is not None:
        ranked = ranked[:top]
    best = None
    found = 0
    for (a, b, c) in ranked:
        for s in Sm:
            d = s - a
            if d <= 0 or d in (a, b, c):
                continue
            if (b + d) in Sset and (c + d) in Sset:
                found += 1
                A = tuple(sorted((a, b, c, d)))
                if best is None or max(A) > max(best):
                    best = A
    return best, found


def height_scan(primes, cutoffs):
    rows = []
    for X in cutoffs:
        trips, nsm = primitive_triples(primes, X)
        mx3 = max((max(t) for t in trips), default=0)
        arg3 = max(trips, key=max) if trips else None
        best4, n4 = extend_to_four(trips, primes, X)
        rows.append(
            {
                "S": list(primes),
                "sum_cutoff": X,
                "n_smooth_upto_cutoff": nsm,
                "n_primitive_triples": len(trips),
                "max_element_over_primitive_3sets": mx3,
                "argmax_3set": list(arg3) if arg3 else None,
                "n_primitive_4sets_found": n4,
                "max_4set": list(best4) if best4 else None,
                "max_element_over_primitive_4sets": max(best4) if best4 else 0,
            }
        )
    return rows


# ---------------------------------------------------------------- C. threshold


def psi_simplex_bounds(k: int, logN: float) -> dict:
    """Rigorous sandwich on log Psi(N, first k primes) by lattice points in
    the simplex {e >= 0 : sum e_i log p_i <= log N}.

    lower: volume of the simplex           (every lattice point owns a cube)
    upper: volume of the dilated simplex   (log N + sum_i log p_i)
    """
    from math import lgamma, log1p

    P = FIRST_PRIMES_LONG[:k]
    lp = [log(p) for p in P]
    theta = sum(lp)
    sum_log_lp = sum(log(x) for x in lp)
    log_kfact = lgamma(k + 1)

    def vol(L):
        if L <= 0:
            return float("-inf")
        return k * log(L) - log_kfact - sum_log_lp

    # Rankin's trick: Psi(x,S) <= x^sigma * prod_{p in S} (1 - p^-sigma)^-1,
    # rigorous for every sigma > 0.  Minimise numerically.
    def rankin(sigma):
        return sigma * logN - sum(log1p(-(p ** (-sigma))) for p in P)

    lo, hi = 1e-4, 3.0
    for _ in range(200):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if rankin(m1) < rankin(m2):
            hi = m2
        else:
            lo = m1
    sigma_opt = (lo + hi) / 2
    upper = min(vol(logN + theta), logN, rankin(sigma_opt))

    return {
        "k": k,
        "log_N": logN,
        "theta_p_k": theta,
        "sigma_opt": sigma_opt,
        "log_psi_lower": max(vol(logN), 0.0),
        "log_psi_upper": upper,
        "lower_over_k": max(vol(logN), 0.0) / k,
        "upper_over_k": upper / k,
    }


def sieve_primes(n: int) -> tuple[int, ...]:
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return tuple(i for i in range(n + 1) if sieve[i])


FIRST_PRIMES_LONG = sieve_primes(200000)


def threshold_table() -> list[dict]:
    """log Psi/k at log N = c * theta(p_k), for growing k.  The horn needs o(k)."""
    rows = []
    for k in (10, 50, 200, 1000, 5000):
        theta = sum(log(p) for p in FIRST_PRIMES_LONG[:k])
        for c in (0.001, 0.01, 0.1, 0.5, 1.0, 2.0):
            rows.append(psi_simplex_bounds(k, c * theta) | {"c_logN_over_theta": c})
    return rows


# ---------------------------------------------------------------- main

if __name__ == "__main__":
    res: dict = {}

    res["audit_r_186989_witnesses"] = audit()

    res["height_scan_2_3"] = height_scan((2, 3), [10**4, 10**6, 10**9, 10**12, 10**15])
    res["height_scan_2_3_5"] = height_scan((2, 3, 5), [10**4, 10**6])

    res["psi_threshold"] = threshold_table()

    out = Path(__file__).with_name("results_probe.json")
    out.write_text(json.dumps(res, indent=2, default=str))

    for r in res["audit_r_186989_witnesses"]:
        print(
            f"k={r['k']:2d} |A|={r['claimed_size']:2d} ok={r['all_sums_S_smooth']} "
            f"max={r['max_element']:3d} rad={r['rad_S']:7d} eps={r['eps_max_over_rad']}"
        )
    print()
    for key in ("height_scan_2_3", "height_scan_2_3_5"):
        print(key)
        for r in res[key]:
            print(
                f"  cutoff=1e{len(str(r['sum_cutoff']))-1:<2d} smooth={r['n_smooth_upto_cutoff']:5d} "
                f"triples={r['n_primitive_triples']:7d} max3={r['max_element_over_primitive_3sets']:>18d} "
                f"n4={r['n_primitive_4sets_found']:6d} max4={r['max_element_over_primitive_4sets']:>18d}"
            )
    print()
    print("k     c=logN/theta   log_psi_lower/k   log_psi_upper/k")
    for r in res["psi_threshold"]:
        print(
            f"{r['k']:5d} {r['c_logN_over_theta']:>10.2f} {r['lower_over_k']:>16.4f} {r['upper_over_k']:>16.4f}"
        )
    print(f"\nwrote {out}")
