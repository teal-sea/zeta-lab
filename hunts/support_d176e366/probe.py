"""Erdos #126, p-adic block-pruning arm: the checks behind RESULTS.md.

Stdlib only.  `python3 hunts/support_d176e366/probe.py` (~1 min) writes
results.json next to this file.

Setting: S a set of k primes, A a finite set of distinct positive integers with
every a+b (a != b in A) free of prime factors outside S.  g(k) = max |A|.

Nothing here is evidence for or against RH (docs/08).
"""

import json
import itertools
import os
import random
from math import gcd

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]


# ---------------------------------------------------------------- basics

def smooth(n, S):
    """True iff n has no prime factor outside S.  Trial division, no sieve."""
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1


def admissible(A, S):
    A = sorted(A)
    return all(smooth(a + b, S) for a, b in itertools.combinations(A, 2))


def prime_support(n):
    out, d = [], 2
    while d * d <= n:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    if n > 1:
        out.append(n)
    return sorted(set(out))


# ---------------------------------------------- max subset with coprime sums

def max_coprime_subset(A, T):
    """max |A'|, A' subset of A, with gcd(a+b, prod T) = 1 for all pairs in A'.

    Exact.  Branch and bound over the compatibility graph.
    """
    A = sorted(A)
    n = len(A)
    M = 1
    for p in T:
        M *= p
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if gcd(A[i] + A[j], M) == 1:
                adj[i].add(j)
                adj[j].add(i)
    best = [0]
    best_set = [()]

    def expand(cur, cand):
        if len(cur) + len(cand) <= best[0]:
            return
        if not cand:
            if len(cur) > best[0]:
                best[0] = len(cur)
                best_set[0] = tuple(A[i] for i in cur)
            return
        for v in sorted(cand):
            if len(cur) + len(cand) <= best[0]:
                return
            expand(cur + [v], {u for u in cand if u > v and u in adj[v]})
            cand = cand - {v}

    expand([], set(range(n)))
    if best[0] == 0 and n:
        best[0], best_set[0] = 1, (A[0],)
    return best[0], list(best_set[0])


# ------------------------------------------------------ clique search for g_N

def g_bounded(S, N):
    """Exhaustive max |A| inside [1, N].  Returns (size, witness)."""
    verts = list(range(1, N + 1))
    idx = {v: i for i, v in enumerate(verts)}
    adj = [set() for _ in verts]
    for i, a in enumerate(verts):
        for b in verts[i + 1:]:
            if smooth(a + b, S):
                adj[i].add(idx[b])
                adj[idx[b]].add(i)
    best = [0]
    best_set = [()]

    def expand(cur, cand):
        if len(cur) + len(cand) <= best[0]:
            return
        if not cand:
            if len(cur) > best[0]:
                best[0] = len(cur)
                best_set[0] = tuple(verts[i] for i in cur)
            return
        for v in sorted(cand):
            if len(cur) + len(cand) <= best[0]:
                return
            expand(cur + [v], {u for u in cand if u > v and u in adj[v]})
            cand = cand - {v}

    expand([], set(range(len(verts))))
    return best[0], list(best_set[0])


# ---------------------------------------------------------------- the checks

def check_witness_audit():
    """Re-verify r_186989's table rows from scratch, and its arm-2 claim."""
    rows = [
        (1, [2], [1, 3]),
        (2, [2, 3], [1, 5, 7, 11]),
        (3, [2, 3, 5], [1, 3, 7, 17, 47]),
        (4, [2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
        (5, [2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
        (6, [2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
        (7, [2, 3, 5, 7, 11, 13, 17],
         [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
    ]
    out = []
    for k, S, A in rows:
        ok = admissible(A, S)
        sup = sorted({p for a, b in itertools.combinations(sorted(A), 2)
                      for p in prime_support(a + b)})
        out.append({"k": k, "S": S, "witness": A, "size": len(A),
                    "verified_admissible": ok, "sum_prime_support": sup})
    return out


def check_no_three_powers_of_two(emax=60):
    """Endgame: S = {2} admits no 3-element set.  Proof is in RESULTS.md;
    this is the numerical companion.  Every candidate triple is determined by
    (a+b, a+c, b+c) = (2^x, 2^y, 2^z), so enumerate exponents, not integers."""
    hits = []
    for x in range(1, emax):
        for y in range(1, emax):
            for z in range(1, emax):
                s = (1 << x) + (1 << y) + (1 << z)
                if s % 2:
                    continue
                a = s // 2 - (1 << z)
                b = s // 2 - (1 << y)
                c = s // 2 - (1 << x)
                if a > 0 and b > 0 and c > 0 and len({a, b, c}) == 3:
                    hits.append((a, b, c, x, y, z))
    return {"exponents_to": emax, "triples_found": hits}


def check_full_block_pruning(rows):
    """phi(A, S\\{2}) <= 2 for every measured witness, and the retention
    ratios for every proper block T."""
    out = []
    for row in rows:
        S, A = row["S"], row["witness"]
        odd = [p for p in S if p != 2]
        full, wit = max_coprime_subset(A, odd)
        blocks = []
        for r in range(1, len(odd) + 1):
            for T in itertools.combinations(odd, r):
                size, _ = max_coprime_subset(A, list(T))
                prod = 1.0
                for p in T:
                    prod *= (p - 1) / (2.0 * p)
                blocks.append({
                    "T": list(T), "phi": size,
                    "ratio": size / len(A),
                    "two_to_minus_r": 2.0 ** -r,
                    "generic_upper": prod * len(A) + r,
                })
        out.append({"k": row["k"], "S": S, "n": len(A),
                    "phi_full_block": full, "full_block_witness": wit,
                    "blocks": blocks})
    return out


def check_factorisation_lemma(trials=200, seed=11):
    """Lemma 1: A' has all pair sums coprime to T iff, for each p in T, the
    residues of A' mod p meet no antipodal pair and carry at most one element
    in the class 0.  Checked by comparing the brute-force optimum against the
    optimum over products of half-systems."""
    rng = random.Random(seed)
    bad = []
    for _ in range(trials):
        T = rng.choice([[3, 5], [3, 7], [5, 7], [3, 5, 7], [3, 11]])
        A = rng.sample(range(1, 200), rng.randint(6, 14))
        brute, _ = max_coprime_subset(A, T)
        # optimum over products of half-systems, zero classes handled exactly
        best = 0
        halves = []
        for p in T:
            pairs = [(c, p - c) for c in range(1, (p + 1) // 2)]
            halves.append([set(ch) for ch in itertools.product(*pairs)])
        for choice in itertools.product(*halves):
            keep = [a for a in A
                    if all(a % p in H or a % p == 0
                           for p, H in zip(T, choice))]
            # at most one element per prime may sit in that prime's 0 class
            sub_best = 0
            for m in range(len(keep), 0, -1):
                if m <= sub_best:
                    break
                found = False
                for cand in itertools.combinations(keep, m):
                    ok = True
                    for p in T:
                        if sum(1 for a in cand if a % p == 0) > 1:
                            ok = False
                            break
                    if ok:
                        found = True
                        break
                if found:
                    sub_best = m
                    break
            best = max(best, sub_best)
        if best != brute:
            bad.append({"T": T, "A": A, "brute": brute, "product": best})
    return {"trials": trials, "mismatches": bad}


def check_tightness(blocks=((3, 5), (3, 7), (5, 7), (3, 5, 7),
                            (3, 5, 7, 11), (3, 5, 7, 11, 13))):
    """Theorem 3: on an equidistributed A (a full residue system mod prod T)
    the exact optimum is prod_{p in T} (p-1)/2 + r, hence a fraction
    prod (p-1)/(2p) + r/|A| of A -- strictly below 2^{-r} once |A| is large.
    Brute-forced where that is cheap, formula elsewhere."""
    out = []
    for T in blocks:
        M = 1
        pred = 1
        for p in T:
            M *= p
            pred *= (p - 1) // 2
        pred += len(T)
        rec = {"T": list(T), "n": M, "predicted_opt": pred,
               "predicted_fraction": pred / M,
               "two_to_minus_r": 2.0 ** -len(T),
               "beats_2^-r": pred / M > 2.0 ** -len(T)}
        if M <= 105:
            opt, wit = max_coprime_subset(list(range(1, M + 1)), list(T))
            rec["brute_opt"] = opt
            rec["brute_matches_formula"] = (opt == pred)
            rec["witness"] = wit
        out.append(rec)
    return out


def check_outside_prime_claim(qs=(3, 5, 7, 11, 13)):
    """r_186989 loose thread 3 claims |A| <= p-1 when p is not in S.  The
    residue constraint is real; the bound it is claimed to give is not.
    Counterexample family: A inside one nonzero residue class mod q."""
    out = []
    for q in qs:
        # every element == 1 mod q, so every pair sum == 2 mod q, so q never
        # divides a pair sum, for a set of any size.
        A = [1 + q * i for i in range(3 * q)]
        sums_hit_zero = any((a + b) % q == 0
                            for a, b in itertools.combinations(A, 2))
        out.append({"q": q, "size": len(A), "bound_claimed": q - 1,
                    "any_pair_sum_divisible_by_q": sums_hit_zero})
    return out


def check_residue_profile(rows):
    """Are the measured extremal witnesses equidistributed mod p in S?"""
    out = []
    for row in rows:
        S, A = row["S"], row["witness"]
        prof = {}
        for p in S:
            counts = [0] * p
            for a in A:
                counts[a % p] += 1
            used = {c for c in range(p) if counts[c]}
            antipodal = sorted({(c, (p - c) % p) for c in used
                                if (p - c) % p in used and c <= (p - c) % p})
            prof[str(p)] = {"counts": counts, "classes_used": len(used),
                            "antipodal_pairs_used": [list(x) for x in antipodal]}
        out.append({"k": row["k"], "n": len(A), "profile": prof})
    return out


def check_small_exhaustive(kmax=5, N=120):
    """Independent re-run of g_N in a small box, as an audit of r_186989's
    claim that every optimum lives below 50."""
    out = []
    for k in range(1, kmax + 1):
        S = PRIMES[:k]
        size, wit = g_bounded(S, N)
        out.append({"k": k, "S": S, "N": N, "g_N": size, "witness": wit})
    return out


def check_orbit_count_is_not_phi():
    """Theorem 3' footnote: phi is not the number of sign-orbits A meets.
    A = {1, 2} mod (3,5) lies in two distinct orbits but 3 | 1+2, so phi = 1."""
    T = [3, 5]
    A = [1, 2]
    orb = {tuple(tuple(sorted((a % p, (-a) % p))) for p in T) for a in A}
    phi, wit = max_coprime_subset(A, T)
    return {"A": A, "T": T, "orbits_met": len(orb), "phi": phi,
            "phi_below_orbit_count": phi < len(orb), "witness": wit}


def main():
    res = {}
    res["orbit_count_is_not_phi"] = check_orbit_count_is_not_phi()
    res["witness_audit"] = check_witness_audit()
    res["no_three_powers_of_two"] = check_no_three_powers_of_two()
    res["full_block_pruning"] = check_full_block_pruning(res["witness_audit"])
    res["factorisation_lemma"] = check_factorisation_lemma()
    res["tightness"] = check_tightness()
    res["outside_prime_claim"] = check_outside_prime_claim()
    res["residue_profile"] = check_residue_profile(res["witness_audit"])
    res["small_exhaustive"] = check_small_exhaustive()

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "results.json"), "w") as fh:
        json.dump(res, fh, indent=2, sort_keys=True)

    print("witnesses all admissible:",
          all(r["verified_admissible"] for r in res["witness_audit"]))
    print("power-of-two triples:", res["no_three_powers_of_two"]["triples_found"])
    print("factorisation mismatches:",
          len(res["factorisation_lemma"]["mismatches"]))
    for t in res["tightness"]:
        print("tightness", t["T"], "n", t["n"], "predicted", t["predicted_opt"],
              "brute", t.get("brute_opt", "-"),
              "fraction %.4f" % t["predicted_fraction"],
              "vs 2^-r %.4f" % t["two_to_minus_r"],
              "beats:", t["beats_2^-r"])
    for b in res["full_block_pruning"]:
        print("k=%d n=%d phi(S\\{2})=%d" % (b["k"], b["n"], b["phi_full_block"]))
    for c in res["outside_prime_claim"]:
        print("outside prime q=%d: set of size %d, q | some pair sum: %s"
              % (c["q"], c["size"], c["any_pair_sum_divisible_by_q"]))
    for s in res["small_exhaustive"]:
        print("g_%d(%d) = %d  %s" % (s["N"], s["k"], s["g_N"], s["witness"]))


if __name__ == "__main__":
    main()
