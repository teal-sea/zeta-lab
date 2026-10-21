"""Erdos #126, analytic-prime-divisors arm: numerical checks for RESULTS.md.

Stdlib only.  Run:  python hunts/support_95a76f59/probe.py
Writes results.json beside this file.

Nothing here is evidence for or against RH (docs/08).  Nothing here is a proof;
the proofs are in RESULTS.md and the code only checks their arithmetic.
"""

import json
import math
import os
from itertools import combinations

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]


def factor_over(n, S):
    """Return (exponent dict over S, unfactored remainder)."""
    e, m = {}, n
    for p in S:
        while m % p == 0:
            m //= p
            e[p] = e.get(p, 0) + 1
    return e, m


def is_smooth(n, S):
    return factor_over(n, S)[1] == 1


def valid(A, S):
    return all(is_smooth(a + b, S) for a, b in combinations(sorted(A), 2))


def prime_mass(A, S):
    """log P, the per-prime masses e_p*log p, and B(A) = log P / max mass."""
    logP = 0.0
    mass = {p: 0.0 for p in S}
    exps = {p: 0 for p in S}
    for a, b in combinations(sorted(A), 2):
        s = a + b
        logP += math.log(s)
        e, rem = factor_over(s, S)
        for p, v in e.items():
            mass[p] += v * math.log(p)
            exps[p] += v
    top = max(mass.values()) if mass else float("inf")
    return {
        "logP": logP,
        "mass": {str(p): mass[p] for p in S},
        "exponents": {str(p): exps[p] for p in S},
        "max_mass": top,
        "max_mass_fraction": top / logP if logP else None,
        "B": logP / top if top else None,
    }


def occupancy(A, q):
    """Residue classes mod q occupied by A, and the largest class."""
    cls = {}
    for a in A:
        cls.setdefault(a % q, []).append(a)
    return len(cls), max(len(v) for v in cls.values())


def antipodal_ok(A, q):
    """True iff no two distinct elements of A sum to 0 mod q."""
    return all((a + b) % q != 0 for a, b in combinations(sorted(A), 2))


# ---------------------------------------------------------------- witnesses
WITNESSES = [
    (1, [2], [1, 3]),
    (2, [2, 3], [1, 5, 7, 11]),
    (3, [2, 3, 5], [1, 3, 7, 17, 47]),
    (4, [2, 3, 5, 7], [1, 2, 3, 5, 7, 13]),
    (5, [2, 3, 5, 7, 11], [1, 2, 5, 9, 13, 19, 23, 31]),
    (6, [2, 3, 5, 7, 11, 13], [1, 2, 3, 5, 7, 9, 13, 19, 23, 47]),
    (7, [2, 3, 5, 7, 11, 13, 17], [1, 3, 5, 6, 7, 11, 15, 19, 21, 29, 49]),
]


def check_witnesses():
    out = []
    for k, S, A in WITNESSES:
        rec = {"k": k, "S": S, "A": A, "n": len(A), "X": max(A)}
        rec["valid"] = valid(A, S)
        rec.update(prime_mass(A, S))
        # what the product route would establish about k, on a real optimum
        rec["product_route_gives_k_at_least"] = rec["B"]
        rec["log2_n"] = math.log2(len(A))
        # residue structure at primes outside S
        occ = {}
        for q in PRIMES:
            if q in S:
                continue
            if q > 4 * max(A):
                break
            n_cls, big = occupancy(A, q)
            occ[str(q)] = {
                "classes_occupied": n_cls,
                "cap_(q+1)/2": (q + 1) // 2,
                "within_cap": n_cls <= (q + 1) // 2,
                "largest_class": big,
                "antipodal_free": antipodal_ok(A, q),
                "n_le_q_minus_1": len(A) <= q - 1,
            }
        rec["outside_S"] = occ
        out.append(rec)
    return out


# ------------------------------------------------- the adversarial family
def omega_family(n, p, m, r=1):
    """Omega(n,p,m): n/2 elements = i*p^m + r, n/2 elements = j*p^m - r.

    Satisfies every hypothesis a counting estimate on P can use (distinct
    positive integers, range [1,X], residue distribution mod every prime
    power), and gcd = 1.  It is not claimed to be a valid Erdos configuration.
    """
    h = n // 2
    q = p ** m
    A = [i * q + r for i in range(1, h + 1)] + [j * q - r for j in range(1, h + 1)]
    return sorted(set(A))


def omega_report(n, p, m):
    A = omega_family(n, p, m)
    X = max(A)
    g = 0
    for a in A:
        g = math.gcd(g, a)
    logP = sum(math.log(a + b) for a, b in combinations(A, 2))
    # mass carried by p alone
    e_p = 0
    for a, b in combinations(A, 2):
        s = a + b
        v = 0
        while s % p == 0:
            s //= p
            v += 1
        e_p += v
    mass = e_p * math.log(p)
    return {
        "n": len(A),
        "p": p,
        "m": m,
        "X": X,
        "gcd": g,
        "logP": logP,
        "mass_at_p": mass,
        "fraction": mass / logP,
        "B": logP / mass,
    }


def omega_prime_family(n, p, m):
    """Omega'(n,p,m) = {i*p^m : i=1..n-1} u {1}.  gcd = 1, all elements
    distinct and positive, and C(n-1,2) of the C(n,2) pairs are divisible by
    p^m.  Whole-set gcd normalisation does not touch it."""
    return sorted([i * p ** m for i in range(1, n)] + [1])


def omega_prime_report(n, p, m):
    A = omega_prime_family(n, p, m)
    g = 0
    for a in A:
        g = math.gcd(g, a)
    logP, e_p = 0.0, 0
    for a, b in combinations(A, 2):
        s = a + b
        logP += math.log(s)
        while s % p == 0:
            s //= p
            e_p += 1
    mass = e_p * math.log(p)
    return {"n": len(A), "p": p, "m": m, "X": max(A), "gcd": g, "logP": logP,
            "mass_at_p": mass, "fraction": mass / logP, "B": logP / mass}


# ------------------------------------------- pigeonhole-mod-q refutation
def ap_family(n, Q):
    """A = {1 + i*M}, M = product of odd primes <= Q.

    For every odd prime q <= Q, A occupies the single class 1 mod q, so no two
    elements sum to 0 mod q however large n is.  Hence pigeonhole mod a single
    odd prime bounds nothing.
    """
    M = 1
    for q in PRIMES:
        if q > Q:
            break
        if q != 2:
            M *= q
    return [1 + i * M for i in range(n)], M


def ap_report(n, Q):
    A, M = ap_family(n, Q)
    checks = {}
    for q in PRIMES:
        if q > Q or q == 2:
            continue
        checks[str(q)] = {
            "antipodal_free": antipodal_ok(A, q),
            "classes_occupied": occupancy(A, q)[0],
        }
    return {"n": n, "Q": Q, "M": M, "X": max(A), "per_prime": checks,
            "all_antipodal_free": all(c["antipodal_free"] for c in checks.values())}


def pi(x):
    return sum(1 for q in PRIMES if q <= x) if x <= PRIMES[-1] else None


def main():
    res = {
        "note": "Erdos #126 analytic arm. Not evidence for or against RH.",
        "witnesses": check_witnesses(),
        "adversarial_omega": [
            omega_report(n, p, m)
            for n, p, m in [
                (20, 3, 1), (20, 3, 2), (20, 3, 4), (20, 3, 8),
                (20, 101, 1), (20, 101, 2), (20, 101, 4),
                (60, 101, 4), (60, 1009, 6),
            ]
        ],
        "adversarial_omega_prime": [
            omega_prime_report(n, p, m)
            for n, p, m in [
                (20, 3, 1), (20, 3, 4), (20, 3, 16), (20, 3, 64),
                (60, 101, 8), (60, 101, 32), (60, 101, 128),
            ]
        ],
        "pigeonhole_refutation": [ap_report(n, 31) for n in (5, 40)],
    }
    res["findings"] = [
        {"id": "T1", "status": "proved",
         "claim": "k >= B(A) = log P / max_p e_p log p, and B(A) is exactly the "
                  "strength of the product route."},
        {"id": "T2", "status": "proved",
         "claim": "H_{p,t} is a disjoint union of complete bipartite graphs on "
                  "antipodal class pairs plus cliques on self-antipodal classes."},
        {"id": "T3", "status": "proved",
         "claim": "N_t(p) <= min(C(n,2), (n/2)(X/p^t + 1))."},
        {"id": "T4", "status": "proved",
         "claim": "Ceiling. Counting+range+residue estimates give at most k >= 1+o(1); "
                  "adding gcd normalisation and one-step recursion, at most k >= 2+o(1). "
                  "The product route cannot reproduce Erdos-Turan's log_2 n.",
         "witness_families": ["Omega'(n,p,m) = {1} u {i p^m}", "Omega(n,p,m) = {i p^m + 1} u {j p^m - 1}"]},
        {"id": "P5a", "status": "proved",
         "claim": "For every prime q outside S, A occupies at most (q+1)/2 classes mod q; "
                  "|A| <= 2 whenever 2 is not in S."},
        {"id": "P5b", "status": "derived-not-independently-checked",
         "claim": "n <= 3(X+Q^2)/(pi(Q)-k); in particular n = O(sqrt(X) log X)."},
        {"id": "P5d", "status": "proved",
         "claim": "Smooth-counting lane is capped: k >= log n / loglog(2X), which beats "
                  "log_2 n only if X < e^2. Capped below Erdos-Turan even granting X <= n^C."},
        {"id": "A1", "status": "audit",
         "claim": "r_186989 loose thread 3 ('prove |A| <= p-1 by pigeonhole mod p') is false "
                  "as stated; {1+iM} with M a product of odd primes is antipodal-free mod every "
                  "odd q <= Q at any size. Replacement is P5a."},
        {"id": "A2", "status": "audit",
         "claim": "r_186989 sections 2 and 4 proofs check out; its seven witnesses re-verified "
                  "valid by independent trial division. Exhaustiveness of its searches not re-run."},
    ]
    # headline numbers
    ws = res["witnesses"]
    res["summary"] = {
        "all_witnesses_valid": all(w["valid"] for w in ws),
        "product_route_B_on_witnesses": {str(w["k"]): round(w["B"], 3) for w in ws},
        "log2_n_on_witnesses": {str(w["k"]): round(w["log2_n"], 3) for w in ws},
        "omega_B_min": min(o["B"] for o in res["adversarial_omega"]),
        "omega_max_fraction": max(o["fraction"] for o in res["adversarial_omega"]),
        "omega_prime_B_min": min(o["B"] for o in res["adversarial_omega_prime"]),
        "omega_prime_max_fraction": max(o["fraction"] for o in res["adversarial_omega_prime"]),
        "occupancy_cap_holds_everywhere": all(
            v["within_cap"] and v["antipodal_free"]
            for w in ws for v in w["outside_S"].values()
        ),
        "pigeonhole_unbounded": all(r["all_antipodal_free"] for r in res["pigeonhole_refutation"]),
    }
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=2, sort_keys=True)
    print(json.dumps(res["summary"], indent=2, sort_keys=True))
    print("\nadversarial family Omega(n,p,m): B = best bound the product route yields")
    for o in res["adversarial_omega"]:
        print(f"  n={o['n']:3d} p={o['p']:5d} m={o['m']}  X={o['X']:.3g}"
              f"  fraction={o['fraction']:.4f}  B={o['B']:.4f}  gcd={o['gcd']}")
    print(f"\nwrote {path}")


if __name__ == "__main__":
    main()
