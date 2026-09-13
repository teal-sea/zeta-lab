"""
Independent check of ENDPOINT_SHARP.md section 4, case (a,r)=1, q not
dividing r ("Corrected" case): the claim that for a primitive real
character chi mod q, and g = gcd(q,r) < q, the sum of chi(c) over the
coset {c mod q : (c,q)=1, c == a mod g} is exactly zero.

Written from scratch for this review. Builds real primitive characters
directly (not via a library Dirichlet-character routine) for every
allowed conductor shape q = m, 4m, or 8m with m odd squarefree
(the two sign choices at 8), then brute-force sums over every proper
divisor g of q and every admissible residue class a mod g.

This tests strictly more cases than ENDPOINT_SHARP.md section 7 item (3)
(which used q in {3,5,7,11,13,15,21,33,105,4,8} only).
"""
from math import gcd
from itertools import product

import sympy


def squarefree_odd_numbers(limit):
    out = []
    for m in range(1, limit + 1, 2):
        if sympy.factorint(m) and all(e == 1 for e in sympy.factorint(m).values()):
            out.append(m)
    return out


def jacobi_char(m):
    """Real primitive character mod m for odd squarefree m>1 (Jacobi symbol),
    or the trivial character if m==1."""
    def chi(n):
        n = n % m
        if m == 1:
            return 1
        if gcd(n, m) != 1:
            return 0
        return sympy.jacobi_symbol(n, m)
    return chi


def chi4(n):
    n = n % 4
    if n % 2 == 0:
        return 0
    return 1 if n % 4 == 1 else -1


def chi8_plus(n):
    # Kronecker symbol (2/n) extended as a character mod 8: n mod 8 in {1,7}->1, {3,5}->-1
    r = n % 8
    if r % 2 == 0:
        return 0
    return 1 if r in (1, 7) else -1


def chi8_minus(n):
    # (-2/n) as character mod 8: n mod 8 in {1,3}->1, {5,7}->-1
    r = n % 8
    if r % 2 == 0:
        return 0
    return 1 if r in (1, 3) else -1


def build_real_primitive_chars(qmax):
    """Yield (q, chi) for real primitive characters of conductor q<=qmax,
    q of shape m, 4m, or 8m with m odd squarefree >1, plus q=4,8 alone."""
    chars = []
    odds = squarefree_odd_numbers(qmax)
    for m in odds:
        if m > 1:
            chars.append((m, jacobi_char(m)))
        # 4m
        if 4 * m <= qmax:
            cm = jacobi_char(m) if m > 1 else (lambda n: 1)
            def chi(n, cm=cm):
                return chi4(n) * cm(n)
            chars.append((4 * m, chi))
        # 8m, two sign choices
        if 8 * m <= qmax:
            cm = jacobi_char(m) if m > 1 else (lambda n: 1)
            def chip(n, cm=cm):
                return chi8_plus(n) * cm(n)
            def chin(n, cm=cm):
                return chi8_minus(n) * cm(n)
            chars.append((8 * m, chip))
            chars.append((8 * m, chin))
    return chars


def divisors(q):
    return [d for d in range(1, q + 1) if q % d == 0]


def main():
    chars = build_real_primitive_chars(200)
    print(f"testing {len(chars)} (q, chi) pairs, conductors up to 200")

    total_cosets = 0
    failures = []
    for q, chi in chars:
        # sanity: chi should be totally multiplicative and real on (Z/q)*,
        # and *primitive* -- we trust the construction, but double check
        # chi is not identically zero on units and takes only {-1,0,1}.
        vals = {chi(n) for n in range(q) if gcd(n, q) == 1}
        if not vals <= {-1, 0, 1}:
            failures.append((q, 'non-real-values', vals))
            continue
        for g in divisors(q):
            if g == q:
                continue
            for a in range(g):
                if gcd(a, g) != 1:
                    continue
                total_cosets += 1
                s = sum(chi(c) for c in range(q) if gcd(c, q) == 1 and c % g == a % g)
                # chi is primitive mod q, g<q, so chi restricted to the
                # kernel K = ker((Z/q)* -> (Z/g)*) must be nontrivial,
                # hence this coset sum must vanish exactly.
                if s != 0:
                    failures.append((q, g, a, s))

    print(f"total cosets tested: {total_cosets}")
    if failures:
        print(f"FAILURES: {len(failures)}")
        for f in failures[:20]:
            print("  ", f)
    else:
        print("No counterexamples found: every coset sum of chi over a proper "
              "sub-progression vanished, as claimed.")

    # Separately double check the "impossible branch" claim: if (a,r)=1 and
    # g=gcd(q,r), can (a,g)>1 ever happen? g | r always, so gcd(a,r)=1
    # forces gcd(a,g)=1. Brute-force confirm over many (q,r,a).
    print()
    print("Checking whether (a,r)=1 with g=gcd(q,r) can ever give (a,g)>1:")
    bad = 0
    for q in range(1, 60):
        for r in range(1, 60):
            g = gcd(q, r)
            for a in range(1, max(q, r) + 5):
                if gcd(a, r) == 1 and gcd(a, g) != 1:
                    bad += 1
    print(f"  violations found: {bad} (expected 0, since g | r)")


if __name__ == '__main__':
    main()
