"""Explicit primes between consecutive k-th powers for small n, with Pratt certificates.

A Pratt certificate for an odd prime p is a base a and the full factorisation
p - 1 = prod q_i^e_i such that a^(p-1) = 1 mod p and a^((p-1)/q_i) != 1 mod p
for every i; then a has order p - 1, so p is prime (Lucas).  Every q_i > 2
carries its own certificate.  ``check`` re-derives everything with integer
arithmetic only; ``make`` uses sympy merely to find the factorisation and the
next prime, and nothing it says is trusted.
"""

from __future__ import annotations

from math import prod

import sympy


def make(p: int) -> dict:
    if p == 2:
        return {"p": 2}
    fac = sympy.factorint(p - 1)
    for a in range(2, p):
        if pow(a, p - 1, p) != 1:
            continue
        if all(pow(a, (p - 1) // q, p) != 1 for q in fac):
            return {"p": p, "a": a,
                    "factors": [[q, e, make(q)] for q, e in sorted(fac.items())]}
    raise ValueError(f"no witness found for {p}")


def check(cert: dict) -> bool:
    """Integer-only verification of a certificate tree."""
    p = cert["p"]
    if p == 2:
        return "factors" not in cert
    a, factors = cert["a"], cert["factors"]
    if p < 3 or not 1 < a < p:
        return False
    if prod(q ** e for q, e, _ in factors) != p - 1:
        return False
    if any(e < 1 for _, e, _ in factors):
        return False
    if pow(a, p - 1, p) != 1:
        return False
    for q, _, sub in factors:
        if sub["p"] != q or pow(a, (p - 1) // q, p) == 1 or not check(sub):
            return False
    return True


def witness(n: int, k: int) -> dict:
    """The least prime above n^k, with certificate, for the interval (n^k, (n+1)^k)."""
    lo, hi = n ** k, (n + 1) ** k
    p = int(sympy.nextprime(lo))
    return {"n": n, "k": k, "prime": p, "inside": lo < p < hi, "certificate": make(p)}


def check_witness(w: dict) -> bool:
    n, k, p = w["n"], w["k"], w["prime"]
    return n ** k < p < (n + 1) ** k and w["certificate"]["p"] == p and check(w["certificate"])
