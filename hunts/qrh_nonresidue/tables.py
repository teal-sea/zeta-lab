"""Exact tables used as controls: least nonresidues, primitive roots, witnesses.

Everything here is integer arithmetic (numpy int64 with operands below 2^31,
or Python integers), so the tables are exact.  They are the non-model oracle
the bounds of RESULTS.md are checked against.
"""

from __future__ import annotations

import math
from math import gcd

import numpy as np


def prime_sieve(n: int) -> np.ndarray:
    """Boolean array is_prime[0..n]."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p:: p] = False
    return s


def spf_sieve(n: int) -> np.ndarray:
    """Smallest prime factor of 0..n (int32); spf[0] = spf[1] = 0."""
    spf = np.zeros(n + 1, dtype=np.int32)
    for p in range(2, int(n ** 0.5) + 1):
        if spf[p] == 0:
            block = spf[p * p:: p]
            mask = block == 0
            block[mask] = p
            spf[p * p:: p] = block
    rest = np.nonzero(spf == 0)[0]
    spf[rest] = rest
    spf[:2] = 0
    return spf


def modpow_vec(base, exp: np.ndarray, mod: np.ndarray) -> np.ndarray:
    """Elementwise base^exp mod mod, all moduli below 3e9 (int64 safe)."""
    mod = mod.astype(np.int64)
    exp = exp.astype(np.int64).copy()
    b = (np.broadcast_to(np.asarray(base, dtype=np.int64), mod.shape) % mod).copy()
    r = np.ones_like(mod) % mod
    while True:
        odd = (exp & 1).astype(bool)
        if odd.any():
            r[odd] = (r[odd] * b[odd]) % mod[odd]
        exp >>= 1
        if not exp.any():
            break
        b = (b * b) % mod
    return r


def least_nonresidues(ps: np.ndarray, small_primes: np.ndarray) -> np.ndarray:
    """Least quadratic nonresidue n(p) for odd primes ps (it is a prime)."""
    out = np.zeros(len(ps), dtype=np.int64)
    todo = np.arange(len(ps))
    for ell in small_primes:
        if len(todo) == 0:
            break
        p = ps[todo]
        sel = p != ell
        v = np.ones(len(todo), dtype=np.int64)
        v[sel] = modpow_vec(int(ell), (p[sel] - 1) // 2, p[sel])
        hit = sel & (v == p - 1)
        out[todo[hit]] = ell
        todo = todo[~hit]
    if len(todo):
        raise RuntimeError("small prime list too short")
    return out


def distinct_prime_factors(m: np.ndarray, spf: np.ndarray, width: int = 10) -> np.ndarray:
    """Matrix of distinct prime factors of each m (0-padded), via spf."""
    m = m.astype(np.int64).copy()
    out = np.zeros((len(m), width), dtype=np.int64)
    col = np.zeros(len(m), dtype=np.int64)
    last = np.zeros(len(m), dtype=np.int64)
    while True:
        act = m > 1
        if not act.any():
            break
        idx = np.nonzero(act)[0]
        f = spf[m[idx]].astype(np.int64)
        new = f != last[idx]
        ii = idx[new]
        out[ii, col[ii]] = f[new]
        col[ii] += 1
        last[idx] = f
        m[idx] //= f
    return out


def least_primitive_roots(ps: np.ndarray, factors: np.ndarray, candidates) -> np.ndarray:
    """Least element of ``candidates`` that is a primitive root mod p."""
    out = np.zeros(len(ps), dtype=np.int64)
    todo = np.arange(len(ps))
    for a in candidates:
        if len(todo) == 0:
            break
        p = ps[todo]
        ok = (p % a) != 0
        for j in range(factors.shape[1]):
            f = factors[todo, j]
            use = ok & (f > 0)
            if not use.any():
                continue
            v = modpow_vec(int(a), (p[use] - 1) // f[use], p[use])
            bad = np.zeros(len(todo), dtype=bool)
            bad[np.nonzero(use)[0][v == 1]] = True
            ok &= ~bad
        out[todo[ok]] = a
        todo = todo[~ok]
    if len(todo):
        raise RuntimeError("candidate list too short")
    return out


def least_strong_witness(ns: np.ndarray, max_base: int = 200) -> np.ndarray:
    """Least a >= 2 that is a Miller-Rabin (strong) witness for odd composite n."""
    ns = ns.astype(np.int64)
    d = ns - 1
    s = np.zeros(len(ns), dtype=np.int64)
    while True:
        even = (d & 1) == 0
        if not even.any():
            break
        d[even] >>= 1
        s[even] += 1
    out = np.zeros(len(ns), dtype=np.int64)
    todo = np.arange(len(ns))
    for a in range(2, max_base + 1):
        if len(todo) == 0:
            break
        n = ns[todo]
        x = modpow_vec(a, d[todo], n)
        liar = (x == 1) | (x == n - 1)
        ss = s[todo]
        for r in range(1, int(ss.max()) if len(ss) else 0):
            act = (~liar) & (ss > r)
            if not act.any():
                break
            x[act] = (x[act] * x[act]) % n[act]
            liar |= act & (x == n - 1)
        wit = ~liar
        out[todo[wit]] = a
        todo = todo[~wit]
    if len(todo):
        raise RuntimeError("max_base too small")
    return out


def is_strong_liar(a: int, n: int) -> bool:
    """Python-integer Miller-Rabin liar test (any size n)."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return True
    return False


def least_strong_witness_int(n: int, limit: int = 10_000) -> int:
    for a in range(2, limit):
        if not is_strong_liar(a, n):
            return a
    raise RuntimeError("no witness below limit")


def legendre_nonresidue_int(p: int, limit: int = 100_000) -> int:
    """Least quadratic nonresidue of a large odd prime p (Euler's criterion)."""
    for a in range(2, limit):
        if pow(a, (p - 1) // 2, p) == p - 1:
            return a
    raise RuntimeError("no nonresidue below limit")


def factor_small(n: int) -> list[int]:
    """Distinct prime factors by trial division plus Pollard rho (Python ints)."""
    out = []
    for p in (2, 3, 5, 7, 11, 13):
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_probable_prime(m):
            if m not in out:
                out.append(m)
            continue
        f = _rho(m)
        stack += [f, m // f]
    return sorted(set(out))


def _is_probable_prime(n: int) -> bool:
    """Deterministic for n < 3.3e24 (bases through 41, Sorenson-Webster)."""
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        if n % p == 0:
            return n == p
    return all(is_strong_liar(a, n) for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41))


def _rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    c = 1
    while True:
        x = y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = gcd(abs(x - y), n)
        if d != n:
            return d
        c += 1


def is_primitive_root_int(a: int, p: int, qs: list[int]) -> bool:
    return a % p != 0 and all(pow(a, (p - 1) // q, p) != 1 for q in qs)


def least_primitive_root_int(p: int, prime_only: bool = False) -> int:
    qs = factor_small(p - 1)
    a = 1
    while True:
        a += 1
        if prime_only and not all(a % d for d in range(2, int(a ** 0.5) + 1)):
            continue
        if is_primitive_root_int(a, p, qs):
            return a


def generation_bound(q: int, primes: list[int]) -> int:
    """Least prime P with <primes <= P, coprime to q> = (Z/qZ)^*.

    Equals max over nonprincipal chi mod q of the least prime p with
    chi(p) not in {0, 1} (RESULTS.md, Lemma 6).  Requires q >= 3.
    """
    phi = sum(1 for a in range(1, q) if gcd(a, q) == 1)
    H = np.zeros(q, dtype=bool)
    H[1] = True
    size = 1
    for p in primes:
        if q % p == 0:
            continue
        r = p % q
        if H[r]:
            continue
        coset = np.nonzero(H)[0]
        cur = coset
        while True:
            cur = (cur * r) % q
            if H[cur[0]]:
                break
            H[cur] = True
            size += len(cur)
        if size == phi:
            return p
    raise RuntimeError("prime list too short")


def euler_phi(q: int) -> int:
    result, m, p = q, q, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    if m > 1:
        result -= result // m
    return result


def log8(q: int) -> float:
    return math.log(q) ** 8
