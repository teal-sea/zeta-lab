"""Brute-force checks of the finite-field and finite-ring counting statements.

Every count is an exact enumeration over an explicit field or ring table
(`common.GF`), never a formula; the formula is what is being compared.
"""
from __future__ import annotations

import itertools
import math
import random
from fractions import Fraction

import numpy as np

from . import common as C
from .common import Q, result


def _det_mod(Mx, p):
    """Determinant of an integer matrix modulo a prime p, by elimination."""
    a = [[int(v) % p for v in row] for row in Mx]
    n, det = len(a), 1
    for c in range(n):
        piv = next((r for r in range(c, n) if a[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            a[c], a[piv] = a[piv], a[c]
            det = -det
        det = det * a[c][c] % p
        inv = pow(a[c][c], -1, p)
        for r in range(c + 1, n):
            f = a[r][c] * inv % p
            if f:
                a[r] = [(x - f * y) % p for x, y in zip(a[r], a[c])]
    return det % p


def _symmetric_matrices(n, p, rng, limit):
    idx = [(i, j) for i in range(n) for j in range(i, n)]
    total = p ** len(idx)
    if total <= limit:
        codes = range(total)
    else:
        codes = [rng.randrange(total) for _ in range(limit)]
    for code in codes:
        B = np.zeros((n, n), dtype=np.int64)
        for k, (i, j) in enumerate(idx):
            B[i, j] = B[j, i] = (code // p ** k) % p
        if _det_mod(B, p):
            yield B


def _all_vectors(n, p):
    return np.array(list(itertools.product(range(p), repeat=n)), dtype=np.int64)


def _quadric_counts(B, X, p, half):
    v = ((X @ B) % p * X).sum(axis=1) % p
    if half:
        v = v * pow(2, -1, p) % p
    return np.bincount(v, minlength=p)


def quadric_even(p):
    """|N_s - q^(2M-1)| <= bound for the form (1/2) x^T B x in 2M variables over F_q, q odd prime."""
    bound, s_nonzero, strict = p["bound"], bool(p["s_nonzero"]), bool(p.get("strict", False))
    rng = random.Random(20261120)
    worst, where, n_cases = Fraction(0), None, 0
    for q, M, limit in p["cases"]:
        X = _all_vectors(2 * M, q)
        b = {"M": Fraction(q) ** M, "M-1": Fraction(q) ** (M - 1), "M/2": Fraction(q) ** M / 2}[bound]
        for B in _symmetric_matrices(2 * M, q, rng, limit):
            cnt = _quadric_counts(B, X, q, half=True)
            for s in range(q):
                if s_nonzero and s == 0:
                    continue
                n_cases += 1
                dev = abs(int(cnt[s]) - q ** (2 * M - 1))
                if dev > b or (strict and dev == b):
                    return result(False, n_cases, witness=dict(q=q, M=M, B=B.tolist(), s=s, count=int(cnt[s]),
                                                               deviation=dev, bound=str(b)))
                if dev / b > worst:
                    worst, where = dev / b, dict(q=q, M=M, s=s, deviation=dev)
    return result(True, n_cases, margin=1 - float(worst), tightest=where, sharp=float(worst), slack=1 / float(worst),
                  tested_range="(q, M, number of matrices tried): " + str([list(c) for c in p["cases"]]),
                  notes="exact enumeration of F_q^(2M); every symmetric B with det != 0 when there are at most "
                        "`limit` of them, else a seeded random sample")


def quadric_sq(p):
    """(N_beta - q^(n-1))^2 <= q^n / divisor for the form x^T S x over F_q, q odd prime, n >= 1."""
    divisor = Q(p["divisor"])
    rng = random.Random(20261121)
    worst, where, n_cases = Fraction(0), None, 0
    for q, n, limit in p["cases"]:
        X = _all_vectors(n, q)
        b = Fraction(q) ** n / divisor
        for S in _symmetric_matrices(n, q, rng, limit):
            cnt = _quadric_counts(S, X, q, half=False)
            for beta in range(q):
                n_cases += 1
                dev2 = (int(cnt[beta]) - q ** C.monus(n, 1)) ** 2
                if dev2 > b:
                    return result(False, n_cases, witness=dict(q=q, n=n, S=S.tolist(), beta=beta,
                                                               count=int(cnt[beta]), lhs=dev2, rhs=str(b)))
                if dev2 / b > worst:
                    worst, where = dev2 / b, dict(q=q, n=n, beta=beta, lhs=dev2)
    return result(True, n_cases, margin=1 - float(worst), tightest=where, sharp=float(worst), slack=1 / float(worst),
                  tested_range="(q, n, number of matrices tried): " + str([list(c) for c in p["cases"]]),
                  notes="exact enumeration; the ratio (1 - 1/q)^2 at beta = 0 on a hyperbolic plane tends to 1 with q")


def _iter_conv(F, dist, M):
    out = dist
    for _ in range(M - 1):
        out = F.convolve(out, dist)
    return out


def herm_norm(p):
    """#{x in k^M : sum sigma(x_i) x_i = c} = q^(M-1) (q^M - sign^M), |k| = q^2, c fixed by sigma, c != 0."""
    sign = int(p["sign"])
    n_cases = 0
    for pr, e, Mmax in p["fields"]:                 # k = GF(pr^(2e)) has q = pr^e
        F = C.GF(pr, 2 * e)
        q = pr ** e
        sigma = [F.power(x, q) for x in range(F.q)]
        assert all(sigma[sigma[x]] == x for x in range(F.q)) and any(sigma[x] != x for x in range(F.q))
        # the only involutions of a finite field are the identity and this one (cyclic Galois group)
        fixed = [x for x in range(F.q) if sigma[x] == x]
        assert len(fixed) == q
        dist = [0] * F.q
        for x in range(F.q):
            dist[int(F.mul[sigma[x]][x])] += 1
        for M in range(1, Mmax + 1):
            cnt = _iter_conv(F, dist, M)
            for c in fixed:
                if c == 0:
                    continue
                n_cases += 1
                rhs = q ** (M - 1) * (q ** M - sign ** M)
                if cnt[c] != rhs:
                    return result(False, n_cases, witness=dict(q=q, M=M, c=c, count=cnt[c], formula=rhs))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0,
                  tested_range="(p, e, M up to): " + str([list(f) for f in p["fields"]]) + ", q = p^e, field of q^2 elements",
                  notes="exact: the norm x * x^q tabulated on the field, then convolved M times over its additive group")


def dot_count(p):
    """#{(x, y) in k^M x k^M : x . y = c} = q^(2M-1) + sign q^(M-1) for c != 0, any finite field."""
    sign = int(p["sign"])
    n_cases = 0
    for pr, e, Mmax in p["fields"]:
        F = C.GF(pr, e)
        q = F.q
        dist = [0] * q
        for x in range(q):
            for y in range(q):
                dist[int(F.mul[x][y])] += 1
        for M in range(1, Mmax + 1):
            cnt = _iter_conv(F, dist, M)
            for c in range(1, q):
                n_cases += 1
                rhs = q ** (2 * M - 1) + sign * q ** (M - 1)
                if cnt[c] != rhs:
                    return result(False, n_cases, witness=dict(q=q, M=M, c=c, count=cnt[c], formula=rhs))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0,
                  tested_range="(p, e, M up to): " + str([list(f) for f in p["fields"]]),
                  notes="exact, characteristic 2 included")


def unitary_count(p):
    """#{X in M_m(k) : sigma(X)^T X = 1} = q^(m^2) prod_{j=1..m} (1 - (sign/q)^j), |k| = q^2."""
    sign = int(p["sign"])
    n_cases, seen = 0, []
    for pr, e, mmax in p["fields"]:
        F = C.GF(pr, 2 * e)
        q = pr ** e
        sigma = np.array([F.power(x, q) for x in range(F.q)])
        for m in range(0, mmax + 1):
            n_cases += 1
            if m == 0:
                count = 1                                   # the empty matrix
            else:
                total = F.q ** (m * m)
                codes = np.arange(total, dtype=np.int64)
                X = np.stack([(codes // F.q ** k) % F.q for k in range(m * m)], axis=1).reshape(total, m, m)
                ok = np.ones(total, dtype=bool)
                for i in range(m):
                    for j in range(m):
                        acc = np.zeros(total, dtype=np.int64)
                        for k in range(m):
                            acc = F.add[acc, F.mul[sigma[X[:, k, i]], X[:, k, j]]]
                        ok &= acc == (1 if i == j else 0)
                count = int(ok.sum())
            rhs = Fraction(q) ** (m * m) * math.prod(1 - (Fraction(sign, q)) ** j for j in range(1, m + 1))
            seen.append((q, m, count))
            if count != rhs:
                return result(False, n_cases, witness=dict(q=q, m=m, count=count, formula=str(rhs)))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0, counts=seen,
                  tested_range="(p, e, m up to): " + str([list(f) for f in p["fields"]]),
                  notes="exact enumeration of all m x m matrices over the field of q^2 elements")


def _mobius(n):
    f = C.factorint(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def subfield_elements(p):
    """2d #{z in F_(g^d), z != 0, deg z != d} < g^d - 1 for primes g >= g_min, d >= 1."""
    gmin, gmax, dmax = int(p["g_min"]), int(p["g_max"]), int(p["d_max"])

    def formula(g, d):
        full = sum(_mobius(d // e) * g ** e for e in range(1, d + 1) if d % e == 0)
        return (g ** d - 1) - full if d > 1 else 0          # for d = 1 every element has degree 1
    # brute force on explicit fields validates the count formula
    brute = 0
    for g, d in ((2, 2), (2, 3), (3, 2), (3, 3), (5, 2), (5, 3), (7, 2), (7, 3), (11, 2), (13, 2)):
        F = C.GF(g, d)
        cnt = 0
        for z in range(1, F.q):
            k, w = 1, F.power(z, g)
            while w != z:
                w = F.power(w, g)
                k += 1
            cnt += k != d
        assert cnt == formula(g, d), (g, d, cnt, formula(g, d))
        brute += 1
    worst, where, n_cases = None, None, 0
    for g in [int(x) for x in C.primes_upto(gmax) if x >= gmin]:
        for d in range(1, dmax + 1):
            n_cases += 1
            lhs, rhs = 2 * d * formula(g, d), C.monus(g ** d, 1)
            if not lhs < rhs:
                return result(False, n_cases, witness=dict(g=g, d=d, lhs=lhs, rhs=rhs))
            r = Fraction(rhs, lhs) if lhs else None
            if r is not None and (worst is None or r < worst):
                worst, where = r, dict(g=g, d=d, lhs=lhs, rhs=rhs)
    return result(True, n_cases, margin=float(worst) - 1, tightest=where, sharp=1 / float(worst), slack=float(worst),
                  brute_force_fields=brute, tested_range=f"primes {gmin} <= g <= {gmax}, 1 <= d <= {dmax}",
                  notes="the count is the necklace formula, validated by Frobenius-orbit enumeration on ten explicit fields")


def quad_char_count(p):
    """2 #{y in ZMod p : chi(y) = e} = p - 1 for e = +-1."""
    primes = [int(x) for x in C.primes_upto(int(p["P"])) if x >= int(p["p_min"])]
    n_cases = 0
    for q in primes:
        squares = {y * y % q for y in range(1, q)}
        for e in p["e_values"]:
            n_cases += 1
            if e == 1:
                cnt = len(squares)
            elif e == -1:
                cnt = (q - 1) - len(squares)
            else:
                cnt = 1 if e == 0 else 0
            if 2 * cnt != C.monus(q, 1):
                return result(False, n_cases, witness=dict(p=q, e=e, count=cnt, lhs=2 * cnt, rhs=q - 1))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0,
                  tested_range=f"primes {p['p_min']} <= p <= {p['P']}", notes="exact enumeration of squares")


def roots_of_unity_count(p):
    """#{x in ZMod n : x^d = 1} <= factor * d over the stated family of n."""
    family, factor, nmax, dmax = p["family"], int(p["factor"]), int(p["n_max"]), int(p["d_max"])
    worst, where, n_cases = Fraction(0), None, 0
    if family == "two_power":
        ns = [2 ** w for w in range(1, int(p["w_max"]) + 1)]
    else:
        ns = []
        for n in range(1, nmax + 1):
            units = [x for x in range(n) if math.gcd(x, n) == 1] if n > 1 else [0]
            if family == "all":
                ns.append(n)
                continue
            phi = len(units)
            cyc = n == 1
            for u in units:
                k, w = 1, u
                while w != 1 % n:
                    w = w * u % n
                    k += 1
                if k == phi:
                    cyc = True
                    break
            if cyc:
                ns.append(n)
    for n in ns:
        for d in range(1, dmax + 1):
            n_cases += 1
            cnt = sum(1 for x in range(n) if pow(x, d, n) == 1 % n)
            if cnt > factor * d:
                return result(False, n_cases, witness=dict(n=n, d=d, count=cnt, bound=factor * d))
            r = Fraction(cnt, factor * d)
            if r > worst:
                worst, where = r, dict(n=n, d=d, count=cnt)
    return result(True, n_cases, margin=1 - float(worst), tightest=where, sharp=float(worst) * factor, slack=1 / float(worst),
                  tested_range=f"{len(ns)} moduli, 1 <= d <= {dmax}", notes="exact enumeration")


def gl2_card(p):
    n, bound = int(p["n"]), int(p["bound"])
    cnt = sum(1 for a, b, c, d in itertools.product(range(n), repeat=4) if math.gcd((a * d - b * c) % n, n) == 1)
    if cnt > bound:
        return result(False, 1, witness=dict(count=cnt, bound=bound))
    return result(True, 1, margin=bound - cnt, tightest=dict(count=cnt), sharp=cnt, slack=bound / cnt,
                  notes="exact enumeration of the 2 x 2 matrices over ZMod n with unit determinant")
