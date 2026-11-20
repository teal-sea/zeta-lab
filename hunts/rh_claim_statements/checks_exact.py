"""Exact (integer, rational) checks, with Arb only where a logarithm is compared.

Lean's conventions are implemented literally: truncated subtraction on the
naturals (`common.monus`), floor division, `Nat.log`, `padicValNat p 0 = 0`,
`Real.log 0 = 0`, `x / 0 = 0`, `Nat.totient 0 = 0`.
"""
from __future__ import annotations

import math
from fractions import Fraction

import numpy as np
from flint import arb, ctx

from . import common as C
from .common import A, Q, lo, up, result


def _lean_log(n):
    """Real.log of a natural number as a ball: log 0 = 0."""
    return arb(0) if n == 0 else arb(n).log()


# ---------------------------------------------------------------------------
# P01  pi(m) log m < K m for 1 <= m < N
# ---------------------------------------------------------------------------

def prime_count_log(p):
    K, N = Q(p["K"]), int(p["N"])
    mask = C.prime_mask(N)
    pi = np.cumsum(mask)
    best, arg = -1.0, None
    with ctx.workprec(C.bits(p)):
        KK = A(K)
        for m in range(1, N):
            lhs = int(pi[m]) * arb(m).log()
            rhs = KK * m
            if lhs >= rhs:
                return result(False, m, witness=dict(m=m, pi=int(pi[m]), lhs=float(lhs.mid()), rhs=float(rhs.mid())))
            if not (lhs < rhs):
                return result(None, m, notes=f"undecided at m={m}")
            r = up(lhs / m)
            if r > best:
                best, arg = r, m
    return result(True, N - 1, margin=float(K) - best, tightest=dict(m=arg, pi=int(pi[arg])),
                  sharp=best, slack=float(K) / best,
                  notes="every integer of the stated range, each strict inequality decided by an Arb enclosure of log m")


# ---------------------------------------------------------------------------
# P02a / P03  3 pi(s) <= s + c for s0 <= s <= S
# ---------------------------------------------------------------------------

def prime_count_linear(p):
    c, s0, S = int(p["c"]), int(p["s0"]), int(p["S"])
    pi = np.cumsum(C.prime_mask(S)).astype(np.int64)
    s = np.arange(S + 1, dtype=np.int64)
    slack = (s + c - 3 * pi)[s0:]
    i = int(np.argmin(slack))
    if slack[i] < 0:
        return result(False, i + 1, witness=dict(s=s0 + i, pi=int(pi[s0 + i]), lhs=int(3 * pi[s0 + i]), rhs=s0 + i + c))
    return result(True, S - s0 + 1, margin=int(slack[i]), tightest=dict(s=s0 + i, pi=int(pi[s0 + i])),
                  sharp=c - int(slack[i]), slack=int(slack[i]), tested_range=f"{s0} <= s <= {S}",
                  notes="exact integers; the additive constant could be lowered by `slack` on this range")


# ---------------------------------------------------------------------------
# P02b  centralBinom n <= (2n)^pi(sqrt(2n)) 4^(2n/div) (2n)^#{n < p <= 2n}
# ---------------------------------------------------------------------------

def central_binom(p):
    div, n0, N = int(p["div"]), int(p["n0"]), int(p["N"])
    pi = np.cumsum(C.prime_mask(2 * N + 1))
    worst, arg = None, None
    for n in range(n0, N + 1):
        lhs = math.comb(2 * n, n)
        rhs = (2 * n) ** int(pi[math.isqrt(2 * n)]) * 4 ** ((2 * n) // div) * (2 * n) ** int(pi[2 * n] - pi[n])
        if lhs > rhs:
            return result(False, n - n0 + 1, witness=dict(n=n, log2_lhs=lhs.bit_length(), log2_rhs=rhs.bit_length()))
        m = rhs.bit_length() - lhs.bit_length()
        if worst is None or m < worst:
            worst, arg = m, n
    return result(True, N - n0 + 1, margin=worst, tightest=dict(n=arg), slack=None,
                  tested_range=f"{n0} <= n <= {N}", notes="exact big integers; margin is the difference of bit lengths")


# ---------------------------------------------------------------------------
# P02c / P07  1/(K log N) <= sum of 1/p over primes N/2 < p <= N - 3
# ---------------------------------------------------------------------------

def inv_log_prime_sum(p):
    K, N0, N1 = Q(p["K"]), int(p["N0"]), int(p["N1"])
    mask = C.prime_mask(N1)
    inv = np.zeros(N1 + 1)
    pr = np.flatnonzero(mask)
    inv[pr] = 1.0 / pr
    S = np.cumsum(inv)
    Ns = np.arange(N0, N1 + 1)
    hi = np.maximum(Ns - 3, 0)
    lo_i = Ns // 2
    sums = np.where(hi > lo_i, S[hi] - S[lo_i], 0.0)
    with np.errstate(divide="ignore", invalid="ignore"):
        logs = np.log(np.maximum(Ns, 1).astype(float))
        lhs = np.where(logs > 0, 1.0 / (float(K) * logs), 0.0)     # Lean: 1/(K * 0) = 0
        ratio = np.where(lhs > 0, sums / lhs, np.inf)
    order = np.argsort(ratio)[:64]

    def exact(N):
        s = sum(Fraction(1, int(q)) for q in range(N // 2 + 1, N - 2) if q >= 2 and mask[q])
        if N < 2:
            return True, None                                       # 0 <= sum
        with ctx.workprec(C.bits(p, 128)):
            l = 1 / (A(K) * arb(N).log())
            sa = A(s)
            return (True if l <= sa else (False if l > sa else None)), up(sa / l) if s else 0.0

    worst, arg = math.inf, None
    for i in order:
        N = int(Ns[i])
        ok, r = exact(N)
        if ok is False:
            return result(False, int(i) + 1, witness=dict(N=N, sum_times_K_logN=r,
                          why="exact rational sum against an Arb enclosure of 1/(K log N)"))
        if ok is None:
            return result(None, int(i) + 1, notes=f"undecided at N={N}")
        if r is not None and r < worst:
            worst, arg = r, N
    # everything else: float64 with an allowance far below its margin
    rest = np.delete(ratio, order)
    if rest.size and rest.min() < 1.0 + 1e-6:
        return result(None, len(Ns), notes="a float margin is inside the allowance")
    return result(True, len(Ns), margin=worst - 1, tightest=dict(N=arg), sharp=float(K) / worst, slack=worst,
                  tested_range=f"{N0} <= N <= {N1}",
                  notes="the 64 tightest N by exact rational sums against Arb; the rest by float64 prefix sums, "
                        "whose rounding error (< 1e-9) is far below their margin")


# ---------------------------------------------------------------------------
# P04a, P04b, P10a  Chebyshev-type sums
# ---------------------------------------------------------------------------

def chebyshev(p):
    kind, N1 = p["kind"], int(p["N1"])
    N_arb = min(N1, int(p.get("N_arb", 3000)))
    mask = C.prime_mask(N1)
    lam = np.zeros(N1 + 1)
    base = np.zeros(N1 + 1, dtype=np.int64)
    for q in np.flatnonzero(mask):
        q = int(q)
        pk = q
        while pk <= N1:
            base[pk] = q
            pk *= q
    nz = base > 0
    lam[nz] = np.log(base[nz].astype(float))
    n = np.arange(N1 + 1, dtype=float)
    if kind == "psi_plus":                       # psi(N) + 1 + log N <= K N,  N >= 1
        K = Q(p["K"])
        lhs = np.cumsum(lam)[1:] + 1 + np.log(n[1:]); rhs = float(K) * n[1:]
        stat = lhs / n[1:]; start = 1
    elif kind == "lambda_over_n":                # sum Lambda(n)/n <= log N + c,  N >= 1
        c = Q(p["c"])
        with np.errstate(divide="ignore", invalid="ignore"):
            t = np.where(n > 0, lam / np.maximum(n, 1), 0.0)
        lhs = np.cumsum(t)[1:]; rhs = np.log(n[1:]) + float(c)
        stat = lhs - np.log(n[1:]); start = 1
    elif kind == "theta":                        # theta(Y) <= Y log b,  Y >= 0
        b = Q(p["base"])
        th = np.where(mask, np.log(np.maximum(n, 1)), 0.0)
        lhs = np.cumsum(th); rhs = n * math.log(float(b))
        with np.errstate(divide="ignore", invalid="ignore"):
            stat = np.where(n > 0, lhs / np.maximum(n, 1), 0.0); start = 0
    else:
        raise ValueError(kind)
    # Arb on the initial segment, where the inequality is tightest
    with ctx.workprec(C.bits(p)):
        acc = arb(0)
        for N in range(start, N_arb + 1):
            if kind == "theta":
                if mask[N]:
                    acc += arb(N).log()
                L, R = acc, N * A(Q(p["base"])).log()
            elif kind == "psi_plus":
                if base[N]:
                    acc += arb(int(base[N])).log()
                L, R = acc + 1 + arb(N).log(), A(Q(p["K"])) * N
            else:
                if base[N]:
                    acc += arb(int(base[N])).log() / N
                L, R = acc, arb(N).log() + A(Q(p["c"]))
            if L > R:
                return result(False, N, witness=dict(N=N, lhs=float(L.mid()), rhs=float(R.mid())))
            if not (L <= R):
                return result(None, N, notes=f"undecided at N={N}")
    tail = (rhs - lhs)[N_arb + 1 - start:]
    scale = np.maximum(1.0, np.abs(rhs[N_arb + 1 - start:]))
    if tail.size and (tail / scale).min() < 1e-6:
        return result(None, N1, notes="a float margin is inside the allowance")
    i = int(np.argmax(stat))
    sharp = float(stat[i])
    stated = float(Q(p.get("K", p.get("c", 0)))) if kind != "theta" else math.log(float(Q(p["base"])))
    return result(True, N1 + 1 - start, margin=stated - sharp, tightest=dict(N=i + start, statistic=sharp),
                  sharp=sharp, slack=(stated / sharp) if (kind != "lambda_over_n" and sharp > 0) else stated - sharp,
                  tested_range=f"{start} <= N <= {N1}",
                  notes=f"Arb for N <= {N_arb}; float64 with a 1e-6 relative allowance beyond, where the margin is far larger")


# ---------------------------------------------------------------------------
# P06  sum over any finite set of primes of log p / p^2 <= K
# ---------------------------------------------------------------------------

def prime_sum_log_p2(p):
    K, P = Q(p["K"]), int(p["P"])
    with ctx.workprec(C.bits(p, 128)):
        S = arb(0)
        for q in C.primes_upto(P):
            q = int(q)
            S += arb(q).log() / (arb(q) * q)
        tail = (arb(P).log() + 1) / P            # sum_{n>P} log n/n^2 <= int_P^oo log t/t^2 dt, P >= 2
        total = S + tail
        if S > A(K):
            return result(False, P, witness=dict(set=f"all primes <= {P}", sum_lower=lo(S), K=float(K)))
        ok = bool(total <= A(K))
    return result(True if ok else None, P, margin=float(K) - up(total), tightest=dict(set="all primes"),
                  sharp=[lo(S), up(total)], slack=[float(K) / up(total), float(K) / lo(S)], tail_covered=ok,
                  cover_basis="every finite set of primes: the terms are positive, so each finite sum is at most the "
                              "partial sum to P plus the integral tail bound (log P + 1)/P",
                  notes="complete: the terms are positive, so the supremum over finite sets is the full series, "
                        "enclosed between the partial sum to P and that plus (log P + 1)/P")


# ---------------------------------------------------------------------------
# P08  sum_{p <= B} log p/(p(p-1)) <= log 2 * sum num/den
# ---------------------------------------------------------------------------

def prime_log_sum_small(p):
    B, terms = int(p["B"]), [(int(a), int(b)) for a, b in p["terms"]]
    with ctx.workprec(C.bits(p, 128)):
        lhs = arb(0)
        for q in C.primes_upto(B):
            q = int(q)
            lhs += arb(q).log() / (arb(q) * (q - 1))
        rhs = arb(2).log() * A(sum(Fraction(a, b) for a, b in terms))
        if lhs > rhs:
            return result(False, 1, witness=dict(lhs=float(lhs.mid()), rhs=float(rhs.mid())))
        ok = bool(lhs <= rhs)
        m = lo(rhs - lhs)
    return result(True if ok else None, 1, margin=m, tightest=dict(point="the single instance"),
                  sharp=float(lhs.mid()), slack=float((rhs / lhs).mid()),
                  notes="one inequality between two explicit real numbers, decided by Arb at 128 bits")


# ---------------------------------------------------------------------------
# P10c  sum_{p<=n} floor((n+shift)/p) log p <= log n!   (strict for the mutant)
# ---------------------------------------------------------------------------

def log_factorial_prime_sum(p):
    N, shift, strict = int(p["N"]), int(p.get("shift", 0)), bool(p.get("strict", False))
    primes = [int(q) for q in C.primes_upto(N + 1)]
    vfact = {q: 0 for q in primes}
    equal = []
    with ctx.workprec(C.bits(p, 128)):
        for n in range(0, N + 1):
            if n >= 2:
                for q, e in C.factorint(n).items():
                    vfact[q] += e
            coeff = {q: (n + shift) // q - vfact[q] for q in primes if q <= n}
            pos = any(c > 0 for c in coeff.values())
            allzero = all(c == 0 for c in coeff.values())
            if allzero:
                equal.append(n)
                if strict:
                    return result(False, n + 1, witness=dict(n=n, why="both sides are equal, coefficient by coefficient"))
                continue
            if pos:
                d = sum((c * arb(q).log() for q, c in coeff.items()), arb(0))      # LHS - RHS
                if d > 0:
                    return result(False, n + 1, witness=dict(n=n, lhs_minus_rhs=lo(d)))
                if not (d < 0):
                    return result(None, n + 1, notes=f"undecided at n={n}")
    return result(True, N + 1, margin=0.0, tightest=dict(equal_at=equal), sharp="equality", slack=1.0,
                  tested_range=f"0 <= n <= {N}",
                  notes="log n! = sum_p v_p(n!) log p, so the comparison is exact in the integer coefficients "
                        "(Arb only if signs are mixed); equality exactly when n < 4")


# ---------------------------------------------------------------------------
# P11  Nat.Prime n for explicit n
# ---------------------------------------------------------------------------

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)      # deterministic below 3.3e24


def _miller_rabin(n, bases):
    """Returns a witness base if n is composite for one of the bases, else None."""
    if n < 2:
        return 0
    for q in bases:
        if n % q == 0:
            return None if n == q else q
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return a
    return None


def _trial_division_proof(n):
    """True iff no prime <= sqrt(n) divides n (own sieve, numpy remainders)."""
    r = math.isqrt(n)
    pr = C.primes_upto(r).astype(np.int64)
    return not bool((np.int64(n) % pr == 0).any())


def _lucas_proof(n, primes):
    """Pocklington-Lucas: `primes` are all prime factors of n - 1; find for each q a base a with
    a^(n-1) = 1 and gcd(a^((n-1)/q) - 1, n) = 1. Returns the bases, or None."""
    m = n - 1
    for q in primes:
        while m % q == 0:
            m //= q
    if m != 1:
        return None                       # the list does not factor n - 1 completely
    out = {}
    for q in primes:
        for a in range(2, 200):
            if pow(a, n - 1, n) != 1:
                return None               # n is composite (Fermat)
            if math.gcd(pow(a, (n - 1) // q, n) - 1, n) == 1:
                out[q] = a
                break
        else:
            return None
    return out


def literal_prime(p):
    n = int(p["n"])
    import cypari2
    pari = cypari2.Pari()
    routes = {}
    routes["pari_isprime"] = bool(pari.isprime(pari(str(n))))
    w = _miller_rabin(n, _MR_BASES)
    routes["own_miller_rabin_12_bases"] = w is None
    if n < 10 ** 15:
        routes["own_trial_division_to_sqrt"] = _trial_division_proof(n)
    if p.get("nm1_primes"):
        qs = [int(q) for q in p["nm1_primes"]]
        small_ok = all((_trial_division_proof(q) if q < 10 ** 15 else False) for q in qs)
        cert = _lucas_proof(n, qs) if small_ok else None
        routes["own_lucas_n_minus_1"] = cert is not None
    verdicts = set(routes.values())
    if verdicts == {True}:
        return result(True, 1, margin=None, routes=routes, digits=len(str(n)),
                      notes="PARI isprime is a proof at these sizes (BPSW below 2^64, where it is exhaustively "
                            "verified; APRCL or the n-1 test above); the own routes share no code with it")
    if verdicts == {False}:
        return result(False, 1, routes=routes, witness=dict(miller_rabin_witness=w,
                      small_factor=next((int(q) for q in C.primes_upto(10 ** 5) if n % int(q) == 0 and n != int(q)), None)))
    return result(None, 1, routes=routes, notes="routes disagree")


# ---------------------------------------------------------------------------
# P12a  log |Phi_m(x)| = Lambda(m), x = 1 (statement) or -1 (mutant)
# ---------------------------------------------------------------------------

def cyclotomic_value(p):
    from .checks_analytic import _cyclotomic_cached
    x, m0, M_poly, M_rec = int(p["x"]), int(p["m0"]), int(p["M_poly"]), int(p["M_rec"])
    vals = {}
    for m in range(1, M_poly + 1):
        co = _cyclotomic_cached(m)
        vals[m] = sum(c * x ** i for i, c in enumerate(co))
    if x == 1:
        # second route: prod_{d | m, d > 1} Phi_d(1) = m, by exact division
        rec = {1: 0}
        for m in range(2, M_rec + 1):
            prod = 1
            for d in range(2, m):
                if m % d == 0:
                    prod *= rec[d]
            assert m % prod == 0
            rec[m] = m // prod
            if m <= M_poly:
                assert rec[m] == vals[m], "the two routes for Phi_m(1) disagree"
        vals.update(rec)
    n = 0
    for m in sorted(vals):
        if m < m0:
            continue
        n += 1
        v = abs(vals[m])
        base = C.prime_power_base(m)             # Lambda(m) = log base, or 0
        # Real.log v with log 0 = 0:  log v = log b  iff  v = b (b >= 2);  log v = 0 iff v in {0, 1}
        ok = (v == base) if base else (v in (0, 1))
        if not ok:
            return result(False, n, witness=dict(m=m, abs_value=v, vonMangoldt="log %d" % base if base else "0"))
    return result(True, n, margin=0.0, sharp="identity", slack=1.0, tested_range=f"{m0} <= m <= {max(vals)}",
                  notes="exact integers: Phi_m(1) is p when m is a power of the prime p and 1 otherwise; "
                        "polynomial route to M_poly, divisor-product route beyond")


# ---------------------------------------------------------------------------
# P12b  sum_{m | m' | N} Lambda(m') phi(N/m') = phi(N) Lambda(m)/phi(m)
# ---------------------------------------------------------------------------

def vonmangoldt_weight_sum(p):
    Nmax, allow_one = int(p["N_max"]), bool(p.get("allow_m_eq_1", False))
    n = 0
    for N in range(1, Nmax + 1):
        divs = [d for d in range(1, N + 1) if N % d == 0]
        phi = {d: C.totient(d) for d in divs}
        ppb = {d: C.prime_power_base(d) for d in divs}
        for m in divs:
            if m == 1 and not allow_one:
                continue
            n += 1
            lhs = {}
            for m2 in divs:
                if m2 % m == 0 and ppb[m2]:
                    lhs[ppb[m2]] = lhs.get(ppb[m2], 0) + phi[N // m2]
            rhs = {ppb[m]: Fraction(phi[N], phi[m])} if ppb[m] else {}
            if {k: Fraction(v) for k, v in lhs.items() if v} != {k: v for k, v in rhs.items() if v}:
                return result(False, n, witness=dict(N=N, m=m, lhs_coefficients=str(lhs), rhs_coefficients=str(rhs),
                              why="coefficients of log p differ; logs of distinct primes are linearly independent over Q"))
    return result(True, n, margin=0.0, sharp="identity", slack=1.0, tested_range=f"1 <= N <= {Nmax}, every m | N",
                  notes="exact rational coefficients of log p on both sides")


# ---------------------------------------------------------------------------
# totients
# ---------------------------------------------------------------------------

def totient_sq(p):
    """N^2 <= c (2 omega(N) - 1) phi(N)^2 for N0 <= N <= N1, natural-number subtraction."""
    c, N0, N1, strict = int(p["c"]), int(p["N0"]), int(p["N1"]), bool(p.get("strict", False))
    phi = C.totient_sieve(N1); om = C.omega_sieve(N1)
    N = np.arange(N1 + 1, dtype=np.int64)
    fac = np.maximum(2 * om - 1, 0)                         # truncated subtraction
    rhs = c * fac * phi * phi
    lhs = N * N
    bad = (lhs >= rhs) if strict else (lhs > rhs)
    bad[:N0] = False
    if bad.any():
        i = int(np.flatnonzero(bad)[0])
        return result(False, i - N0 + 1, witness=dict(N=i, lhs=int(lhs[i]), rhs=int(rhs[i]), omega=int(om[i]), phi=int(phi[i])))
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(lhs > 0, rhs / np.maximum(lhs, 1), np.inf)
    ratio[:N0] = np.inf
    i = int(np.argmin(ratio))
    return result(True, N1 - N0 + 1, margin=float(ratio[i]) - 1, tightest=dict(N=i), sharp=c / float(ratio[i]),
                  slack=float(ratio[i]), tested_range=f"{N0} <= N <= {N1}", notes="exact int64 sieve")


def totient_prime_power_minus_one(p):
    """2n(p^n - 1) < (p-1) phi(p^n - 1) for primes p > c n^2, n >= 2."""
    import cypari2
    pari = cypari2.Pari()
    c, P2, Pn, nmax = Q(p["c"]), int(p["P2"]), int(p["Pn"]), int(p["n_max"])
    worst, where, n_cases = math.inf, None, 0
    sharp, sharp_at = 0.0, None
    for n in range(2, nmax + 1):
        for q in C.primes_upto(P2 if n == 2 else Pn):
            q = int(q)
            m = q ** n - 1
            phi = int(pari.eulerphi(pari(str(m))))
            if m < 10 ** 9:
                assert phi == C.totient(m), "PARI and the own totient disagree"
            holds = 2 * n * m < (q - 1) * phi
            if not holds:
                if q / n ** 2 > sharp:
                    sharp, sharp_at = q / n ** 2, (q, n)
            if c * n * n < q:
                n_cases += 1
                if not holds:
                    return result(False, n_cases, witness=dict(p=q, n=n, lhs=2 * n * m, rhs=(q - 1) * phi))
                r = (q - 1) * phi / (2 * n * m)
                if r < worst:
                    worst, where = r, dict(p=q, n=n)
    return result(True, n_cases, margin=worst - 1, tightest=where, sharp=sharp, slack=float(c) / sharp if sharp else None,
                  largest_p_over_n2_among_failures=dict(value=sharp, at=sharp_at),
                  tested_range=f"n = 2: p <= {P2}; 3 <= n <= {nmax}: p <= {Pn}",
                  notes="phi(p^n - 1) from PARI, cross-checked by an own factorisation below 1e9; `sharp` is the "
                        "largest p/n^2 at which the conclusion fails with the hypothesis dropped")


def totient_le_sq(p):
    c1, c2, N1 = int(p["c1"]), int(p["c2"]), int(p["N1"])
    phi = C.totient_sieve(N1)
    phi[0] = 0
    N = np.arange(N1 + 1, dtype=np.int64)
    bad1 = N > c1 * phi * phi
    bad2 = (N % 2 == 1) & (N > c2 * phi * phi)
    for bad, which in ((bad1, "first conjunct"), (bad2, "second conjunct (odd n)")):
        if bad.any():
            i = int(np.flatnonzero(bad)[0])
            return result(False, i + 1, witness=dict(n=i, phi=int(phi[i]), which=which))
    eq = [int(i) for i in np.flatnonzero((N == c1 * phi * phi) | ((N % 2 == 1) & (N == c2 * phi * phi)))]
    return result(True, N1 + 1, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"0 <= n <= {N1}", notes="exact int64 sieve; equality at the listed n")


def totient_small_divides(p):
    b, D, N1 = int(p["b"]), int(p["D"]), int(p["N1"])
    phi = C.totient_sieve(N1)
    ks = [int(k) for k in np.flatnonzero(phi <= b) if k >= 1]
    for k in ks:
        if D % k:
            return result(False, len(ks), witness=dict(k=k, phi=int(phi[k])))
    return result(True, N1, margin=0, tightest=dict(k_with_small_totient=ks), sharp="exact", slack=1.0,
                  tested_range=f"1 <= k <= {N1}", notes="exact; the list of k with phi(k) <= b is complete on the range")


def totient_sigma(p):
    j, N, Kmax, strict = int(p["j"]), int(p["N"]), int(p["K_max"]), bool(p.get("strict", False))
    n_cases, eq = 0, []
    for n in range(1, N + 1):
        f = C.factorint(n)
        phi = C.totient(n)
        for K in range(0, Kmax + 1):
            n_cases += 1
            sig = 1
            for q, e in f.items():
                sig *= sum(q ** (j * i) for i in range(e * K + 1))
            lhs, rhs = phi * sig, n ** (K + 1)
            if lhs > rhs or (strict and lhs == rhs):
                return result(False, n_cases, witness=dict(n=n, K=K, lhs=lhs, rhs=rhs))
            if lhs == rhs and len(eq) < 8:
                eq.append((n, K))
    return result(True, n_cases, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"1 <= n <= {N}, 0 <= K <= {Kmax}", notes="exact integers")


def harmonic_squarefree(p):
    Qmax, qmax, strict = int(p["Q_max"]), int(p["q_max"]), bool(p.get("strict", False))
    sqfree = [all(e == 1 for e in C.factorint(f).values()) if f else False for f in range(Qmax + 1)]
    phi = [C.totient(f) for f in range(max(Qmax, qmax) + 1)]
    H = [Fraction(0)]
    for n in range(1, Qmax + 1):
        H.append(H[-1] + Fraction(1, n))
    worst, where, n_cases = None, None, 0
    for q in range(1, qmax + 1):
        acc = Fraction(0)
        for Qv in range(0, Qmax + 1):
            if Qv >= 1 and sqfree[Qv] and math.gcd(Qv, q) == 1:
                acc += Fraction(1, phi[Qv])
            n_cases += 1
            rhs = Fraction(q, phi[q]) * acc
            if H[Qv] > rhs or (strict and H[Qv] == rhs):
                return result(False, n_cases, witness=dict(Q=Qv, q=q, lhs=str(H[Qv]), rhs=str(rhs)))
            if Qv >= 1:
                r = rhs / H[Qv]
                if worst is None or r < worst:
                    worst, where = r, dict(Q=Qv, q=q)
    return result(True, n_cases, margin=float(worst) - 1, tightest=where, sharp=1 / float(worst), slack=float(worst),
                  tested_range=f"0 <= Q <= {Qmax}, 1 <= q <= {qmax}", notes="exact rationals")


# ---------------------------------------------------------------------------
# factorials and p-adic valuations
# ---------------------------------------------------------------------------

def minkowski_const(p):
    """(4/pi)^r n!/n^n <= 1 for n >= 1 and r in the stated range."""
    rule, strict, N = p["r_rule"], bool(p.get("strict", False)), int(p["N"])
    worst, where, n_cases = -math.inf, None, 0
    with ctx.workprec(C.bits(p, 128)):
        l4pi = (4 / arb.pi()).log()
        for n in range(1, N + 1):
            rmax = n // 2 if rule == "2r<=n" else n
            for r in ([0, rmax] if n > 60 else range(0, rmax + 1)):
                n_cases += 1
                if r == 0:
                    lhs = Fraction(math.factorial(n), n ** n)
                    if lhs > 1 or (strict and lhs == 1):
                        return result(False, n_cases, witness=dict(n=n, r=0, value=str(lhs), why="exact rational"))
                    v = float(lhs)
                else:
                    d = r * l4pi + arb(n + 1).lgamma() - n * arb(n).log()     # log of the left side
                    if d > 0:
                        return result(False, n_cases, witness=dict(n=n, r=r, log_lhs=lo(d)))
                    if not (d < 0):
                        return result(None, n_cases, notes=f"undecided at n={n}, r={r}")
                    v = math.exp(up(d))
                if v > worst:
                    worst, where = v, dict(n=n, r=r)
    return result(True, n_cases, margin=1 - worst, tightest=where, sharp=worst, slack=1 / worst,
                  tested_range=f"1 <= n <= {N}", notes="r = 0 exact; r >= 1 by Arb on the logarithm; equality at (n, r) = (1, 0)")


def fact_pow(p):
    strict, N = bool(p.get("strict", False)), int(p["N"])
    eq = []
    for n in range(0, N + 1):
        lhs, rhs = 2 ** n * math.factorial(n + 1), (n + 1) ** (n + 1)
        if lhs > rhs or (strict and lhs == rhs):
            return result(False, n + 1, witness=dict(n=n, lhs=str(lhs)[:40], rhs=str(rhs)[:40]))
        if lhs == rhs:
            eq.append(n)
    return result(True, N + 1, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"0 <= n <= {N}", notes="exact integers")


def legendre_digits(p):
    """n/(p-1) - v_p(n!) <= Nat.log p n + add."""
    add, strict, N = Q(p["add"]), bool(p.get("strict", False)), int(p["N"])
    n_cases, eq = 0, []
    for q in p["primes"]:
        q = int(q)
        v = 0
        for n in range(0, N + 1):
            if n >= 1:
                v += C.padic_val(q, n)
            n_cases += 1
            lhs = Fraction(n, q - 1) - v
            rhs = C.nat_log(q, n) + add
            if lhs > rhs or (strict and lhs == rhs):
                return result(False, n_cases, witness=dict(p=q, n=n, lhs=str(lhs), rhs=str(rhs)))
            if lhs == rhs and len(eq) < 12:
                eq.append((q, n))
    return result(True, n_cases, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"p in {list(p['primes'])}, 0 <= n <= {N}",
                  notes="exact rationals; equality at n = p^k - 1 (all digits p - 1)")


def padic_choose(p):
    strict, N = bool(p.get("strict", False)), int(p["N"])
    n_cases, eq = 0, []
    for q in p["primes"]:
        q = int(q)
        for n in range(0, N + 1):
            row = [math.comb(n, k) for k in range(0, n + 3)]          # k > n gives 0: padicValNat p 0 = 0
            L = C.nat_log(q, n)
            for k, b in enumerate(row):
                n_cases += 1
                v = C.padic_val(q, b)
                if v > L or (strict and v == L):
                    return result(False, n_cases, witness=dict(p=q, n=n, k=k, v=v, nat_log=L))
                if v == L and L > 0 and len(eq) < 8:
                    eq.append((q, n, k))
    return result(True, n_cases, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"p in {list(p['primes'])}, 0 <= n <= {N}, 0 <= k <= n + 2", notes="exact integers")


def padic_factorial(p):
    """v_l(k!) <= (k - 1)/(l - 1) for k >= k0."""
    k0, strict, N = int(p["k0"]), bool(p.get("strict", False)), int(p["N"])
    n_cases, eq = 0, []
    for q in p["primes"]:
        q = int(q)
        v = 0
        for k in range(0, N + 1):
            if k >= 1:
                v += C.padic_val(q, k)
            if k < k0:
                continue
            n_cases += 1
            rhs = Fraction(k - 1, q - 1)
            if v > rhs or (strict and v == rhs):
                return result(False, n_cases, witness=dict(l=q, k=k, v=v, rhs=str(rhs)))
            if v == rhs and len(eq) < 12:
                eq.append((q, k))
    return result(True, n_cases, margin=0, tightest=dict(equality_at=eq), sharp=1.0, slack=1.0,
                  tested_range=f"l in {list(p['primes'])}, {k0} <= k <= {N}", notes="exact rationals; equality at k = l^j")


def four_padic(p):
    add, pmin, N = int(p["add"]), int(p["p_min"]), int(p["N"])
    worst, where, n_cases = None, None, 0
    for q in [int(x) for x in C.primes_upto(60) if x >= pmin]:
        for s in range(1, N + 1):
            n_cases += 1
            lhs, rhs = 4 * C.padic_val(q, s) + add, 3 * s
            if lhs > rhs:
                return result(False, n_cases, witness=dict(p=q, s=s, lhs=lhs, rhs=rhs))
            if worst is None or rhs - lhs < worst:
                worst, where = rhs - lhs, dict(p=q, s=s)
    return result(True, n_cases, margin=worst, tightest=where, sharp=add + worst, slack=worst,
                  tested_range=f"primes {pmin} <= p < 60, 1 <= s <= {N}", notes="exact integers")


def coef_nat(p):
    require, N = bool(p.get("require", True)), int(p["N"])
    n_cases = 0
    mon = C.monus

    def desc(a, s):
        r = 1
        for i in range(s):
            r *= mon(a, i)
        return r
    for Av in range(0, N + 1):
        for o in range(0, N + 1):
            for s in range(0, N + 1):
                for j in range(0, N + 1):
                    if require and s + j > o:
                        continue
                    n_cases += 1
                    lhs = math.comb(Av, o) * math.factorial(o)
                    a1, o1 = mon(mon(Av, s), j), mon(mon(o, s), j)
                    rhs = math.comb(a1, o1) * math.factorial(o1) * (math.comb(mon(Av, s), j) * math.factorial(j)) * desc(Av, s)
                    if lhs != rhs:
                        return result(False, n_cases, witness=dict(A=Av, o=o, s=s, j=j, lhs=lhs, rhs=rhs))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0, tested_range=f"0 <= A, o, s, j <= {N}",
                  notes="exact integers with truncated subtraction as Lean reads it")


def alt_vandermonde(p):
    sign, N = int(p["sign"]), int(p["N"])
    n_cases = 0
    for B in range(0, N + 1):
        for z in range(0, N + 1):
            for l in range(0, N + 1):
                n_cases += 1
                lhs = sum(sign ** j * math.comb(B, j) * math.comb(z + B + (l - j), l - j) for j in range(l + 1))
                if lhs != math.comb(z + l, l):
                    return result(False, n_cases, witness=dict(B=B, z=z, l=l, lhs=lhs, rhs=math.comb(z + l, l)))
    return result(True, n_cases, margin=0, sharp="identity", slack=1.0, tested_range=f"0 <= B, z, l <= {N}",
                  notes="exact integers")


# ---------------------------------------------------------------------------
# A07  number of (n+1)-tuples in [1, M] with product <= M is at most M (add + log M)^n
# ---------------------------------------------------------------------------

def tuples_count(p):
    add, strict, Mmax, nmax = Q(p["add"]), bool(p.get("strict", False)), int(p["M_max"]), int(p["n_max"])
    memo = {}

    def T(k, m):                      # k-tuples of positive integers with product <= m
        if k == 0:
            return 1
        if k == 1:
            return m
        key = (k, m)
        if key not in memo:
            tot, a = 0, 1
            while a <= m:                 # group the a with the same floor(m / a)
                v = m // a
                a2 = m // v
                tot += (a2 - a + 1) * T(k - 1, v)
                a = a2 + 1
            memo[key] = tot
        return memo[key]
    worst, where, n_cases = -1.0, None, 0
    with ctx.workprec(C.bits(p, 128)):
        for n in range(0, nmax + 1):
            for M in range(1, Mmax + 1):
                n_cases += 1
                cnt = T(n + 1, M)
                if n == 0 or M == 1:
                    rhs_exact = M * (add ** n if M == 1 else 1)            # log 1 = 0 exactly
                    if cnt > rhs_exact or (strict and cnt == rhs_exact):
                        return result(False, n_cases, witness=dict(n=n, M=M, count=cnt, rhs=str(rhs_exact), why="exact"))
                    r = float(Fraction(cnt) / rhs_exact) if rhs_exact else math.inf
                else:
                    rhs = M * (A(add) + arb(M).log()) ** n
                    if arb(cnt) > rhs:
                        return result(False, n_cases, witness=dict(n=n, M=M, count=cnt, rhs=float(rhs.mid())))
                    if not (arb(cnt) < rhs):
                        return result(None, n_cases, notes=f"undecided at n={n}, M={M}")
                    r = up(arb(cnt) / rhs)
                if r > worst:
                    worst, where = r, dict(n=n, M=M)
    return result(True, n_cases, margin=1 - worst, tightest=where, sharp=worst, slack=1 / worst,
                  tested_range=f"0 <= n <= {nmax}, 1 <= M <= {Mmax}",
                  notes="exact counts by recursion on floor(M/a); equality for n = 0 and for M = 1")


# ---------------------------------------------------------------------------
# A09a  sum_{i=1}^N min(1, x/p^i) <= K x/p
# ---------------------------------------------------------------------------

def sum_min(p):
    K, neg = Q(p["K"]), bool(p.get("allow_negative", False))
    worst, where, n_cases = Fraction(0), None, 0
    xs = [Fraction(k, 8) for k in range(0, 161)] + [Fraction(2) ** j for j in range(5, 12)] + \
         [Fraction(3) ** j for j in range(3, 8)] + [Fraction(1, 1000), Fraction(999, 1000)]
    if neg:
        xs = [-x for x in xs if x] + xs
    for q in (2, 3, 5, 7, 11):
        for x in xs:
            acc = Fraction(0)
            for N in range(0, 41):
                if N >= 1:
                    acc += min(Fraction(1), x / q ** N)
                n_cases += 1
                rhs = K * x / q
                if acc > rhs:
                    return result(False, n_cases, witness=dict(p=q, x=str(x), N=N, lhs=str(acc), rhs=str(rhs)))
                if rhs > 0 and acc / rhs > worst:
                    worst, where = acc / rhs, dict(p=q, x=str(x), N=N)
    return result(True, n_cases, margin=1 - float(worst), tightest=where, sharp=float(K * worst), slack=1 / float(worst),
                  tested_range="p in {2,3,5,7,11}, N <= 40, x on a rational grid in [0, 2048]",
                  notes="exact rationals; the ratio tends to 1 for p = 2, x <= 2, N -> infinity and is not attained")


# ---------------------------------------------------------------------------
# A09b  H_N <= add + log N
# ---------------------------------------------------------------------------

def harmonic_log(p):
    add, strict, N1 = Q(p["add"]), bool(p.get("strict", False)), int(p["N1"])
    worst, where = None, None
    with ctx.workprec(C.bits(p, 128)):
        H = Fraction(0)
        Ha = arb(0)
        for N in range(0, N1 + 1):
            if N >= 1:
                Ha += arb(1) / N
                if N <= 64:
                    H += Fraction(1, N)
            if N <= 1:                                           # log 0 = log 1 = 0: exact
                if H > add or (strict and H == add):
                    return result(False, N + 1, witness=dict(N=N, lhs=str(H), rhs=str(add), why="exact"))
                continue
            rhs = A(add) + arb(N).log()
            if Ha > rhs:
                return result(False, N + 1, witness=dict(N=N, lhs=float(Ha.mid()), rhs=float(rhs.mid())))
            if not (Ha < rhs):
                return result(None, N + 1, notes=f"undecided at N={N}")
            m = lo(rhs - Ha)
            if worst is None or m < worst:
                worst, where = m, N
    return result(True, N1 + 1, margin=0.0, tightest=dict(equality_at=[1], next_smallest_margin=worst, at=where),
                  sharp=1.0, slack=1.0, tested_range=f"0 <= N <= {N1}",
                  notes="N = 0, 1 exact (log 0 = log 1 = 0); N >= 2 by Arb; equality at N = 1")


# ---------------------------------------------------------------------------
# A11 / A12  the sigma exponents
# ---------------------------------------------------------------------------

def _sig_core(l, g, h, j):
    """((3g) + M / l^(j-1)) * l / (l-1)^2 with M = (h + 2g) div (l - 1) + 1, natural arithmetic."""
    Mp = (h + 2 * g) // C.monus(l, 1) + 1 if C.monus(l, 1) else 0 + 1        # n / 0 = 0 on the naturals
    return (3 * g + Fraction(Mp, l ** C.monus(j, 1))) * l / Fraction(l - 1) ** 2 if l != 1 else Fraction(0)


def nok_exponent(p):
    const, lmin = Q(p["const"]), int(p["l_min"])
    quads = [(Fraction(0), Fraction(0), Fraction(0), Fraction(0)), (Fraction(7, 3), Fraction(-5), Fraction(7, 3), Fraction(-5)),
             (Fraction(0), Fraction(1), Fraction(2), Fraction(3)), (Fraction(10), Fraction(0), Fraction(10), Fraction(1, 7))]
    worst, where, n_cases = None, None, 0
    for l in range(lmin, 14):
        for g in range(0, 14):
            for h in range(0, 50):
                for j in range(1, 5):
                    sigma = math.floor(_sig_core(l, g, h, j)) + 1                 # sigNOK
                    B = Fraction(3, 2) * (h + 2 * g) / Fraction(l - 1) ** (j + 1) + Fraction(9, 4) * g + const
                    for ell in (0, 1, 5):
                        for (r, kap, R, K) in quads:
                            n_cases += 1
                            lhs = 2 * r + 4 * sigma + max(r, 2 * (2 * sigma + r + 2 * g * ell)) + 2 * kap
                            rhs = 4 * R + 8 * B + 4 * g * ell + 2 * K
                            if lhs > rhs:
                                return result(False, n_cases, witness=dict(l=l, g=g, h=h, j=j, ell=ell, r=str(r),
                                              kappa=str(kap), R=str(R), K=str(K), sigma=sigma, lhs=str(lhs), rhs=str(rhs)))
                            if worst is None or rhs - lhs < worst:
                                worst, where = rhs - lhs, dict(l=l, g=g, h=h, j=j, sigma=sigma)
    return result(True, n_cases, margin=float(worst), tightest=where, sharp=float(const - worst / 8), slack=float(worst / 8),
                  tested_range=f"{lmin} <= l <= 13, g <= 13, h <= 49, j <= 4, three ell, four (r, kappa, R, K)",
                  notes="exact rationals, sigNOK unfolded; `slack` is how far the additive constant could drop")


def sigma_exponent(p):
    const, lmin = Q(p["const"]), int(p["l_min"])
    worst, where, n_cases = None, None, 0
    for l in range(lmin, 14):
        for g in range(0, 14):
            for h in range(0, 50):
                for j in range(1, 5):
                    n_cases += 1
                    sigE = max(0, math.ceil(_sig_core(l, g, h, j) + 1))           # Nat.ceil
                    B = Fraction(3, 2) * (h + 2 * g) / Fraction(l - 1) ** (j + 1) + Fraction(9, 4) * g + const
                    if sigE > B:
                        return result(False, n_cases, witness=dict(l=l, g=g, h=h, j=j, sigE=sigE, bound=str(B)))
                    if worst is None or B - sigE < worst:
                        worst, where = B - sigE, dict(l=l, g=g, h=h, j=j, sigE=sigE)
    return result(True, n_cases, margin=float(worst), tightest=where, sharp=float(const - worst), slack=float(worst),
                  tested_range=f"{lmin} <= l <= 13, g <= 13, h <= 49, j <= 4",
                  notes="exact rationals, sigE and Mpar unfolded")
