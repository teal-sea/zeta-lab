"""Exact finite checks for early lifts and the N=14 arithmetic-cap example.

This is a bounded check of the accompanying argument, not a uniform estimate
for psi(N)-N. Coefficients and logarithmic prime coefficients are Fractions.
No coefficient search or primality oracle enters the perfect-power cap.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from fractions import Fraction as F
from functools import lru_cache
import importlib
import json
from pathlib import Path
import platform
import time


BASE6 = {1: F(1), 2: F(-1), 3: F(-1), 6: F(-1)}
CHEBYSHEV30 = {1: F(1), 2: F(-1), 3: F(-1), 5: F(-1), 30: F(1)}
SEEDS = (("base6", 6, 6, BASE6), ("chebyshev30", 30, 6, CHEBYSHEV30))
CUTOFFS = (*range(2, 129), 1296)
LEVELS = (0, 1, 2)


def natural(n, minimum=0):
    if type(n) is not int or n < minimum:
        raise ValueError(f"expected integer >= {minimum}, got {n!r}")
    return n


def combine(*terms):
    """Add (rational multiplier, prime-log coefficient mapping) terms."""
    out = {}
    for multiplier, vector in terms:
        for p, coefficient in vector.items():
            out[p] = out.get(p, F(0)) + F(multiplier) * coefficient
    return {p: a for p, a in sorted(out.items()) if a}


def floor_sum(c, q):
    natural(q)
    return sum((F(a) * (q // j) for j, a in c.items()), F(0))


def validate_seed(c, period, radix):
    """Verify balance and the entire seed period; return its height H."""
    natural(period, 2)
    natural(radix, 2)
    if radix > period or not c:
        raise ValueError("need a nonempty seed and radix <= period")
    if any(type(j) is not int or j < 1 or period % j for j in c):
        raise ValueError("every seed index must divide the period")
    if any(type(a) not in (int, F) for a in c.values()):
        raise ValueError("seed coefficients must be exact integers or Fractions")
    if sum((F(a) / j for j, a in c.items()), F(0)):
        raise ValueError("seed is not balanced")
    values = [floor_sum(c, r) for r in range(period)]
    if any(v < (1 if 1 <= r < radix else 0) for r, v in enumerate(values)):
        raise ValueError("seed fails its period or [1, radix) lower bound")
    return max(values)


def early_lift(c, period, radix, K):
    validate_seed(c, period, radix)
    natural(K)
    out = {}
    for k in range(K + 1):
        for j, a in c.items():
            index = j * radix**k
            out[index] = out.get(index, F(0)) + a
    return {j: F(a) for j, a in sorted(out.items()) if a}


def integer_root(n, k):
    """Floor kth root by integer comparisons, including large perfect powers."""
    natural(n)
    natural(k, 1)
    if k == 1 or n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length() + k - 1) // k)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi**k <= n else lo


@lru_cache(maxsize=None)
def perfect_power_exponent(n):
    """Largest r with n=a^r, a>=2; use r(1)=1 and u(1)=0."""
    natural(n, 1)
    for r in range(n.bit_length() - 1, 1, -1):
        if integer_root(n, r)**r == n:
            return r
    return 1


@lru_cache(maxsize=None)
def trial_factors(n):
    """Independent trial-division oracle, used only to check logarithmic identities."""
    natural(n, 1)
    factors, divisor = [], 2
    while divisor * divisor <= n:
        exponent = 0
        while n % divisor == 0:
            n //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor += 1
    if n > 1:
        factors.append((n, 1))
    return tuple(factors)


def log_vector(n):
    return {p: F(e) for p, e in trial_factors(n)}


def mangoldt_vector(n):
    factors = trial_factors(n)
    return {factors[0][0]: F(1)} if len(factors) == 1 else {}


def cap_vector(n, cap="log"):
    if cap not in ("log", "perfect_power"):
        raise ValueError(f"unknown cap {cap!r}")
    return combine((F(1, perfect_power_exponent(n)) if cap == "perfect_power" else F(1), log_vector(n)))


@lru_cache(maxsize=None)
def factorial_vector_items(n):
    """Legendre factorial exponents, independent of the quotient-cell assembly."""
    natural(n)
    result = {}
    for p in range(2, n + 1):
        if trial_factors(p) != ((p, 1),):
            continue
        value, power = 0, p
        while power <= n:
            value += n // power
            power *= p
        result[p] = F(value)
    return tuple(result.items())


def cells(N, cap="log"):
    natural(N, 2)
    masses, caps = {}, {}
    for d in range(2, N + 1):
        q = N // d
        masses[q] = combine((1, masses.get(q, {})), (1, mangoldt_vector(d)))
        caps[q] = combine((1, caps.get(q, {})), (1, cap_vector(d, cap)))
    return masses, caps


def paid_cost_vectors(N, c, cap="log"):
    masses, caps = cells(N, cap)
    B = combine(*((a, dict(factorial_vector_items(N // j))) for j, a in c.items()))
    convolution = combine(*((floor_sum(c, q), m) for q, m in masses.items()))
    if B != convolution:
        raise AssertionError("factorial and independent Mangoldt routes disagree")
    penalty = combine(*((max(F(0), 1 - floor_sum(c, q)), u) for q, u in caps.items()))
    return {"factorial": B, "penalty": penalty, "total": combine((1, B), (1, penalty))}


def require_complete_cost(N, c, claimed_total, cap="log"):
    if claimed_total != paid_cost_vectors(N, c, cap)["total"]:
        raise ValueError("claimed total omits or changes part of the paid cost")


def nonnegative_coefficients(vector):
    """A sufficient exact sign check; never treats a mixed-sign vector as decided."""
    return all(a >= 0 for a in vector.values())


def verify_n14():
    c = {1: F(1), 2: F(-1), 3: F(-3, 2)}
    m, w = cells(14)
    assert set(m) == {1, 2, 3, 4, 7}
    h = {q: {2: a} for q, a in {1: F(-1, 2), 2: F(1, 2), 3: F(1), 4: F(0), 7: F(-1, 2)}.items()}
    x = {q: combine((1, m[q]), (1, h[q])) for q in m}
    for q in m:
        assert nonnegative_coefficients(x[q])
        assert nonnegative_coefficients(combine((1, w[q]), (-1, x[q])))
    for j in (1, 2, 3):
        assert not combine(*((q // j, h[q]) for q in m))
        assert combine(*((q // j, x[q]) for q in m)) == dict(factorial_vector_items(14 // j))
    psi = combine(*((1, v) for v in m.values()))
    original = paid_cost_vectors(14, c)
    refined = paid_cost_vectors(14, c, "perfect_power")
    gain = {2: F(1, 2)}
    assert combine((1, original["total"]), (-1, psi)) == gain
    assert combine(*((1, hq) for hq in h.values())) == gain
    assert refined["total"] == psi
    assert original["penalty"] and original["factorial"] != original["total"]
    return {"N": 14, "support": 3, "coefficients": c,
            "W": {q: floor_sum(c, q) for q in sorted(m)}, "psi": psi,
            "primal_original": original, "primal_refined": refined,
            "dual_mass": x, "dual_shift": h, "original_excess": gain,
            "refined_excess": {}, "factorial_moments_checked": 3,
            "cap_rows_checked": len(m)}


def leading_constant_vector(seed, radix):
    """Exact prime-log coefficients of kappa/(1-1/radix)."""
    natural(radix, 2)
    return combine(*((-F(a) / j / (1 - F(1, radix)), log_vector(j))
                     for j, a in seed.items()))


def bound_assertions(seed, period, radix, N, K):
    """Return exact rational-plus-log expressions whose nonnegativity is checked."""
    H = validate_seed(seed, period, radix)
    c = early_lift(seed, period, radix, K)
    cost = paid_cost_vectors(N, c)
    R, A = radix**(K + 1), sum(map(abs, seed.values()), F(0))
    main = combine((F(N) * (1 - F(1, R)), leading_constant_vector(seed, radix)))
    remainder = combine(*((A, combine((1, log_vector(N)), (-1, log_vector(radix**k))))
                          for k in range(K + 1) if N > radix**k))
    remainder_constant = A * (K + 1)
    penalty_bound = (combine((H / (1 - F(1, radix)) * F(N, R),
                             combine((1, log_vector(N)), (-1, log_vector(R))))) if N > R else {})
    difference = combine((1, cost["factorial"]), (-1, main))
    return (("penalty", F(0), combine((1, penalty_bound), (-1, cost["penalty"]))),
            ("factorial_upper", remainder_constant, combine((1, remainder), (-1, difference))),
            ("factorial_lower", remainder_constant, combine((1, remainder), (1, difference))),
            ("complete_upper", remainder_constant,
             combine((1, main), (1, remainder), (1, penalty_bound), (-1, cost["total"]))))


def _dyadic(man, exponent):
    return F(int(man)) * (F(2) ** int(exponent))


@contextmanager
def log_intervals(backend, dps):
    """Yield rational log enclosures without leaving any precision state changed."""
    cache = {}
    if backend == "python-flint":
        from flint import arb, ctx
        old = ctx.prec
        ctx.prec = 4 * dps + 32
        def evaluate(n):
            a = arb(n).log()
            return tuple(_dyadic(*endpoint.man_exp()) for endpoint in (a.lower(), a.upper()))
        restore = lambda: setattr(ctx, "prec", old)
    elif backend == "mpmath.iv":
        import mpmath as mp
        old = mp.iv.prec
        mp.iv.dps = dps
        def evaluate(n):
            endpoints = mp.iv.log(mp.iv.mpf(n))._mpi_
            return tuple(_dyadic(-man if sign else man, exponent)
                         for sign, man, exponent, _ in endpoints)
        restore = lambda: setattr(mp.iv, "prec", old)
    else:
        raise ValueError(f"unknown backend {backend!r}")
    def logarithm(n):
        if n not in cache:
            cache[n] = evaluate(n)
        return cache[n]
    try:
        yield logarithm
    finally:
        restore()


def enclose_expression(constant, vector, logarithm):
    lo = hi = F(constant)
    for p, a in vector.items():
        left, right = logarithm(p)
        lo += a * (left if a >= 0 else right)
        hi += a * (right if a >= 0 else left)
    return lo, hi


def numeric_checks(assertions):
    reports, refined = {}, {}
    for backend, module in (("python-flint", "flint"), ("mpmath.iv", "mpmath")):
        try:
            imported = importlib.import_module(module)
        except ImportError as exc:
            reports[backend] = {"status": "UNAVAILABLE", "reason": str(exc)}
            continue
        previous = None
        for dps in (35, 70):
            with log_intervals(backend, dps) as logarithm:
                current = [enclose_expression(a, v, logarithm) for _, a, v in assertions]
            for i, (lo, hi) in enumerate(current):
                if lo < 0:
                    raise AssertionError(f"{backend} {dps} digits cannot prove {assertions[i][0]} >= 0: {lo}, {hi}")
                if previous is not None and max(lo, previous[i][0]) > min(hi, previous[i][1]):
                    raise AssertionError("precision refinements disagree")
            previous = current
        refined[backend] = current
        reports[backend] = {"status": "PASS", "version": imported.__version__,
                            "decimal_precision_requests": [35, 70],
                            "assertions_per_precision": len(assertions),
                            "precision_overlap_checks": len(assertions)}
    crosschecks = 0
    if len(refined) == 2:
        left, right = refined.values()
        for a, b in zip(left, right, strict=True):
            if max(a[0], b[0]) > min(a[1], b[1]):
                raise AssertionError("independent log backends disagree")
            crosschecks += 1
    return {"backends": reports, "cross_backend_overlap_checks": crosschecks,
            "available_backends": list(refined)}


def run_checks():
    start = time.monotonic()
    counts = {"seeds": 0, "seed_period_rows": 0, "floor_rows": 0,
              "base6_deficit_rows": 0, "truncation_cases": 0, "cap_integers": 0}
    assert [floor_sum(BASE6, q) for q in range(6)] == [0, 1, 1, 1, 1, 2]
    assertions = []
    for name, period, radix, seed in SEEDS:
        H = validate_seed(seed, period, radix)
        counts["seeds"] += 1
        counts["seed_period_rows"] += period
        for K in LEVELS:
            c = early_lift(seed, period, radix, K)
            R = radix**(K + 1)
            for q in range(1, max(CUTOFFS) + 1):
                W = floor_sum(c, q)
                direct = sum((floor_sum(seed, q // radix**k) for k in range(K + 1)), F(0))
                assert W == direct and W >= 0
                assert 0 <= max(0, 1 - W) <= 1
                assert W >= 1 if q < R else True
                assert floor_sum(seed, q) == floor_sum(seed, q % period) <= H
                tail, power = F(0), R
                while power <= q:
                    tail += floor_sum(seed, q // power)
                    power *= radix
                assert max(0, 1 - W) <= tail
                counts["floor_rows"] += 1
                if name == "base6":
                    assert max(0, 1 - W) == int(q % R == 0)
                    counts["base6_deficit_rows"] += 1
            for N in CUTOFFS:
                rows = bound_assertions(seed, period, radix, N, K)
                assertions.extend((f"{name}:N={N}:K={K}:{label}", a, v) for label, a, v in rows)
                counts["truncation_cases"] += 1
    for n in range(1, max(CUTOFFS) + 1):
        cap, truth = cap_vector(n, "perfect_power"), mangoldt_vector(n)
        assert nonnegative_coefficients(combine((1, cap), (-1, truth)))
        factors = trial_factors(n)
        if len(factors) == 1:
            assert cap == truth
        counts["cap_integers"] += 1
    example = verify_n14()
    numerics = numeric_checks(assertions)
    complete = len(numerics["available_backends"]) == 2
    return {"status": "PASS" if complete else "EXACT_PASS_NUMERICAL_COVERAGE_INCOMPLETE",
            "python": platform.python_version(), "runtime_seconds": time.monotonic() - start,
            "arithmetic": "Fraction floor sums and prime-log vectors; independent directed log intervals",
            "cutoffs": list(CUTOFFS), "levels": list(LEVELS), "counts": counts,
            "numeric_inequalities": len(assertions), "numeric_checks": numerics, "n14": example,
            "finite_assertions": ["seed balance, period and height", "early-lift and omitted-tail identities",
                                  "base6 exact divisibility deficit", "complete penalty and factorial error bounds",
                                  "perfect-power cap dominates trial-factored Mangoldt mass", "N14 primal/dual equality"],
            "nonclaims": ["finite checks do not prove the general lemma", "no uniform estimate for psi(N)-N",
                          "no asymptotic improvement from fixed seeds", "no novelty or RH conclusion"]}


def json_ready(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): json_ready(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_ready(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        report = run_checks()
    except Exception as exc:
        args.output.write_text(json.dumps({"status": "FAIL", "error_type": type(exc).__name__, "error": str(exc)}, indent=2) + "\n")
        raise
    args.output.write_text(json.dumps(json_ready(report), indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "counts": report["counts"],
                      "numeric_inequalities": report["numeric_inequalities"], "output": str(args.output)}))
    return 0 if report["status"] == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
