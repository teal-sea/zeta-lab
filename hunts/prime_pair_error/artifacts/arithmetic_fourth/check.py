"""Bounded checks of ARITHMETIC_FOURTH.md, never an asymptotic experiment."""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import signal
import sys
import time
from collections import defaultdict
from fractions import Fraction

for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[name] = "1"

from mpmath import mp
from scipy.integrate import quad

BASE = "2da62eb9842db72d4f6bad09c6f13efe384d6ab7"


def factor(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def root_fifth(n):
    low, high = 0, n + 1
    while high - low > 1:
        middle = (low + high) // 2
        if middle ** 5 <= n:
            low = middle
        else:
            high = middle
    return low


def tables(N):
    fac = [factor(n) for n in range(N + 1)]
    mu = [0] + [0 if any(a > 1 for a in fac[n].values())
                else (-1) ** len(fac[n]) for n in range(1, N + 1)]
    lam = [{} for _ in range(N + 1)]
    divs = [[] for _ in range(N + 1)]
    for n in range(1, N + 1):
        if len(fac[n]) == 1:
            lam[n] = {next(iter(fac[n])): 1}
        for multiple in range(n, N + 1, n):
            divs[multiple].append(n)
    return fac, mu, lam, divs


def add_vector(out, vector, scale=1):
    for p, a in vector.items():
        out[p] = out.get(p, 0) + scale * a


def clean(vector):
    return {p: a for p, a in vector.items() if a}


def identity_case(N):
    assert N <= 625
    U = V = root_fifth(N * N)
    fac, mu, lam, divs = tables(N)
    checked = unique = powers = 0
    for t in range(1, N + 1):
        result = dict(lam[t]) if t <= V else {}
        for d in divs[t]:
            if d <= U:
                add_vector(result, fac[t // d], mu[d])
                for c in divs[t // d]:
                    if c <= V:
                        add_vector(result, lam[c], -mu[d])
            else:
                for c in divs[t // d]:
                    if c > V:
                        add_vector(result, lam[c], mu[d])
        assert clean(result) == lam[t], (N, t, result, lam[t])
        checked += 1
        if len(fac[t]) == 1 and next(iter(fac[t].values())) >= 2:
            powers += 1
        v, w, h = {}, {}, {}
        for c in divs[t]:
            if c <= V or not lam[c]:
                continue
            add_vector(v, lam[c])
            add_vector(w if next(iter(fac[c].values())) == 1 else h, lam[c])
        combined = dict(w)
        add_vector(combined, h)
        assert clean(combined) == v
        if V < t <= N // (U + 1):
            assert len(w) <= 1
            if w:
                p = next(iter(w))
                assert w[p] == 1 and fac[t][p] == 1
                assert t // p < V
            unique += 1
    return {"N": N, "U": U, "V": V, "identities_checked": checked,
            "proper_prime_powers_in_identity": powers,
            "unique_prime_support_cases": unique, "status": "passed"}


def intervals(N, Q):
    major = []
    for q in range(1, Q + 1):
        for a in range(1, q + 1):
            if math.gcd(a, q) != 1:
                continue
            center = Fraction(a % q, q)
            radius = Fraction(Q, q * N)
            lo, hi = center - radius, center + radius
            if lo < 0:
                major.extend([(Fraction(0), hi), (1 + lo, Fraction(1))])
            else:
                major.append((lo, hi))
    major.sort()
    minor, end = [], Fraction(0)
    for lo, hi in major:
        assert lo >= end
        if lo > end:
            minor.append((end, lo))
        end = hi
    if end < 1:
        minor.append((end, Fraction(1)))
    return major, minor


def real_fraction(x):
    return mp.mpf(x.numerator) / x.denominator


def kernel_values(N, Q, mu, divs, minor):
    phi = [sum(math.gcd(a, q) == 1 for a in range(1, q + 1))
           for q in range(1, Q + 1)]
    zero = 1 - mp.mpf(2 * Q) / N * mp.fsum(
        mp.mpf(phi[q - 1]) / q for q in range(1, Q + 1))
    kernel, max_error = [zero], mp.mpf(0)
    for r in range(2 * N + 1):
        if r:
            value = -mp.fsum(
                sum(d * mu[q // d] for d in divs[math.gcd(q, r)])
                * mp.sin(2 * mp.pi * r * Q / (q * N)) / (mp.pi * r)
                for q in range(1, Q + 1))
            kernel.append(value)
            independent = mp.fsum(
                (mp.exp(2j * mp.pi * r * real_fraction(hi))
                 - mp.exp(2j * mp.pi * r * real_fraction(lo)))
                / (2j * mp.pi * r) for lo, hi in minor)
        else:
            value = zero
            independent = mp.fsum(real_fraction(hi - lo) for lo, hi in minor)
        max_error = max(max_error, abs(value - independent))
    assert max_error < mp.mpf("1e-45")
    return kernel, max_error


def convolution(a, b):
    result = defaultdict(mp.mpf)
    for t, x in a.items():
        for s, y in b.items():
            result[t + s] += x * y
    return dict(result)


def autocorrelation(a):
    result = defaultdict(mp.mpf)
    for t, x in a.items():
        for s, y in a.items():
            result[t - s] += x * y
    return dict(result)


def integral(coefficients, kernel, absolute=False):
    terms = [value * kernel[abs(r)] for r, value in coefficients.items()]
    return mp.fsum(abs(x) if absolute else x for x in terms)


def block_case():
    N = 256
    M = U = V = root_fifth(N * N)
    K, Q = 2 * V, math.isqrt(N) // 3
    fac, mu, lam, divs = tables(N)
    major, minor = intervals(N, Q)
    kernels, kernel_error = kernel_values(N, Q, mu, divs, minor)
    v, w, h = [mp.mpf(0)] * (N + 1), [mp.mpf(0)] * (N + 1), [mp.mpf(0)] * (N + 1)
    prime_of = {}
    for n in range(1, N + 1):
        for d in divs[n]:
            if d > V and lam[d]:
                p = next(iter(lam[d]))
                value = mp.log(p)
                v[n] += value
                if fac[d][p] == 1:
                    w[n] += value
                    prime_of[n] = p
                else:
                    h[n] += value
        assert abs(v[n] - w[n] - h[n]) < mp.mpf("1e-47")
    bp, bh, rows, raw_pairs = defaultdict(mp.mpf), defaultdict(mp.mpf), {}, []
    for m in range(M + 1, 2 * M + 1):
        row = {}
        for n in range(K + 1, min(2 * K, N // m) + 1):
            if w[n]:
                row[m * n] = w[n]
                bp[m * n] += mu[m] * w[n]
            if h[n]:
                bh[m * n] += mu[m] * h[n]
            raw_pairs.append((m * n, mu[m] * w[n], mu[m] * h[n]))
        rows[m] = row
    bp, bh = {t: x for t, x in bp.items() if x}, {t: x for t, x in bh.items() if x}
    A = autocorrelation(convolution(bp, bp))
    H = autocorrelation(convolution(bh, bh))
    S, repeated = defaultdict(mp.mpf), defaultdict(mp.mpf)
    for m, row in rows.items():
        row_corr = autocorrelation(row)
        for r, x in row_corr.items():
            S[r] += mu[m] ** 2 * x
        for r, x in convolution(row_corr, row_corr).items():
            repeated[r] += mu[m] ** 4 * x
    P = convolution(S, S)
    P = {r: 2 * P.get(r, mp.mpf(0)) - repeated.get(r, mp.mpf(0))
         for r in set(P) | set(repeated)}
    assert min(P.values()) > -mp.mpf("1e-40")
    R = {r: A.get(r, mp.mpf(0)) - P.get(r, mp.mpf(0)) for r in set(A) | set(P)}
    ip, ih, paired, residual = (integral(c, kernels) for c in (A, H, P, R))
    assert min(ip, ih, paired) > -mp.mpf("1e-38")
    assert abs(ip - paired - residual) < mp.mpf("1e-38")
    for j in range(11):
        alpha = mp.mpf(j) / 11
        magnitudes = [mu[m] ** 2 * abs(mp.fsum(x * mp.exp(2j * mp.pi * t * alpha)
                      for t, x in row.items())) ** 2 for m, row in rows.items()]
        direct = 2 * mp.fsum(magnitudes) ** 2 - mp.fsum(x * x for x in magnitudes)
        expanded = mp.fsum(x * mp.exp(2j * mp.pi * r * alpha) for r, x in P.items())
        assert abs(direct - expanded) < mp.mpf("1e-36")
    float_pairs = [(t, float(p), float(hh)) for t, p, hh in raw_pairs]
    evaluations = 0

    def integrand(alpha, position):
        nonlocal evaluations
        evaluations += 1
        z = sum(complex(math.cos(2 * math.pi * t * alpha),
                        math.sin(2 * math.pi * t * alpha)) * values[position]
                for t, *values in float_pairs)
        return abs(z) ** 4

    quadratures, reported_errors = [], []
    for position, reference in enumerate((ip, ih)):
        values = [quad(integrand, float(lo), float(hi), args=(position,),
                       epsabs=1e-7, epsrel=1e-10, limit=200)
                  for lo, hi in minor]
        value = sum(x for x, error in values)
        error = sum(error for x, error in values)
        assert abs(mp.mpf(value) - reference) < mp.mpf("1e-8") * max(1, abs(reference))
        quadratures.append(value)
        reported_errors.append(error)
    ns = [n for n in range(K + 1, min(2 * K, N // (M + 1)) + 1) if w[n]]
    distinct_pairs, maximum_bucket = 0, 0
    for n1 in ns:
        for n4 in ns:
            if prime_of[n1] == prime_of[n4]:
                continue
            d = n4 // math.gcd(n1, n4)
            assert d >= prime_of[n4] > U
            buckets = defaultdict(int)
            for m in range(M + 1, 2 * M + 1):
                buckets[m % d] += 1
            maximum_bucket = max(maximum_bucket, max(buckets.values()))
            distinct_pairs += 1
    assert distinct_pairs > 0 and maximum_bucket == 1
    report = {"N": N, "U": U, "V": V, "M": M, "K": K, "Q": Q,
              "raw_pairs": len(raw_pairs), "prime_coefficients_nonzero": len(bp),
              "proper_power_coefficients_nonzero": len(bh),
              "minor_intervals": len(minor), "kernel_integers_checked": 2 * N + 1,
              "kernel_max_error": mp.nstr(kernel_error, 10),
              "kernel_zero": mp.nstr(kernels[0], 25),
              "prime_fourth_full_circle": mp.nstr(A.get(0, 0), 25),
              "prime_fourth_r0_contribution": mp.nstr(kernels[0] * A.get(0, 0), 25),
              "prime_fourth_off_diagonal": mp.nstr(ip - kernels[0] * A.get(0, 0), 25),
              "prime_fourth_minor": mp.nstr(ip, 25),
              "prime_absolute_kernel_completion": mp.nstr(integral(A, kernels, True), 25),
              "paired_full_circle": mp.nstr(P.get(0, 0), 25),
              "paired_minor": mp.nstr(paired, 25),
              "nonpaired_r0_contribution": mp.nstr(kernels[0] * R.get(0, 0), 25),
              "nonpaired_off_diagonal": mp.nstr(residual - kernels[0] * R.get(0, 0), 25),
              "nonpaired_minor": mp.nstr(residual, 25),
              "proper_power_fourth_minor": mp.nstr(ih, 25),
              "independent_float_quadratures": quadratures,
              "quad_reported_absolute_errors": reported_errors,
              "quad_evaluations": evaluations,
              "distinct_prime_slope_pairs_checked": distinct_pairs,
              "maximum_progression_bucket": maximum_bucket, "status": "passed"}
    return report


def timed_out(signum, frame):
    raise TimeoutError("60-second diagnostic cap reached")


def main():
    start = time.monotonic()
    here = Path(__file__).resolve()
    root = here.parents[4]
    report = {"status": "running", "base_revision": BASE, "processes": 1,
              "numerical_threads": 1, "decimal_precision": 50,
              "wall_limit_seconds": 60, "identity_cases": [],
              "identity_cutoffs_requested": [36, 256, 625], "fourier_blocks_requested": 1,
              "scope": "bounded identities and finite quadrature, no asymptotic inference"}
    signal.signal(signal.SIGALRM, timed_out)
    signal.alarm(60)
    code = 0
    try:
        with mp.workdps(50):
            for N in (36, 256, 625):
                report["identity_cases"].append(identity_case(N))
            report["block_case"] = block_case()
        report["status"] = "passed"
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = {"type": type(exc).__name__, "message": str(exc)}
        code = 1
    finally:
        signal.alarm(0)
        report["elapsed_seconds"] = round(time.monotonic() - start, 6)
        report["identity_cutoffs_completed"] = len(report["identity_cases"])
        report["fourier_blocks_completed"] = int("block_case" in report)
        report["script_sha256"] = hashlib.sha256(here.read_bytes()).hexdigest()
        report["proof_sha256"] = hashlib.sha256(
            (root / "hunts/prime_pair_error/ARITHMETIC_FOURTH.md").read_bytes()).hexdigest()
        text = json.dumps(report, sort_keys=True, indent=2) + "\n"
        here.with_name("result.json").write_text(text)
        print(text, end="")
    return code


if __name__ == "__main__":
    sys.exit(main())
