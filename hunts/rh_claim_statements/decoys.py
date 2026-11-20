"""Decoys: the same statement shapes on neighbours that carry no arithmetic.

A claim that a matched null also satisfies says nothing about the primes or
about zeta. These three controls ask, for three of the sharper claims, whether
a non-arithmetic neighbour passes the same test.
"""
from __future__ import annotations

import math
import random

import numpy as np
from flint import arb, ctx

from . import checks_analytic as ca
from . import common as C


def hurwitz_real_zeros():
    """C08's shape, zeta(sigma) != 0 on (0, 1), for Hurwitz zeta(sigma, a)."""
    out = {}
    for a in ("1/4", "1/3", "2/3", "3/4"):
        r = ca.real_nonvanishing(dict(a="0", b="1", hurwitz=a))
        out[a] = dict(holds=r["holds"], witness=r.get("witness"))
    return dict(decoy="Hurwitz zeta(sigma, a) on (0, 1)", by_parameter=out,
                reading="zeta(0, a) = 1/2 - a is positive for a < 1/2 while zeta(sigma, a) -> -oo at 1-, so the "
                        "statement fails for a = 1/4 and 1/3 and the test says so; it holds for a = 2/3 and 3/4")


def random_sequences_l1(samples=2000, seed=20261120):
    """C16's shape, 1/(20(q+1)) <= L(1, chi), for random mean-zero +-1 sequences of period q."""
    rng = random.Random(seed)
    out = {}
    with ctx.workprec(64):
        for q in (8, 12, 20, 30, 60):
            psi = [float((arb(n) / q).digamma().mid()) for n in range(1, q + 1)]
            bound = 1.0 / (20 * (q + 1))
            bad = neg = 0
            for _ in range(samples):
                signs = [1] * (q // 2) + [-1] * (q // 2)
                rng.shuffle(signs)
                L = -sum(s * p for s, p in zip(signs, psi)) / q
                bad += L < bound - 1e-9
                neg += L < -1e-9
            out[str(q)] = dict(fraction_violating=bad / samples, fraction_negative=neg / samples)
    return dict(decoy="random +-1 sequences of period q with zero mean, L(1, a) = sum a(n)/n", samples=samples, seed=seed,
                by_period=out,
                reading="about half of the random sequences have L(1, a) < 0: the lower bound is a statement about "
                        "characters, not about mean-zero periodic sequences, although its constant is loose")


def cramer_prime_count(samples=200, seed=20261120, N=131072):
    """C21's shape, pi(m) log m < 1.26 m for 1 <= m < 2^17, for Cramer random sets."""
    rng = np.random.default_rng(seed)
    n = np.arange(N, dtype=float)
    prob = np.zeros(N)
    prob[2] = 1.0
    prob[3:] = np.minimum(1.0, 1.0 / np.log(n[3:]))
    logs = np.zeros(N); logs[1:] = np.log(n[1:])
    viol = viol1000 = 0
    maxima = []
    for _ in range(samples):
        cnt = np.cumsum(rng.random(N) < prob)
        ratio = np.zeros(N); ratio[1:] = cnt[1:] * logs[1:] / n[1:]
        viol += bool((ratio >= 1.26).any())
        viol1000 += bool((ratio[1000:] >= 1.26).any())
        maxima.append(float(ratio.max()))
    return dict(decoy="Cramer random sets: n >= 3 is kept with probability 1/log n, independently", samples=samples, seed=seed,
                fraction_violating=viol / samples, fraction_violating_beyond_1000=viol1000 / samples,
                median_max_ratio=float(np.median(maxima)),
                reading="a density-matched random set fails the bound in most samples (through its fluctuations at "
                        "small m), so the constant 1.26 is specific to the actual primes; beyond m = 1000 the random "
                        "sets fail it less often")


def run_all():
    return dict(hurwitz_real_zeros=hurwitz_real_zeros(), random_sequences_l1=random_sequences_l1(),
                cramer_prime_count=cramer_prime_count())
