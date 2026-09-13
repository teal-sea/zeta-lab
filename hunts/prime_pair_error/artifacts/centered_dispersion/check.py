"""One fixed, bounded check of the centered dispersion argument.

Run from the repository root with .venv/bin/python. Exact checks concern
finite identities; floating Fourier checks do not prove asymptotic bounds.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import signal
import sys
import time
from fractions import Fraction as Q

for _name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[_name] = "1"

N = 216
R = 6
U = V = 8
Y = 14
GRID = 4 * N + 1
LIMIT_SECONDS = 60
HERE = Path(__file__).resolve().parent
PROOF = HERE.parents[1] / "CENTERED_DISPERSION.md"


def factor(n):
    out = {}
    for p in range(2, math.isqrt(n) + 1):
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def add(target, source, scale=1):
    for p, a in source.items():
        target[p] = target.get(p, 0) + scale * a
        if not target[p]:
            del target[p]


def alarm_handler(_signum, _frame):
    raise TimeoutError(f"fixed diagnostic exceeded {LIMIT_SECONDS} seconds")


def run():
    import numpy as np
    from mpmath import mp

    factors = [None] + [factor(n) for n in range(1, N + 1)]
    mu = [0] + [
        0 if any(a > 1 for a in factors[n].values())
        else (-1) ** len(factors[n]) for n in range(1, N + 1)
    ]
    phi = [0] + [
        math.prod((p - 1) * p ** (a - 1) for p, a in factors[n].items())
        for n in range(1, N + 1)
    ]
    divs = [None] + [
        [d for d in range(1, n + 1) if n % d == 0]
        for n in range(1, N + 1)
    ]
    lv = [None] + [
        {next(iter(factors[n])): 1} if len(factors[n]) == 1 else {}
        for n in range(1, N + 1)
    ]
    primes = [p for p in range(2, N + 1) if factors[p] == {p: 1}]
    assert U**5 <= N**2 < (U + 1)**5
    assert R**3 == N and Y == math.isqrt(N)

    av, bv = [{}], [{}]
    for t in range(1, N + 1):
        a, b = {}, {}
        if t <= V:
            add(a, lv[t])
        for d in divs[t]:
            if d <= U:
                add(a, factors[t // d], mu[d])
                for c in divs[t // d]:
                    if c <= V:
                        add(a, lv[c], -mu[d])
            else:
                for c in divs[t // d]:
                    if c > V:
                        add(b, lv[c], mu[d])
        combined = dict(a)
        add(combined, b)
        assert combined == lv[t], (t, a, b, lv[t])
        av.append(a)
        bv.append(b)

    semiprimes, squares = [], []
    for p in primes:
        if p <= U:
            continue
        if p * p <= N:
            assert av[p*p] == {p: 2} and bv[p*p] == {p: -1}
            squares.append(p*p)
        for q in primes:
            if p < q and p*q <= N:
                assert av[p*q] == {p: 1, q: 1}
                assert bv[p*q] == {p: -1, q: -1}
                semiprimes.append(p*q)
    assert semiprimes and squares

    def ram(q, n):
        return sum(d * mu[q // d] for d in divs[math.gcd(q, n)])

    def hsum(r):
        return sum((Q(mu[q]**2, phi[q]) for q in range(1, r+1)), Q())

    def ss(r, h):
        return sum((Q(mu[q]**2 * ram(q, h), phi[q]**2)
                    for q in range(1, r+1)), Q())

    lam = [Q()] + [
        sum((Q(mu[q] * ram(q, n), phi[q]) for q in range(1, R+1)), Q())
        for n in range(1, N+1)
    ]
    hr, hy = hsum(R), hsum(Y)
    br = Q(3, 2) * R * sum(Q(mu[q]**2 * q, phi[q])
                          for q in range(1, R+1))
    corr_lam = [
        sum((lam[n] * lam[n+h] for n in range(1, N-h+1)), Q())
        for h in range(N+1)
    ]
    eta = [corr_lam[h] - (N-h) * ss(R, h) for h in range(N+1)]
    assert all(abs(v) <= br for v in eta)
    model_norm = 2 * sum(v*v for v in eta[1:])
    assert model_norm <= 2 * N * br**2

    period = math.lcm(*range(1, R+1))
    assert 2*period <= N
    for h in range(period):
        assert sum(lam[n] * lam[n+h] for n in range(1, period+1)) == period*ss(R, h)

    cross_vec, deficit_vec, psi_vec = {}, {}, {}
    prime_power_checks = 0
    for n in range(1, N+1):
        add(psi_vec, lv[n])
        add(cross_vec, lv[n], lam[n])
        if lv[n]:
            p = next(iter(lv[n]))
            deficit = Q(p, p-1) * sum(
                (Q(mu[r]**2, phi[r]) for r in range(1, R//p+1)
                 if math.gcd(r, p) == 1), Q())
            assert lam[n] == hr - deficit
            add(deficit_vec, lv[n], deficit)
            prime_power_checks += 1
    expected_cross = {}
    add(expected_cross, psi_vec, hr)
    add(expected_cross, deficit_vec, -1)
    assert cross_vec == expected_cross

    with mp.workdps(50):
        def m(q):
            return mp.mpf(q.numerator) / q.denominator if isinstance(q, Q) else mp.mpf(q)

        def value(vec):
            return mp.fsum(m(a)*mp.log(p) for p, a in vec.items())

        lambda_mp = [mp.mpf(0)] + [value(v) for v in lv[1:]]
        lam_mp = list(map(m, lam))
        d_n = mp.fsum(v*v for v in lambda_mp)
        d_r = m(corr_lam[0])
        psi = value(psi_vec)
        s_r = mp.fsum((lambda_mp[n]-lam_mp[n])**2 for n in range(1, N+1))
        evaluated_s = d_n + N*m(hr) - 2*m(hr)*psi + 2*value(deficit_vec) + m(eta[0])
        assert abs(s_r-evaluated_s) < mp.mpf("1e-42")
        corr_prime = [mp.fsum(lambda_mp[n]*lambda_mp[n+h]
                             for n in range(1, N-h+1))
                      for h in range(N+1)]
        j_center = 2*mp.fsum((corr_prime[h]-(N-h)*m(ss(Y, h)))**2
                            for h in range(1, N+1))
        transfer = 2*mp.fsum((corr_prime[h]-m(corr_lam[h]))**2
                            for h in range(1, N+1))
        env = psi + N + R**2*(1+2*mp.log(R))
        envelope_bound = env**2*s_r - (d_n-d_r)**2
        assert transfer <= envelope_bound

        freqs = [(Q(a, q), Q(mu[q], phi[q])) for q in range(1, R+1)
                 for a in range(q) if math.gcd(a, q) == 1]
        kernel_defects = []
        for h in (0, 1, 2, 5, N-1, N):
            terms = []
            for x, wx in freqs:
                for z, wz in freqs:
                    if x == z:
                        continue
                    t = m(x-z)
                    kernel = (mp.exp(2j*mp.pi*(N-h+mp.mpf("0.5"))*t)
                              - mp.exp(1j*mp.pi*t)) / (2j*mp.sin(mp.pi*t))
                    terms.append(m(wx*wz)*mp.exp(-2j*mp.pi*h*m(z))*kernel)
            kernel_defects.append(abs(mp.fsum(terms)-m(eta[h])))
        assert max(kernel_defects) < mp.mpf("1e-42")

        angles = np.arange(GRID, dtype=float)/GRID
        expo = np.exp(2j*np.pi*np.outer(angles, np.arange(1, N+1)))
        f_grid = expo @ np.array([float(v) for v in lambda_mp[1:]])
        a_grid = expo @ np.array([float(value(v)) for v in av[1:]])
        b_grid = expo @ np.array([float(value(v)) for v in bv[1:]])

        def kernel_grid(x):
            beta = (angles-float(x)+0.5) % 1-0.5
            out = np.full(GRID, N, dtype=complex)
            mask = np.abs(beta) > 1e-14
            t = beta[mask]
            out[mask] = np.exp(1j*np.pi*(N+1)*t)*np.sin(np.pi*N*t)/np.sin(np.pi*t)
            return out

        h_grid = np.zeros(GRID, dtype=complex)
        vr_grid = np.zeros(GRID)
        vy_grid = np.zeros(GRID)
        for q in range(1, Y+1):
            for a in range(q):
                if math.gcd(a, q) == 1:
                    k = kernel_grid(Q(a, q))
                    term = mu[q]**2/phi[q]**2 * np.abs(k)**2
                    vy_grid += term
                    if q <= R:
                        h_grid += mu[q]/phi[q]*k
                        vr_grid += term
        aa, hh = np.abs(f_grid)**2, np.abs(h_grid)**2
        g = aa-vy_grid-float(d_n-N*m(hy))
        x = aa-hh-float(d_n-d_r)
        z = hh-vr_grid-float(d_r-N*m(hr))
        tail = vy_grid-vr_grid-N*float(hy-hr)
        w = f_grid-h_grid
        phase_loss = 4*np.mean(np.imag(f_grid*np.conj(h_grid))**2)
        weighted_transfer = np.mean(np.abs(f_grid+h_grid)**2*np.abs(w)**2)
        grid_j = np.mean(g*g)
        grid_d = np.mean(x*x)
        expansion_j = (np.mean(aa**2)-2*np.mean(aa*vy_grid)
                       + np.mean(vy_grid**2)-float(d_n-N*m(hy))**2)
        phase_d = weighted_transfer-phase_loss-float(d_n-d_r)**2
        defects = {
            "vaughan_fourier": float(np.max(np.abs(f_grid-a_grid-b_grid))),
            "centered_decomposition": float(np.max(np.abs(g-x-z+tail))),
            "centered_norm_relative": abs(grid_j/float(j_center)-1),
            "four_integral_expansion_relative": abs(expansion_j/float(j_center)-1),
            "transfer_norm_relative": abs(grid_d/float(transfer)-1),
            "phase_identity_relative": abs(phase_d/float(transfer)-1),
            "model_norm_relative": abs(np.mean(z*z)/float(model_norm)-1),
        }
        assert defects["vaughan_fourier"] < 1e-9
        assert defects["centered_decomposition"] < 1e-9
        assert all(v < 1e-10 for k, v in defects.items() if k.endswith("relative"))
        return {
            "status": "passed",
            "parameters": {"N": N, "U": U, "V": V, "R": R, "y": Y, "grid": GRID},
            "limits": {"seconds": LIMIT_SECONDS, "numerical_threads": 1, "cutoffs": 1},
            "exact_checks": {
                "vaughan_coefficients": N,
                "distinct_semiprime_products": semiprimes,
                "prime_squares": squares,
                "prime_power_formula": prime_power_checks,
                "uniform_remainder_checks": N+1,
                "full_period_correlations": period,
                "prime_model_cross_identity": 1,
                "h_R": str(hr), "B_R": str(br),
                "largest_remainder": str(max(map(abs, eta))),
                "largest_remainder_over_bound": str(max(map(abs, eta))/br),
                "model_centered_norm_squared": str(model_norm),
            },
            "mp50_checks": {
                "signed_kernel_checks": len(kernel_defects),
                "largest_kernel_defect": mp.nstr(max(kernel_defects), 16),
                "s_R": mp.nstr(s_r, 22),
                "evaluated_s_R_defect": mp.nstr(abs(s_r-evaluated_s), 16),
                "prime_centered_norm_squared": mp.nstr(j_center, 22),
                "complete_transfer_norm_squared": mp.nstr(transfer, 22),
                "transfer_envelope_bound": mp.nstr(envelope_bound, 22),
                "deficit_D_N_R": mp.nstr(value(deficit_vec), 22),
            },
            "floating_grid": {
                "defects": defects,
                "weighted_transfer_before_phase_subtraction": float(weighted_transfer),
                "phase_loss": float(phase_loss),
                "constant_square_subtraction": float(d_n-d_r)**2,
                "scope": "Finite float cross-checks, not asymptotic evidence or interval enclosures.",
            },
        }


if __name__ == "__main__":
    started = time.perf_counter()
    signal.signal(signal.SIGALRM, alarm_handler)
    signal.alarm(LIMIT_SECONDS)
    record = {"status": "failed"}
    exit_code = 1
    try:
        record = run()
        exit_code = 0
    except Exception as exc:
        record.update(error_type=type(exc).__name__, error=str(exc))
    finally:
        signal.alarm(0)
        record["elapsed_seconds"] = time.perf_counter()-started
        record["proof_sha256"] = hashlib.sha256(PROOF.read_bytes()).hexdigest()
        record["script_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        record["base_commit"] = "2da62eb9842db72d4f6bad09c6f13efe384d6ab7"
        (HERE / "result.json").write_text(json.dumps(record, indent=2)+"\n")
        print(json.dumps(record, indent=2))
    sys.exit(exit_code)
