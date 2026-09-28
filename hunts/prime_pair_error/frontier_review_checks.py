"""Fresh bounded audit diagnostics. All numbers are non-enclosing numerics.

No repository implementation or author's diagnostic is imported.
Planned workload: q <= 24; N <= 65; fixed complex exponent; under one minute.
"""
import cmath
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
from flint import dirichlet_char

mp.mp.dps = 45
ROOT = Path(__file__).parent


def factors(n):
    result = {}
    for p in range(2, n + 1):
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        if n == 1:
            break
    return result


def mu(n):
    fs = factors(n)
    return 0 if any(a > 1 for a in fs.values()) else (-1) ** len(fs)


def units(q):
    return [a for a in range(1, q + 1) if math.gcd(a, q) == 1]


def cv(z):
    return complex(float(z.real), float(z.imag))


def chars(q):
    return [dirichlet_char(q, a) for a in units(q)]


def tau(ch, q):
    return sum(cv(ch(a)) * cmath.exp(2j * math.pi * a / q) for a in units(q))


gauss = {"characters": 0, "noncoprime_repetition_cases": 0,
         "max_induction_defect": 0.0, "max_diagonalization_defect": 0.0,
         "max_gauss_mass_defect": 0.0}
for q in range(1, 25):
    cs = chars(q)
    ts = [tau(ch, q) for ch in cs]
    gauss["max_gauss_mass_defect"] = max(
        gauss["max_gauss_mass_defect"], abs(sum(abs(t)**2 for t in ts)-len(cs)**2))
    for ch, tq in zip(cs, ts):
        d = ch.conductor()
        inducing = [p for p in chars(d)
                    if all(abs(cv(ch(a))-cv(p(a))) < 1e-12 for a in units(q))]
        assert len(inducing) == 1
        ch0 = inducing[0]
        predicted = mu(q // d) * cv(ch0(q // d)) * tau(ch0, d)
        gauss["max_induction_defect"] = max(
            gauss["max_induction_defect"], abs(tq-predicted))
        gauss["characters"] += 1
        if math.gcd(q // d, d) > 1:
            gauss["noncoprime_repetition_cases"] += 1
    # Arbitrary coefficients distinguish the Fourier identity from prime-specific accidents.
    coeffs = {n: complex((n*n+3) % 11-4, (n*7) % 5-2) for n in range(1, 18)}
    H = 17
    left = sum(abs(sum(v*cmath.exp(2j*math.pi*a*n/q)
                       for n, v in coeffs.items() if math.gcd(n, q) == 1)
                   -mu(q)*H/len(cs))**2 for a in units(q))
    right = 0.0
    for ch, tq in zip(cs, ts):
        sch = sum(v*cv(ch(n)) for n, v in coeffs.items())
        right += (mu(q)**2*abs(sch-H)**2 if ch.is_principal()
                  else abs(tq)**2*abs(sch)**2)/len(cs)
    gauss["max_diagonalization_defect"] = max(
        gauss["max_diagonalization_defect"], abs(left-right))


def lam(n):
    fs = factors(n)
    return mp.log(next(iter(fs))) if len(fs) == 1 else mp.mpf(0)


def numeric(v):
    return float(abs(v))


arithmetic = {"N_values": list(range(2, 21)) + [63, 64, 65],
              "NK_pairs": 0, "max_divisor_defect": 0.0,
              "max_renewal_defect": 0.0, "max_Q_over_variation": 0.0,
              "wrong_constant_min_defect_over_N": float("inf")}
for N in arithmetic["N_values"]:
    weights = [mp.mpf(0)] + [lam(n) for n in range(1, N+1)]
    ps = [mp.mpf(0)]
    for w in weights[1:]:
        ps.append(ps[-1]+w)
    rn = lambda k: ps[N//k] - mp.mpf(N)/k
    G = mp.loggamma(N+1)-N*mp.harmonic(N)
    arithmetic["max_divisor_defect"] = max(
        arithmetic["max_divisor_defect"], numeric(sum(rn(k) for k in range(1, N+1))-G))
    for K in range(1, N+1):
        y = mp.mpf(N)/K
        int_finite = sum(weights[n]*(mp.mpf(1)/n-1/y)
                         for n in range(1, N//K+1))-mp.log(y)
        Q = sum(rn(k) for k in range(K+1, N+1))-N*int_finite
        tail = -1-mp.euler-int_finite
        lhs = sum(rn(k) for k in range(1, K+1))-N*tail
        rhs = G+(1+mp.euler)*N-Q
        arithmetic["max_renewal_defect"] = max(
            arithmetic["max_renewal_defect"], numeric(lhs-rhs))
        arithmetic["max_Q_over_variation"] = max(
            arithmetic["max_Q_over_variation"], numeric(Q)/(float(ps[N//K]+y)))
        wrong_tail = -mp.euler-int_finite
        wrong_lhs = sum(rn(k) for k in range(1, K+1))-N*wrong_tail
        arithmetic["wrong_constant_min_defect_over_N"] = min(
            arithmetic["wrong_constant_min_defect_over_N"], numeric(wrong_lhs-rhs)/N)
        arithmetic["NK_pairs"] += 1


rho = mp.mpc("0.75", "2")
z = mp.zeta(rho)
mode = {"rho": str(rho), "zeta_modulus": float(abs(z)),
        "N_values": [16, 17, 64, 65], "max_exact_power_defect": 0.0,
        "max_transfer_error_normalized": 0.0,
        "max_boundary_forcing_error": 0.0,
        "wrong_closed_endpoint_min_defect": float("inf")}
for N in mode["N_values"]:
    for K in range(1, N+1):
        y = mp.mpf(N)/K
        raw = sum((mp.mpf(N)/k)**rho for k in range(1, K+1))
        raw -= N*y**(rho-1)/(1-rho)
        formula = mp.mpf(N)**rho*(sum(mp.mpf(k)**(-rho) for k in range(1, K+1))
                                    -mp.mpf(K)**(1-rho)/(1-rho))
        mode["max_exact_power_defect"] = max(mode["max_exact_power_defect"], numeric(raw-formula))
        mode["max_transfer_error_normalized"] = max(
            mode["max_transfer_error_normalized"], numeric(raw-z*N**rho)/float(y**rho.real))
    coeff = 2/(1-rho)
    raw_boundary = sum((mp.mpf(N)/k)**rho - (coeff if N < 2*k else 0)
                       for k in range(1, N+1))
    compact_formula = N**rho*sum(mp.mpf(k)**(-rho) for k in range(1, N+1))
    compact_formula -= coeff*(N-N//2)
    mode["max_boundary_forcing_error"] = max(
        mode["max_boundary_forcing_error"], numeric(raw_boundary-z*N**rho))
    assert abs(raw_boundary-compact_formula) < mp.mpf("1e-38")
    if N % 2 == 0:
        wrong = sum((mp.mpf(N)/k)**rho - (coeff if N <= 2*k else 0)
                    for k in range(1, N+1))
        mode["wrong_closed_endpoint_min_defect"] = min(
            mode["wrong_closed_endpoint_min_defect"], numeric(wrong-compact_formula))


def cutoff(u):
    if u <= 2:
        return mp.mpf(0)
    if u >= 3:
        return mp.mpf(1)
    v = u-2
    return 3*v*v-2*v*v*v


def bump(u):
    return (u-3)**2*(4-u)**2 if 3 <= u <= 4 else mp.mpf(0)


J = mp.quad(lambda u: cutoff(u)*u**(rho-2), [2, 3])+3**(rho-1)/(1-rho)
Jb = mp.quad(lambda u: bump(u)/u**2, [3, 4])
F = lambda u: cutoff(u)*u**rho-J/Jb*bump(u)
normalization = mp.quad(lambda u: F(u)/u**2, [1, 2, 3, 4])+4**(rho-1)/(1-rho)
model = {"rho": str(rho), "normalization_defect": numeric(normalization),
         "max_TF_minus_zeta_power": 0.0,
         "scope": "A fixed nonzero zeta value checks retention of the leading term; no zero is assumed or searched."}
for N in [4, 16, 17, 64, 65]:
    model["max_TF_minus_zeta_power"] = max(model["max_TF_minus_zeta_power"],
        numeric(sum(F(mp.mpf(N)/k) for k in range(1, N+1))-z*N**rho))

results = {"grade": "bounded non-enclosing diagnostics, not a universal proof",
           "gauss": gauss, "arithmetic": arithmetic, "power_mode": mode,
           "smooth_model": model,
           "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [ROOT/'FAREY_BASELINE_REPAIR.md', ROOT/'SIGNED_MEAN_RENEWAL.md']}}
target = ROOT/'frontier_review_checks.json'
target.write_text(json.dumps(results, indent=2)+'\n')
print(json.dumps(results, indent=2))
