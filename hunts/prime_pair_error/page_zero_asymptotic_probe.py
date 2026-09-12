"""Finite checks for PAGE_ZERO_ASYMPTOTIC.md.

Three measurements at fixed N. None of them tests an asymptotic statement about
primes; no exceptional zero is reachable at these N, so every beta below is a toy.

(1) The mean square of the truncated singular series
        S_*(h) = prod_{p < Z, p not dividing q} alpha_p(h)
    over 1 <= h <= N coprime to q, against (phi(q)/q) M_2(q; Z) with
        M_2(q; Z) = prod_{p < Z, p not dividing q} E_p,  E_2 = 2,  E_p = 1 + (p-1)^(-3),
    which is the constant PAGE_ZERO_ASYMPTOTIC.md section 3 derives. Also the full
    singular series S(h) against C_3 = prod_p (1 + (p-1)^(-3)), the Z -> infinity value.

(2) The correction energy A = 2 sum_{h <= N} C_{q,beta,Z}(h)^2 of SIEGEL_UNIFORMITY.md
    (19), computed term by term for toy data (q, chi, beta) with beta = 1 - kappa/sqrt(log N),
    split into its linear, cross and quadratic parts; the linear part against
        (2/q^2) (q/phi(q))^4 (phi(q)/q) M_2(q; Z) int_0^N (chi(-1) J_1 + J_2)^2 dh ;
    and that integral against its leading term, (4/3) N^(2 beta + 1)/beta^2 for even chi
    and ((15 - pi^2)/18) delta^2 N^(2 beta + 1)/beta^2 for odd chi, delta = 1 - beta.

(3) The parity remark of MAJOR_ARC_EXPLICIT.md section 5, which no check had read:
    Im(conj(K_N(theta)) I_beta(theta)) on 1/(16 N) <= theta <= 1/(8 N) keeps one sign and
    has size (kappa/sqrt(log N)) N^(1 + beta).

Run from the repository root with .venv/bin/python. Writes
results_page_zero_asymptotic_probe.json next to this file. About a minute.
"""
from __future__ import annotations

import json
import math
import os
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "results_page_zero_asymptotic_probe.json")

_GL_X, _GL_W = np.polynomial.legendre.leggauss(16)


# ----------------------------------------------------------------------------- arithmetic
def primes_below(x: int) -> np.ndarray:
    if x < 3:
        return np.array([], dtype=np.int64)
    sieve = np.ones(x, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(math.isqrt(x - 1)) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    return np.nonzero(sieve)[0]


def prime_factors(q: int) -> list[int]:
    out, m, p = [], q, 2
    while p * p <= m:
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        out.append(m)
    return out


def euler_phi(q: int) -> int:
    r = q
    for p in prime_factors(q):
        r = r // p * (p - 1)
    return r


def moebius(q: int) -> int:
    ps = prime_factors(q)
    for p in ps:
        if q % (p * p) == 0:
            return 0
    return (-1) ** len(ps)


def truncated_singular_series(N: int, Z: float, q: int) -> np.ndarray:
    """S_*(h) for 0 <= h <= N (index 0 unused): prod over p < Z, p not | q, of alpha_p(h)."""
    s = np.ones(N + 1)
    for p in primes_below(int(math.ceil(Z))):
        p = int(p)
        if p >= Z or q % p == 0:
            continue
        if p == 2:
            s[1::2] = 0.0
            s[2::2] *= 2.0
        else:
            s *= p * (p - 2) / (p - 1) ** 2
            s[p::p] *= (p - 1) / (p - 2)
    return s


def full_singular_series(N: int) -> np.ndarray:
    """The Hardy-Littlewood S(h), 0 <= h <= N: 2 C_2 prod_{p | h, p > 2} (p-1)/(p-2) on even h."""
    ps = primes_below(N + 1)
    C2 = float(np.prod(1.0 - 1.0 / (ps[ps > 2] - 1.0) ** 2))
    s = np.zeros(N + 1)
    s[2::2] = 2.0 * C2
    for p in ps[ps > 2]:
        p = int(p)
        s[p::p] *= (p - 1) / (p - 2)
    return s


def M2(q: int, Z: float) -> float:
    m = 1.0
    for p in primes_below(int(math.ceil(Z))):
        p = int(p)
        if p >= Z or q % p == 0:
            continue
        m *= 2.0 if p == 2 else 1.0 + (p - 1.0) ** -3
    return m


def C3_constant(limit: int = 10**6) -> float:
    ps = primes_below(limit)
    return float(np.prod(1.0 + (ps - 1.0) ** -3))


def ramanujan_sum(N: int, q: int) -> np.ndarray:
    """c_q(h), 0 <= h <= N, for squarefree q."""
    c = np.ones(N + 1)
    for p in prime_factors(q):
        c *= -1.0
        c[p::p] *= -(p - 1.0)
    return c


def jacobi_character(N: int, q: int) -> np.ndarray:
    """chi(h) = (h/q), 0 <= h <= N, for odd squarefree q: the primitive real character mod q."""
    chi = np.ones(N + 1)
    h = np.arange(N + 1)
    for p in prime_factors(q):
        table = np.full(p, -1.0)
        table[0] = 0.0
        table[np.unique((np.arange(1, p) ** 2) % p)] = 1.0
        chi *= table[h % p]
    return chi


def coprime_mask(N: int, q: int) -> np.ndarray:
    m = np.ones(N + 1, dtype=bool)
    for p in prime_factors(q):
        m[0::p] = False
    return m


# ------------------------------------------------------------------------ the J weights
def J1_J2(N: int, beta: float) -> tuple[np.ndarray, np.ndarray]:
    """J_1(h), J_2(h) of SIEGEL_UNIFORMITY.md (15)-(16) for 0 <= h <= N, closed forms."""
    h = np.arange(N + 1, dtype=float)
    T = N - h
    J1 = np.where(T >= 1.0, 1.0 + (np.maximum(T, 1.0) ** beta - 1.0) / beta, T)
    J2 = (float(N) ** beta - h ** beta) / beta
    return J1, J2


def J12(N: int, beta: float, chunk: int = 4000, panels: int = 24) -> np.ndarray:
    """J_12(h) = int_0^{N-h} max(1,t)^(beta-1) (t+h)^(beta-1) dt, 0 <= h <= N.

    The piece over [0,1] is closed form; the piece over [1, N-h] is composite
    Gauss-Legendre on panels log-spaced in t, chunked over h."""
    delta = 1.0 - beta
    h = np.arange(N + 1, dtype=float)
    T = N - h
    out = np.zeros(N + 1)
    # [0, min(1,T)] piece: int_0^a (t+h)^(-delta) dt = ((a+h)^beta - h^beta)/beta
    a = np.minimum(T, 1.0)
    out += ((a + h) ** beta - h ** beta) / beta
    idx = np.nonzero(T > 1.0)[0]
    for start in range(0, len(idx), chunk):
        ii = idx[start:start + chunk]
        Ti = T[ii][:, None]
        hi = h[ii][:, None]
        edges = np.exp(np.linspace(0.0, 1.0, panels + 1)[None, :] * np.log(Ti))  # (m, panels+1)
        lo = edges[:, :-1, None]
        hi_ = edges[:, 1:, None]
        t = 0.5 * (hi_ - lo) * _GL_X[None, None, :] + 0.5 * (hi_ + lo)
        w = 0.5 * (hi_ - lo) * _GL_W[None, None, :]
        vals = np.exp(-delta * np.log(t) - delta * np.log(t + hi[:, :, None]))
        out[ii] += np.sum(w * vals, axis=(1, 2))
    return out


def integral_over_h(N: int, f, panels: int = 4000) -> float:
    """int_0^N f(h) dh for a smooth f given as a vectorised function, composite Gauss-Legendre."""
    edges = np.linspace(0.0, float(N), panels + 1)
    lo, hi = edges[:-1][:, None], edges[1:][:, None]
    x = 0.5 * (hi - lo) * _GL_X[None, :] + 0.5 * (hi + lo)
    w = 0.5 * (hi - lo) * _GL_W[None, :]
    return float(np.sum(w * f(x)))


def scaled_integrals(beta: float) -> dict:
    """The one-variable integrals of PAGE_ZERO_ASYMPTOTIC.md section 3:
        Jplus(beta)  = int_0^1 ((1-u)^beta + 1 - u^beta)^2 du            -> 4/3,
        Jminus(beta) = int_0^1 ((1-u)^beta - 1 + u^beta)^2 du            ~ (15 - pi^2) delta^2 / 18,
        J12(beta)    = int_0^1 ( int_0^{1-u} x^(-delta) (x+u)^(-delta) dx )^2 du -> 1/3,
    with delta = 1 - beta. Composite Gauss-Legendre; the inner integral of J12 on panels
    log-spaced in x down to 1e-14 (the integrand's singularity at x = 0 is integrable)."""
    delta = 1.0 - beta
    panels = 2000
    edges = np.linspace(0.0, 1.0, panels + 1)
    lo, hi = edges[:-1][:, None], edges[1:][:, None]
    u = (0.5 * (hi - lo) * _GL_X[None, :] + 0.5 * (hi + lo)).ravel()
    w = (0.5 * (hi - lo) * _GL_W[None, :]).ravel()
    plus = float(np.sum(w * ((1 - u) ** beta + 1 - u ** beta) ** 2))
    minus = float(np.sum(w * ((1 - u) ** beta - 1 + u ** beta) ** 2))
    inner = np.zeros_like(u)
    xe = np.exp(np.linspace(np.log(1e-14), 0.0, 401))  # relative to the upper limit 1-u
    for i, ui in enumerate(u):
        top = 1.0 - ui
        e = xe * top
        a, b = e[:-1][:, None], e[1:][:, None]
        x = 0.5 * (b - a) * _GL_X[None, :] + 0.5 * (b + a)
        wx = 0.5 * (b - a) * _GL_W[None, :]
        inner[i] = float(np.sum(wx * np.exp(-delta * np.log(x) - delta * np.log(x + ui))))
    j12 = float(np.sum(w * inner ** 2))
    return {"Jplus": plus, "Jminus": minus, "J12": j12, "delta": delta,
            "Jplus_over_4_3": plus / (4.0 / 3.0),
            "Jminus_over_limit": minus / ((15.0 - math.pi ** 2) / 18.0 * delta ** 2),
            "J12_over_1_3": 3.0 * j12}


def J1_J2_continuous(x: np.ndarray, N: int, beta: float) -> tuple[np.ndarray, np.ndarray]:
    T = N - x
    J1 = np.where(T >= 1.0, 1.0 + (np.maximum(T, 1.0) ** beta - 1.0) / beta, T)
    J2 = (float(N) ** beta - x ** beta) / beta
    return J1, J2


# ------------------------------------------------------------- exponential-sum quantities
def I_beta(beta: float, theta: float, N: int) -> complex:
    n_osc = abs(theta) * (N - 1)
    panels = int(4 * n_osc) + 64
    edges = np.exp(np.linspace(0.0, math.log(N), panels + 1))
    a = edges[:-1][:, None]
    b = edges[1:][:, None]
    t = 0.5 * (b - a) * _GL_X[None, :] + 0.5 * (b + a)
    w = 0.5 * (b - a) * _GL_W[None, :]
    return complex(np.sum(w * np.exp((beta - 1) * np.log(t) + 2j * math.pi * theta * t)))


def K_N(theta: float, N: int) -> complex:
    if abs(theta) < 1e-15:
        return complex(N)
    return (np.exp(2j * math.pi * theta * (N + 1)) - np.exp(2j * math.pi * theta)) / (
        np.exp(2j * math.pi * theta) - 1.0
    )


# ------------------------------------------------------------------------------- main
def main():
    t0 = time.time()
    out = {"note": "toy beta values; no exceptional zero exists at these N; nothing here tests "
                   "an asymptotic statement about primes"}
    C3 = C3_constant()
    out["C_3"] = C3

    # (1) mean square of the truncated singular series on h coprime to q
    rows = []
    for N in (10**5, 10**6):
        Z = math.exp(math.sqrt(math.log(N)))
        for q in (1, 3, 5, 7, 15, 21):
            s = truncated_singular_series(N, Z, q)
            mask = coprime_mask(N, q)
            mask[0] = False
            measured = float(np.sum(s[mask] ** 2)) / N
            predicted = euler_phi(q) / q * M2(q, Z)
            rows.append({"N": N, "Z": Z, "q": q, "mean_square_measured": measured,
                         "mean_square_predicted": predicted, "ratio": measured / predicted})
        S = full_singular_series(N)
        rows.append({"N": N, "q": 1, "full_singular_series_mean_square": float(np.sum(S[1:] ** 2)) / N,
                     "C_3": C3, "ratio": float(np.sum(S[1:] ** 2)) / N / C3})
    out["mean_square_of_S_star"] = rows

    # (2) the correction energy against its evaluation
    rows = []
    I_odd = (15.0 - math.pi ** 2) / 18.0
    for N in (10**4, 10**5):
        ell = math.log(N)
        Z = math.exp(math.sqrt(ell))
        for kappa in (0.3, 1.0):
            beta = 1.0 - kappa / math.sqrt(ell)
            delta = 1.0 - beta
            J1, J2 = J1_J2(N, beta)
            J12v = J12(N, beta)
            sc = scaled_integrals(beta)
            J12_sq_integral_all = float(np.sum(J12v[1:N] ** 2)) + 0.5 * float(J12v[0] ** 2 + J12v[N] ** 2)
            rows.append({"N": N, "kappa": kappa, "beta": beta, "scaled_integrals": sc,
                         "J12_h_integral_over_N4beta1_J12beta":
                             J12_sq_integral_all / (float(N) ** (4 * beta - 1) * sc["J12"])})
            for q in (3, 5, 7, 13, 15, 21):
                chi = jacobi_character(N, q)
                chi_m1 = 1.0
                for p in prime_factors(q):
                    chi_m1 *= (-1.0) ** ((p - 1) // 2)
                s = truncated_singular_series(N, Z, q)
                cq = ramanujan_sum(N, q)
                mu = moebius(q)
                phi = euler_phi(q)
                pref = (q / phi) ** 2
                lin = pref * s * (-mu * chi / q) * (chi_m1 * J1 + J2)
                quad = pref * s * (cq / q) * J12v
                lin[0] = quad[0] = 0.0
                A_lin = 2.0 * float(np.sum(lin ** 2))
                A_cross = 4.0 * float(np.sum(lin * quad))
                A_quad = 2.0 * float(np.sum(quad ** 2))
                A = 2.0 * float(np.sum((lin + quad) ** 2))
                integral = integral_over_h(
                    N, lambda x: (lambda j: (chi_m1 * j[0] + j[1]) ** 2)(J1_J2_continuous(x, N, beta)))
                P_lin = (2.0 / q ** 2) * (q / phi) ** 4 * (phi / q) * M2(q, Z) * integral
                # the quadratic piece: mean of S_*^2 c_q^2 is M_2 phi(q) by independence, and
                # int_0^N J_12^2 dh by the trapezoid rule on the integer values (J_12 is smooth)
                J12_sq_integral = float(np.sum(J12v[1:N] ** 2)) + 0.5 * float(J12v[0] ** 2 + J12v[N] ** 2)
                P_quad = 2.0 * (q / phi) ** 4 / q ** 2 * M2(q, Z) * phi * J12_sq_integral
                leading_quad = float(N) ** (4 * beta - 1) / 3.0
                exact_scaled = (sc["Jplus"] if chi_m1 > 0 else sc["Jminus"]) * float(N) ** (2 * beta + 1) / beta ** 2
                if chi_m1 > 0:
                    leading = (4.0 / 3.0) * float(N) ** (2 * beta + 1) / beta ** 2
                    M_asym = (8.0 / 3.0) * M2(q, Z) * (q / phi) ** 3 / q ** 2 * float(N) ** (2 * beta + 1)
                else:
                    leading = I_odd * delta ** 2 * float(N) ** (2 * beta + 1) / beta ** 2
                    M_asym = ((15.0 - math.pi ** 2) / 9.0) * M2(q, Z) * (q / phi) ** 3 / q ** 2 \
                        * delta ** 2 * float(N) ** (2 * beta + 1)
                rows.append({
                    "N": N, "kappa": kappa, "beta": beta, "q": q, "chi_minus_one": chi_m1,
                    "A_exact": A, "A_linear": A_lin, "A_cross": A_cross, "A_quadratic": A_quad,
                    "quadratic_over_linear": A_quad / A_lin, "cross_over_linear": A_cross / A_lin,
                    "P_linear_from_M2_and_exact_integral": P_lin,
                    "ratio_A_linear_over_P_linear": A_lin / P_lin,
                    "integral_over_leading_term": integral / leading,
                    "integral_over_exact_scaled_form": integral / exact_scaled,
                    "P_quadratic_from_M2_and_J12_integral": P_quad,
                    "ratio_A_quadratic_over_P_quadratic": A_quad / P_quad,
                    "J12_integral_over_leading_term": J12_sq_integral / leading_quad,
                    "ratio_A_exact_over_asymptotic_formula": A / M_asym,
                    "N_to_2beta_plus_1_over_q2": float(N) ** (2 * beta + 1) / q ** 2,
                })
    out["correction_energy"] = rows

    # (3) the parity remark: sign and size of Im(conj(K_N) I_beta) near theta = 1/(8N)
    rows = []
    for N in (10**4, 10**5):
        ell = math.log(N)
        for kappa in (0.3, 1.0):
            beta = 1.0 - kappa / math.sqrt(ell)
            delta = kappa / math.sqrt(ell)
            vals = []
            for Ntheta in np.linspace(1.0 / 16.0, 1.0 / 8.0, 17):
                theta = Ntheta / N
                v = np.conj(K_N(theta, N)) * I_beta(beta, theta, N)
                vals.append(v.imag / (delta * float(N) ** (1 + beta)))
            vals = np.array(vals)
            rows.append({"N": N, "kappa": kappa, "beta": beta,
                         "Im_over_delta_N_1_plus_beta_min": float(vals.min()),
                         "Im_over_delta_N_1_plus_beta_max": float(vals.max()),
                         "one_sign": bool(np.all(vals < 0) or np.all(vals > 0)),
                         "sign": int(np.sign(vals[0]))})
    out["parity_remark"] = rows

    out["elapsed_s"] = time.time() - t0
    with open(OUT, "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
