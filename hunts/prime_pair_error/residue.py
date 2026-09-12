"""Prime-pair error, second pass: a fixed-coefficient residue-class correction.

Continues probe.py, whose notation is kept: psi_2(N, k) is the von Mangoldt pair
count, S(k) the singular series (S(odd) = 0), e(N, k) = psi_2(N, k) - S(k)(N - k) for
1 <= k <= N, E(N) = 2 sum_k e(N, k)^2.  The first pass measured that the signed part
of e on even k is S(k) [R(N) + R(N - k) - R(k)] with R = psi - x.  This pass derives
that formula as the q = 1 member of a family indexed by a modulus q, writes down the
q = 3 member (the modulo-3 correction) and the q = 30 member (divisibility by 2, 3
and 5 treated together), and evaluates all three at cutoffs the first pass never used.

The decomposition at a modulus q, with phi = phi(q) and w = q / phi:

    M_q(n)    = w 1[(n, q) = 1],  M_q(0) = 0        periodic model of Lambda
    Lambda'   = Lambda 1[(n, q) = 1]                 Lambda on the reduced classes
    delta'    = Lambda' - M_q                        centered, supported on reduced classes

    psi_2(N, k) = A_q + L_q + X_q + D_q              (I1) exact, 1 <= k <= N

    A_q = sum_{n <= N-k} M(n) M(n+k)                             periodic baseline
    L_q = sum_{n <= N-k} [M(n) delta'(n+k) + delta'(n) M(n+k)]   linear endpoint terms
    X_q = sum over pairs with a member a power of a prime dividing q   exceptional
    D_q = sum_{n <= N-k} delta'(n) delta'(n+k)                   remaining correlation

Exact facts used below, each pinned by tests/test_prime_pair_residue.py:

    (I2) A_q = S_q(k)(N - k) + rho_q(N, k),  S_q(k) = q nu_q(k) / phi^2 = prod_{p|q} sigma_p(k),
         nu_q(k) = #{a mod q : (a, q) = 1 = (a + k, q)},  |rho_q| <= w^2 nu_q(k),
         sigma_p(k) = p/(p-1) if p | k, p(p-2)/(p-1)^2 otherwise.
    (I3) S(k) = S_q(k) S^(q)(k), S^(q) the same product over the primes not dividing q.
    (I4) L_q is a linear combination of psi(x; q, b) over reduced b at x = N, k, N - k,
         plus a bounded periodic sawtooth; for q = 3 it is, with chi the character mod 3,
         L_3 = S_3(k) [R'(N) + R'(N-k) - R'(k)] + (3/4) chi(k) [psi(N-k, chi) - psi(N, chi) + psi(k, chi)]
         + sawtooth, R'(x) = psi(x) - x - (log 3) floor(log_3 x).

The one heuristic (H_q): the primes not dividing q act on the reduced classes mod q
as all primes act on the integers, so D_q = (S^(q)(k) - 1)(A_q + L_q) + centered noise.
Under H_q the prediction for e(N, k) is

    c_q(N, k) = S^(q)(k) [rho_q(N, k) + L_q(N, k)] + X_q(N, k),

with every coefficient fixed at 1 by the derivation, and c_1 is exactly the first
pass's S(k)[R(N) + R(N-k) - R(k)].  The residual Z_q = e - c_q = D_q - (S^(q) - 1)(A_q + L_q)
is what H_q says is centered.  Nothing here is fit: the post-hoc slopes reported are
diagnostics and enter no prediction.  Nothing bears on RH (docs/08).

Run:  .venv/bin/python hunts/prime_pair_error/residue.py [--max-n 7000000] [--fresh N ...]
Writes hunts/prime_pair_error/results_residue.json.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import probe  # noqa: E402

C2 = probe.C2

#: Every coefficient a fit could have moved, with the value the derivation fixes.
#: Frozen 2026-09-06 before the fresh-cutoff run.  The test pins that no entry differs
#: from its derived value and that no prediction reads the pair counts.
FROZEN = {
    "q1_alpha_over_R_N": 1.0,   # e ~ S(k)[alpha + gamma (R(N-k) - R(k))], alpha = R(N)
    "q1_beta_B": 0.0,           # no prime-power-deficit profile for the von Mangoldt count
    "q1_gamma_R": 1.0,
    "coef_baseline_rho": 1.0,   # c_q = S^(q)(k) [rho_q + L_q] + X_q
    "coef_endpoint_L": 1.0,
    "coef_exceptional_X": 1.0,
}
#: Cutoffs the first pass never evaluated (it used 10^3, 10^4, 10^5, 10^6, 3 x 10^6, 10^7).
FRESH_CUTOFFS = [200_000, 500_000, 2_000_000, 5_000_000, 7_000_000]
FIRST_PASS_CUTOFFS = [1_000, 10_000, 100_000, 1_000_000, 3_000_000, 10_000_000]
#: The three corrections compared, by modulus; 210 is a diagnostic of the residual only.
MODULI = (1, 3, 30)
NEXT_MODULUS = 210


# ---------------------------------------------------------------------------
# arithmetic of the modulus
# ---------------------------------------------------------------------------

def primes_up_to(N: int) -> np.ndarray:
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    return np.nonzero(sieve)[0]


def prime_divisors(q: int) -> list[int]:
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


def reduced_residues(q: int) -> list[int]:
    """Residues a mod q with (a, q) = 1; [0] for q = 1."""
    return [a for a in range(q) if math.gcd(a, q) == 1]


def sigma_p(p: int, k: np.ndarray) -> np.ndarray:
    """The local factor of the singular series at p, as a function of k."""
    return np.where(k % p == 0, p / (p - 1.0), p * (p - 2.0) / (p - 1.0) ** 2)


def S_q(k: np.ndarray, q: int) -> np.ndarray:
    """S_q(k) = prod_{p | q} sigma_p(k); ones for q = 1."""
    out = np.ones(len(k), dtype=np.float64)
    for p in prime_divisors(q):
        out *= sigma_p(p, k)
    return out


def nu_table(q: int) -> np.ndarray:
    """nu_q(r) = #{a mod q reduced : a + r reduced}, indexed by r = k mod q."""
    red = reduced_residues(q)
    is_red = np.zeros(q, dtype=bool)
    is_red[red] = True
    return np.array([sum(is_red[(a + r) % q] for a in red) for r in range(q)], dtype=np.int64)


def singular_series_coprime(N: int, q: int) -> np.ndarray:
    """S^(q)(k) = prod_{p not dividing q} sigma_p(k) for 0 <= k <= N (index 0 set to 0).

    Independent of probe.singular_series: it is the same product with the primes
    dividing q left out, and the pair multiply back to S(k) at every k (I3)."""
    S = np.ones(N + 1, dtype=np.float64)
    c = C2
    for p in primes_up_to(N):
        if p == 2:
            if q % 2:
                S[1::2] = 0.0
                S[0::2] *= 2.0
            continue
        if q % p == 0:
            c /= 1.0 - 1.0 / (p - 1.0) ** 2
            continue
        S[p::p] *= (p - 1.0) / (p - 2.0)
    S *= c
    S[0] = 0.0
    return S


# ---------------------------------------------------------------------------
# the four pieces, exact
# ---------------------------------------------------------------------------

def periodic_baseline(N: int, q: int) -> tuple[np.ndarray, np.ndarray]:
    """A_q(N, k) and rho_q(N, k) = A_q - S_q(k)(N - k), for k = 1..N."""
    k = np.arange(1, N + 1)
    red = reduced_residues(q)
    is_red = np.zeros(q, dtype=bool)
    is_red[red] = True
    w = q / len(red)
    kmod = k % q
    A = np.zeros(N, dtype=np.float64)
    for a in red:
        valid = is_red[(a + kmod) % q]
        if q == 1:
            cnt = (N - k).astype(np.float64)
        else:
            cnt = np.where(N - k >= a, (N - k - a) // q + 1, 0).astype(np.float64)
        A[valid] += w * w * cnt[valid]
    rho = A - S_q(k, q) * (N - k)
    return A, rho


def model_and_centered(lam: np.ndarray, N: int, q: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """M_q, Lambda' and delta' on 0..N."""
    n = np.arange(N + 1)
    red = reduced_residues(q)
    is_red_n = np.isin(n % q, red)
    is_red_n[0] = False
    M = np.where(is_red_n, q / len(red), 0.0)
    lam_red = np.where(is_red_n, lam[: N + 1], 0.0)
    return M, lam_red, lam_red - M


def endpoint_terms(dprime: np.ndarray, N: int, q: int) -> np.ndarray:
    """L_q(N, k) for k = 1..N, from the centered cumulative sums in residue classes.

    Per reduced residue b, Psi'_b(x) = sum_{n <= x, n = b (q)} delta'(n).  Then
      sum_n M(n) delta'(n+k) = w sum_{b : (b-k, q) = 1} [Psi'_b(N) - Psi'_b(k)],
      sum_n delta'(n) M(n+k) = w sum_{a : (a+k, q) = 1} Psi'_a(N-k).
    Memory is one class at a time, so q = 210 costs 48 passes and no extra arrays."""
    k = np.arange(1, N + 1)
    n = np.arange(N + 1)
    red = reduced_residues(q)
    is_red = np.zeros(q, dtype=bool)
    is_red[red] = True
    w = q / len(red)
    kmod = k % q
    nmod = n % q
    L = np.zeros(N, dtype=np.float64)
    for b in red:
        cum = np.cumsum(np.where(nmod == b, dprime[: N + 1], 0.0))
        m1 = is_red[(b - kmod) % q]
        L[m1] += w * (cum[N] - cum[k[m1]])
        m2 = is_red[(b + kmod) % q]
        L[m2] += w * cum[(N - k)[m2]]
    return L


def exceptional_pairs(lam: np.ndarray, N: int, q: int) -> np.ndarray:
    """X_q(N, k) for k = 1..N: pairs with at least one member a power of a prime
    dividing q, by direct enumeration over that O(log N) support."""
    n = np.arange(N + 1)
    exc = [int(m) for m in np.nonzero((lam[: N + 1] > 0) & (np.gcd(n, q) > 1))[0]]
    X = np.zeros(N + 1, dtype=np.float64)
    for m in exc:
        lm = lam[m]
        X[1 : N - m + 1] += lm * lam[m + 1 : N + 1]       # partner m + k
        X[1:m] += lm * lam[m - 1 : 0 : -1]                # partner m - k
    for i, m in enumerate(exc):                            # both exceptional: counted twice
        for m2 in exc[i + 1 :]:
            X[m2 - m] -= lam[m] * lam[m2]
    return X[1:]


def chi3_closed_form(lam: np.ndarray, N: int, S: np.ndarray) -> np.ndarray:
    """The modulo-3 correction written with the character mod 3 (I4), for k = 1..N:

      c_3 = S(k)[R'(N) + R'(N-k) - R'(k)]
            + S(k) chi(k) [psi(N-k, chi) - psi(N, chi) + psi(k, chi)]
            + S^(3)(k) [rho_3 + sawtooth] + X_3,

    where the sawtooth is the exact difference between x/2 and (3/2) #{n <= x : n = b (3)}.
    Independent of endpoint_terms(): it never forms residue-class cumulative sums of
    delta', only psi, psi(., chi) and floor counts."""
    n = np.arange(N + 1)
    k = np.arange(1, N + 1)
    lam_ = lam[: N + 1]
    chi = np.zeros(N + 1)
    chi[1::3] = 1.0
    chi[2::3] = -1.0
    psi = np.cumsum(lam_)
    psi_chi = np.cumsum(lam_ * chi)
    psi_0 = np.cumsum(np.where(n % 3 == 0, lam_, 0.0))     # powers of 3
    Rp = psi - psi_0 - n
    Rp[0] = 0.0
    x = n.astype(np.float64)
    # sawtooth eta_b(x) = x/2 - (3/2) #{n <= x: n = b (3)}, b = 1, 2
    cnt1 = np.where(n >= 1, (n - 1) // 3 + 1, 0)
    cnt2 = np.where(n >= 2, (n - 2) // 3 + 1, 0)
    eta = {1: x / 2 - 1.5 * cnt1, 2: x / 2 - 1.5 * cnt2}
    chi_k = chi[1:]
    S3 = S_q(k, 3)
    Scop = S[1 : N + 1] / np.where(S3 > 0, S3, 1.0)
    base = S[1 : N + 1] * (Rp[N] + Rp[N - k] - Rp[k])
    char = S[1 : N + 1] * chi_k * (psi_chi[N - k] - psi_chi[N] + psi_chi[k])
    # sawtooth part of L_3, exactly: w sum_b [eta_b(N) - eta_b(k)] + w sum_a eta_a(N-k)
    # over the same residue sets as endpoint_terms; w = 3/2
    saw = np.zeros(N)
    for kmod_val, bs, as_ in ((0, (1, 2), (1, 2)), (1, (2,), (1,)), (2, (1,), (2,))):
        m = (k % 3) == kmod_val
        for b in bs:
            saw[m] += 1.5 * (eta[b][N] - eta[b][k[m]])
        for a in as_:
            saw[m] += 1.5 * eta[a][(N - k)[m]]
    _, rho3 = periodic_baseline(N, 3)
    X3 = exceptional_pairs(lam, N, 3)
    return base + char + Scop * (rho3 + saw) + X3


# ---------------------------------------------------------------------------
# the corrections and their evaluation
# ---------------------------------------------------------------------------

def correction(lam: np.ndarray, N: int, q: int, S: np.ndarray) -> dict:
    """c_q(N, k) = S^(q)(k)[rho_q + L_q] + X_q on k = 1..N, with the pieces.

    Reads only Lambda (one-point data) and the singular series; never psi_2."""
    _, rho = periodic_baseline(N, q)
    _, _, dprime = model_and_centered(lam, N, q)
    L = endpoint_terms(dprime, N, q)
    X = exceptional_pairs(lam, N, q) if q > 1 else np.zeros(N)
    Scop = singular_series_coprime(N, q)[1 : N + 1]
    c = (FROZEN["coef_baseline_rho"] * Scop * rho
         + FROZEN["coef_endpoint_L"] * Scop * L
         + FROZEN["coef_exceptional_X"] * X)
    return {"c": c, "rho": rho, "L": L, "X": X, "Scop": Scop, "dprime": dprime}


def original_correction(lam: np.ndarray, N: int, S: np.ndarray) -> np.ndarray:
    """The first pass's formula with its predicted coefficients: S(k)[R(N) + R(N-k) - R(k)]."""
    k = np.arange(1, N + 1)
    n = np.arange(N + 1, dtype=np.float64)
    R = np.cumsum(lam[: N + 1]) - n
    R[0] = 0.0
    a = FROZEN["q1_alpha_over_R_N"] * R[N]
    g = FROZEN["q1_gamma_R"]
    return S[1 : N + 1] * (a + g * (R[N - k] - R[k]))


def product_form(lam: np.ndarray, N: int, q: int, S: np.ndarray, X: np.ndarray, Scop: np.ndarray) -> np.ndarray:
    """The un-linearised H_q prediction minus S(k)(N-k), for k < N (0 at k = N):
    X + S^(q)(k) (q/(N-k)) sum_a psi(N-k; q, a) [psi(N; q, a+k) - psi(k; q, a+k)] - S(k)(N-k)."""
    k = np.arange(1, N + 1)
    n = np.arange(N + 1)
    red = reduced_residues(q)
    nmod = n % q
    kmod = k % q
    lam_ = lam[: N + 1]
    cums = {a: np.cumsum(np.where(nmod == a, lam_, 0.0)) for a in red}
    tot = np.zeros(N)
    for a in red:
        for b in red:
            m = kmod == ((b - a) % q)
            tot[m] += cums[a][(N - k)[m]] * (cums[b][N] - cums[b][k[m]])
    inner = k < N
    out = np.zeros(N)
    out[inner] = (X[inner] + Scop[inner] * q / (N - k[inner]) * tot[inner]
                  - S[1 : N + 1][inner] * (N - k[inner]))
    return out


def _class_means(y: np.ndarray, key: np.ndarray, classes) -> list[dict]:
    rows = []
    for c in classes:
        m = key == c
        cnt = int(m.sum())
        if cnt < 2:
            rows.append({"class": int(c), "count": cnt})
            continue
        mu = float(y[m].mean())
        se = float(y[m].std(ddof=1) / math.sqrt(cnt))
        rows.append({"class": int(c), "count": cnt, "mean": mu, "se": se, "z": mu / se if se else None})
    return rows


def three_profile_fit(e: np.ndarray, lam: np.ndarray, lam_p: np.ndarray, N: int, S: np.ndarray) -> dict:
    """The first pass's joint fit on even k < N, re-implemented: y = S(k)[alpha + beta (B - mean B) + gamma (R(N-k) - R(k))].
    Post-hoc diagnostic only."""
    k = np.arange(1, N + 1)
    n = np.arange(N + 1, dtype=np.float64)
    R = np.cumsum(lam[: N + 1]) - n
    R[0] = 0.0
    pt = np.cumsum(lam[: N + 1] - lam_p[: N + 1])
    B = pt[N - k] + pt[N] - pt[k]
    Sk = S[1 : N + 1]
    ev = (k % 2 == 0) & (k < N)
    Bc = B - float(B[ev].mean())
    A = np.stack([Sk[ev], (Sk * Bc)[ev], (Sk * (R[N - k] - R[k]))[ev]], axis=1)
    coef, *_ = np.linalg.lstsq(A, e[ev], rcond=None)
    r = e[ev] - A @ coef
    s2 = float(r @ r) / (ev.sum() - 3)
    se = np.sqrt(np.diag(np.linalg.inv(A.T @ A)) * s2)
    return {"alpha": float(coef[0]), "R_N": float(R[N]), "beta_B": float(coef[1]),
            "gamma_R": float(coef[2]), "se": [float(x) for x in se]}


def analyse(N: int, lam: np.ndarray, lam_p: np.ndarray, S: np.ndarray, with_next: bool = True) -> dict:
    t0 = time.time()
    k = np.arange(1, N + 1)
    psi2 = probe.psi2_fft(lam, N)[1:]
    pred = S[1 : N + 1] * (N - k)
    e = psi2 - pred
    even = (k % 2 == 0)
    inner = even & (k < N)
    sum_e2 = float(e @ e)
    out: dict = {
        "N": N,
        "E_over_N2log2N": 2 * sum_e2 / (N * N * math.log(N) ** 2),
        "sum_e2_all_k": sum_e2,
        "sum_e2_even_k": float(e[even] @ e[even]),
        "mean_e_all_k": float(e.mean()),
        "mean_e_even_k": float(e[even].mean()),
        "first_pass_fit_at_fresh_N": three_profile_fit(e, lam, lam_p, N, S),
    }
    # the original formula, and the q = 1 member of the family, must coincide.
    # Per modulus: build the pieces, take their sizes and run the exact checks at
    # once, and keep only c_q, so memory stays at a few arrays of length N.
    c_orig = original_correction(lam, N, S)
    moduli = list(MODULI) + ([NEXT_MODULUS] if with_next else [])
    corr: dict[int, np.ndarray] = {}
    pieces: dict = {}
    ident: dict = {}
    for q in moduli:
        cq = correction(lam, N, q, S)
        corr[q] = cq["c"]
        pieces[str(q)] = {
            "rms_Scop_rho": float(np.sqrt(np.mean((cq["Scop"] * cq["rho"])[even] ** 2))),
            "max_abs_rho": float(np.max(np.abs(cq["rho"]))),
            "rms_Scop_L": float(np.sqrt(np.mean((cq["Scop"] * cq["L"])[even] ** 2))),
            "rms_X": float(np.sqrt(np.mean(cq["X"][even] ** 2))),
            "max_abs_X": float(np.max(np.abs(cq["X"]))),
            "mean_c_even_k": float(cq["c"][even].mean()),
            "mean_c_all_k": float(cq["c"].mean()),
        }
        if q == 1:
            out["check_q1_equals_original_formula_maxabs"] = float(np.max(np.abs(cq["c"] - c_orig)))
        if q in (3, 30):
            # the exact identity (I1): D_q by subtraction against D_q by an independent FFT
            A, _ = periodic_baseline(N, q)
            D_sub = psi2 - A - cq["L"] - cq["X"]
            D_fft = probe.psi2_fft(cq["dprime"], N)[1:]
            ident[str(q)] = float(np.max(np.abs(D_sub - D_fft)))
            del A, D_sub, D_fft
        if q == 30:
            # (I3) at every k, and the product (un-linearised) form of H_30
            out["check_I3_S_eq_Sq_times_Scop_maxabs"] = float(np.max(np.abs(S_q(k, 30) * cq["Scop"] - S[1 : N + 1])))
            cp = product_form(lam, N, 30, S, cq["X"], cq["Scop"])
            Zp = e - cp
            out["product_form_q30"] = {
                "maxabs_prod_minus_linear_k_lt_N": float(np.max(np.abs((cp - cq["c"])[k < N]))),
                "reduction_all_k": 1.0 - float(Zp @ Zp) / sum_e2,
            }
            del cp, Zp
        if q == 3:
            out["check_chi3_closed_form_vs_general_maxabs"] = float(np.max(np.abs(chi3_closed_form(lam, N, S) - cq["c"])))
        del cq
    del c_orig
    out["check_identity_I1_maxabs"] = ident
    out["pieces"] = pieces
    out["rms_c3_minus_c1_even"] = float(np.sqrt(np.mean((corr[3] - corr[1])[even] ** 2)))
    out["rms_c30_minus_c3_even"] = float(np.sqrt(np.mean((corr[30] - corr[3])[even] ** 2)))
    # the comparison: squared error before and after each frozen correction
    comp = {}
    for q in moduli:
        c = corr[q]
        Z = e - c
        row = {
            "sum_Z2_all_k": float(Z @ Z),
            "reduction_all_k": 1.0 - float(Z @ Z) / sum_e2,
            "reduction_even_k": 1.0 - float(Z[even] @ Z[even]) / float(e[even] @ e[even]),
            "share_c2_over_e2_even": float(c[even] @ c[even]) / float(e[even] @ e[even]),
            "posthoc_slope_e_on_c_even": float(e[even] @ c[even]) / float(c[even] @ c[even]),
            "corr_e_c_even": float(np.corrcoef(e[even], c[even])[0, 1]),
            "mean_Z_even_k": float(Z[even].mean()),
            "mean_Z_all_k": float(Z.mean()),
            "residual_over_N2log2N": 2 * float(Z @ Z) / (N * N * math.log(N) ** 2),
        }
        comp[str(q)] = row
    out["comparison"] = comp
    # where the residual concentrates, for Z_30 (and e, Z_1, Z_3 for contrast)
    Z30 = e - corr[30]
    conc: dict = {}
    ki = k[inner]
    for name, y in (("e", e), ("Z1", e - corr[1]), ("Z3", e - corr[3]), ("Z30", Z30)):
        yi = y[inner]
        conc[name] = {
            "by_k_mod_3": _class_means(yi, ki % 3, range(3)),
            "by_k_mod_30_even": _class_means(yi, ki % 30, range(0, 30, 2)),
            "by_k_mod_7": _class_means(yi, ki % 7, range(7)),
            "by_k_mod_11": _class_means(yi, ki % 11, range(11)),
            "by_k_mod_13": _class_means(yi, ki % 13, range(13)),
        }
    dec = np.minimum((10 * ki) // N, 9)
    z2 = Z30[inner] ** 2
    conc["Z30_share_by_decile_of_k_over_N"] = [float(z2[dec == d].sum() / z2.sum()) for d in range(10)]
    conc["e_share_by_decile_of_k_over_N"] = [float((e[inner] ** 2)[dec == d].sum() / (e[inner] ** 2).sum()) for d in range(10)]
    conc["Z30_mean_by_decile"] = _class_means(Z30[inner], dec, range(10))
    Si = S[1 : N + 1][inner]
    qs = np.quantile(Si, [0, 0.2, 0.4, 0.6, 0.8, 1.0])
    sb = np.clip(np.searchsorted(qs, Si, side="right") - 1, 0, 4)
    conc["Z30_mean_by_S_quintile"] = _class_means(Z30[inner], sb, range(5))
    if with_next:
        # does the mod-7 structure of Z_30 match what the q = 210 member predicts?
        inc = (corr[NEXT_MODULUS] - corr[30])[inner]
        conc["q210_increment_by_k_mod_7"] = _class_means(inc, ki % 7, range(7))
        conc["Z210_by_k_mod_7"] = _class_means((e - corr[NEXT_MODULUS])[inner], ki % 7, range(7))
        conc["corr_Z30_with_q210_increment_even"] = float(np.corrcoef(Z30[inner], inc)[0, 1])
        conc["slope_Z30_on_q210_increment_even"] = float(Z30[inner] @ inc / (inc @ inc))
    out["concentration"] = conc
    # The k-sum weighted by the character mod 3, the object of statement (T) in RESULTS.md:
    #   T(N) = sum_{k <= N} chi(k) e(N, k).  Under H_3, with S(k) replaced by its class
    # mean 3/2 on even k not divisible by 3, T(N) is (3/2) sum_{k even, 3 not | k}
    # [psi(N-k, chi) - psi(N, chi) + psi(k, chi)], and with the class sum replaced by a
    # third of the full sum it is sum_{x < N} psi(x, chi) - ((N-1)/2) psi(N, chi).
    chi = np.zeros(N + 1)
    chi[1::3] = 1.0
    chi[2::3] = -1.0
    chik = chi[1:]
    psi_chi = np.cumsum(lam[: N + 1] * chi)
    cls = even & (k % 3 != 0) & (k < N)
    prof = psi_chi[N - k] - psi_chi[N] + psi_chi[k]
    T_meas = float(chik @ e)
    T_int = float(psi_chi[:N].sum()) - 0.5 * (N - 1) * float(psi_chi[N])
    out["T_chi3"] = {
        "T_measured": T_meas,
        "T_from_c1": float(chik @ corr[1]),
        "T_from_c3": float(chik @ corr[3]),
        "T_from_c30": float(chik @ corr[30]),
        "T_class_mean_S": 1.5 * float(prof[cls].sum()),
        "T_integral_form": T_int,
        "T_odd_k_part": float((chik * e)[~even].sum()),
        "N_to_3_over_2": N ** 1.5,
        "ratio_measured_over_integral": T_meas / T_int if T_int else None,
        "residual_over_N_c3": (T_meas - float(chik @ corr[3])) / N,
        "residual_over_N_integral": (T_meas - T_int) / N,
        "residual_over_NlogN_integral": (T_meas - T_int) / (N * math.log(N)),
    }
    out["seconds"] = time.time() - t0
    return out


def print_summary(d: dict) -> None:
    N = d["N"]
    print(f"\nN = {N}: E/(N^2 log^2 N) = {d['E_over_N2log2N']:.5f}   ({d['seconds']:.1f}s)")
    print(f"  checks: q1 = original {d['check_q1_equals_original_formula_maxabs']:.1e}; "
          f"identity I1 {d['check_identity_I1_maxabs']}; I3 {d['check_I3_S_eq_Sq_times_Scop_maxabs']:.1e}; "
          f"chi3 closed form {d['check_chi3_closed_form_vs_general_maxabs']:.1e}")
    f = d["first_pass_fit_at_fresh_N"]
    print(f"  first-pass fit here: alpha={f['alpha']:.1f} (R(N)={f['R_N']:.1f}) beta={f['beta_B']:.3f} gamma={f['gamma_R']:.3f}")
    print(f"  mean e (even k) = {d['mean_e_even_k']:.1f}")
    for q, row in d["comparison"].items():
        p = d["pieces"][q]
        print(f"  q={q:>3}: reduction all-k {100*row['reduction_all_k']:.3f}%  even-k {100*row['reduction_even_k']:.3f}%  "
              f"share c^2/e^2 {100*row['share_c2_over_e2_even']:.3f}%  post-hoc slope {row['posthoc_slope_e_on_c_even']:.3f}  "
              f"mean Z even {row['mean_Z_even_k']:.1f}  | rms S*L {p['rms_Scop_L']:.0f} rms X {p['rms_X']:.1f} max|rho| {p['max_abs_rho']:.1f}")
    pf = d["product_form_q30"]
    print(f"  product form q=30: max|prod - linear| {pf['maxabs_prod_minus_linear_k_lt_N']:.1f}, reduction {100*pf['reduction_all_k']:.3f}%")
    print(f"  rms(c3 - c1) = {d['rms_c3_minus_c1_even']:.0f}, rms(c30 - c3) = {d['rms_c30_minus_c3_even']:.0f}")
    c = d["concentration"]
    for name in ("e", "Z1", "Z3", "Z30"):
        rows = c[name]["by_k_mod_3"]
        print(f"  {name:>3} by k mod 3: " + "  ".join(f"[{r['class']}] {r['mean']:.0f}±{r['se']:.0f}" for r in rows))
    for mod in ("by_k_mod_7", "by_k_mod_11", "by_k_mod_13"):
        rows = c["Z30"][mod]
        print(f"  Z30 {mod}: " + " ".join(f"{r['z']:+.1f}" for r in rows) + "   (z-scores)")
    if "q210_increment_by_k_mod_7" in c:
        print("  Z30 by k mod 7 (mean):   " + " ".join(f"{r['mean']:+.0f}" for r in c["Z30"]["by_k_mod_7"]))
        print("  q=210 increment mod 7:   " + " ".join(f"{r['mean']:+.0f}" for r in c["q210_increment_by_k_mod_7"]))
        print("  Z210 by k mod 7 (z):     " + " ".join(f"{r['z']:+.1f}" for r in c["Z210_by_k_mod_7"]))
        print(f"  corr(Z30, q210 increment) = {c['corr_Z30_with_q210_increment_even']:.3f}, slope {c['slope_Z30_on_q210_increment_even']:.3f}")
    T = d["T_chi3"]
    print(f"  T(N) = sum chi3(k) e: measured {T['T_measured']:.4e}; from c1 {T['T_from_c1']:.4e}; from c3 {T['T_from_c3']:.4e}; "
          f"class-mean-S {T['T_class_mean_S']:.4e}; integral form {T['T_integral_form']:.4e}; N^1.5 {T['N_to_3_over_2']:.2e}")
    print(f"     ratio meas/integral {T['ratio_measured_over_integral']:.4f}; (meas - c3)/N {T['residual_over_N_c3']:.2f}; "
          f"(meas - integral)/N {T['residual_over_N_integral']:.2f}; odd-k part {T['T_odd_k_part']:.3e}")
    print("  Z30 share by decile of k/N: " + " ".join(f"{x:.3f}" for x in c["Z30_share_by_decile_of_k_over_N"]))
    print("  Z30 mean by S-quintile:     " + " ".join(f"{r['mean']:+.0f}±{r['se']:.0f}" for r in c["Z30_mean_by_S_quintile"]))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=max(FRESH_CUTOFFS))
    ap.add_argument("--fresh", type=int, nargs="*", default=None,
                    help="cutoffs to evaluate (default: the fresh list, filtered by --max-n)")
    ap.add_argument("--out", default=str(HERE / "results_residue.json"))
    ap.add_argument("--no-next", action="store_true", help="skip the q = 210 diagnostic")
    args = ap.parse_args(argv)
    t0 = time.time()
    Ns = [N for N in (args.fresh or FRESH_CUTOFFS) if N <= args.max_n]
    if not Ns:
        raise SystemExit("no cutoff at or below --max-n")
    overlap = sorted(set(Ns) & set(FIRST_PASS_CUTOFFS))
    print(f"cutoffs {Ns}; first-pass overlap {overlap or 'none'}; frozen coefficients {FROZEN}")
    lam, lam_p = probe.von_mangoldt(max(Ns))
    S = probe.singular_series(max(Ns))
    res: dict = {"paper": "arXiv:2308.14888", "frozen": FROZEN, "cutoffs": Ns,
                 "first_pass_overlap": overlap, "moduli": list(MODULI), "next_modulus": NEXT_MODULUS}
    runs = []
    for N in Ns:
        d = analyse(N, lam, lam_p, S, with_next=not args.no_next)
        print_summary(d)
        runs.append(d)
    res["runs"] = runs
    res["seconds_total"] = time.time() - t0
    Path(args.out).write_text(json.dumps(res, indent=1))
    print(f"\nwrote {args.out}  ({res['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
