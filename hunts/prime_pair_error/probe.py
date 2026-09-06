"""Prime-pair error: reproduce Chou, Haag, Huryn, Ledoan (arXiv:2308.14888) and
decompose the error by separation.

Definitions, exactly as in the paper:

    psi_2(N, k) = sum_{n, n' <= N, n' - n = k} Lambda(n) Lambda(n')
    S(k)        = 2 C_2 prod_{p | k, p > 2} (p - 1)/(p - 2)   (k even),  0  (k odd)
    e(N, k)     = psi_2(N, k) - S(k) (N - k)                  (1 <= k <= N)
    E(N)        = sum_{1 <= |k| <= N} e(N, k)^2 = 2 sum_{k=1}^{N} e(N, k)^2

The prediction S(k)(N - k) is held fixed; nothing here is refit.

psi_2(N, .) is the autocorrelation of the von Mangoldt sequence truncated at
N, computed by FFT and cross-checked against a direct pair count (numpy) and a
pure-Python pair count (no numpy) at small N.

Run:  .venv/bin/python hunts/prime_pair_error/probe.py [--max-n 10000000]
Writes hunts/prime_pair_error/results.json.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from mpmath import mp

HERE = Path(__file__).resolve().parent

# Twin-prime constant, C_2 = prod_{p > 2} (1 - 1/(p-1)^2).  Computed once at
# 30 digits from the Euler product with a tail bound rather than pasted in;
# the paper's 0.66016... is the check.
def twin_prime_constant(P: int = 4_000_000) -> float:
    """C_2 = prod_{p > 2} (1 - 1/(p-1)^2), direct product over p <= P.
    The tail sum_{p > P} 1/(p-1)^2 is below 1/(P log P), so the product is
    good to about 1e-8; the pinned reference below is the 30-digit value."""
    sieve = np.ones(P + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(P ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    odd = np.nonzero(sieve)[0][1:].astype(np.float64)
    return float(np.exp(np.sum(np.log1p(-1.0 / (odd - 1.0) ** 2))))


C2 = 0.6601618158468695739278121100145  # reference value (Wrench 1961); checked below
TWO_C2 = 2.0 * C2


def von_mangoldt(N: int) -> tuple[np.ndarray, np.ndarray]:
    """Lambda(n) for 0 <= n <= N (index 0 and 1 are zero), and the
    primes-only version Lambda restricted to primes (proper powers zeroed)."""
    spf = np.zeros(N + 1, dtype=np.int64)
    # smallest prime factor sieve
    spf[2:] = np.arange(2, N + 1)
    lim = int(N ** 0.5) + 1
    for i in range(2, lim):
        if spf[i] == i:
            block = spf[i * i :: i]
            mask = block == np.arange(i * i, N + 1, i)
            block[mask] = i
            spf[i * i :: i] = block
    lam = np.zeros(N + 1, dtype=np.float64)
    lam_prime = np.zeros(N + 1, dtype=np.float64)
    is_prime = spf == np.arange(N + 1)
    is_prime[:2] = False
    p_idx = np.nonzero(is_prime)[0]
    lam_prime[p_idx] = np.log(p_idx)
    lam[p_idx] = np.log(p_idx)
    # proper prime powers p^a, a >= 2
    for p in p_idx[p_idx <= int(N ** 0.5) + 1]:
        q = p * p
        while q <= N:
            lam[q] = math.log(p)
            q *= p
    return lam, lam_prime


def singular_series(N: int) -> np.ndarray:
    """S(k) for 0 <= k <= N.  S(0) is set to 0 (undefined in the paper)."""
    S = np.ones(N + 1, dtype=np.float64)
    sieve = np.ones(N + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = False
    primes = np.nonzero(sieve)[0]
    for p in primes[primes > 2]:
        S[p::p] *= (p - 1.0) / (p - 2.0)
    S *= TWO_C2
    S[1::2] = 0.0
    S[0] = 0.0
    return S


def singular_series_python(k: int) -> float:
    """S(k) by trial division, no numpy, for an independent check."""
    if k % 2:
        return 0.0
    s, m, p = 2.0 * C2, k, 3
    while m % 2 == 0:
        m //= 2
    while p * p <= m:
        if m % p == 0:
            s *= (p - 1.0) / (p - 2.0)
            while m % p == 0:
                m //= p
        p += 2
    if m > 1:
        s *= (m - 1.0) / (m - 2.0)
    return s


def psi2_fft(lam: np.ndarray, N: int) -> np.ndarray:
    """psi_2(N, k) for 0 <= k <= N via FFT autocorrelation of lam[0..N]."""
    a = lam[: N + 1]
    L = 1 << int(math.ceil(math.log2(2 * (N + 1))))
    F = np.fft.rfft(a, n=L)
    ac = np.fft.irfft(F * np.conj(F), n=L)[: N + 1]
    return ac


def psi2_direct(lam: np.ndarray, N: int, block: int = 400) -> np.ndarray:
    """psi_2(N, k), 0 <= k <= N, by explicit pair enumeration (numpy)."""
    idx = np.nonzero(lam[: N + 1])[0]
    w = lam[idx]
    out = np.zeros(N + 1, dtype=np.float64)
    for s in range(0, len(idx), block):
        m = idx[s : s + block]
        wm = w[s : s + block]
        d = np.subtract.outer(idx, m)  # n' - n with n = m
        ww = np.multiply.outer(w, wm)
        keep = d >= 0
        out += np.bincount(d[keep], weights=ww[keep], minlength=N + 1)[: N + 1]
    return out


def psi2_python(N: int) -> list[float]:
    """Pure-Python psi_2(N, k), no numpy, for an independent small-N check."""
    lam = {}
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p ** 0.5) + 1)):
            q = p
            while q <= N:
                lam[q] = math.log(p)
                q *= p
    keys = sorted(lam)
    out = [0.0] * (N + 1)
    for i, n in enumerate(keys):
        for m in keys[i:]:
            out[m - n] += lam[n] * lam[m]
    return out


def E_of_N(psi2: np.ndarray, S: np.ndarray, N: int) -> float:
    k = np.arange(1, N + 1)
    e = psi2[1 : N + 1] - S[1 : N + 1] * (N - k)
    return 2.0 * float(np.dot(e, e))


def truncate5(x: float) -> float:
    return math.floor(x * 1e5) / 1e5


PAPER_TABLE_1 = [
    (1_000, 0.09464), (10_000, 0.12327), (20_000, 0.13061), (30_000, 0.14507),
    (40_000, 0.15081), (50_000, 0.15480), (60_000, 0.16124), (70_000, 0.17745),
    (80_000, 0.15953), (90_000, 0.16192), (100_000, 0.16857),
]


def decompose(N: int, lam: np.ndarray, lam_p: np.ndarray, S: np.ndarray) -> dict:
    """Break E(N) down by separation size and arithmetic of k, and measure
    the candidate structured components.  Everything is over 1 <= k <= N,
    doubled for +-k."""
    psi2 = psi2_fft(lam, N)
    theta2 = psi2_fft(lam_p, N)          # pairs of genuine primes only
    k = np.arange(1, N + 1)
    Sk = S[1 : N + 1]
    pred = Sk * (N - k)
    e = psi2[1:] - pred
    e2 = e * e
    E = 2.0 * float(e2.sum())
    P = psi2[1:] - theta2[1:]            # pairs with a proper prime power
    e_theta = theta2[1:] - pred
    notN = k < N                          # pred(N) = 0; keep ratios finite

    out: dict = {"N": N, "E": E, "E_over_N2log2N": E / (N * N * math.log(N) ** 2)}

    # --- by size of separation: deciles of k/N
    dec = np.minimum((10 * k) // N, 9)
    out["share_by_decile_of_k_over_N"] = [float(2 * e2[dec == d].sum() / E) for d in range(10)]
    # --- odd vs even
    odd = (k % 2) == 1
    out["share_odd_k"] = float(2 * e2[odd].sum() / E)
    # --- by 2-adic valuation and small odd prime divisors (even k only)
    v2 = np.zeros(N + 1, dtype=np.int64)
    kk = np.arange(N + 1)
    t = kk.copy()
    for _ in range(40):
        m = (t > 0) & (t % 2 == 0)
        if not m.any():
            break
        v2[m] += 1
        t[m] //= 2
    v2 = v2[1:]
    classes = {
        "v2=1": (v2 == 1), "v2=2": (v2 == 2), "v2>=3": (v2 >= 3),
        "3|k": (k % 3 == 0) & ~odd, "3∤k even": (k % 3 != 0) & ~odd,
        "5|k": (k % 5 == 0) & ~odd, "15|k": (k % 15 == 0) & ~odd,
        "105|k": (k % 105 == 0) & ~odd,
    }
    classes = {name: m & notN for name, m in classes.items()}
    cls = {}
    for name, m in classes.items():
        cnt = int(m.sum())
        cls[name] = {
            "count": cnt,
            "share_of_E": float(2 * e2[m].sum() / E),
            "share_of_k": cnt / N,
            "mean_e2": float(e2[m].mean()) if cnt else None,
            "mean_pred": float(pred[m].mean()) if cnt else None,
            "mean_e2_over_pred": float((e2[m] / pred[m]).mean()) if cnt else None,
            "mean_e": float(e[m].mean()) if cnt else None,
        }
    out["by_class"] = cls

    # --- Poisson-type scaling: within even k, bin by S(k) and by k/N, and
    # report mean e^2 / (S(k)(N-k)) per cell.  A flat table means the
    # arithmetic of k enters the error only through S(k).
    ev = ~odd & notN
    Se = Sk[ev]; ee2 = e2[ev]; pe = pred[ev]; ke = k[ev]
    # S-bins: quantile edges of S among even k
    qs = np.quantile(Se, [0, 0.25, 0.5, 0.75, 0.9, 1.0])
    sbin = np.clip(np.searchsorted(qs, Se, side="right") - 1, 0, 4)
    kbin = np.minimum((5 * ke) // N, 4)
    table = []
    for i in range(5):
        row = []
        for j in range(5):
            m = (sbin == i) & (kbin == j)
            row.append(float((ee2[m] / pe[m]).mean()) if m.sum() > 20 else None)
        table.append(row)
    out["e2_over_pred_by_Sbin_x_kbin"] = {"S_edges": [float(x) for x in qs], "table": table}
    # log-log slope of mean e^2 against mean pred across S-bins at fixed k-bin
    # (exponent gamma in e^2 ~ S^gamma); use 20 S-quantile bins in the first
    # k-fifth where pred varies little in k.
    m0 = kbin == 0
    q20 = np.quantile(Se[m0], np.linspace(0, 1, 21))
    b20 = np.clip(np.searchsorted(q20, Se[m0], side="right") - 1, 0, 19)
    xs, ys = [], []
    for b in range(20):
        mm = b20 == b
        if mm.sum() > 20:
            xs.append(math.log(Se[m0][mm].mean()))
            ys.append(math.log(ee2[m0][mm].mean()))
    slope = float(np.polyfit(xs, ys, 1)[0]) if len(xs) > 3 else None
    out["gamma_e2_vs_S_small_k"] = slope
    floor = []
    for j in range(5):
        mj = kbin == j
        qj = np.quantile(Se[mj], np.linspace(0, 1, 21))
        bj = np.clip(np.searchsorted(qj, Se[mj], side="right") - 1, 0, 19)
        xs, ys = [], []
        for b in range(20):
            mm = bj == b
            if mm.sum() > 20:
                xs.append(pe[mj][mm].mean()); ys.append(ee2[mj][mm].mean())
        if len(xs) > 3:
            Bc, Ac = np.polyfit(xs, ys, 1)
            floor.append({"k_fifth": j, "A": float(Ac), "B": float(Bc),
                          "A_over_NlogN": float(Ac) / (N * math.log(N)),
                          "A_over_N": float(Ac) / N,
                          "B_over_log2N": float(Bc) / math.log(N) ** 2})
        else:
            floor.append({"k_fifth": j, "A": None, "B": None})
    out["floor_fit_e2_eq_A_plus_B_pred"] = floor

    # --- structured components
    psi = np.cumsum(lam[: N + 1]); x = np.arange(N + 1, dtype=np.float64)
    R = psi - x                                   # psi(x) - x
    R[0] = 0.0
    ebar = float(e.mean())
    out["mean_e"] = ebar
    out["R_N"] = float(R[N])
    out["share_of_E_from_mean"] = 2 * N * ebar * ebar / E
    # exact identity: sum_{1<=|k|<=N} psi_2 = psi(N)^2 - sum Lambda^2, so
    # mean_k e = [psi(N)^2 - sum Lambda^2 - 2 sum_k (N-k) S(k)] / (2N)
    lam2 = float(np.dot(lam[: N + 1], lam[: N + 1]))
    ident = (float(psi[N]) ** 2 - lam2 - 2.0 * float(pred.sum())) / (2 * N)
    out["mean_e_from_identity"] = ident
    # constant in sum_{k<=h} S(k) = h - (1/2) log h + c, at h = N
    out["singular_series_sum_constant_at_N"] = float(S[1 : N + 1].sum()) - N + 0.5 * math.log(N)
    out["mean_e_minus_R_N"] = ebar - float(R[N])
    out["mean_e_even_k"] = float(e[~odd].mean())
    out["mean_e_odd_k"] = float(e[odd].mean())
    # q = 1 explicit-formula profile  s1(k) = R(N) - R(k) + R(N - k)
    s1 = R[N] - R[1 : N + 1] + R[N - k]
    beta = float(np.dot(e, s1) / np.dot(s1, s1))
    out["profile_q1"] = {
        "beta": beta,
        "corr": float(np.corrcoef(e, s1)[0, 1]),
        "share_of_E": 2 * beta * beta * float(np.dot(s1, s1)) / E,
    }
    # prime-power pairs: P(N,k) = psi_2 - theta_2, and the profile
    # B(N,k) = (psi-theta)(N-k) + (psi-theta)(N) - (psi-theta)(k)
    pt = np.cumsum(lam[: N + 1] - lam_p[: N + 1])
    B = pt[N - k] + pt[N] - pt[1 : N + 1]
    SB = Sk * B
    out["prime_power_pairs"] = {
        "share_of_E_from_P": 2 * float(np.dot(P, P)) / E,
        "cross_term_4_sum_etheta_P_over_E": 4 * float(np.dot(e_theta, P)) / E,
        "share_of_E_from_e_theta": 2 * float(np.dot(e_theta, e_theta)) / E,
        "mean_P": float(P.mean()),
        "mean_e_theta": float(e_theta.mean()),
        "sqrtN": math.sqrt(N),
        "psi_minus_theta_N": float(pt[N]),
        "coef_P_on_SB": float(np.dot(P, SB) / np.dot(SB, SB)),
        "coef_e_on_SB": float(np.dot(e, SB) / np.dot(SB, SB)),
        "coef_etheta_on_SB": float(np.dot(e_theta, SB) / np.dot(SB, SB)),
        "corr_P_SB": float(np.corrcoef(P, SB)[0, 1]),
        "corr_e_SB": float(np.corrcoef(e, SB)[0, 1]),
        "corr_etheta_SB": float(np.corrcoef(e_theta, SB)[0, 1]),
        "share_of_E_along_SB": 2 * float(np.dot(e, SB)) ** 2 / float(np.dot(SB, SB)) / E,
    }
    def _se(y, x):
        c = float(np.dot(y, x) / np.dot(x, x)); r = y - c * x
        return math.sqrt(float(np.dot(r, r)) / (len(y) - 1) / float(np.dot(x, x)))
    out["prime_power_pairs"]["se_coef_on_SB_indep"] = _se(e, SB)
    # --- joint fit on even k < N of  y = S(k) [alpha + beta (B - mean B) + gamma (R(N-k) - R(k))]
    # for y in e, e_theta, P.  The three profiles: a flat S-modulated offset
    # (compare alpha with psi(N)-N for e), the prime-power deficit shape, and the
    # antisymmetric zero profile from the q = 1 arc.
    evk = ~odd & notN
    Bc = B - float(B[evk].mean())
    A = np.stack([Sk[evk], (Sk * Bc)[evk], (Sk * (R[N - k] - R[1 : N + 1]))[evk]], axis=1)
    AtA_inv = np.linalg.inv(A.T @ A)
    joint = {"mean_B_even": float(B[evk].mean()), "R_N": float(R[N]),
             "theta_N_minus_N": float(R[N] - pt[N])}
    for name, y in (("e", e), ("e_theta", e_theta), ("P", P)):
        yy = y[evk]
        coef = AtA_inv @ (A.T @ yy)
        r = yy - A @ coef
        s2 = float(np.dot(r, r)) / (len(yy) - 3)
        se = np.sqrt(np.diag(AtA_inv) * s2)
        fitted = A @ coef
        tot = float(np.dot(yy, yy))
        joint[name] = {
            "alpha": float(coef[0]), "beta_B": float(coef[1]), "gamma_R": float(coef[2]),
            "se": [float(x) for x in se],
            "share_of_sum_y2_explained": float(np.dot(fitted, fitted)) / tot,
            "residual_over_N2log2N": 2 * float(np.dot(r, r)) / (N * N * math.log(N) ** 2),
            "corr_y_fitted": float(np.corrcoef(yy, fitted)[0, 1]),
        }
    out["joint_fit_even_k"] = joint
    # e_theta against its own prediction minus S*B: does the residual mean vanish?
    resid = e_theta + SB
    out["prime_power_pairs"]["mean_e_theta_plus_SB"] = float(resid.mean())
    out["prime_power_pairs"]["mean_e_theta_plus_SB_over_sqrtN"] = float(resid.mean()) / math.sqrt(N)
    out["prime_power_pairs"]["mean_e_theta_over_sqrtN"] = float(e_theta.mean()) / math.sqrt(N)
    out["prime_power_pairs"]["R_N_over_sqrtN"] = float(R[N]) / math.sqrt(N)
    # E_theta: the error of genuine prime pairs against the same fixed prediction,
    # and after removing the S*B profile
    out["E_theta_over_N2log2N"] = 2 * float(np.dot(e_theta, e_theta)) / (N * N * math.log(N) ** 2)
    out["E_theta_minus_SB_over_N2log2N"] = 2 * float(np.dot(resid, resid)) / (N * N * math.log(N) ** 2)
    # Same for psi_2 error with the q=1 profile removed
    r1 = e - beta * s1
    out["E_minus_q1_over_N2log2N"] = 2 * float(np.dot(r1, r1)) / (N * N * math.log(N) ** 2)
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=10_000_000)
    ap.add_argument("--out", default=str(HERE / "results.json"))
    args = ap.parse_args(argv)
    t0 = time.time()
    res: dict = {"paper": "arXiv:2308.14888", "C2_reference": C2}

    # 0. the constant
    c2 = twin_prime_constant()
    res["C2_product_to_4e6"] = c2
    print(f"C_2 product to 4e6 = {c2:.10f}  (reference {C2:.10f}, diff {c2 - C2:.2e})")

    # 1. implementation cross-checks
    lam_small, lam_p_small = von_mangoldt(100_000)
    py = psi2_python(2000)
    fft_s = psi2_fft(lam_small, 2000)
    d_py = float(np.max(np.abs(np.array(py) - fft_s)))
    dir_1e5 = psi2_direct(lam_small, 100_000)
    fft_1e5 = psi2_fft(lam_small, 100_000)
    d_dir = float(np.max(np.abs(dir_1e5 - fft_1e5)))
    res["check_fft_vs_python_N2000_maxabs"] = d_py
    res["check_fft_vs_direct_N1e5_maxabs"] = d_dir
    print(f"FFT vs pure-Python (N=2000): max|diff| = {d_py:.2e}")
    print(f"FFT vs direct pairs (N=1e5): max|diff| = {d_dir:.2e}")
    assert d_py < 1e-6 and d_dir < 1e-4

    # singular series: sieve against trial division at every k <= 3e4, and the
    # sum  sum_{k<=h} S(k) - h + (1/2) log h  (Friedlander-Goldston shape)
    S_small = singular_series(100_000)
    d_S = max(abs(S_small[k] - singular_series_python(k)) for k in range(1, 30_001))
    res["check_singular_series_sieve_vs_trial_division_maxabs"] = d_S
    print(f"singular series sieve vs trial division (k<=3e4): max|diff| = {d_S:.2e}")
    assert d_S < 1e-12
    print("S(2), S(6), S(30), S(210) =", [round(float(S_small[k]), 6) for k in (2, 6, 30, 210)])

    # 2. Table 1 of the paper
    rows = []
    print("\nTable 1: E(N)/(N^2 log^2 N)")
    print(f"{'N':>8} {'computed':>12} {'trunc5':>9} {'paper':>9} {'match':>6}")
    for N, paper in PAPER_TABLE_1:
        val = E_of_N(psi2_fft(lam_small, N), S_small, N) / (N * N * math.log(N) ** 2)
        tr = truncate5(val)
        ok = abs(tr - paper) < 1e-9
        rows.append({"N": N, "computed": val, "truncated": tr, "paper": paper, "match": ok})
        print(f"{N:>8} {val:>12.7f} {tr:>9.5f} {paper:>9.5f} {str(ok):>6}")
    res["table1"] = rows
    res["table1_all_match"] = all(r["match"] for r in rows)

    # Figure 3: the curve for N <= 1000 (max, argmax, value at 1000)
    S_1k = S_small
    curve = []
    for N in range(2, 1001):
        curve.append(E_of_N(psi2_fft(lam_small, N), S_1k, N) / (N * N * math.log(N) ** 2))
    curve = np.array(curve)
    res["figure3"] = {"max": float(curve.max()), "argmax_N": int(curve.argmax() + 2),
                      "at_1000": float(curve[-1]), "min_N_ge_100": float(curve[98:].min())}
    print(f"\nFigure 3 curve: max {curve.max():.4f} at N={curve.argmax()+2}, value at 1000 = {curve[-1]:.5f}")

    # 3. decomposition at the paper's N and beyond
    Ns = [1_000, 10_000, 100_000]
    for N in (1_000_000, 3_000_000, 10_000_000):
        if N <= args.max_n:
            Ns.append(N)
    lam, lam_p = von_mangoldt(max(Ns))
    S = singular_series(max(Ns))
    dec = []
    for N in Ns:
        t1 = time.time()
        d = decompose(N, lam, lam_p, S)
        d["seconds"] = time.time() - t1
        dec.append(d)
        pp = d["prime_power_pairs"]
        print(f"\nN={N}: E/(N^2 log^2 N) = {d['E_over_N2log2N']:.5f}   ({d['seconds']:.1f}s)")
        print(f"  share by decile of k/N: {' '.join(f'{x:.3f}' for x in d['share_by_decile_of_k_over_N'])}")
        print(f"  share odd k: {d['share_odd_k']:.2e}")
        for name, c in d["by_class"].items():
            print(f"  {name:>9}: k-share {c['share_of_k']:.3f}  E-share {c['share_of_E']:.3f}  "
                  f"mean e^2/pred {c['mean_e2_over_pred']:.2f}  mean e {c['mean_e']:.1f}")
        print(f"  gamma (e^2 ~ S^gamma, small k): {d['gamma_e2_vs_S_small_k']}")
        print(f"  mean e = {d['mean_e']:.2f},  psi(N)-N = {d['R_N']:.2f},  share of E from mean: {d['share_of_E_from_mean']:.4f}")
        print(f"  q=1 profile: beta={d['profile_q1']['beta']:.3f} corr={d['profile_q1']['corr']:.3f} share={d['profile_q1']['share_of_E']:.4f}")
        print(f"  prime-power pairs: share_P={pp['share_of_E_from_P']:.4f} cross={pp['cross_term_4_sum_etheta_P_over_E']:.4f} "
              f"share_etheta={pp['share_of_E_from_e_theta']:.4f}")
        print(f"     mean P={pp['mean_P']:.1f} sqrtN={pp['sqrtN']:.1f} (psi-theta)(N)={pp['psi_minus_theta_N']:.1f} "
              f"mean e_theta={pp['mean_e_theta']:.1f}")
        print(f"     coef on S*B: P {pp['coef_P_on_SB']:.3f} (corr {pp['corr_P_SB']:.3f}), e {pp['coef_e_on_SB']:.3f} "
              f"(corr {pp['corr_e_SB']:.3f}), e_theta {pp['coef_etheta_on_SB']:.3f} (corr {pp['corr_etheta_SB']:.3f})")
        print(f"     share of E along S*B: {pp['share_of_E_along_SB']:.4f}")
        print(f"     E_theta/(N^2log^2N)={d['E_theta_over_N2log2N']:.5f}  after removing S*B: {d['E_theta_minus_SB_over_N2log2N']:.5f}")
        print(f"  identity mean e = {d['mean_e_from_identity']:.2f}; mean e - (psi(N)-N) = {d['mean_e_minus_R_N']:.2f}; "
              f"sum S(k)-N+log(N)/2 = {d['singular_series_sum_constant_at_N']:.3f}; mean e even/odd = {d['mean_e_even_k']:.1f}/{d['mean_e_odd_k']:.1f}")
        print("  floor fit e^2 = A + B*pred per k-fifth: " + "  ".join(
            f"[{f['k_fifth']}: A/(N logN)={f['A_over_NlogN']:.2f} B/log2N={f['B_over_log2N']:.3f}]"
            for f in d['floor_fit_e2_eq_A_plus_B_pred'] if f['A'] is not None))
        print(f"  se(coef on S*B, indep approx) = {pp['se_coef_on_SB_indep']:.3f}")
        jf = d["joint_fit_even_k"]
        print(f"  joint fit y = S(k)[alpha + beta (B - {jf['mean_B_even']:.0f}) + gamma (R(N-k) - R(k))], even k;  "
              f"psi(N)-N = {jf['R_N']:.1f}, theta(N)-N = {jf['theta_N_minus_N']:.1f}")
        for nm in ("e", "e_theta", "P"):
            j = jf[nm]
            print(f"     {nm:>7}: alpha={j['alpha']:9.1f}±{j['se'][0]:.1f}  beta={j['beta_B']:6.3f}±{j['se'][1]:.3f}  "
                  f"gamma={j['gamma_R']:6.3f}±{j['se'][2]:.3f}  explained {j['share_of_sum_y2_explained']:.4f}  "
                  f"resid/(N^2log^2N)={j['residual_over_N2log2N']:.5f}")
        print("  e^2/pred by S-bin (rows) x k-fifth (cols):")
        for row in d["e2_over_pred_by_Sbin_x_kbin"]["table"]:
            print("     " + " ".join(f"{x:7.2f}" if x is not None else "     --" for x in row))
    res["decomposition"] = dec
    Nmax = max(Ns)
    psi2_big = psi2_fft(lam, Nmax)
    spot = []
    for kk in (2, 6, 30, 210, 2310, Nmax // 3, Nmax - 2):
        direct = float(np.dot(lam[: Nmax + 1 - kk], lam[kk : Nmax + 1]))
        spot.append({"N": Nmax, "k": kk, "fft": float(psi2_big[kk]), "direct": direct,
                     "absdiff": abs(direct - float(psi2_big[kk]))})
    res["spot_check_largest_N"] = spot
    print(f"\nspot check at N={Nmax}: max |fft - direct| = {max(s['absdiff'] for s in spot):.2e}")
    del psi2_big
    res["seconds_total"] = time.time() - t0
    Path(args.out).write_text(json.dumps(res, indent=1))
    print(f"\nwrote {args.out}  ({res['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
