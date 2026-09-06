"""Prime-pair error, third pass: the character-weighted sum of Section 12 as a Wronskian.

Notation as in probe.py and residue.py.  chi is the non-principal character mod 3,
P(x) = psi(x, chi) = sum_{n <= x} Lambda(n) chi(n), R(x) = psi(x) - x, and

    T(N) = sum_{k=1}^{N} chi(k) [psi_2(N, k) - S(k)(N - k)],
    I(N) = sum_{j=0}^{N-1} P(j) - (N/2) P(N)  =  integral_0^N P(x) dx - (N/2) P(N),

so that RESULTS.md Section 12's statement (T) reads T(N) = I(N) + O(N^{1+eps}).

Exact identities (each pinned in tests/test_prime_pair_residue.py, on arbitrary weights
as well as on Lambda):

    (E1)  For f supported on n != 0 (mod 3), with A, B its class prefix sums on the
          classes 1 and 2 mod 3 and P = A - B, r = A + B - n,
              sum_{n < m <= N} f(n) f(m) chi(m - n) = sum_n [A(n-1) dB(n) - B(n-1) dA(n)]
                                                    = sum_{j=0}^{N-1} P(j) - ((N-1)/2) P(N) + W(N),
              W(N) = (1/2) sum_{n=1}^{N} [P(n-1) dr(n) - r(n-1) dP(n)].
          The first equality is the definition of the prefix sums; the second is the
          expansion A = (n + r + P)/2, B = (n + r - P)/2, and rests on the fact that
          chi(m - n) = (chi(n) - chi(m))/2 whenever 3 divides neither n nor m.
    (E2)  The pairs with a member divisible by 3 contribute
              X_chi(N) = sum_{3 | n} f(n) [P(N) - 2 P(n)].
    (E3)  Hence T(N) - I(N) = W(N) + P(N)/2 + X_chi(N) - H_chi(N),
              H_chi(N) = sum_{k <= N} chi(k) S(k) (N - k).
    (E4)  W(N) = R(N) P(N)/2 - J(N) + Q(N),   J(N) = sum_{m <= N} Lambda(m) chi(m) R(m),
          with Q(N) an explicit sum of one-point terms, |Q(N)| <= 2 psi(N) log_3 N + 2 N,
          so that (T) is equivalent to J(N) - R(N) P(N)/2 = O(N^{1+eps}).

The conditional bound (RH for zeta and for L(s, chi_3) gives J(N) = O(N log^4 N)) is
argued in RESULTS.md; nothing here computes a zero of any L-function.  Everything this
script prints is an exact evaluation of the identities above from prefix sums; the
pair count enters only through psi_2, to check (E3) against the actual T(N).

Run:  .venv/bin/python hunts/prime_pair_error/wronskian.py [--cutoffs N ...]
Writes hunts/prime_pair_error/results_wronskian.json.
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
CUTOFFS = [200_000, 500_000, 2_000_000, 5_000_000, 7_000_000]


def chi3(N: int) -> np.ndarray:
    """chi(n) for 0 <= n <= N, the non-principal character mod 3."""
    chi = np.zeros(N + 1)
    chi[1::3] = 1.0
    chi[2::3] = -1.0
    return chi


# ---------------------------------------------------------------------------
# the two sides of (E1)-(E3), from prefix sums only
# ---------------------------------------------------------------------------

def class_prefix_sums(f: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """A(n), B(n): prefix sums of f over n = 1, 2 (mod 3); f[0] is ignored."""
    N = len(f) - 1
    n = np.arange(N + 1)
    g = f.astype(np.float64).copy()
    g[0] = 0.0
    A = np.cumsum(np.where(n % 3 == 1, g, 0.0))
    B = np.cumsum(np.where(n % 3 == 2, g, 0.0))
    return A, B


def reduced_pair_sum_by_classes(f: np.ndarray) -> float:
    """sum_n [A(n-1) dB(n) - B(n-1) dA(n)], the left side of (E1) via prefix sums."""
    A, B = class_prefix_sums(f)
    dA, dB = np.diff(A), np.diff(B)          # index n-1 holds the jump at n, n = 1..N
    return float(A[:-1] @ dB - B[:-1] @ dA)


def wronskian(P: np.ndarray, r: np.ndarray) -> float:
    """W(N) = (1/2) sum_{n=1}^N [P(n-1) dr(n) - r(n-1) dP(n)] for cumulative P, r on 0..N."""
    return 0.5 * float(P[:-1] @ np.diff(r) - r[:-1] @ np.diff(P))


def reduced_pair_sum_by_wronskian(f: np.ndarray) -> tuple[float, dict]:
    """The right side of (E1): sum_{j<N} P(j) - ((N-1)/2) P(N) + W(N)."""
    N = len(f) - 1
    A, B = class_prefix_sums(f)
    P = A - B
    r = A + B - np.arange(N + 1, dtype=np.float64)
    W = wronskian(P, r)
    main = float(P[:N].sum()) - 0.5 * (N - 1) * float(P[N])
    return main + W, {"main_Nminus1": main, "W": W, "P_N": float(P[N]), "r_N": float(r[N])}


def exceptional_by_formula(f: np.ndarray) -> float:
    """X_chi(N) = sum_{3 | n} f(n) [P(N) - 2 P(n)]  (E2)."""
    N = len(f) - 1
    A, B = class_prefix_sums(f)
    P = A - B
    n = np.arange(N + 1)
    m = (n % 3 == 0) & (n > 0)
    return float(np.sum(f[m] * (P[N] - 2.0 * P[m])))


def pair_sum_direct(f: np.ndarray) -> tuple[float, float]:
    """sum_{n<m<=N} f(n) f(m) chi(m-n), split into (3 not | nm, 3 | nm), by explicit
    O(N^2) enumeration.  Independent of every prefix-sum routine above."""
    N = len(f) - 1
    chi = chi3(N)
    idx = np.nonzero(f[1:])[0] + 1
    red = 0.0
    exc = 0.0
    for i, n in enumerate(idx):
        ms = idx[i + 1 :]
        vals = f[n] * f[ms] * chi[ms - n]
        both = (n % 3 != 0) & (ms % 3 != 0)
        red += float(vals[both].sum())
        exc += float(vals[~both].sum())
    return red, exc


def H_chi(N: int, S: np.ndarray) -> float:
    """H_chi(N) = sum_{k <= N} chi(k) S(k) (N - k)."""
    k = np.arange(1, N + 1)
    return float((chi3(N)[1:] * S[1 : N + 1]) @ (N - k))


def H_chi_by_divisor_expansion(N: int) -> float:
    """H_chi(N) again, from S(k) = 2 C_2 sum_{d | k, d odd squarefree} g(d), g(p) = 1/(p-2):
    H = -2 C_2 sum_{d odd sqfree, 3 not | d} g(d) chi(d) integral_0^N 1[floor(x/2d) = 1 (3)] dx.
    Shares no code with probe.singular_series."""
    tot = 0.0
    # g(d) chi(d) for odd squarefree d up to N/2 with 3 not dividing d, by a sieve
    D = N // 2
    g = np.ones(D + 1)
    sqfree = np.ones(D + 1, dtype=bool)
    for p in range(3, D + 1):
        if g[p] != 1.0 or not sqfree[p]:
            continue
        if any(p % q == 0 for q in range(2, int(p ** 0.5) + 1)):
            continue
        g[p::p] *= 1.0 / (p - 2.0)
        sqfree[p * p :: p * p] = False
    chi = chi3(D)
    for d in range(1, D + 1, 2):
        if not sqfree[d] or d % 3 == 0:
            continue
        # integral_0^N 1[floor(x / 2d) = 1 mod 3] dx, exactly
        L = 2 * d
        J = N // L                    # floor(x/L) takes values 0..J on [0, N]
        full = sum(L for j in range(1, J, 3))          # complete cells j = 1, 4, 7, ... < J
        part = (N - J * L) if J % 3 == 1 else 0        # the last, partial cell
        tot += g[d] * chi[d] * (full + part)
    return -2.0 * C2 * tot


def G_infinity(P: int = 2_000_000) -> float:
    """prod_{p > 3} (1 + chi(p)/(p-2)), the constant in H_chi(N) ~ -(2 C_2/3) G N."""
    primes = np.nonzero(probe.von_mangoldt(P)[1])[0]
    primes = primes[primes > 3]
    chi = chi3(P)
    return float(np.prod(1.0 + chi[primes] / (primes - 2.0)))


# ---------------------------------------------------------------------------
# (E4): W split into the two remainder terms and the explicit one-point rest
# ---------------------------------------------------------------------------

def split_W(lam: np.ndarray, N: int) -> dict:
    """W = R(N) P(N)/2 - J(N) + Q(N) with every piece exact.

    From (E1): dr(n) = Lambda'(n) - 1 with Lambda' = Lambda on 3 not | n, and
    dP(n) = Lambda(n) chi(n).  Abel summation of sum P(n-1) dR(n) against
    sum R(n) dP(n), with R(n) - R(n-1) = Lambda(n) - 1, gives
        W = R(N) P(N)/2 - sum_m Lambda(m) chi(m) R(m)
            + (1/2) [ sum_m Lambda(m)^2 chi(m) - P(N) - (log 3) sum_j P(3^j - 1)
                      + sum_m Lambda(m) chi(m) psi_0(m-1) ],
    psi_0(x) = sum_{n <= x, 3 | n} Lambda(n)."""
    lam_ = lam[: N + 1]
    n = np.arange(N + 1)
    chi = chi3(N)
    psi = np.cumsum(lam_)
    R = psi - n.astype(np.float64)
    R[0] = 0.0
    P = np.cumsum(lam_ * chi)
    psi0 = np.cumsum(np.where(n % 3 == 0, lam_, 0.0))
    J = float(np.sum(lam_ * chi * R))
    pow3 = n[(n > 0) & (n % 3 == 0) & (lam_ > 0)]
    Q = 0.5 * (float(np.sum(lam_ ** 2 * chi)) - float(P[N])
               - math.log(3) * float(P[pow3 - 1].sum())
               + float(np.sum(lam_[1:] * chi[1:] * psi0[:-1])))
    return {"RP_half": 0.5 * float(R[N] * P[N]), "J": J, "Q": Q,
            "W_from_split": 0.5 * float(R[N] * P[N]) - J + Q,
            "R_N": float(R[N]), "P_N": float(P[N]),
            "Q_bound": 2.0 * float(psi[N]) * math.log(N) / math.log(3) + 2.0 * N}


# ---------------------------------------------------------------------------
# evaluation at a cutoff
# ---------------------------------------------------------------------------

def evaluate(N: int, lam: np.ndarray, S: np.ndarray, psi2: np.ndarray | None = None) -> dict:
    """Every piece of (E3) and (E4) at N; T(N) itself needs psi_2 (FFT), all else is prefix sums."""
    t0 = time.time()
    lam_ = lam[: N + 1]
    chi = chi3(N)
    k = np.arange(1, N + 1)
    P = np.cumsum(lam_ * chi)
    I = float(P[:N].sum()) - 0.5 * N * float(P[N])
    # (E1)/(E2) on the reduced and exceptional parts of Lambda
    f_red = np.where(np.arange(N + 1) % 3 == 0, 0.0, lam_)
    red_wr, parts = reduced_pair_sum_by_wronskian(f_red)
    X = exceptional_by_formula(lam_)
    H = H_chi(N, S)
    sp = split_W(lam_, N)
    out = {
        "N": N,
        "I": I,
        "W": parts["W"],
        "P_N_half": 0.5 * float(P[N]),
        "X_chi": X,
        "H_chi": H,
        "aux": 0.5 * float(P[N]) + X - H,          # P/2 + X - H
        "T_from_identity": I + parts["W"] + 0.5 * float(P[N]) + X - H,
        "split": sp,
        "check_E4_W_minus_split": parts["W"] - sp["W_from_split"],
        "logN": math.log(N),
    }
    if psi2 is not None:
        e = psi2[1 : N + 1] - S[1 : N + 1] * (N - k)
        T = float(chi[1:] @ e)
        out["T_measured"] = T
        out["check_E3_T_minus_identity"] = T - out["T_from_identity"]
    # sizes, in the units the conjecture is about
    for key in ("W", "X_chi", "H_chi", "aux"):
        out[key + "_over_N"] = out[key] / N
    out["J_over_N"] = sp["J"] / N
    out["RP_half_over_N"] = sp["RP_half"] / N
    out["W_over_NlogN"] = parts["W"] / (N * math.log(N))
    out["J_over_NlogN"] = sp["J"] / (N * math.log(N))
    out["seconds"] = time.time() - t0
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cutoffs", type=int, nargs="*", default=CUTOFFS)
    ap.add_argument("--out", default=str(HERE / "results_wronskian.json"))
    ap.add_argument("--no-pairs", action="store_true", help="skip the FFT pair count (identity check against T)")
    args = ap.parse_args(argv)
    t0 = time.time()
    Ns = sorted(args.cutoffs)
    lam, _ = probe.von_mangoldt(max(Ns))
    S = probe.singular_series(max(Ns))
    G = G_infinity()
    res = {"paper": "arXiv:2308.14888", "cutoffs": Ns, "G_infinity": G,
           "c_H": -2.0 * C2 * G / 3.0, "runs": []}
    print(f"G_inf = prod_(p>3) (1 + chi(p)/(p-2)) = {G:.6f};  c_H = -(2 C_2/3) G = {res['c_H']:.6f}")
    for N in Ns:
        psi2 = None if args.no_pairs else probe.psi2_fft(lam, N)
        d = evaluate(N, lam, S, psi2)
        res["runs"].append(d)
        print(f"\nN = {N}  ({d['seconds']:.1f}s)")
        if "T_measured" in d:
            print(f"  T measured {d['T_measured']:.6e}  identity {d['T_from_identity']:.6e}  "
                  f"diff {d['check_E3_T_minus_identity']:.2e}")
        print(f"  I = {d['I']:.6e};  W = {d['W']:.4e}  (W/N = {d['W_over_N']:+.3f}, W/(N log N) = {d['W_over_NlogN']:+.4f})")
        print(f"  P/2 + X - H = {d['aux']:.4e}  (/N = {d['aux_over_N']:+.4f});  H/N = {d['H_chi_over_N']:+.4f} vs c_H {res['c_H']:+.4f};  X/N = {d['X_chi_over_N']:+.4f}")
        sp = d["split"]
        print(f"  W = RP/2 - J + Q:  RP/2 = {sp['RP_half']:.4e}  J = {sp['J']:.4e}  Q = {sp['Q']:.4e}  "
              f"(|Q| bound {sp['Q_bound']:.1e});  E4 residual {d['check_E4_W_minus_split']:.2e}")
        print(f"  J/N = {d['J_over_N']:+.3f}   J/(N log N) = {d['J_over_NlogN']:+.4f}   RP/(2N) = {d['RP_half_over_N']:+.3f}   "
              f"R(N) = {sp['R_N']:+.1f}  P(N) = {sp['P_N']:+.1f}")
    res["seconds_total"] = time.time() - t0
    Path(args.out).write_text(json.dumps(res, indent=1))
    print(f"\nwrote {args.out}  ({res['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
