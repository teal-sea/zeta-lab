"""Measures RANK3_ROUTE_D.md's exact cross term

    Sigma_cross(q) = sum_{b != b' mod q}^* c_q(b-b') X(b,b'),

(D7)'s boxed identity, at a ladder of moduli q and cutoffs N, against the
diagonal term Sigma_diag(q) = phi(q) sum_b^* T(q,b) and against the
cancellation-free ceiling phi(q)(phi(q)-1) sum_b^* T(q,b) that
RANK3_ROUTE_D.md Section 3 proves but does not resolve. Both b, b' range
over the phi(q) reduced residues mod q (the star). Definitions, exactly as
in RANK3_ROUTE_D.md Sections 1-3 and UPPER_BOUND.md Section 2:

    Delta(t;q,b) = psi(t;q,b) - t/phi(q),
    psi(t;q,b)   = sum_{n<=t, n = b (q)} Lambda(n),
    T(q,b)       = sum_{t=1}^N Delta(t;q,b)^2
                   + sum_{t=1}^{N-1} [Delta(N;q,b)-Delta(t;q,b)]^2,
    X(b,b')      = sum_{t=1}^N Delta(t;q,b)Delta(t;q,b')
                   + sum_{t=1}^{N-1} [Delta(N;q,b)-Delta(t;q,b)][Delta(N;q,b')-Delta(t;q,b')],
    c_q(k)       = sum_{1<=a<=q, (a,q)=1} exp(2 pi i a k / q)   (Ramanujan sum).

RANK3_ROUTE_D.md Section 3 states plainly that whether Sigma_cross(q) sits
near 0 (consistent with treating it as negligible) or near its
Cauchy-Schwarz ceiling phi(q)(phi(q)-1) sum_b T(q,b) (D8) "is not
determined by UPPER_BOUND.md or RESULTS.md -- both are consistent with the
exact identity (D7)". This script measures the actual ratio, it does not
derive a new bound.

Lambda(n) is reused from probe.von_mangoldt (the smallest-prime-factor
sieve already in this hunt), the same function residue.py builds on, and
cross-checked here against an independent direct-enumeration computation
(sympy.primerange over prime powers), the same second method
rank3_bdh_probe.py and rank3_fourth_moment_probe.py use. c_q(k) is computed
from its defining exponential sum and cross-checked against the classical
closed form c_q(k) = mu(q/g) phi(q) / phi(q/g), g = gcd(q,k) (Mobius via
sympy). T(q,b) is additionally cross-checked, at one small (q,N), against
an independent computation built from an explicit finite convolution of
d_b(n) = Lambda(n) 1[n=b(q)] - 1/phi(q) with the constant sequence 1 on
1..N (the same convolution RANK3_ROUTE_D.md Section 2 sets up before
reading off the partial-sum formula (D5)), rather than trusting the
partial-sum formula alone.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_cross_term_probe.py
Writes hunts/prime_pair_error/results_rank3_cross_term_probe.json
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from sympy import mobius, primerange, totient

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import probe  # noqa: E402  (reused: probe.von_mangoldt)

MODULI = [2, 3, 5, 6, 7, 10, 11, 13]
N_LADDER = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]


def reduced_residues(q: int) -> list[int]:
    return [b for b in range(q) if math.gcd(b, q) == 1]


def von_mangoldt_reference(n_max: int) -> np.ndarray:
    """Independent second method for Lambda: direct enumeration of prime
    powers via sympy.primerange, as rank3_bdh_probe.py and
    rank3_fourth_moment_probe.py already do in this hunt."""
    lam = np.zeros(n_max + 1, dtype=np.float64)
    for p in primerange(2, n_max + 1):
        logp = math.log(p)
        pk = p
        while pk <= n_max:
            lam[pk] = logp
            pk *= p
    return lam


def ramanujan_sum_direct(q: int, k: int) -> float:
    """c_q(k) from its defining exponential sum (UPPER_BOUND.md Section 2)."""
    if q == 1:
        return 1.0
    a = np.array(reduced_residues(q), dtype=np.float64)
    return float(np.sum(np.cos(2.0 * np.pi * a * (k % q) / q)))


def ramanujan_sum_classical(q: int, k: int) -> float:
    """Classical closed form, the second method: c_q(k) = mu(q/g) phi(q)/phi(q/g),
    g = gcd(q, k)."""
    g = math.gcd(q, k)
    m = q // g
    return float(mobius(m) * totient(q) / totient(m))


def delta_table(lam: np.ndarray, q: int, N: int) -> dict[int, np.ndarray]:
    """Delta(t;q,b) for t = 0..N, one array per reduced residue b."""
    residues = reduced_residues(q)
    phi_q = len(residues)
    n = np.arange(N + 1)
    nmod = n % q
    t = n.astype(np.float64)
    out = {}
    for b in residues:
        mask = nmod == b
        psi = np.cumsum(np.where(mask, lam[: N + 1], 0.0))
        out[b] = psi - t / phi_q
    return out


def T_and_X(delta: dict[int, np.ndarray], N: int) -> tuple[dict[int, float], dict[tuple[int, int], float]]:
    residues = sorted(delta)
    T: dict[int, float] = {}
    for b in residues:
        D = delta[b]
        DN = D[N]
        s1 = float(np.sum(D[1 : N + 1] ** 2))
        s2 = float(np.sum((DN - D[1:N]) ** 2))
        T[b] = s1 + s2
    X: dict[tuple[int, int], float] = {}
    for b in residues:
        Db = delta[b]
        DbN = Db[N]
        for bp in residues:
            if bp == b:
                continue
            Dbp = delta[bp]
            s1 = float(np.sum(Db[1 : N + 1] * Dbp[1 : N + 1]))
            s2 = float(np.sum((DbN - Db[1:N]) * (Dbp[N] - Dbp[1:N])))
            X[(b, bp)] = s1 + s2
    return T, X


def T_via_convolution(lam: np.ndarray, q: int, b: int, N: int) -> float:
    """Independent second method for T(q,b): build d_b(n) on 1..N, convolve
    with the constant sequence 1 on 1..N (K_N's coefficients), and take the
    sum of squares of the resulting coefficients -- Parseval on the
    explicit finite trigonometric polynomial, the same object
    RANK3_ROUTE_D.md Section 2 convolves before reading off (D5). This does
    not reuse the partial-sum formula at all, it recomputes from the
    convolution definition."""
    phi_q = len(reduced_residues(q))
    n = np.arange(1, N + 1)
    d_b = np.where((n % q) == b, lam[1 : N + 1], 0.0) - 1.0 / phi_q
    conv = np.convolve(d_b, np.ones(N))  # coefficients at m = 2 .. 2N
    return float(np.sum(conv ** 2))


def analyse(q: int, N: int, lam: np.ndarray) -> dict:
    t0 = time.time()
    residues = reduced_residues(q)
    phi_q = len(residues)
    delta = delta_table(lam, q, N)
    T, X = T_and_X(delta, N)
    sum_T = sum(T.values())
    sigma_diag = phi_q * sum_T
    ceiling = phi_q * (phi_q - 1) * sum_T
    sigma_cross = 0.0
    max_cauchy_schwarz_violation = 0.0
    for (b, bp), val in X.items():
        k = b - bp
        c = ramanujan_sum_direct(q, k)
        sigma_cross += c * val
        bound = math.sqrt(T[b] * T[bp])
        max_cauchy_schwarz_violation = max(max_cauchy_schwarz_violation, abs(val) - bound)
    return {
        "q": q,
        "N": N,
        "phi_q": phi_q,
        "sum_T": sum_T,
        "sigma_diag_phi_times_sumT": sigma_diag,
        "sigma_cross": sigma_cross,
        "ceiling_cancellation_free": ceiling,
        "ratio_cross_over_diag": (sigma_cross / sigma_diag) if sigma_diag else None,
        "ratio_cross_over_ceiling": (sigma_cross / ceiling) if ceiling else None,
        "max_cauchy_schwarz_violation": max_cauchy_schwarz_violation,
        "seconds": time.time() - t0,
    }


def cross_checks(lam_sieve: np.ndarray, max_n_check: int) -> dict:
    lam_ref = von_mangoldt_reference(max_n_check)
    lam_diff = float(np.max(np.abs(lam_sieve[: max_n_check + 1] - lam_ref)))

    ram_diff = 0.0
    for q in MODULI:
        for k in range(-q, q + 1):
            d = ramanujan_sum_direct(q, k) - ramanujan_sum_classical(q, k)
            ram_diff = max(ram_diff, abs(d))

    conv_diff = 0.0
    q_small, N_small = 3, 500
    for b in reduced_residues(q_small):
        delta = delta_table(lam_sieve, q_small, N_small)
        T_formula, _ = T_and_X(delta, N_small)
        T_conv = T_via_convolution(lam_sieve, q_small, b, N_small)
        conv_diff = max(conv_diff, abs(T_formula[b] - T_conv))

    return {
        "lambda_sieve_vs_direct_enumeration_maxabsdiff": lam_diff,
        "lambda_checked_up_to": max_n_check,
        "ramanujan_sum_direct_vs_classical_maxabsdiff": ram_diff,
        "T_partial_sum_formula_vs_convolution_maxabsdiff": conv_diff,
        "T_convolution_check_q": q_small,
        "T_convolution_check_N": N_small,
    }


def summarize(runs: list[dict]) -> dict:
    """Per-q summary of where the measured ratio sits between 0 (diagonal-only
    weight mu(q)^2/phi(q)) and 1 (cancellation-free weight mu(q)^2)."""
    by_q: dict[int, list[dict]] = {}
    for r in runs:
        by_q.setdefault(r["q"], []).append(r)
    per_q = {}
    for q, rows in by_q.items():
        ratios_diag = [r["ratio_cross_over_diag"] for r in rows if r["ratio_cross_over_diag"] is not None]
        ratios_ceil = [r["ratio_cross_over_ceiling"] for r in rows if r["ratio_cross_over_ceiling"] is not None]
        per_q[str(q)] = {
            "ratio_cross_over_diag_by_N": {str(r["N"]): r["ratio_cross_over_diag"] for r in rows},
            "ratio_cross_over_ceiling_by_N": {str(r["N"]): r["ratio_cross_over_ceiling"] for r in rows},
            "min_ratio_cross_over_ceiling": min(ratios_ceil) if ratios_ceil else None,
            "max_ratio_cross_over_ceiling": max(ratios_ceil) if ratios_ceil else None,
        }
    all_ceil_ratios = [r["ratio_cross_over_ceiling"] for r in runs if r["ratio_cross_over_ceiling"] is not None]
    verdict = None
    if all_ceil_ratios:
        lo, hi = min(all_ceil_ratios), max(all_ceil_ratios)
        if hi < 0.5:
            verdict = (
                f"Across every measured (q,N), Sigma_cross(q)/ceiling stays in "
                f"[{lo:.4f}, {hi:.4f}], well under 1/2 and generally far under 1: "
                f"at these q and N, Sigma_cross(q) sits much closer to the "
                f"diagonal-consistent-with-negligible end of the range than to "
                f"its proved cancellation-free ceiling. This is a finite "
                f"measurement, not an asymptotic statement; it does not settle "
                f"whether the ratio stays bounded away from 1 as q, N grow."
            )
        elif lo > 0.5:
            verdict = (
                f"Across every measured (q,N), Sigma_cross(q)/ceiling stays in "
                f"[{lo:.4f}, {hi:.4f}], above 1/2: at these q and N, Sigma_cross(q) "
                f"sits closer to its proved cancellation-free ceiling than to zero. "
                f"This is a finite measurement, not an asymptotic statement; it "
                f"does not settle the behavior as q, N grow."
            )
        else:
            verdict = (
                f"Sigma_cross(q)/ceiling ranges over [{lo:.4f}, {hi:.4f}] across the "
                f"measured (q,N), straddling 1/2: neither the near-0 nor the "
                f"near-ceiling picture holds uniformly at this scale. This is a "
                f"finite measurement, not an asymptotic statement."
            )
    return {"per_q": per_q, "overall_ratio_cross_over_ceiling_range": [min(all_ceil_ratios), max(all_ceil_ratios)] if all_ceil_ratios else None,
            "verdict": verdict}


def main() -> int:
    t0 = time.time()
    max_n = max(N_LADDER)
    lam, _ = probe.von_mangoldt(max_n)
    checks = cross_checks(lam, max_n_check=min(max_n, 50_000))
    print("cross-checks:", json.dumps(checks, indent=1))

    runs = []
    for q in MODULI:
        for N in N_LADDER:
            r = analyse(q, N, lam)
            runs.append(r)
            rd = "n/a" if r["ratio_cross_over_diag"] is None else f"{r['ratio_cross_over_diag']:+.5f}"
            rc = "n/a" if r["ratio_cross_over_ceiling"] is None else f"{r['ratio_cross_over_ceiling']:+.5f}"
            print(
                f"q={q:>2} N={N:>8}: sigma_cross={r['sigma_cross']:+.6e}  "
                f"diag={r['sigma_diag_phi_times_sumT']:.6e}  ceiling={r['ceiling_cancellation_free']:.6e}  "
                f"ratio/diag={rd}  ratio/ceiling={rc}"
            )

    summary = summarize(runs)
    print("\n" + (summary["verdict"] or "no verdict computed"))

    out = {
        "definition": (
            "Sigma_cross(q) = sum_{b != b' mod q}^* c_q(b-b') X(b,b'), "
            "RANK3_ROUTE_D.md equation (D7); ratio_cross_over_diag is "
            "Sigma_cross(q) / (phi(q) sum_b^* T(q,b)), the quantity the task "
            "asks for; ratio_cross_over_ceiling is Sigma_cross(q) divided by "
            "the proved cancellation-free ceiling "
            "phi(q)(phi(q)-1) sum_b^* T(q,b) from RANK3_ROUTE_D.md Section 3."
        ),
        "moduli": MODULI,
        "N_ladder": N_LADDER,
        "cross_checks": checks,
        "runs": runs,
        "summary": summary,
        "seconds_total": time.time() - t0,
    }
    out_path = HERE / "results_rank3_cross_term_probe.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}  ({out['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
