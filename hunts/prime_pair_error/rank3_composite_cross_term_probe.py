"""Extends RANK3_CROSS_TERM_CANCELLATION.md's identity (CC1)-(CC2) from prime
q to composite SQUAREFREE q, by evaluating the off-diagonal Gauss-sum matrix

    G(chi,chi') = sum_{a mod q}^* tau_a(chibar) * conj(tau_a(chibar')),
    tau_a(chibar) = sum_{b mod q}^* chibar(b) e(ab/q),

for EVERY pair of nonprincipal Dirichlet characters chi, chi' mod q
(imprimitive ones included), not just primitive ones. RANK3_CROSS_TERM_
CANCELLATION.md Section 3 uses primality only to get the primitive-character
twist tau_a(chibar) = chi(a) tau(chibar), |tau(chibar)|^2 = q, for EVERY
nonprincipal chi mod a prime q (automatic there since every nonprincipal
character mod a prime is primitive). This script shows, and numerically
verifies, that:

  (1) The twist identity tau_a(chibar) = chi(a) tau(chibar) itself needs NO
      primitivity: it holds for every character chi mod q (principal or
      not, primitive or not) and every a with gcd(a,q)=1, because b -> ab
      is a bijection of Z/qZ whenever gcd(a,q)=1 and chi is completely
      multiplicative (chi(ab) = chi(a)chi(b), both sides 0 together when
      gcd(b,q)>1). Consequently G(chi,chi') = tau(chibar)conj(tau(chibar'))
      * sum_a^* chi(a)chibar'(a) = phi(q) tau(chibar)conj(tau(chibar')) *
      1[chi=chi'] by plain character orthogonality over a -- valid for
      EVERY q, prime or composite, and needs nothing about primitivity or
      squarefreeness either. G(chi,chi') = 0 off the diagonal, unconditionally.

  (2) What DOES depend on primitivity is the DIAGONAL value |tau(chibar)|^2.
      For chi mod q induced by a primitive character chi* mod q* (conductor
      q*), d := q/q*, and q SQUAREFREE (so gcd(d,q*)=1 automatically, every
      divisor pair of a squarefree modulus is coprime), the classical
      reduction of an imprimitive Gauss sum to the primitive one inducing it
      is tau(chi) = mu(d) chi*(d) tau(chi*), hence |tau(chi)|^2 = q* (the
      conductor), not q. So G(chi,chi) = phi(q) * conductor(chi) -- equal to
      phi(q)*q only when chi is itself primitive mod q (conductor = q,
      e.g. always true for prime q); strictly smaller when chi is
      imprimitive, which happens only for composite q.

This is the resolution of RANK3_CROSS_TERM_CANCELLATION.md Section 4's wall:
its identity (CC1) implicitly assumed |tau(chibar)|^2 = q for every
nonprincipal chi -- true only when every such chi is primitive, i.e. only
for prime q. Point (1) shows the off-diagonal vanishing that (CC1) actually
needs survives unconditionally; point (2) shows the diagonal normalization
that fails is repairable by replacing q with conductor(chi) character-by-
character. This script derives the resulting exact identity for Sigma_cross(q)
at composite squarefree q (RANK3_COMPOSITE_CROSS_TERM.md has the full
derivation) and verifies it, together with a fully independent brute-force
computation of G(chi,chi') straight from its definition (no Gauss-sum
formula assumed), against the existing ground-truth machinery.

Lambda(n) is reused from probe.von_mangoldt; Sigma_diag(q), Sigma_cross(q),
T(q,b), c_q, reduced_residues, delta_table, T_and_X are reused from
rank3_cross_term_probe.py (not reimplemented); E(q) is reused from
rank3_cross_term_cancellation_probe.py (not reimplemented). The only new
machinery here is character enumeration mod q (via CRT of cyclic characters
at each prime factor) and the M_chi / G(chi,chi') computations, which have
no counterpart in either sibling script.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_composite_cross_term_probe.py
Writes hunts/prime_pair_error/results_rank3_composite_cross_term_probe.json
"""
from __future__ import annotations

import itertools
import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from sympy import mobius

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import probe  # noqa: E402  (reused: probe.von_mangoldt)
import rank3_cross_term_probe as base  # noqa: E402  (reused: reduced_residues, delta_table, T_and_X, ramanujan_sum_direct)
import rank3_cross_term_cancellation_probe as cc  # noqa: E402  (reused: E_quantity, T_N_baseline)

MODULI = [6, 10, 14, 15, 21]
N_LADDER = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]


# ---------------------------------------------------------------------------
# Character enumeration mod q, q squarefree: CRT product of cyclic characters
# at each prime factor.
# ---------------------------------------------------------------------------

def factor_squarefree(q: int) -> list[int]:
    factors = []
    m = q
    p = 2
    while p * p <= m:
        if m % p == 0:
            factors.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        factors.append(m)
    return factors


def primitive_root_small(p: int) -> int:
    if p == 2:
        return 1
    for g in range(2, p):
        seen = set()
        x = 1
        for _ in range(p - 1):
            x = (x * g) % p
            seen.add(x)
        if len(seen) == p - 1:
            return g
    raise ValueError(f"no primitive root found for p={p}")


def dlog_table(p: int, g: int) -> dict[int, int]:
    table = {}
    x = 1
    for k in range(p - 1):
        table[x] = k
        x = (x * g) % p
    return table


def enumerate_characters(q: int):
    """Returns (factors, dlogs, orders, chars): chars is a list of dicts
    {'j': tuple, 'conductor': int}, one per character mod q (principal
    included, at j = (0,...,0), conductor 1)."""
    factors = factor_squarefree(q)
    roots = [primitive_root_small(p) for p in factors]
    dlogs = [dlog_table(p, g) for p, g in zip(factors, roots)]
    orders = [p - 1 for p in factors]
    chars = []
    for idx in itertools.product(*[range(o) for o in orders]):
        conductor = 1
        for j, p in zip(idx, factors):
            if j != 0:
                conductor *= p
        chars.append({"j": idx, "conductor": conductor})
    return factors, dlogs, orders, chars


def character_values(n_arr: np.ndarray, q: int, factors: list[int], dlogs: list[dict], j_tuple: tuple) -> np.ndarray:
    """chi(n) for n in n_arr, chi indexed by j_tuple. chi(n)=0 whenever
    gcd(n,q)>1 (checked against EVERY prime factor, not just the ones with
    j_i != 0 -- an induced character still vanishes off the full modulus
    q's reduced residues, even along the factor(s) it is trivial at)."""
    phase = np.zeros(len(n_arr), dtype=np.float64)
    valid = np.ones(len(n_arr), dtype=bool)
    for p, dlog, j in zip(factors, dlogs, j_tuple):
        r = n_arr % p
        valid &= r != 0
        if j != 0:
            lut = np.zeros(p, dtype=np.int64)
            for res, k in dlog.items():
                lut[res] = k
            k_arr = lut[np.where(r == 0, 1, r)]  # placeholder for r=0, masked out by `valid` anyway
            phase = phase + j * k_arr.astype(np.float64) / (p - 1)
    chi = np.where(valid, np.exp(2j * np.pi * phase), 0.0 + 0.0j)
    return chi


# ---------------------------------------------------------------------------
# M_chi = integral |K_N L(chi)|^2, the (D5)-shaped Parseval formula applied
# to the complex partial sums S_chi(t) = sum_{n<=t} Lambda(n) chi(n).
# ---------------------------------------------------------------------------

def M_chi(lam: np.ndarray, q: int, factors: list[int], dlogs: list[dict], j_tuple: tuple, N: int) -> tuple[float, np.ndarray]:
    n = np.arange(N + 1)
    chi_vals = character_values(n, q, factors, dlogs, j_tuple)
    s = np.cumsum(lam[: N + 1] * chi_vals)
    sN = s[N]
    s1 = float(np.sum(np.abs(s[1 : N + 1]) ** 2))
    s2 = float(np.sum(np.abs(sN - s[1:N]) ** 2))
    return s1 + s2, s


def M_chi_via_convolution(lam: np.ndarray, q: int, factors: list[int], dlogs: list[dict], j_tuple: tuple, N: int) -> float:
    """Independent second method: explicit convolution of Lambda(n)chi(n)
    with the constant sequence 1 on 1..N, sum of squared magnitudes of the
    resulting coefficients (same convolution RANK3_ROUTE_D.md Section 2 and
    rank3_cross_term_probe.T_via_convolution use, generalized to complex
    coefficients)."""
    n = np.arange(1, N + 1)
    chi_vals = character_values(n, q, factors, dlogs, j_tuple)
    seq = lam[1 : N + 1] * chi_vals
    conv = np.convolve(seq, np.ones(N))
    return float(np.sum(np.abs(conv) ** 2))


# ---------------------------------------------------------------------------
# Direct, brute-force G(chi,chi') from its definition -- no Gauss-sum formula
# assumed, an independent check of the theoretical claim.
# ---------------------------------------------------------------------------

def tau_a_table(q: int, factors: list[int], dlogs: list[dict], chars: list[dict]) -> np.ndarray:
    """tau_a(chibar) for every reduced residue a and every character chi in
    `chars`, computed directly as sum_{b mod q}^* chibar(b) e(ab/q)."""
    residues = np.array(base.reduced_residues(q), dtype=np.int64)
    nchars = len(chars)
    na = len(residues)
    out = np.zeros((nchars, na), dtype=complex)
    for ci, ch in enumerate(chars):
        chi_b = character_values(residues, q, factors, dlogs, ch["j"])
        chibar_b = np.conj(chi_b)
        for ai, a in enumerate(residues):
            phase = np.exp(2j * np.pi * a * residues / q)
            out[ci, ai] = np.sum(chibar_b * phase)
    return out, residues


def G_matrix_direct(q: int, factors: list[int], dlogs: list[dict], chars: list[dict]) -> np.ndarray:
    tau, residues = tau_a_table(q, factors, dlogs, chars)
    # G[i,j] = sum_a tau[i,a] * conj(tau[j,a])
    G = tau @ np.conj(tau).T
    return G


# ---------------------------------------------------------------------------
# Main per-(q,N) analysis
# ---------------------------------------------------------------------------

def analyse(q: int, N: int, lam: np.ndarray, T_N: float) -> dict:
    t0 = time.time()
    residues = base.reduced_residues(q)
    phi_q = len(residues)
    delta = base.delta_table(lam, q, N)
    T, X = base.T_and_X(delta, N)
    sum_T = sum(T.values())
    sigma_diag = phi_q * sum_T
    sigma_cross = 0.0
    for (b, bp), val in X.items():
        c = base.ramanujan_sum_direct(q, b - bp)
        sigma_cross += c * val

    factors, dlogs, orders, chars = enumerate_characters(q)
    nonprincipal = [ch for ch in chars if ch["conductor"] > 1]

    sum_M = 0.0
    W = 0.0
    for ch in nonprincipal:
        m_val, _ = M_chi(lam, q, factors, dlogs, ch["j"], N)
        sum_M += m_val
        W += (q - ch["conductor"]) * m_val

    E = cc.E_quantity(lam, q, N)

    cc1p_predicted_sigma_diag = E + sum_M  # (CC1'), general q, no primality used
    predicted_sigma_cross = ((q - phi_q) * sigma_diag - (q - 1) * E - W) / phi_q

    denom_cross = max(abs(sigma_cross), abs(predicted_sigma_cross), 1.0)
    denom_diag = max(abs(sigma_diag), abs(cc1p_predicted_sigma_diag), 1.0)

    new_bound = q * sum_T
    old_ceiling = phi_q * phi_q * sum_T

    row = {
        "q": q,
        "N": N,
        "phi_q": phi_q,
        "num_characters": len(chars),
        "num_nonprincipal": len(nonprincipal),
        "conductors": sorted(ch["conductor"] for ch in nonprincipal),
        "sum_T": sum_T,
        "T_N_baseline": T_N,
        "sigma_diag": sigma_diag,
        "sigma_cross": sigma_cross,
        "sigma_diag_plus_cross": sigma_diag + sigma_cross,
        "E": E,
        "sum_M_chi": sum_M,
        "W": W,
        "cc1prime_predicted_sigma_diag": cc1p_predicted_sigma_diag,
        "cc1prime_rel_err": abs(sigma_diag - cc1p_predicted_sigma_diag) / denom_diag,
        "predicted_sigma_cross_new_identity": predicted_sigma_cross,
        "new_identity_rel_err": abs(sigma_cross - predicted_sigma_cross) / denom_cross,
        "cc2gen_new_bound": new_bound,
        "cc2gen_holds": (sigma_diag + sigma_cross) <= new_bound * (1 + 1e-9) + 1e-6,
        "old_ceiling_diag_plus_cross": old_ceiling,
        "cc2gen_improvement_factor_vs_old_ceiling": old_ceiling / new_bound if new_bound else None,
        "seconds": time.time() - t0,
    }
    return row


def G_check(q: int) -> dict:
    """Independent brute-force check: G(chi,chi') computed straight from its
    definition, compared to the theoretical phi(q)*conductor(chi)*1[chi=chi']."""
    factors, dlogs, orders, chars = enumerate_characters(q)
    nonprincipal = [ch for ch in chars if ch["conductor"] > 1]
    phi_q = len(base.reduced_residues(q))
    G = G_matrix_direct(q, factors, dlogs, nonprincipal)
    n = len(nonprincipal)
    off_diag_max_abs = 0.0
    for i in range(n):
        for j in range(n):
            if i != j:
                off_diag_max_abs = max(off_diag_max_abs, abs(G[i, j]))
    diag_rel_err = 0.0
    diag_values = []
    for i, ch in enumerate(nonprincipal):
        predicted = phi_q * ch["conductor"]
        measured = G[i, i].real
        diag_values.append({"j": ch["j"], "conductor": ch["conductor"], "measured": measured, "predicted": predicted})
        if abs(G[i, i].imag) > 1e-6 * max(1.0, abs(measured)):
            diag_rel_err = max(diag_rel_err, 1.0)  # flag: diagonal should be real
        denom = max(abs(measured), abs(predicted), 1.0)
        diag_rel_err = max(diag_rel_err, abs(measured - predicted) / denom)
    return {
        "q": q,
        "phi_q": phi_q,
        "num_nonprincipal": n,
        "off_diag_max_abs_G": off_diag_max_abs,
        "diag_rel_err_max": diag_rel_err,
        "diag_values": diag_values,
    }


def M_chi_convolution_check(lam: np.ndarray) -> dict:
    """One small (q,N) cross-check of M_chi's partial-sum formula against
    explicit convolution, at q=6 (the smallest composite squarefree modulus
    here), N=500, for its one nonprincipal character."""
    q, N = 6, 500
    factors, dlogs, orders, chars = enumerate_characters(q)
    nonprincipal = [ch for ch in chars if ch["conductor"] > 1]
    ch = nonprincipal[0]
    m_formula, _ = M_chi(lam, q, factors, dlogs, ch["j"], N)
    m_conv = M_chi_via_convolution(lam, q, factors, dlogs, ch["j"], N)
    return {
        "q": q,
        "N": N,
        "conductor": ch["conductor"],
        "M_chi_partial_sum_formula": m_formula,
        "M_chi_convolution": m_conv,
        "abs_diff": abs(m_formula - m_conv),
    }


def main() -> int:
    t0 = time.time()
    max_n = max(N_LADDER)
    lam, _ = probe.von_mangoldt(max_n)

    print("Direct (brute-force, no Gauss-sum formula) check of G(chi,chi'):")
    g_checks = {}
    for q in MODULI:
        gc = G_check(q)
        g_checks[str(q)] = gc
        print(
            f"  q={q:>2}: phi(q)={gc['phi_q']:>2}  nonprincipal={gc['num_nonprincipal']:>2}  "
            f"max|off-diag G|={gc['off_diag_max_abs_G']:.3e}  "
            f"diag rel err (vs phi(q)*conductor)={gc['diag_rel_err_max']:.3e}"
        )

    conv_check = M_chi_convolution_check(lam)
    print(f"\nM_chi convolution cross-check: {json.dumps(conv_check, indent=1)}")

    print("\nPer-(q,N) identity checks:")
    runs = []
    for q in MODULI:
        for N in N_LADDER:
            T_N = cc.T_N_baseline(lam, N)
            r = analyse(q, N, lam, T_N)
            runs.append(r)
            print(
                f"q={q:>2} N={N:>8}: sigma_cross={r['sigma_cross']:+.6e}  "
                f"predicted={r['predicted_sigma_cross_new_identity']:+.6e}  "
                f"rel_err={r['new_identity_rel_err']:.3e}  "
                f"cc1prime_rel_err={r['cc1prime_rel_err']:.3e}  "
                f"cc2gen_holds={r['cc2gen_holds']}  "
                f"improvement={r['cc2gen_improvement_factor_vs_old_ceiling']:.4f}"
            )

    worst_new_identity_rel_err = max(r["new_identity_rel_err"] for r in runs)
    worst_cc1prime_rel_err = max(r["cc1prime_rel_err"] for r in runs)
    all_cc2gen_hold = all(r["cc2gen_holds"] for r in runs)
    worst_g_diag_err = max(g["diag_rel_err_max"] for g in g_checks.values())
    worst_g_offdiag = max(g["off_diag_max_abs_G"] for g in g_checks.values())

    verdict = (
        f"Brute-force G(chi,chi') (no Gauss-sum formula assumed): off-diagonal "
        f"max |G| = {worst_g_offdiag:.3e} across q in {MODULI} (should be 0); "
        f"diagonal G(chi,chi) matches phi(q)*conductor(chi) to worst relative "
        f"error {worst_g_diag_err:.3e}. The generalized identity (CC1'), "
        f"Sigma_diag(q) = E(q) + sum_chi M_chi, holds at worst relative error "
        f"{worst_cc1prime_rel_err:.3e} across every (q,N) tested (q composite "
        f"squarefree, no primality used in its derivation). The new exact "
        f"identity for Sigma_cross(q) -- (q-phi(q))Sigma_diag(q)/phi(q) - "
        f"(q-1)E(q)/phi(q) - W(q)/phi(q), W(q) = sum_chi (q-conductor(chi))M_chi "
        f"-- holds at worst relative error {worst_new_identity_rel_err:.3e} "
        f"across every (q,N) in {MODULI} x {N_LADDER}. The resulting bound "
        f"Sigma_diag(q)+Sigma_cross(q) <= q*sum_b^* T(q,b) holds at every row: "
        f"{all_cc2gen_hold} -- the SAME ceiling (CC2) proves for prime q, now "
        f"unconditional for every squarefree q."
    )
    print("\n" + verdict)

    out = {
        "definitions": (
            "G(chi,chi') = sum_a^* tau_a(chibar) conj(tau_a(chibar')), "
            "tau_a(chibar) = sum_b^* chibar(b) e(ab/q). Theory: G(chi,chi')=0 "
            "for chi!=chi' (any q, no primitivity needed -- tau_a(chibar)="
            "chi(a)tau(chibar) holds whenever gcd(a,q)=1, by the bijection "
            "b->ab on Z/qZ, then character orthogonality over a). "
            "G(chi,chi)=phi(q)*conductor(chi) (needs q squarefree, via the "
            "classical imprimitive-Gauss-sum reduction tau(chi)=mu(d)chi*(d)"
            "tau(chi*), d=q/conductor(chi)). New identity: Sigma_cross(q) = "
            "[(q-phi(q))Sigma_diag(q) - (q-1)E(q) - W(q)] / phi(q), "
            "W(q) = sum_{chi!=chi0}(q-conductor(chi))M_chi >= 0, "
            "M_chi = sum_t|S_chi(t)|^2 + sum_t|S_chi(N)-S_chi(t)|^2, "
            "S_chi(t) = sum_{n<=t} Lambda(n)chi(n). Reduces to (CC1) at q "
            "prime (conductor(chi)=q for every nonprincipal chi there, so "
            "W(q)=0 identically)."
        ),
        "moduli": MODULI,
        "N_ladder": N_LADDER,
        "G_direct_checks": g_checks,
        "M_chi_convolution_check": conv_check,
        "runs": runs,
        "worst_new_identity_rel_err": worst_new_identity_rel_err,
        "worst_cc1prime_rel_err": worst_cc1prime_rel_err,
        "all_cc2gen_hold": all_cc2gen_hold,
        "worst_g_diag_rel_err": worst_g_diag_err,
        "worst_g_offdiag_abs": worst_g_offdiag,
        "verdict": verdict,
        "seconds_total": time.time() - t0,
    }
    out_path = HERE / "results_rank3_composite_cross_term_probe.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}  ({out['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
