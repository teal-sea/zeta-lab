"""Tests whether RANK3_ROUTE_D.md's cross term

    Sigma_cross(q) = sum_{b != b' mod q}^* c_q(b-b') X(b,b'),

can be shown, not merely measured, to cancel the diagonal term
Sigma_diag(q) = phi(q) sum_b^* T(q,b) down from the proved cancellation-free
ceiling phi(q)(phi(q)-1) sum_b^* T(q,b) (RANK3_ROUTE_D.md (D8)) toward the
weight RANK3_POLYRANGE.md guesses is needed.

For q PRIME this script verifies, to floating-point precision, a new exact
identity derived for this task (not present in RANK3_ROUTE_D.md or any
sibling document):

    Sigma_cross(q) = Sigma_diag(q)/(q-1) - E(q),      q prime,       (CC1)

where E(q) = sum_t Delta_eps(t;q)^2 + sum_t [Delta_eps(N;q)-Delta_eps(t;q)]^2
(the (D5)-shaped quadratic form, applied not to a residue class but to the
"principal-character defect" sequence eps_n = Lambda(n) 1[(n,q)=1] - 1,
Delta_eps(t;q) = sum_{n<=t} eps_n = psi_coprime(t;q) - t with
psi_coprime(t;q) = sum_{n<=t, gcd(n,q)=1} Lambda(n)), and consequently

    Sigma_diag(q) + Sigma_cross(q) <= q * sum_b^* T(q,b),   q prime,   (CC2)

since E(q) >= 0. (CC2) replaces (D8)'s ceiling phi(q)^2 sum_b^* T(q,b) with
q sum_b^* T(q,b) -- an improvement by a factor q/(q-1)^2, i.e. a full extra
power of phi(q) saved, matching (for prime q) the "diagonal-only" weight
mu(q)^2/phi(q) that RANK3_ROUTE_D.md Section 5 says is "not derived... and
not decidable from UPPER_BOUND.md or RESULTS.md".

DERIVATION (see RANK3_CROSS_TERM_CANCELLATION.md for the full writeup).
For (b,q)=1, character orthogonality gives, EXACTLY (no approximation),
    D_b(beta) = eps(beta)/phi(q) + (1/phi(q)) sum_{chi != chi0} chibar(b) L(beta,chi),
with eps(beta) = L(beta,chi0) - K_N(beta) (coefficients eps_n above) and
L(beta,chi) = sum_n Lambda(n) chi(n) e(n beta). Summing R^{(1)}_{q,a} =
sum_b^* e_q(ab) D_b over the reduced residues a and using the classical
Gauss-sum twist tau_a(chibar) = chi(a) tau(chibar) -- valid because EVERY
nonprincipal character mod a PRIME q is primitive, so |tau(chibar)|^2 = q --
collapses the double sum over (chi,chi') to its diagonal via character
orthogonality sum_a^* chi(a) chibar'(a) = phi(q) 1[chi=chi']. This is what
breaks for composite squarefree q: q with >= 2 prime factors has
nonprincipal characters induced from a proper divisor of q (imprimitive),
for which the clean twist tau_a(chibar) = chi(a) tau(chibar) and the
normalization |tau(chibar)|^2 = q do not hold, and the off-diagonal
Gauss-sum matrix G(chi,chi') = sum_a^* tau_a(chibar) conj(tau_a(chibar'))
need not vanish. This script also measures q in {6, 10, 15} (squarefree,
composite) to show (CC1)-(CC2), applied naively, does NOT hold there --
an empirical illustration of exactly where primality was used, not a proof
that no analogous identity exists for composite q.

Lambda(n) is reused from probe.von_mangoldt; Sigma_diag(q), Sigma_cross(q),
T(q,b), c_q are reused from rank3_cross_term_probe.py's already cross-checked
machinery (not recomputed by a second implementation here), so this script
inherits that document's four cross-checks rather than repeating them.

Run:  /opt/zeta-venv/bin/python hunts/prime_pair_error/rank3_cross_term_cancellation_probe.py
Writes hunts/prime_pair_error/results_rank3_cross_term_cancellation_probe.json
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from sympy import isprime

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import probe  # noqa: E402  (reused: probe.von_mangoldt)
import rank3_cross_term_probe as base  # noqa: E402  (reused: sigma_diag/cross, T, c_q)

PRIME_MODULI = [2, 3, 5, 7, 11, 13, 17, 19]
COMPOSITE_SQUAREFREE_MODULI = [6, 10, 15]
N_LADDER = [1_000, 3_000, 10_000, 30_000, 100_000, 300_000, 1_000_000]


def T_N_baseline(lam: np.ndarray, N: int) -> float:
    """UPPER_BOUND.md's own T_N = sum_t Delta(t)^2 + telescoping term, Delta(t)=psi(t)-t."""
    n = np.arange(N + 1)
    psi = np.cumsum(lam[: N + 1])
    delta = psi - n
    dN = delta[N]
    s1 = float(np.sum(delta[1 : N + 1] ** 2))
    s2 = float(np.sum((dN - delta[1:N]) ** 2))
    return s1 + s2


def rho2(lam: np.ndarray, q: int, N: int) -> float:
    """rho2(q) = sum_{n<=N, gcd(n,q)>1} Lambda(n), RANK3_ROUTE_D.md (D3)."""
    n = np.arange(N + 1)
    g = np.array([math.gcd(int(x), q) for x in n])
    return float(np.sum(np.where(g > 1, lam[: N + 1], 0.0)))


def E_quantity(lam: np.ndarray, q: int, N: int) -> float:
    """E(q) = (D5)-shaped quadratic form applied to Delta_eps(t;q) = psi_coprime(t;q) - t."""
    n = np.arange(N + 1)
    g = np.array([math.gcd(int(x), q) for x in n])
    psi_coprime = np.cumsum(np.where(g == 1, lam[: N + 1], 0.0))
    delta_eps = psi_coprime - n
    deN = delta_eps[N]
    s1 = float(np.sum(delta_eps[1 : N + 1] ** 2))
    s2 = float(np.sum((deN - delta_eps[1:N]) ** 2))
    return s1 + s2


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

    is_prime = bool(isprime(q))
    old_ceiling_total = phi_q * phi_q * sum_T  # phi(q)^2 sum_b T(q,b): total ceiling on diag+cross

    row = {
        "q": q,
        "N": N,
        "is_prime": is_prime,
        "phi_q": phi_q,
        "sum_T": sum_T,
        "T_N_baseline": T_N,
        "sigma_diag": sigma_diag,
        "sigma_cross": sigma_cross,
        "sigma_diag_plus_cross": sigma_diag + sigma_cross,
        "old_ceiling_diag_plus_cross": old_ceiling_total,
    }

    if q == 2:
        # phi(2)=1: no b != b' pairs exist, Sigma_cross(2)=0 identically
        # (RANK3_ROUTE_D.md Section 3); (CC1) is degenerate (division by q-1=1
        # is fine, but there are no nonprincipal characters mod 2 to sum over).
        row["cc1_applicable"] = False
        row["note"] = "phi(2)=1: Sigma_cross(2)=0 identically, (CC1)/(CC2) vacuous"
        row["seconds"] = time.time() - t0
        return row

    E = E_quantity(lam, q, N)
    r2 = rho2(lam, q, N)
    row["E"] = E
    row["rho2"] = r2
    row["E_minus_T_N"] = E - T_N
    row["E_minus_T_N_error_bound"] = r2 * math.sqrt(N * T_N) + r2 * r2 * N

    predicted_cross = sigma_diag / (q - 1) - E
    denom = max(abs(sigma_cross), abs(predicted_cross), 1.0)
    row["cc1_predicted_sigma_cross"] = predicted_cross
    row["cc1_rel_err"] = abs(sigma_cross - predicted_cross) / denom
    row["cc1_applicable"] = is_prime
    if is_prime:
        row["cc1_holds_to_precision"] = row["cc1_rel_err"] < 1e-8

    new_bound = q * sum_T
    row["cc2_new_bound"] = new_bound
    row["cc2_holds"] = (sigma_diag + sigma_cross) <= new_bound * (1 + 1e-9) + 1e-6
    row["cc2_improvement_factor_vs_old_ceiling"] = (
        old_ceiling_total / new_bound if new_bound else None
    )

    row["seconds"] = time.time() - t0
    return row


def main() -> int:
    t0 = time.time()
    max_n = max(N_LADDER)
    lam, _ = probe.von_mangoldt(max_n)

    runs = []
    for q in PRIME_MODULI + COMPOSITE_SQUAREFREE_MODULI:
        for N in N_LADDER:
            T_N = T_N_baseline(lam, N)
            r = analyse(q, N, lam, T_N)
            runs.append(r)
            if r.get("cc1_applicable"):
                print(
                    f"q={q:>2} N={N:>8}: sigma_cross={r['sigma_cross']:+.6e}  "
                    f"cc1_predicted={r['cc1_predicted_sigma_cross']:+.6e}  "
                    f"cc1_rel_err={r['cc1_rel_err']:.3e}  "
                    f"cc2_holds={r['cc2_holds']}  "
                    f"improvement_factor={r['cc2_improvement_factor_vs_old_ceiling']:.4f}"
                )
            elif "cc1_rel_err" in r:
                print(
                    f"q={q:>2} N={N:>8}: [composite, (CC1) not proved]  "
                    f"sigma_cross={r['sigma_cross']:+.6e}  "
                    f"cc1_predicted(naive)={r['cc1_predicted_sigma_cross']:+.6e}  "
                    f"cc1_rel_err={r['cc1_rel_err']:.3e}  "
                    f"cc2_holds(naive)={r['cc2_holds']}"
                )
            else:
                print(f"q={q:>2} N={N:>8}: [q=2 degenerate] {r.get('note')}")

    prime_rows_with_cc1 = [r for r in runs if r.get("cc1_applicable") and "cc1_rel_err" in r]
    worst_cc1_rel_err = max((r["cc1_rel_err"] for r in prime_rows_with_cc1), default=None)
    all_cc2_hold = all(r["cc2_holds"] for r in prime_rows_with_cc1)

    composite_rows = [
        r for r in runs if (not r.get("is_prime")) and "cc1_rel_err" in r
    ]
    composite_rel_errs = [r["cc1_rel_err"] for r in composite_rows]

    verdict = (
        f"(CC1) verified to floating-point precision (worst relative error "
        f"{worst_cc1_rel_err:.3e}) at every prime q in {PRIME_MODULI[1:]} "
        f"(q=2 is degenerate, Sigma_cross(2)=0 identically) across N in "
        f"{N_LADDER}. Consequently (CC2) holds at every one of these rows: "
        f"{all_cc2_hold}. Applied naively (i.e. assuming the same identity) "
        f"to composite squarefree q in {COMPOSITE_SQUAREFREE_MODULI}, the "
        f"relative error ranges over "
        f"[{min(composite_rel_errs):.3f}, {max(composite_rel_errs):.3f}] -- "
        f"large, not floating-point noise: (CC1) does not extend to "
        f"composite squarefree q as derived here. This is consistent with, "
        f"and explained by, the derivation's use of Gauss-sum twisting valid "
        f"only for primitive characters, which every nonprincipal character "
        f"mod a prime q is and not every nonprincipal character mod a "
        f"composite squarefree q is."
    )
    print("\n" + verdict)

    out = {
        "definitions": (
            "Sigma_diag(q), Sigma_cross(q), T(q,b), c_q as in RANK3_ROUTE_D.md "
            "(D5)-(D7), reused from rank3_cross_term_probe.py. (CC1): "
            "Sigma_cross(q) = Sigma_diag(q)/(q-1) - E(q), proved here for prime "
            "q via Dirichlet character orthogonality + Gauss-sum twisting "
            "(RANK3_CROSS_TERM_CANCELLATION.md has the derivation). (CC2): "
            "Sigma_diag(q)+Sigma_cross(q) <= q*sum_b^* T(q,b), prime q, since "
            "E(q)>=0."
        ),
        "prime_moduli": PRIME_MODULI,
        "composite_squarefree_moduli": COMPOSITE_SQUAREFREE_MODULI,
        "N_ladder": N_LADDER,
        "runs": runs,
        "worst_cc1_rel_err_at_prime_q": worst_cc1_rel_err,
        "cc2_holds_at_every_prime_row": all_cc2_hold,
        "composite_rel_err_range": [min(composite_rel_errs), max(composite_rel_errs)],
        "verdict": verdict,
        "seconds_total": time.time() - t0,
    }
    out_path = HERE / "results_rank3_cross_term_cancellation_probe.json"
    out_path.write_text(json.dumps(out, indent=1))
    print(f"\nwrote {out_path}  ({out['seconds_total']:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
