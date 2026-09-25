"""Analysis of tail bounds and defect quantification for Davenport-Heilbronn truncated Weil form.

Replaces the heuristic float mean-density model of dhneg_localize.py with an explicit
derivation and documents why a conservative tail bound remains ATTEMPT_UNRESOLVED.

Mathematical basis and integration-by-parts derivation:
1. For real r, the test function is identically g_v(r) = (1/L) * |F_v(r)|^2 >= 0.
2. For r >= T > omega_N (with omega_N = 2*pi*N/L), the entire function
   F_v(r) = 2 sin(r L / 2) [ v_0/r + sum_{k=1}^N sqrt(2) v_k r / (r^2 - omega_k^2) ]
   has no poles on [T, infty). Expanding in multipole powers r^{-(2m+1)} gives:
       F_v(r) = 2 sin(r L / 2) [ sum_{m=0}^{M-1} mu_{2m} / r^{2m+1} + R_{2M}(r) ]
   where mu_{2m} = v_0 * delta_{m,0} + sum_{k=1}^N sqrt(2) v_k omega_k^{2m}
   and |R_{2M}(r)| <= C_{2M} / [ r^{2M-1} (r^2 - omega_N^2) ]
   with C_{2M} = sum_{k=1}^N sqrt(2) |v_k| omega_k^{2M}.
   Then |F_v(r)| <= F_env(r) and 2 g_v(r) <= G_env(r) = (2 / L) * F_env(r)^2.

3. Integration by parts with an increasing error envelope:
   Let N(t) = N_bar(t) + S(t) be the counting function with dN_bar(t) = d_mean(t) dt.
   If |S(t)| <= B(t) for an increasing envelope B(t) >= 0 with B'(t) >= 0,
   partial summation for non-negative decreasing G_env(t) yields:
       sum_{gamma > T} G_env(gamma) = int_T^infty G_env dN_bar - G_env(T) S(T) - int_T^infty S G_env' dt.
   Since G_env' <= 0 and -S(T) <= B(T):
       -int_T^infty S G_env' dt <= int_T^infty B (-G_env') dt = B(T) G_env(T) + int_T^infty B' G_env dt.
   Adding -G_env(T) S(T) <= B(T) G_env(T), conditional on the existence of a valid
   increasing envelope B(t) with |S(t)| <= B(t) and B'(t) >= 0 for Davenport-Heilbronn,
   the resulting upper bound expression is:
       Tail <= int_T^infty G_env(t) (d_mean(t) + B'(t)) dt + 2 B(T) G_env(T).
   Crucially, this IBP expression is explicitly conditional on a valid increasing DH
   envelope B, includes the derivative B'(t), and is never called a conservative bound
   before that condition is rigorously established.

4. Unresolved Status for Davenport-Heilbronn:
   No explicit counting-function majorant valid for the Davenport-Heilbronn function
   is established from local primary sources. Standard Backlund bounds (such as
   |S(t)| <= 0.2 log t + 2.5 or the lab's Q(t)) are established for the Riemann zeta
   function, not for the Davenport-Heilbronn linear combination
   f(s) = ((1 - i*kappa)/2) L(s, chi) + ((1 + i*kappa)/2) L(s, chibar), which has
   zeros off the critical line.
   Furthermore, G_env on R controls only on-line zeros (real gamma); it does not
   bound off-line zero terms Q_k.
   Consequently, the tail bound theorem is marked ATTEMPT_UNRESOLVED, and this code
   refuses to claim it as a validated conservative bound.

5. Defect Analysis of Prior Scout Code:
   This module quantifies two defects in the prior tail estimate in dhneg_localize.py:
   - Defect 1: Factor-of-2 omission (integrated g_v rather than 2*g_v).
   - Defect 2: Truncation at 600 omitting the tail on [600, infty).
"""

from __future__ import annotations

import json
import math
import os
import sys
from typing import Any, Dict

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))


def load_dyadic_vector():
    """Load the recorded exact dyadic vector for (c=31, N=60) from dhneg_scan.json."""
    scan_path = os.path.join(HERE, "dhneg_scan.json")
    with open(scan_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    dyadic = data["confirm_cell"]["rayleigh_vector_dyadic"]
    with mp.workdps(80):
        v = [mp.mpf(m) * (mp.mpf(2) ** e) for m, e in dyadic]
    return v


def compute_moments(v, L, max_order=14):
    """Compute signed multipole moments mu_{2m} and absolute coefficients C_{2M}."""
    omega = [2 * mp.pi * k / L for k in range(len(v))]
    mus = []
    for m in range(max_order // 2 + 1):
        p = 2 * m
        if p == 0:
            val = v[0] + mp.fsum(mp.sqrt(2) * v[k] for k in range(1, len(v)))
        else:
            val = mp.fsum(mp.sqrt(2) * v[k] * (omega[k] ** p) for k in range(1, len(v)))
        mus.append(val)

    rem_coeffs = {}
    for order in range(2, max_order + 1, 2):
        c_val = mp.fsum(mp.sqrt(2) * abs(v[k]) * (omega[k] ** order) for k in range(1, len(v)))
        rem_coeffs[order] = c_val

    return mus, rem_coeffs


def make_envelopes(v, L, order=12):
    """Construct F_env and G_env at specified multipole expansion order."""
    N = len(v) - 1
    omega_N = 2 * mp.pi * N / L
    mus, rem_coeffs = compute_moments(v, L, max_order=order + 2)
    p_max = order - 2
    c_order = rem_coeffs[order]

    def F_env(r):
        s = mp.fsum(abs(mus[i]) / (r ** (2 * i + 1)) for i in range(p_max // 2 + 1))
        s += c_order / ((r ** (order - 1)) * (r * r - omega_N * omega_N))
        return 2 * s

    def G_env(r):
        fe = F_env(r)
        return 2 * (fe * fe) / L

    return F_env, G_env, omega_N


def dh_mean_density(r):
    """Asymptotic mean zero density for conductor 5: (1 / 2pi) log(5 r / 2pi)."""
    return mp.log(5 * r / (2 * mp.pi)) / (2 * mp.pi)


def conservative_tail_bound(v, L, T=120, order=12, dps=60, envelope_model="backlund") -> Dict[str, Any]:
    """Evaluate candidate tail bound including all IBP terms (including B' envelope derivative).

    Refuses to validate as a conservative bound because no explicit counting-function
    majorant valid for Davenport-Heilbronn is established from local primary sources,
    and G_env does not control off-line zeros. Returns ATTEMPT_UNRESOLVED.
    """
    with mp.workdps(dps):
        T_mp = mp.mpf(T)
        F_env, G_env, omega_N = make_envelopes(v, L, order=order)

        if envelope_model == "backlund":
            # Heuristic Backlund shape B(t) = 0.2 log t + 2.5, B'(t) = 0.2 / t
            b_val = mp.mpf("0.2") * mp.log(T_mp) + mp.mpf("2.5")
            b_prime = lambda r: mp.mpf("0.2") / r
            envelope_desc = "Heuristic Backlund shape B(t) = 0.2 log t + 2.5 (zeta-derived, unproven for DH)"
        elif envelope_model == "weil_Q":
            # Lab's Q envelope from zeta/weil.py:615-644: Q(t) = 0.137 log t + 0.443 log log t + 4.35
            lt = mp.log(T_mp)
            b_val = mp.mpf("0.137") * lt + mp.mpf("0.443") * mp.log(lt) + mp.mpf("4.35")
            b_prime = lambda r: mp.mpf("0.137") / r + mp.mpf("0.443") / (r * mp.log(r))
            envelope_desc = "Lab Weil Q envelope (zeta-derived, unproven for DH)"
        else:
            raise ValueError(f"Unknown envelope model: {envelope_model}")

        # Complete IBP integrand: G_env(t) * (d_mean(t) + B'(t))
        smooth_int_with_bprime = mp.quad(
            lambda r: G_env(r) * (dh_mean_density(r) + b_prime(r)),
            [T_mp, T_mp * 2, T_mp * 5, mp.inf],
        )

        g_at_T = G_env(T_mp)
        osc_margin = 2 * b_val * g_at_T
        candidate_total = smooth_int_with_bprime + osc_margin

        return {
            "T": float(T),
            "order": order,
            "omega_N": float(omega_N),
            "envelope_model": envelope_model,
            "envelope_description": envelope_desc,
            "G_env_at_T": mp.nstr(g_at_T, 10),
            "smooth_density_integral_with_Bprime": mp.nstr(smooth_int_with_bprime, 10),
            "envelope_bound_at_T": float(b_val),
            "oscillation_margin": mp.nstr(osc_margin, 10),
            "candidate_tail_upper_bound": mp.nstr(candidate_total, 10),
            "is_conservative_analytic_bound": False,
            "tail_status": "ATTEMPT_UNRESOLVED",
            "unresolved_reason": (
                "No explicit counting-function majorant valid for Davenport-Heilbronn "
                "is established from local primary sources; real-axis envelope G_env "
                "does not bound off-line zeros."
            ),
        }


def analyze_prior_tail_defects(v, L, dps=60) -> Dict[str, Any]:
    """Analyze the two defects in dhneg_localize.py line 147.

    Prior code:
        tail = mp.quad(lambda r: gv(r) * dens(r), [120, 200, 400, 600])
    Reported: ~2.956e-30.

    Defect 1: Factor-of-2 missing (integrated g_v instead of 2*g_v).
    Defect 2: Truncation at 600 (omitted [600, infty)).
    """
    with mp.workdps(dps):
        import galerkin as G

        F_even = G.F_even(v, L)

        def gv(r):
            f = F_even(r)
            return (f * f) / L

        dens = dh_mean_density

        # As executed in dhneg_localize.py (defective: no factor of 2, stopped at 600)
        i_defective = mp.quad(lambda r: gv(r) * dens(r), [120, 200, 400, 600])

        # Corrected factor of 2 on [120, 600]
        i_factor2_600 = mp.quad(lambda r: 2 * gv(r) * dens(r), [120, 200, 400, 600])

        # Omitted high-frequency tail on [600, infty)
        i_tail_600_inf = mp.quad(lambda r: 2 * gv(r) * dens(r), [600, 1200, 3000, mp.inf])

        # Full corrected mean-density integral (heuristic diagnostic only; not a zero tail or bound)
        i_corrected_total = i_factor2_600 + i_tail_600_inf

        return {
            "defective_prior_tail_reported": mp.nstr(i_defective, 10),
            "corrected_factor2_to_600": mp.nstr(i_factor2_600, 10),
            "omitted_tail_over_600": mp.nstr(i_tail_600_inf, 10),
            "corrected_mean_density_integral": mp.nstr(i_corrected_total, 10),
            "ratio_corrected_to_defective": float(i_corrected_total / i_defective),
        }
