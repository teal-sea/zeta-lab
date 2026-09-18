"""Bounded feasibility checker for the Davenport-Heilbronn (c=31, N=60) cell.

Consumes existing saved artifacts from dhneg_scan.json, evaluates every hypothesis
required for a quantitative Weil-truncation off-line-zero detection claim, and wires
tail_bound.py directly.

Rigor Discipline:
1. Returns 'PASS' only when EVERY input is rigorous (enclosure-carrying);
   otherwise returns 'INCONCLUSIVE'.
2. Actual evidence semantics: no boolean option may relabel float seeds as enclosed
   or complete.
3. If zero coordinates are float seeds, completeness is unverified, tail majorant is
   unsupported, or dictionary proof obligations are open, the gate reports blockers
   and returns INCONCLUSIVE.
"""

from __future__ import annotations

import json
import math
import os
import sys
from typing import Any, Dict

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import tail_bound


def run_feasibility_gate(
    scan_path: str | None = None,
    allow_float_zeros: bool = False,
    allow_mean_density_tail: bool = False,
    **kwargs: Any,
) -> Dict[str, Any]:
    """Audit saved artifacts and evaluate the feasibility gate.

    Strictly enforces rigor: float inputs, unverified completeness, unsupported
    tail majorants, and open dictionary obligations force the verdict to INCONCLUSIVE.
    No boolean option may relabel float seeds as enclosed or complete.
    """
    if scan_path is None:
        scan_path = os.path.join(HERE, "dhneg_scan.json")

    if not os.path.isfile(scan_path):
        return {
            "verdict": "INCONCLUSIVE",
            "recommendation": "ATTEMPT_UNRESOLVED",
            "reason": f"Artifact file not found: {scan_path}",
            "blockers": ["missing_artifact_file"],
            "exact_blockers": ["missing_artifact_file"],
        }

    with open(scan_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    report: Dict[str, Any] = {
        "cell": {"c": 31, "N": 60},
        "arithmetic_side": {},
        "zero_side": {},
        "dictionary": {},
        "blockers": [],
    }

    # -----------------------------------------------------------------------
    # 1. Arithmetic-side audit (eigenvalue negativity)
    # -----------------------------------------------------------------------
    confirm = data.get("confirm_cell", {})
    even_inertia = confirm.get("even_inertia_at_0")  # [60, 1, True]
    odd_inertia = confirm.get("odd_inertia_at_0")    # [60, 0, True]
    rayleigh_up_str = confirm.get("rayleigh_upper_endpoint", "")
    rayleigh_neg = confirm.get("rayleigh_upper_is_negative", False)
    rump_neg = confirm.get("eig_rump_min_strictly_negative", False)

    # Validate even inertia
    inertia_valid = (
        isinstance(even_inertia, list)
        and len(even_inertia) == 3
        and even_inertia[0] == 60
        and even_inertia[1] == 1
        and even_inertia[2] is True
    )

    # Validate Rayleigh upper endpoint
    rayleigh_valid = False
    if rayleigh_neg:
        try:
            clean = rayleigh_up_str.split("+/-")[0].strip("[] ")
            val = float(clean)
            if val < 0:
                rayleigh_valid = True
        except (ValueError, TypeError):
            pass

    arithmetic_hardened = inertia_valid and rayleigh_valid and rump_neg

    report["arithmetic_side"] = {
        "even_inertia_at_0": even_inertia,
        "even_inertia_conclusive": inertia_valid,
        "rayleigh_upper_endpoint": rayleigh_up_str,
        "rayleigh_upper_strictly_negative": rayleigh_valid,
        "rump_min_strictly_negative": rump_neg,
        "status": "HARDENED" if arithmetic_hardened else "INCONCLUSIVE",
    }

    if not arithmetic_hardened:
        report["blockers"].append("arithmetic_eigenvalue_not_hardened")

    # -----------------------------------------------------------------------
    # 2. Zero-side audit (attribution and dictionary inputs)
    # -----------------------------------------------------------------------
    loc = data.get("localization", {})
    dict_31_60 = loc.get("dictionary_31_60", {})

    # Check on-line zeros
    # Artifacts use float seeds from data/dh_zeros_online_T120.json
    # Rule: no boolean option may relabel float seeds as enclosed or complete.
    online_sum_str = dict_31_60.get("online_partial_sum_T120", "")
    is_enclosed_intervals = False
    is_complete_verified = False

    report["zero_side"]["online_zeros"] = {
        "count": 64,
        "cutoff_T": 120,
        "partial_sum": online_sum_str,
        "input_format": "float_seeds_bisection",
        "is_enclosed_intervals": is_enclosed_intervals,
        "is_complete_verified": is_complete_verified,
        "status": "ENCLOSED" if (is_enclosed_intervals and is_complete_verified) else "UNRESOLVED_FLOAT",
    }
    report["blockers"].append("online_zeros_are_unhardened_floats")
    report["blockers"].append("online_zero_list_completeness_unverified")

    # Check off-line zero quadruple
    offline_quad_str = dict_31_60.get("offline_quadruple", "")
    is_offline_box_enclosed = False

    report["zero_side"]["offline_quadruple"] = {
        "quadruple_term": offline_quad_str,
        "coordinates": {"gamma": 85.69934848537759, "delta": 0.3085171824566374},
        "is_enclosed_interval_box": is_offline_box_enclosed,
        "status": "ENCLOSED" if is_offline_box_enclosed else "UNRESOLVED_FLOAT",
    }
    report["blockers"].append("offline_zero_coordinates_are_unhardened_floats")

    # Check tail model: wired directly to tail_bound.py
    v = tail_bound.load_dyadic_vector()
    with mp.workdps(50):
        L = mp.log(31)
        tb_res = tail_bound.conservative_tail_bound(v, L, T=120, order=12, dps=45)
        tail_defects = tail_bound.analyze_prior_tail_defects(v, L, dps=45)

    report["zero_side"]["tail_model"] = {
        "prior_defective_estimate": dict_31_60.get("tail_estimate_over_120", "2.956330061e-30"),
        "corrected_mean_density_integral": tail_defects["corrected_mean_density_integral"],
        "candidate_tail_bound": tb_res["candidate_tail_upper_bound"],
        "model_type": "multipole_envelope_unsupported_majorant",
        "is_conservative_analytic_bound": False,
        "status": "ATTEMPT_UNRESOLVED",
        "unresolved_reason": tb_res["unresolved_reason"],
    }
    report["blockers"].append("tail_model_lacks_valid_dh_counting_majorant")

    # Check Guinand-Weil dictionary formal status
    report["dictionary"] = {
        "basis_transform_compact_support": "PROVED_BY_CONSTRUCTION",
        "algebraic_identity_g_equals_F2_over_L": "PROVED_ANALYTIC",
        "guinand_weil_explicit_formula_for_dh": "OPEN_PROOF_OBLIGATION",
        "galerkin_assembly_pairing": "MEASURED_ASSEMBLY_PORT_CONTINUOUS_PAIRING_UNPROVED",
        "status": "PARTIALLY_FORMALIZED",
    }
    report["blockers"].append("guinand_weil_dh_dictionary_proof_obligations_open")

    # -----------------------------------------------------------------------
    # 3. Margin budget evaluation
    # -----------------------------------------------------------------------
    try:
        lam_val = float(dict_31_60.get("lambda_min", "-1.8739e-31"))
        quad_val = float(dict_31_60.get("offline_quadruple", "-6.7350e-29"))
        online_val = float(dict_31_60.get("online_partial_sum_T120", "5.9537e-29"))
        lam_minus_quad = lam_val - quad_val
        residual = lam_minus_quad - online_val
        mean_density_integral_float = float(tail_defects["corrected_mean_density_integral"])
        # Heuristic diagnostic comparison only: this is an arithmetic difference against
        # the heuristic mean-density integral, NOT a subtraction of a true zero tail or bound.
        heuristic_diff = residual - mean_density_integral_float

        report["margin_budget"] = {
            "lambda_min": lam_val,
            "offline_quadruple_Q1": quad_val,
            "online_partial_sum_T120": online_val,
            "lambda_minus_Q1": lam_minus_quad,
            "ratio_absQ1_to_abslam": abs(quad_val / lam_val) if lam_val != 0 else None,
            "ratio_online_to_absQ1": abs(online_val / quad_val) if quad_val != 0 else None,
            "cancellation_ratio": abs(online_val / quad_val),
            "unexplained_residual_at_T120": residual,
            "residual_fraction_of_Q1": abs(residual / quad_val),
            "heuristic_diagnostic_residual_minus_mean_density_integral": heuristic_diff,
            "net_margin_at_crossing": abs(lam_val),
            "budget_status": "MARGINAL_CROSSING_SENSITIVE",
        }
    except Exception as e:
        report["margin_budget"] = {"error": str(e)}

    # -----------------------------------------------------------------------
    # 4. Reserve Candidate Cell (47, 64) Audit
    # -----------------------------------------------------------------------
    dict_47_64 = loc.get("dictionary_47_64", {})
    if dict_47_64:
        report["reserve_candidate"] = {
            "cell": {"c": 47, "N": 64},
            "status": "MEASURED_RESERVE_CANDIDATE",
            "lambda_min": float(dict_47_64.get("lambda_min", "-0.3163")),
            "offline_quadruple_Q1": float(dict_47_64.get("offline_quadruple", "-0.8307")),
            "online_partial_sum_T120": float(dict_47_64.get("online_partial_sum_T120", "0.4931")),
            "lambda_minus_Q1": float(dict_47_64.get("lambda_minus_quad", "0.5144")),
            "note": "Measured reserve candidate only; no conservative bound evaluated here.",
        }

    # -----------------------------------------------------------------------
    # 5. Final Verdict
    # -----------------------------------------------------------------------
    if len(report["blockers"]) == 0 and arithmetic_hardened:
        report["verdict"] = "PASS"
        report["recommendation"] = "GO"
    else:
        report["verdict"] = "INCONCLUSIVE"
        report["recommendation"] = "ATTEMPT_UNRESOLVED"
        report["exact_blockers"] = list(report["blockers"])

    return report


def main():
    report = run_feasibility_gate()
    out_path = os.path.join(HERE, "gate_31_60.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(f"Gate evaluation complete. Verdict: {report['verdict']}")
    print(f"Recommendation: {report['recommendation']}")
    print("Blockers:")
    for b in report["blockers"]:
        print(f"  - {b}")
    print(f"Saved report to: {out_path}")


if __name__ == "__main__":
    main()
