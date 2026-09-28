"""Tests for the Davenport-Heilbronn (c=31, N=60) feasibility gate package.

Verifies:
1. Hardened arithmetic-side eigenvalue negativity from saved artifacts.
2. Exact algebraic identity g_v(z) = (1/L) * F_v(z)^2 on real and complex inputs.
3. Positivity of g_v on the real axis (guaranteeing that on-line zeros contribute >= 0).
4. Quantification of the factor-of-2 defect in the prior mean-density tail model.
5. Finite candidate bound from the multipole tail expansion, marked ATTEMPT_UNRESOLVED.
6. Rigorous checker discipline: returns INCONCLUSIVE on unhardened float/mean-density inputs.
7. Margin budget reconciliation: on-line sum / |Q1| is 0.8839999976612719, not 98.7%.
8. Lesions proving checker rejects float zeros, unverified completeness, unsupported
   tail majorants, and open dictionary obligations.
9. Verification that no boolean option relabels float seeds as enclosed or complete.
"""

from __future__ import annotations

import json
import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import galerkin as G  # noqa: E402
import gate_checker  # noqa: E402
import tail_bound  # noqa: E402


def test_arithmetic_side_hardened():
    """Verify that arithmetic-side negativity is hardened by 3 independent routes."""
    scan_path = os.path.join(HERE, "dhneg_scan.json")
    assert os.path.isfile(scan_path), "dhneg_scan.json missing"
    with open(scan_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    confirm = data["confirm_cell"]
    # 1. Ball LDL inertia
    assert confirm["even_inertia_at_0"] == [60, 1, True]
    assert confirm["odd_inertia_at_0"] == [60, 0, True]

    # 2. Rayleigh quotient upper endpoint
    rayleigh_str = confirm["rayleigh_upper_endpoint"]
    clean = rayleigh_str.split("+/-")[0].strip("[] ")
    assert float(clean) < 0, f"Rayleigh upper endpoint not negative: {clean}"
    assert confirm["rayleigh_upper_is_negative"] is True

    # 3. Rump eigenvalue enclosure
    assert confirm["eig_rump_min_strictly_negative"] is True


def test_exact_algebraic_identity():
    """Verify g_v(z) == (1/L) * F_v(z)^2 on real axis and complex quadruple point."""
    v = tail_bound.load_dyadic_vector()
    with mp.workdps(60):
        L = mp.log(31)
        gv = G.g_even(v, L)
        Fv = G.F_even(v, L)

        # Real test points
        for r in [1.0, 14.13, 50.0, 85.699, 120.0]:
            g_val = gv(r)
            f_val = Fv(r)
            # g_v is non-negative on real line
            assert g_val >= 0, f"g_v({r}) is negative: {g_val}"
            expected = (f_val * f_val) / L
            assert abs(g_val - expected) < 1e-35 * max(1, abs(g_val))

        # Complex point at the off-line zero
        z = mp.mpc("85.699348485377592171929", "-0.308517182456637385553")
        gz = gv(z)
        fz = Fv(z)
        expected_z = (fz * fz) / L
        rel_diff = abs(gz - expected_z) / abs(gz)
        assert rel_diff < 1e-30, f"Complex identity mismatch: rel_diff={rel_diff}"


def test_factor_two_defect_in_prior_tail():
    """Verify and quantify the factor-of-2 defect in dhneg_localize.py."""
    v = tail_bound.load_dyadic_vector()
    with mp.workdps(50):
        L = mp.log(31)
        res = tail_bound.analyze_prior_tail_defects(v, L, dps=45)

        i_defective = float(res["defective_prior_tail_reported"])
        assert "corrected_full_smooth_tail" not in res, "Old field name must not be present"
        assert "corrected_mean_density_integral" in res, "New field name must be present"
        i_corrected = float(res["corrected_mean_density_integral"])

        # Defective was ~2.96e-30; corrected is ~6.72e-30
        assert 2.5e-30 < i_defective < 3.5e-30
        assert 6.0e-30 < i_corrected < 7.5e-30
        assert res["ratio_corrected_to_defective"] > 2.0


def test_tail_bound_attempt_unresolved():
    """Verify candidate tail bound marks ATTEMPT_UNRESOLVED and includes B' IBP term."""
    v = tail_bound.load_dyadic_vector()
    with mp.workdps(50):
        L = mp.log(31)
        res = tail_bound.conservative_tail_bound(v, L, T=120, order=12, dps=45)

        bound = float(res["candidate_tail_upper_bound"])
        assert bound > 0
        assert bound < 1e-24, f"Order 12 bound unexpectedly large: {bound}"
        assert res["is_conservative_analytic_bound"] is False
        assert res["tail_status"] == "ATTEMPT_UNRESOLVED"
        assert "unresolved_reason" in res


def test_gate_checker_discipline_returns_inconclusive():
    """Verify that the gate checker strictly refuses to pass unhardened float inputs."""
    report = gate_checker.run_feasibility_gate()
    assert report["verdict"] == "INCONCLUSIVE"
    assert report["recommendation"] == "ATTEMPT_UNRESOLVED"
    assert len(report["exact_blockers"]) == 4

    expected_blockers = {
        "online_zeros_are_unhardened_floats",
        "online_zero_list_completeness_unverified",
        "offline_zero_coordinates_are_unhardened_floats",
        "tail_model_lacks_valid_dh_counting_majorant",
    }
    for eb in expected_blockers:
        assert eb in report["exact_blockers"], f"Missing blocker: {eb}"
    assert "guinand_weil_dh_dictionary_proof_obligations_open" not in report["exact_blockers"]


def test_two_track_reporting():
    """Verify two tracks: qualitative existence is GO/PROVED; quantitative attribution is INCONCLUSIVE."""
    report = gate_checker.run_feasibility_gate()
    assert report["qualitative_existence"]["status"] == "PROVED"
    assert report["qualitative_existence"]["recommendation"] == "GO"
    assert report["quantitative_attribution"]["status"] == "INCONCLUSIVE"
    assert report["quantitative_attribution"]["recommendation"] == "ATTEMPT_UNRESOLVED"
    assert report["dictionary"]["status"] == "CLOSED_ORDINARY_PROOF"


def test_margin_budget_reconciliation():
    """Verify margin budget numbers match JSON exactly (88.4%, not 98.7%)."""
    report = gate_checker.run_feasibility_gate()
    budget = report["margin_budget"]

    # Reconciled ratio: on-line partial sum divided by abs(Q1) is exactly 0.8839999976612719
    assert budget["ratio_online_to_absQ1"] == pytest.approx(0.8839999976612719, rel=1e-12)
    assert budget["cancellation_ratio"] == pytest.approx(0.8839999976612719, rel=1e-12)
    assert budget["cancellation_ratio"] < 0.90, "Cancellation is ~88.4%, not 98.7%"

    # Unexplained residual at T120
    assert budget["unexplained_residual_at_T120"] == pytest.approx(7.625194195035724e-30, rel=1e-8)

    # Heuristic diagnostic difference is ~9.00e-31, not 7.87e-31; old field must not exist
    assert "residual_minus_smooth_tail" not in budget, "Old field name must not be present"
    assert "heuristic_diagnostic_residual_minus_mean_density_integral" in budget
    assert budget["heuristic_diagnostic_residual_minus_mean_density_integral"] == pytest.approx(9.003583070357245e-31, rel=1e-6)

    # Reserve candidate cell (47, 64) is recorded only as measured reserve candidate
    reserve = report["reserve_candidate"]
    assert reserve["cell"] == {"c": 47, "N": 64}
    assert reserve["status"] == "MEASURED_RESERVE_CANDIDATE"
    assert reserve["lambda_minus_Q1"] == pytest.approx(0.5143544, rel=1e-5)


def test_checker_rejects_float_zeros_lesion():
    """Lesion test: verify checker identifies float zero seeds and marks UNRESOLVED_FLOAT."""
    report = gate_checker.run_feasibility_gate()
    online_zeros = report["zero_side"]["online_zeros"]
    assert online_zeros["is_enclosed_intervals"] is False
    assert online_zeros["status"] == "UNRESOLVED_FLOAT"
    assert "online_zeros_are_unhardened_floats" in report["exact_blockers"]

    offline_quad = report["zero_side"]["offline_quadruple"]
    assert offline_quad["is_enclosed_interval_box"] is False
    assert offline_quad["status"] == "UNRESOLVED_FLOAT"
    assert "offline_zero_coordinates_are_unhardened_floats" in report["exact_blockers"]


def test_checker_rejects_unverified_completeness_lesion():
    """Lesion test: verify checker flags unverified zero list completeness as a blocker."""
    report = gate_checker.run_feasibility_gate()
    online_zeros = report["zero_side"]["online_zeros"]
    assert online_zeros["is_complete_verified"] is False
    assert "online_zero_list_completeness_unverified" in report["exact_blockers"]


def test_checker_rejects_unsupported_tail_majorant_lesion():
    """Lesion test: verify checker flags lack of valid DH counting majorant as a blocker."""
    report = gate_checker.run_feasibility_gate()
    tail_model = report["zero_side"]["tail_model"]
    assert tail_model["is_conservative_analytic_bound"] is False
    assert tail_model["status"] == "ATTEMPT_UNRESOLVED"
    assert "tail_model_lacks_valid_dh_counting_majorant" in report["exact_blockers"]


def test_checker_reports_dictionary_closed_and_two_tracks():
    """Verify checker reports closed dictionary and two distinct tracks."""
    report = gate_checker.run_feasibility_gate()
    dictionary = report["dictionary"]
    assert dictionary["status"] == "CLOSED_ORDINARY_PROOF"
    assert dictionary["guinand_weil_explicit_formula_for_dh"] == "PROVED_ORDINARY_PROOF"
    assert dictionary["galerkin_assembly_pairing"] == "PROVED_ORDINARY_PROOF"
    assert "guinand_weil_dh_dictionary_proof_obligations_open" not in report["exact_blockers"]


def test_no_boolean_option_relabels_evidence_semantics():
    """Verify that no boolean option relabels float seeds as enclosed or complete."""
    # Attempt to pass permissive flags
    report = gate_checker.run_feasibility_gate(
        allow_float_zeros=True,
        allow_mean_density_tail=True,
    )
    # Evidence semantics must remain honest
    online_zeros = report["zero_side"]["online_zeros"]
    assert online_zeros["is_enclosed_intervals"] is False
    assert online_zeros["is_complete_verified"] is False
    assert online_zeros["status"] == "UNRESOLVED_FLOAT"

    offline_quad = report["zero_side"]["offline_quadruple"]
    assert offline_quad["is_enclosed_interval_box"] is False
    assert offline_quad["status"] == "UNRESOLVED_FLOAT"

    tail_model = report["zero_side"]["tail_model"]
    assert tail_model["is_conservative_analytic_bound"] is False
    assert tail_model["status"] == "ATTEMPT_UNRESOLVED"

    # Verdict must stay INCONCLUSIVE
    assert report["verdict"] == "INCONCLUSIVE"
    assert report["recommendation"] == "ATTEMPT_UNRESOLVED"
    assert len(report["exact_blockers"]) >= 4


def test_stale_field_names_and_overclaims_fail():
    """Verify that stale field names and overclaims fail across artifacts."""
    v = tail_bound.load_dyadic_vector()
    with mp.workdps(45):
        L = mp.log(31)
        res = tail_bound.analyze_prior_tail_defects(v, L, dps=35)
    assert "corrected_full_smooth_tail" not in res
    assert "corrected_mean_density_integral" in res

    report = gate_checker.run_feasibility_gate()
    tail_model = report["zero_side"]["tail_model"]
    assert "corrected_full_smooth_tail" not in tail_model
    assert "corrected_mean_density_integral" in tail_model

    budget = report["margin_budget"]
    assert "residual_minus_smooth_tail" not in budget
    assert "heuristic_diagnostic_residual_minus_mean_density_integral" in budget

    # Check the serialized JSON file
    json_path = os.path.join(HERE, "gate_31_60.json")
    with open(json_path, "r", encoding="utf-8") as f:
        content = f.read()
    assert "corrected_full_smooth_tail" not in content
    assert "residual_minus_smooth_tail" not in content
    assert "corrected_mean_density_integral" in content
    assert "heuristic_diagnostic_residual_minus_mean_density_integral" in content


def test_theorem_feasibility_obligations_and_prose():
    """Verify THEOREM_FEASIBILITY.md obligations, status summary, and conditional IBP discipline."""
    doc_path = os.path.join(HERE, "THEOREM_FEASIBILITY.md")
    assert os.path.isfile(doc_path)
    with open(doc_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    text = "".join(lines)
    assert "corrected_full_smooth_tail" not in text
    assert "residual_minus_smooth_tail" not in text

    # OBL-1 must be CLOSED as ordinary proof
    obl1_lines = [l for l in lines if "| OBL-1 |" in l]
    assert len(obl1_lines) == 1
    assert "CLOSED" in obl1_lines[0]
    assert "ordinary proof" in obl1_lines[0]

    # OBL-3 must be CLOSED as ordinary proof
    obl3_lines = [l for l in lines if "| OBL-3 |" in l]
    assert len(obl3_lines) == 1
    assert "CLOSED" in obl3_lines[0]
    assert "ordinary proof" in obl3_lines[0]

    # Summary must state two tracks: qualitative existence is GO / PROVED, quantitative attribution remains ATTEMPT_UNRESOLVED
    summary_lines = [l for l in lines if "Status summary:" in l]
    assert len(summary_lines) == 1
    assert "qualitative existence track is GO / PROVED" in summary_lines[0]
    assert "Quantitative attribution (OBL-4, OBL-5, OBL-6) remains INCONCLUSIVE / ATTEMPT_UNRESOLVED" in summary_lines[0]

    # IBP expression must be explicitly conditional on valid increasing DH envelope B
    assert "conditional on the existence of a valid increasing envelope B(t)" in text
    assert "never called a conservative bound before that condition" in text

    # Mean-density integral must not be subtracted or presented as a true zero tail or bound
    assert "heuristic diagnostic" in text
    assert "must not be subtracted or presented as a true zero tail or bound" in text

    # Reserve candidate cell (47, 64) is measured-only candidate (no GO or pivot claim)
    assert "MEASURED_RESERVE_CANDIDATE" in text
    assert "no pivot, funding, or GO claim is made" in text

