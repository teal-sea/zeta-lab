"""Pins for DUAL_WITNESS.md: the exact dual witness for T*(31, 1000).

The witness is a basis S of Q_N; the redistributed measure nu = sum_q m_q
(A_S^T)^{-1} A[q,:] has exact rational per-prime coefficients, its moment
identities are checked as exact equalities, its signs by interval
arithmetic, and its gain equals the tight primal certificate's excess.  The
value pinned here is T*(31, 1000) - psi(1000) = 41.2821694429593918...,
which also equals the rational primal upper bound of PR #203 (41.28216944).
"""
from __future__ import annotations

import importlib.util
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HUNT = Path(__file__).resolve().parents[1] / "hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier"


def _load(name: str):
    if str(HUNT) not in sys.path:
        sys.path.insert(0, str(HUNT))
    spec = importlib.util.spec_from_file_location(name, HUNT / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def witness_1000_31():
    dw = _load("dual_witness")
    return dw.witness(1000, 31, dps=60, verbose=False)


def test_exact_witness_at_1000_31(witness_1000_31):
    w = witness_1000_31
    assert w["n_cells"] == 61 and w["n_primes"] == 168
    assert w["basis_is_support"] and len(w["basis_cells"]) == 31
    assert w["moment_identities_exact"]
    assert w["nu_all_nonnegative_by_enclosure"] and w["nu_min_lower_endpoint"] > 1e-3
    assert w["primal_tight_certificate_feasible_on_Q"]
    g_lo, g_hi = float(w["gain_interval"][0]), float(w["gain_interval"][1])
    assert 41.2821694429 < g_lo <= g_hi < 41.2821694430
    assert w["gain_width"] < 1e-50
    # the floating LP objective agrees to solver tolerance, and Codex's
    # rational primal (an upper bound) is not below the exact value
    assert abs(w["lp_gain_float"] - g_lo) < 1e-6
    assert 41.28216944 <= g_hi + 5e-9
    # the emptied cells and their gains (denominator 74 = basis determinant)
    assert w["emptied_cells"] == [7, 11, 13, 14, 18, 20, 23, 31, 32, 34, 52, 62, 111, 125, 142, 200, 250, 333]
    assert all(Fraction(g).denominator in (37, 74) for g in w["emptied_cells_gain_per_unit"].values())
    assert Fraction(w["emptied_cells_gain_per_unit"][200]) == Fraction(141, 74)


def test_exchange_construction_at_1000_31():
    # Construction B (DUAL_WITNESS.md Section 6): greedy prefix-mediated
    # exchanges give an exactly verified witness; three steps already beat
    # every one-sided prefix family, and the two-sided z_q LP reproduces the
    # exact optimum (Lemma 6).
    fm = _load("fake_mass_witness")
    out = fm.construction_a(1000, 31, verbose=False, greedy_steps=3)
    assert out["Q_plus"] == 29 and out["Q_minus_with_mass"] == 0
    assert abs(out["additions_rationalized_gain_float"] - 4 * 0.6931471805599453) < 1e-5
    assert out["additions_rationalized_feasible"] and out["additions_moments_exact"]
    assert all(c["t_max"] == 0.0 and c["binding_s"] == 17 for c in out["constant_parameter"])
    assert out["greedy_moments_exact"] and out["greedy_feasible_by_enclosure"]
    assert len(out["greedy"]) == 3
    assert out["greedy"][0]["a"] == 32 and out["greedy"][0]["b"] == 166
    assert out["greedy_total_gain_float"] > 15.0
    assert abs(out["two_sided_lp_gain_float"] - 41.2821694) < 1e-5


def test_fold_family_fails_at_the_walls_and_rough_shifts_hold():
    # DUAL_WITNESS.md Section 8: the prescribed halving-fold family has exact
    # integer moment identities for every source, its uniform-t version has
    # t* = 0 at (1000, 31) because prefix cell 19 carries no real mass and is
    # drained, and the drain-free rough-shift family gives log 97 at
    # (10^4, 100) from the single source 103 (the coordinator's example).
    ff = _load("fold_family")
    out = ff.evaluate(1000, 31, verbose=False)
    assert out["moment_identities_exact_all_sources"]
    assert 19 in out["zero_mass_prefix_cells"]
    f1 = out["variants"][0]
    assert f1["variant"].startswith("F1") and f1["t_star"] == 0.0 and f1["binding_cell"] == 19 and f1["gain"] == 0.0
    assert out["family_R_rough_shift"]["sources"] == []
    out4 = ff.evaluate(10_000, 100, verbose=False)
    assert out4["moment_identities_exact_all_sources"]
    assert out4["family_R_rough_shift"]["sources"] == [103]
    assert out4["family_R_rough_shift"]["moment_identities_exact"]
    import math

    assert abs(out4["family_R_rough_shift"]["gain"] - math.log(97)) < 1e-9
    assert 33 in out4["zero_mass_prefix_cells"] and out4["variants"][0]["t_star"] == 0.0


def test_compensated_bundle_and_rule_c_at_1000_31():
    # DUAL_WITNESS.md Section 9: the coordinator's bundle Fold(76) + 2Fold(200)
    # + Fold(333) is an exact witness with eps* = log(7)/3 and gain (10/3) log 7;
    # Lemma 8 holds at every top cell; Rule C closes the walls with 2 Fold(333)
    # and gains 5 log 3, while the increasing-r variant nets zero.
    import math

    cf = _load("compensated_fold")
    lem = cf.band_lemma_check(1000, 31)
    assert lem["violations"] == 0 and lem["violations_at_w_eq_y"] == 0
    b = cf.check_bundle(1000, 31, {76: 1, 200: 2, 333: 1})
    assert b["support_ok"] and b["moments_ok"] and b["feasible"]
    assert b["gains_per_unit"] == {76: 2, 200: 4, 333: 0} and b["total_gain_units"] == 10
    assert b["binding_cell"] == 20 and b["eps_star"] == "log(7)/3"
    assert b["withdrawn_cells"][20] == 3 and b["withdrawn_cells"][7] == 7
    assert abs(float(b["gain_interval"][0]) - 10 * math.log(7) / 3) < 1e-12
    c = cf.rule_c(1000, 31, verbose=False, order="clean-gain-r")
    assert c["feasible"] and c["total_gain_units"] == 10 and c["binding_cell"] == 333
    assert c["repairs_added"] == {333: 2}
    assert abs(float(c["gain_interval"][0]) - 5 * math.log(3)) < 1e-12
    c0 = cf.rule_c(1000, 31, verbose=False, order="r")
    assert c0["feasible"] and c0["total_gain_units"] == 0


def test_coordinator_bundle_and_credit_identity_at_10000_100():
    # DUAL_WITNESS.md Section 10: the coordinator's compensated bundle verifies
    # exactly (615 units, binding cell 43, eps* = log(229)/146,
    # E >= (615/146) log 229), the repair block is negative only at walls 54
    # and 62 where it equals -(2U), and k = 2 is the unique feasible seed
    # multiplier.
    import math

    cf = _load("compensated_fold")
    cb = cf.coordinator_bundle(10_000, 100)
    assert cb["n_profitable"] == 28 and cb["sum_g_over_A"] == 91
    assert cb["support_ok"] and cb["moments_ok"] and cb["feasible"]
    assert cb["total_gain_units"] == 615 and cb["binding_cell"] == 43
    assert cb["eps_star"] == "log(229)/146"
    assert abs(float(cb["gain_interval"][0]) - 615 * math.log(229) / 146) < 1e-11
    wa = cb["wall_accounting"]
    # repair block negative only at 54 and 62, equal to -(2U) there
    neg_walls = {w: d for w, d in wa.items() if d["repairs"] < 0}
    assert set(neg_walls) == {54, 62}
    assert wa[54]["repairs"] == -2 and wa[54]["seed_2U"] == 2 and wa[54]["final"] == 0
    assert wa[62]["repairs"] == -4 and wa[62]["seed_2U"] == 4 and wa[62]["final"] == 0
    db = cf.diagnose_rule_c_block(10_000, 100)
    assert db["seed1_deficit_33"] == -11 and db["seed2_deficit_33"] == -22
    assert db["clean_refills_of_33"] == []  # every refill of the binding wall drains another
    assert db["wall_findings"][33]["in_lower_half"] and db["wall_findings"][33]["n_clean_refills"] == 0


def test_signed_fold_expansion_of_the_132_witness():
    # DUAL_WITNESS.md Section 11: the descending recurrence reconstructs the
    # 132.729535 prefix-exchange witness exactly in the fold basis, with 17
    # negative coefficients (the un-folds excluded by the nonnegative family).
    from fractions import Fraction

    sf = _load("signed_fold")
    out = sf.solve(
        10_000, 100,
        str(HUNT / "results/fake_mass_N10000_y100.json"),
        verbose=False,
    )
    assert out["reconstruction_exact_all_cells"] and out["prefix_reconstruction_exact"]
    assert out["gain_from_fold_coeffs_matches"]
    assert Fraction(out["gain_exact"]) == Fraction(26545907, 200000)
    assert out["n_negative"] == 17 and out["n_positive"] == 24
    assert out["negative_cells"] == [102, 113, 123, 125, 126, 128, 129, 133, 142, 144, 151, 156, 163, 172, 227, 256, 303]
    # the three tail negatives feed band negatives (halving tree)
    band = set(c for c in out["negative_cells"] if c <= 200)
    for a in (227, 256, 303):
        assert a // 2 in band


def test_twin_exchange_destination_cancels_and_103_is_feasible():
    # DUAL_WITNESS.md Section 11: X_k = Fold(2k+1) - Fold(2k) cancels the half
    # destination k; X_51 = Fold(103) - Fold(102) is the one feasible-alone
    # twin (source 103 prime), withdrawal only at 103, gain log 97.
    import math
    from fractions import Fraction

    sf = _load("signed_fold")
    fold_family = _load("fold_family")
    from prefix_witness import mobius_table

    mu = mobius_table(100)

    def X(p, a):
        D = {}
        for c, v in sf.fold_measure(p, 100, mu).items():
            D[c] = D.get(c, Fraction(0)) + v
        for c, v in sf.fold_measure(a, 100, mu).items():
            D[c] = D.get(c, Fraction(0)) - v
        return {c: v for c, v in D.items() if v}

    D = X(103, 102)
    # zero moments and cancelled destination 51
    assert all(sum(v * (c // j) for c, v in D.items()) == 0 for j in range(1, 101))
    assert 51 not in D
    # the only withdrawal is at the prime source 103
    assert [c for c, v in D.items() if v < 0] == [103]
    assert fold_family.fold_vectors(103, 100, mu)[1] - fold_family.fold_vectors(102, 100, mu)[1] == 1


def test_h_decomposition_and_confluence_at_10000_100():
    # DUAL_WITNESS.md Section 12: h = -g - F^T beta >= 0, the reduced-cost
    # identity holds exactly on the witness, and the confluence triple
    # C(102) = Fold(204) + Fold(103) - Fold(102) is feasible with gain 5 log 7.
    import math

    gs = _load("grouped_signed")
    hd = gs.h_decomposition(
        10_000, 100, str(HUNT / "results/fake_mass_N10000_y100.json")
    )
    assert hd["h_nonneg"] and hd["identity_holds"]
    assert abs(hd["beta_T_m"] - 66.338409) < 1e-4
    assert abs(hd["witness_gain"] - 132.729535) < 1e-5
    assert hd["negatives_h_zero"] == [113, 163, 303]
    assert hd["top_weighted"][0][1] == 102  # cell 102 carries the largest weight
    c = gs.confluence(10_000, 100, 102)
    assert c["feasible"] and c["moments_zero"]
    assert c["double"] == 204 and c["twin"] == 103 and c["gain_units"] == 5
    assert c["eps_binding"] == 204
    assert abs(c["total_gain"] - 5 * math.log(7)) < 1e-4
    assert not c["walls_drained"]


def test_prefix_family_certifies_nothing_at_1000_31():
    pw = _load("prefix_witness")
    out = pw.prefix_family(1000, 31, verbose=False)
    assert out["closed_form_rates_verified_exactly"]
    assert not out["full_transfer_feasible"]
    assert out["positive_gain_cells"] == {}
    assert abs(out["theta_lp_gain_float"]) < 1e-9
    assert out["rationalized_feasible_by_enclosure"] and out["rationalized_moment_identities_exact"]
    assert out["rough_spike_T_gain"] == 0.0
