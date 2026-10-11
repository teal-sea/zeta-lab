"""Pins for every number `hardy_first_zero`'s MISSION.md and RESULTS.md state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/hardy_first_zero

Everything is recomputed here from `sizing.py`; nothing is read back from
`artifacts/`, and nothing is written into the tree (the mirror module is loaded with
bytecode writing switched off). The planted faults at the bottom are the reason the
other tests mean anything: a remainder bound that a wrong main term also satisfied, a
sign test that passed on an interval with no zero, or a box layer that decided the sign
at a hopeless Taylor order would each make the pins above worthless.

Nothing here bears on RH (`docs/08`).
"""
from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

import mpmath
import pytest
from mpmath import mp

from hunts.hardy_first_zero import gen_boxes as G
from hunts.hardy_first_zero import sizing as S

HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean" / "HardyFirstZero"
A, B = S.A, S.B


@pytest.fixture(autouse=True)
def _restore_mpmath_precision():
    saved = mp.prec
    yield
    mp.prec = saved


def rel(x, y):
    return abs(x - y) / abs(y)


# ---------------------------------------------------------------------------
# The target interval and the endpoint values of Z
# ---------------------------------------------------------------------------


def test_the_interval_contains_the_first_ordinate_and_nothing_else_known():
    assert A == Fraction(1413, 100) and B == Fraction(707, 50)
    assert float(A) < S.GAMMA_1 < float(B)
    assert B - A == Fraction(1, 100)


@pytest.mark.parametrize("backend", ["python-flint", "mpmath.iv"])
def test_endpoint_signs_by_two_backends(backend):
    lo_a, hi_a = S.z_enclosure(A, backend)
    lo_b, hi_b = S.z_enclosure(B, backend)
    assert lo_a <= hi_a < 0 < lo_b <= hi_b
    assert rel(lo_a, -0.0037463383557063) < 1e-12
    assert rel(lo_b, 0.0041856189735666) < 1e-12


def test_the_slope_and_the_theta_increment():
    with mp.workdps(30):
        g1 = mpmath.findroot(mpmath.siegelz, S.GAMMA_1)
        assert abs(g1 - mpmath.mpf("14.134725141734693790457251983562")) < 1e-25
        assert abs(mpmath.diff(mpmath.siegelz, g1) - mpmath.mpf("0.793160433")) < 1e-9
    assert abs(S.theta_increment(A, B) - 0.0040528408849156) < 1e-14


def test_the_true_product_of_the_two_zeta_values():
    ra = S.zeta_arb(A)
    rb = S.zeta_arb(B)
    with mp.workdps(40):
        za = mpmath.mpc((ra[0] + ra[1]) / 2, (ra[2] + ra[3]) / 2)
        zb = mpmath.mpc((rb[0] + rb[1]) / 2, (rb[2] + rb[3]) / 2)
        reX = float(mpmath.re(za * mpmath.conj(zb)))
        # |zeta(1/2 + it)| = |Z(t)|, a check that shares nothing with Z's phase
        assert abs(abs(za) - 0.0037463383557063) < 1e-15
        assert abs(abs(zb) - 0.0041856189735666) < 1e-15
    assert rel(reX, -1.568060e-5) < 1e-5


# ---------------------------------------------------------------------------
# Euler-Maclaurin: the bound holds, and what truncation decides the sign
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "N, bound_a, defect_a",
    [(10, 7.6146e-3, 1.3228e-3), (20, 5.5701e-4, 1.1315e-4), (30, 1.26796e-4, 2.7207e-5)],
)
def test_order4_bound_holds_against_arb(N, bound_a, defect_a):
    with mp.workdps(40):
        ba = float(S.em4_bound(S.s_of(A), N))
        bb = float(S.em4_bound(S.s_of(B), N))
    da = float(S.em_error_upper(A, N))
    db = float(S.em_error_upper(B, N))
    assert rel(ba, bound_a) < 1e-4
    assert rel(da, defect_a) < 1e-3
    assert da < ba / 4 and db < bb / 4  # the bound holds with a factor 4 to spare


def test_the_planned_truncation_and_its_margin():
    d = S.decision(A, B, S.N_PLAN, 4)
    assert S.N_PLAN == 30
    assert d["passes"]
    assert rel(d["re_main_product"], -1.56742e-5) < 1e-4
    assert rel(d["slack"], 1.02309e-6) < 1e-4
    assert abs(d["margin"] - 15.32) < 0.01


def test_minimal_truncations_at_order_4():
    assert {m: S.min_N(A, B, 4, m) for m in (1, 2, 4, 10)} == {1: 15, 2: 18, 4: 21, 10: 27}
    assert abs(S.decision(A, B, 15, 4)["margin"] - 1.0077) < 1e-3


@pytest.mark.slow
def test_minimal_truncation_at_order_2_is_the_lab_trapezoid_cost():
    assert S.min_N(A, B, 2, 1) == 471
    assert abs(S.decision(A, B, 500, 2)["margin"] - 1.112) < 1e-3
    assert not S.decision(A, B, 30, 2)["passes"]


@pytest.mark.slow
def test_trade_table_digits_against_terms():
    rows = S.trade_table()
    got = {r["digits"]: r["N_for_margin"] for r in rows}
    assert got == {
        2: {"1": 15, "2": 18, "4": 21, "10": 27},
        3: {"1": 30, "2": 36, "4": 42, "10": 55},
        4: {"1": 57, "2": 69, "4": 81, "10": 106},
        5: {"1": 102, "2": 121, "4": 145, "10": 187},
        6: {"1": 242, "2": 281, "4": 338, "10": 439},
    }
    for r in rows:  # every interval brackets a sign change
        assert r["Z_a"] < 0 < r["Z_b"]


# ---------------------------------------------------------------------------
# The phase window from Euler's limit
# ---------------------------------------------------------------------------


def test_phase_window_numbers():
    w = S.phase_window(A, B)
    assert w["delta"] == pytest.approx(0.005, abs=1e-15)
    assert w["K"] == pytest.approx(49.94955, abs=1e-9)
    assert w["upper"] == pytest.approx(0.0307236, abs=1e-7)
    assert w["lower"] == pytest.approx(-0.4987801, abs=1e-7)
    assert w["upper_crude"] == pytest.approx(0.0357080, abs=1e-7)
    assert w["lower_crude"] == pytest.approx(-0.5045038, abs=1e-7)
    assert w["cos_floor"] == pytest.approx(0.87541, abs=1e-5)
    # the Lean instantiation uses L = 11/20
    assert max(-w["lower_crude"], w["upper_crude"]) < 11 / 20 < w["half_pi"]


def test_partial_phases_converge_to_the_theta_increment():
    want = {1: 0.00586997, 10: -0.00279266, 100: -0.00400319, 1000: -0.00404897}
    for n, v in want.items():
        assert S.phase_partial(A, B, n) == pytest.approx(v, abs=1e-8)
    limit = -S.theta_increment(A, B)
    assert abs(S.phase_partial(A, B, 1000) - limit) < 5e-6
    # and the limit is the argument of pi^(i delta) Gamma(z) Gamma(w) itself
    with mp.workdps(30):
        al, be = mpmath.mpf(1413) / 200, mpmath.mpf(707) / 100
        V = (mpmath.exp(mpmath.mpc(0, (be - al) * mpmath.log(mpmath.pi)))
             * mpmath.gamma(mpmath.mpc(0.25, al)) * mpmath.gamma(mpmath.mpc(0.25, -be)))
        assert abs(mpmath.arg(V) - limit) < 1e-15  # limit is a float


def test_every_partial_phase_sits_in_the_derived_window():
    w = S.phase_window(A, B)
    for n in list(range(1, 60)) + [100, 500, 2000]:
        assert w["lower"] <= S.phase_partial(A, B, n) <= w["upper"]


# ---------------------------------------------------------------------------
# The box arithmetic, through the lab's mirror
# ---------------------------------------------------------------------------


def test_mirror_boxes_decide_the_sign_at_the_planned_parameters():
    m = S.mirror_sizing()
    assert m["passes"]
    assert 3e-9 < m["box_width_a"] < 4e-9 and 3e-9 < m["box_width_b"] < 4e-9
    assert m["max_term_width"] < 2.2e-10
    assert m["re_product_upper"] == pytest.approx(-1.45539e-5, rel=1e-4)
    assert m["re_product_lower"] == pytest.approx(-1.68590e-5, rel=1e-4)
    assert m["max_endpoint_bits"] == 97


def test_generated_boxes_match_the_generator_and_decide_the_sign():
    M, out = G.tables()
    assert float(G.final_check(M, out)) == pytest.approx(-1.37863e-5, rel=1e-4)
    assert G.eps(G.POINTS["A"]) == Fraction(1091, 5000000)
    assert G.eps(G.POINTS["B"]) == Fraction(547, 2500000)
    assert G.c_const(G.POINTS["A"]) == (Fraction(613663909, 1439329680),
                                        Fraction(-16642146167, 7996276000))
    assert (LEAN / "Boxes.lean").read_text(encoding="utf-8") == G.render(out)


def test_crude_radii_against_the_sharp_bound():
    with mp.workdps(40):
        for t in (A, B):
            ratio = float(G.eps(t)) / float(S.em4_bound(S.s_of(t), 30))
            assert 1.70 < ratio < 1.74


def test_lean_size_as_stated():
    sizes = {p.name: len(p.read_text(encoding="utf-8").splitlines()) for p in LEAN.glob("*.lean")}
    assert sizes["Boxes.lean"] == 837
    assert 2100 <= sum(sizes.values()) <= 2300


def test_dead_route_scales():
    d = S.dead_route_scales()
    assert d["abs_gamma_quarter"] == pytest.approx(2.32927e-5, rel=1e-5)
    assert d["lambda_real"] == pytest.approx(-6.55451e-8, rel=1e-5)
    assert d["lambda_imag_abs"] < 1e-20
    assert d["theta_integral_scale"] == pytest.approx(0.0115169, rel=1e-5)


# ---------------------------------------------------------------------------
# The Lean files: what RESULTS.md calls kernel-checked is what is on disk
# ---------------------------------------------------------------------------


def _lean_text() -> str:
    return "\n".join(p.read_text(encoding="utf-8") for p in sorted(LEAN.glob("*.lean")))


def test_lean_files_carry_no_sorry_no_axiom_and_no_reserved_word():
    text = _lean_text()
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)  # docstrings may discuss the rule
    code = re.sub(r"--.*", "", code)
    assert not re.search(r"\bsorry\b", code)
    assert not re.search(r"^\s*axiom\b", code, flags=re.M)
    assert not re.search(r"\bnative_decide\b", code)
    assert "certif" not in text.lower()


def test_lean_statements_named_in_results_exist():
    text = _lean_text()
    for name in ("theorem exists_zero_of_sign_data", "theorem gammaR_re_pos ",
                 "theorem gammaR_re_pos_first", "lemma Vn_polar", "lemma le_phi",
                 "lemma phi_le", "theorem corrected_trapezoid", "theorem zeta_em4_error",
                 "theorem em30_bound", "theorem zeta_product_re_neg",
                 "theorem first_zero_on_line :"):
        assert name in text, name
    assert "refine gammaR_re_pos (L := 11 / 20)" in text
    assert "sOf (1413 / 100)" in text and "sOf (707 / 50)" in text


# ---------------------------------------------------------------------------
# Planted faults: each of these must go red, or the pins above are decoration
# ---------------------------------------------------------------------------


def test_fault_wrong_sign_of_the_bernoulli_term_breaks_the_bound():
    with mp.workdps(40):
        bound = S.em4_bound(S.s_of(A), 30)
    assert S.em_error_upper(A, 30) < bound
    assert S.em_error_upper(A, 30, b2_sign=-1) > 10 * bound


def test_fault_missing_half_term_breaks_the_bound():
    with mp.workdps(40):
        bound = S.em4_bound(S.s_of(A), 30)
    assert S.em_error_upper(A, 30, half_term=False) > 10 * bound


def test_control_an_interval_without_a_zero_does_not_pass():
    lo, hi = Fraction(1412, 100), Fraction(1413, 100)
    d = S.decision(lo, hi, 30, 4)
    assert not d["passes"] and d["re_main_product"] > 0


def test_lesion_a_low_log_order_cannot_decide():
    m = S.mirror_sizing(nLog=16)
    assert not m["passes"]


def test_lesion_ten_times_the_remainder_cannot_decide(monkeypatch):
    M, out = G.tables()
    real_eps = G.eps
    monkeypatch.setattr(G, "eps", lambda T: 10 * real_eps(T))
    assert G.final_check(M, out) > 0


def test_fault_dropping_the_log_n_normalization_leaves_the_window():
    w = S.phase_window(A, B)
    n = 10_000
    unnormalized = S.phase_partial(A, B, n) + float(w["delta"]) * float(mpmath.log(n))
    assert unnormalized > w["upper"]
