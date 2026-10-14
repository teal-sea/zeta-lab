"""Pins for every number `hardy_ten_zeros`'s MISSION.md and RESULTS.md state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/hardy_ten_zeros

Everything is recomputed here from `sizing.py` and `gen_boxes.py`; nothing is read back
from `artifacts/`, and nothing is written into the tree. The planted faults and lesions
at the bottom are the reason the other tests mean anything: a remainder bound that a
wrong main term also satisfied, a sign test that passed on an interval with no zero, a
composite box that held any value, or radii with no slack to lose would each make the
pins above worthless.

Nothing here bears on RH (`docs/08`), and nothing here says which zeros these are.
"""
from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

import mpmath
import pytest
from mpmath import mp

from hunts.hardy_first_zero import sizing as S1
from hunts.hardy_ten_zeros import gen_boxes as G
from hunts.hardy_ten_zeros import sizing as S

HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean" / "HardyTenZeros"
TAGS = ("2102", "2501", "3042", "3293", "3758", "4091", "4332", "4800", "4977")
PLAN = {"2102": (27, 20), "2501": (39, 23), "3042": (31, 30), "3293": (33, 32),
        "3758": (35, 37), "4091": (38, 59), "4332": (37, 46), "4800": (45, 47),
        "4977": (55, 50)}


@pytest.fixture(autouse=True)
def _restore_mpmath_precision():
    saved = mp.prec
    yield
    mp.prec = saved


@pytest.fixture(scope="module")
def plan_rows():
    return S.plan()


@pytest.fixture(scope="module")
def built(plan_rows):
    M = S1.load_mirror()
    return {r["tag"]: G.build(r, M) for r in plan_rows}


# ---------------------------------------------------------------------------
# The ordinates and the brackets
# ---------------------------------------------------------------------------


def test_ordinates_match_the_stated_values_and_the_ground_truth():
    g = [float(x) for x in S.ordinates()]
    for got, stated in zip(g, S.STATED):
        assert abs(got - stated) < 5e-7
    # CLAUDE.md, ground truth
    assert abs(g[0] - 14.134725141734694) < 1e-12
    assert abs(g[1] - 21.022039638771555) < 1e-12
    assert abs(g[2] - 25.010857580145689) < 1e-12


def test_brackets_are_disjoint_ordered_short_and_below_fifty():
    brs = S.brackets()
    assert [S.tag(a) for a, _ in brs] == ["1413", *TAGS]
    assert brs[0] == (Fraction(1413, 100), Fraction(707, 50))  # hunt #132's interval
    for (a, b), g in zip(brs, S.ordinates()):
        assert b - a == Fraction(1, 100)
        assert float(a) < float(g) < float(b)
        assert 0 < a and b < 50
    for (_, b0), (a1, _) in zip(brs, brs[1:]):
        assert b0 < a1


@pytest.mark.parametrize("backend", ["python-flint", "mpmath.iv"])
def test_every_bracket_has_a_sign_change_of_Z_by_two_backends(backend):
    for a, b in S.brackets():
        lo_a, hi_a = S1.z_enclosure(a, backend)
        lo_b, hi_b = S1.z_enclosure(b, backend)
        assert lo_a <= hi_a and lo_b <= hi_b
        assert hi_a < 0 < lo_b or hi_b < 0 < lo_a


def test_pinned_endpoint_values_of_Z():
    want = {Fraction(2501, 100): -0.0011762, Fraction(4092, 100): 0.0019092,
            Fraction(4977, 100): 0.0054312, Fraction(4978, 100): -0.0087688}
    for t, z in want.items():
        lo, hi = S1.z_enclosure(t, "python-flint")
        assert abs(lo - z) < 5e-8 and hi - lo < 1e-15


# ---------------------------------------------------------------------------
# The phase windows
# ---------------------------------------------------------------------------


def test_hunt_132_window_leaves_the_quarter_turn_from_the_fourth_bracket():
    inside = [S.window_132(a, b)["inside_quarter_turn"] for a, b in S.brackets()]
    assert inside == [True, True, True] + [False] * 7
    assert S.window_132(Fraction(3042, 100), Fraction(3043, 100))["lower"] == pytest.approx(-2.3135, abs=1e-4)
    assert S.window_132(Fraction(4977, 100), Fraction(4978, 100))["lower"] == pytest.approx(-6.1932, abs=1e-4)


def test_tail_window_and_its_lean_instantiation():
    for a, b in S.brackets():
        w = S.window_tail(a, b)
        assert w["inside_quarter_turn"]
        # the Lean instantiation's crude window holds the true one, inside L = 1/5
        assert w["lower_lean"] <= w["lower"] and w["upper"] <= w["upper_lean"]
        assert max(-w["lower_lean"], w["upper_lean"]) < float(S.PHASE_L) < float(mpmath.pi / 2)
    w = S.window_tail(Fraction(4977, 100), Fraction(4978, 100))
    assert w["lower"] == pytest.approx(-0.0581, abs=1e-4)
    assert w["lower_lean"] == pytest.approx(-0.088876, abs=1e-6)
    assert w["upper_lean"] == pytest.approx(0.035708, abs=1e-6)


@pytest.mark.parametrize("tg", ["2102", "4977"])
def test_partial_phases_sit_in_the_tail_window_and_converge(tg):
    a = Fraction(int(tg), 100)
    b = a + Fraction(1, 100)
    w = S.window_tail(a, b)
    for n in list(range(S.PHASE_M, 60)) + [100, 1000, 5000]:
        assert w["lower"] <= S1.phase_partial(a, b, n) <= w["upper"]
    limit = -S.theta_increment(a, b)
    assert abs(S1.phase_partial(a, b, 20000) - limit) < 1e-5


def test_keeping_the_hunt_132_window_would_cost_more_terms():
    d = S.old_window_alternative()
    assert d["window_132"]["inside_quarter_turn"]
    assert d["window_132"]["lower"] == pytest.approx(-1.2386, abs=1e-4)
    assert d["Z_a"][0] == pytest.approx(0.0014645, abs=1e-7)
    assert d["Z_b"][0] == pytest.approx(-0.0013733, abs=1e-7)
    assert (d["N_a"], d["N_b"], d["terms"], d["towers"]) == (80, 83, 163, 45)
    # against the two-decimal bracket the sharpened window allows
    assert PLAN["4977"] == (55, 50) and S.towers(55, 50) == 31


def test_true_phase_increments_are_small():
    incs = [S.theta_increment(a, b) for a, b in S.brackets()]
    assert max(incs) == pytest.approx(0.010348, abs=1e-6)
    assert all(0 < x < 0.011 for x in incs)


# ---------------------------------------------------------------------------
# The truncations, the radii, and the order comparison
# ---------------------------------------------------------------------------


def test_planned_truncations(plan_rows):
    got = {r["tag"]: (r["N_a"], r["N_b"]) for r in plan_rows}
    assert got == PLAN
    assert sum(na + nb for na, nb in got.values()) == 684


def test_lean_radii_are_what_the_side_conditions_need(plan_rows):
    for r in plan_rows:
        for side, t, N in (("a", r["a"], r["N_a"]), ("b", r["b"], r["N_b"])):
            rad = r["rad_" + side]
            assert rad["r"] ** 2 <= N - 1 < (rad["r"] + Fraction(1, 10**6)) ** 2
            assert S.q4(t) <= rad["R"] ** 2
            exact = rad["R"] / (Fraction(N - 1) ** 3 * rad["r"] * Fraction(7, 2) * 720)
            assert exact <= rad["e"] < exact + Fraction(1, 10**12)
            # and the Lean radius is the sharp order-4 bound up to rounding
            with mp.workdps(30):
                sharp = float(S.em_bound(t, N))
            assert 1 < float(rad["e"]) / sharp < 1 + 1e-5


def test_exact_squared_norm_against_the_triangle_inequality_at_fifty():
    """TenSupport.lean's docstring: the exact squared norm is worth about 1.16 at t = 50."""
    T = Fraction(50)
    tri = (Fraction(1, 2) + T) * (Fraction(3, 2) + T) * (Fraction(5, 2) + T) * (Fraction(7, 2) + T)
    ratio = float(tri) / float(S.q4(T)) ** 0.5
    assert ratio == pytest.approx(1.16, abs=0.005)


def test_arb_defect_sits_inside_every_radius(plan_rows):
    d = S.defect_vs_radius(plan_rows)
    assert len(d) == 18
    ratios = [v["ratio"] for v in d.values()]
    assert all(r > 1 for r in ratios)  # the kill condition does not fire
    assert min(ratios) == pytest.approx(6.85, abs=0.01)
    assert max(ratios) == pytest.approx(14.94, abs=0.01)


def test_order_comparison():
    c = S.order_comparison()
    t = c["totals"]
    assert (t["order4_lean"], t["order4_sharp"], t["order6_sharp"], t["order8_sharp"]) == (684, 684, 334, 246)
    assert (t["order4_lean_towers"], t["order6_sharp_towers"], t["order8_sharp_towers"]) == (219, 131, 103)
    m = c["projected_kernel_minutes"]
    assert m["order4_lean"] == pytest.approx(11.16, abs=0.01)
    assert m["order6_sharp"] == pytest.approx(6.68, abs=0.01)
    assert m["order8_sharp"] == pytest.approx(5.25, abs=0.01)


def test_the_margin_costs_about_eleven_percent():
    assert S.margin_cost() == {"1.0": 615, "1.5": 684}


def test_kE_8_covers_the_primes_up_to_157_at_49_78():
    d = S.exp_range_limit()
    nb = d["normBound"]
    assert nb[151] < nb[157] < 256 < nb[163] < nb[167]
    assert nb[157] == pytest.approx(254.228, abs=1e-3)


def test_tower_and_composite_counts(plan_rows):
    towers = sum(1 for r in plan_rows for N in (r["N_a"], r["N_b"])
                 for m in range(2, N + 1) if G.spf(m) == m)
    comps = sum(1 for r in plan_rows for N in (r["N_a"], r["N_b"])
                for m in range(2, N + 1) if G.spf(m) != m)
    assert (towers, comps) == (219, 447)
    assert towers == sum(S.towers(r["N_a"], r["N_b"]) for r in plan_rows)


# ---------------------------------------------------------------------------
# The boxes, through the lab's mirror, and the generated files
# ---------------------------------------------------------------------------


def test_generated_files_match_the_generator_and_decide_the_sign(built):
    want_hi = {"2102": -7.202475e-06, "4091": -8.599096e-06, "4977": -1.313675e-05}
    for tg, d in built.items():
        assert d["hi"] < 0 and d["hi_margin"] < 0
        if tg in want_hi:
            assert float(d["hi"]) == pytest.approx(want_hi[tg], rel=1e-5)
        assert G.path_for(tg).read_text(encoding="utf-8") == G.render(d)


def test_boxes_contain_the_true_terms(built):
    d = built["4977"]
    with mp.workdps(30):
        s = mpmath.mpc(0.5, mpmath.mpf(4977) / 100)
        for m in (2, 6, 12, 29, 53, 55):
            v = mpmath.power(m, -s)
            bx = d["ta"][m]
            assert float(bx.re.lo) <= float(v.real) <= float(bx.re.hi)
            assert float(bx.im.lo) <= float(v.imag) <= float(bx.im.hi)
            assert float(bx.re.hi - bx.re.lo) < 3e-8


# ---------------------------------------------------------------------------
# The Lean files: what RESULTS.md calls kernel-checked is what is on disk
# ---------------------------------------------------------------------------


def _lean_text() -> str:
    files = sorted(LEAN.glob("*.lean")) + [HERE / "lean" / "CheckAxioms.lean"]
    return "\n".join(p.read_text(encoding="utf-8") for p in files)


def test_lean_files_carry_no_sorry_no_axiom_and_no_reserved_word():
    text = _lean_text()
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    assert not re.search(r"\bsorry\b", code)
    assert not re.search(r"^\s*axiom\b", code, flags=re.M)
    assert not re.search(r"\bnative_decide\b", code)
    assert "certif" not in text.lower()


def test_lean_files_have_module_headers_and_fit_the_cap():
    for p in sorted(LEAN.glob("*.lean")) + [HERE / "lean" / "CheckAxioms.lean"]:
        text = p.read_text(encoding="utf-8")
        assert text.startswith("module\n"), p.name
        assert len(text.splitlines()) < 2000, p.name


def test_lean_statements_named_in_results_exist():
    text = _lean_text()
    for name in ("theorem ten_zeros_on_line_below_fifty :", "lemma le_phi_tail",
                 "theorem window_132_fails_at_4977",
                 "theorem gammaR_re_pos_tail", "theorem gammaR_re_pos_short",
                 "theorem emN_bound", "theorem zeta_mem_mainBox", "theorem zero_of_tables",
                 "theorem contains_cpow_mul_coarsen", "theorem cBox_contains"):
        assert name in text, name
    for tg in TAGS:
        a = int(tg)
        assert (f"theorem zero_in_{tg} :\n    ∃ t ∈ Set.Ioo ({a} / 100 : ℝ) ({a + 1} / 100), "
                "riemannZeta (1 / 2 + t * I) = 0") in text
    assert "StrictMono ts" in text and "ts k < 50" in text


def test_no_first_ten_wording():
    """The result is at least ten zeros, not the first ten: no file may say otherwise."""
    for p in list(HERE.rglob("*.md")) + list(HERE.rglob("*.lean")) + list(HERE.rglob("*.py")):
        if p.name == Path(__file__).name:
            continue
        text = p.read_text(encoding="utf-8").lower()
        assert "first ten" not in text, p
        assert "first_ten" not in text, p


# ---------------------------------------------------------------------------
# Planted faults and lesions: each of these must go red, or the pins above are decoration
# ---------------------------------------------------------------------------


def test_fault_wrong_sign_of_the_bernoulli_term_breaks_the_bound_at_49_77():
    t = Fraction(4977, 100)
    with mp.workdps(40):
        bound = S1.em4_bound(S1.s_of(t), 55)
    assert S1.em_error_upper(t, 55) < bound
    assert S1.em_error_upper(t, 55, b2_sign=-1) > 9 * bound
    assert S1.em_error_upper(t, 55, half_term=False) > 20 * bound


def test_control_an_interval_without_a_zero_does_not_pass():
    lo, hi = Fraction(4970, 100), Fraction(4971, 100)
    assert S1.z_enclosure(lo, "python-flint")[0] > 0 and S1.z_enclosure(hi, "python-flint")[0] > 0
    with pytest.raises(ValueError):
        S.choose_truncations(lo, hi, 4, True, n_max=80)


def test_lesion_a_low_log_order_cannot_decide(plan_rows, monkeypatch):
    monkeypatch.setattr(G, "NLOG", 16)
    d = G.build(next(r for r in plan_rows if r["tag"] == "4977"))
    assert d["hi"] > 0


def test_lesion_twice_the_radii_cannot_decide(built):
    M = S1.load_mirror()
    failed = 0
    for d in built.values():
        Ma = G.main_box(M, d["ta"], d["N_a"], d["a"])
        Mb = G.main_box(M, d["tb"], d["N_b"], d["b"])
        hi = G.prod_hi(M, M.cinflate(Ma, 2 * d["rad_a"]["e"]), M.cinflate(Mb, 2 * d["rad_b"]["e"]))
        failed += hi > 0
    assert failed == 9


def test_fault_a_wrong_composite_factorization_misses_the_term(built):
    M = S1.load_mirror()
    d = built["3042"]
    wrong = M.ccoarsen(G.P, M.cmul(d["ta"][2], d["ta"][3]))  # claims 7 = 2 * 3
    with mp.workdps(30):
        v = mpmath.power(7, -mpmath.mpc(0.5, mpmath.mpf(3042) / 100))
    inside = (float(wrong.re.lo) <= float(v.real) <= float(wrong.re.hi)
              and float(wrong.im.lo) <= float(v.imag) <= float(wrong.im.hi))
    assert not inside


def test_fault_the_hunt_132_window_at_the_last_bracket():
    w = S.window_132(Fraction(4977, 100), Fraction(4978, 100))
    assert -w["lower"] > float(mpmath.pi / 2)
