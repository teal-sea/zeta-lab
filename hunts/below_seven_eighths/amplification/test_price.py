"""Hunt #136, lane b78-amplification: every number on LOSS_MAP.md and guo_h11.md is pinned here.

Exact throughout (Fractions, quadratic-field numbers, sympy root isolation); the float LP and
the float cut search in price.py only propose, and every bracket is re-decided exactly.
Planted faults show that the reproductions, the decision procedure, Liu's reconstruction
and the markdown gate can each go red.

Run from the repository root:

    .venv/bin/python -m pytest -n 4 hunts/below_seven_eighths/amplification/test_price.py
"""
from __future__ import annotations

import importlib.util
import re
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

_spec = importlib.util.spec_from_file_location("b78_amplification_price", HERE / "price.py")
pr = importlib.util.module_from_spec(_spec)
sys.modules["b78_amplification_price"] = pr
_spec.loader.exec_module(pr)

S921 = sp.sqrt(921)
HAVE_SOURCES = all(path.is_file() for path, _ in pr.SOURCES.values())
L = pr.LEVEL_RECORD


def sym(v):
    if isinstance(v, pr.Quad):
        return v.sympy()
    if isinstance(v, Fr):
        return sp.Rational(v.numerator, v.denominator)
    return v


def same(a, b) -> bool:
    return sp.simplify(sym(a) - sym(b)) == 0


@pytest.fixture(scope="module")
def H():
    return pr.headline_numbers()


@pytest.fixture(scope="module")
def CURVE():
    return pr.curve()


@pytest.fixture(scope="module")
def THETA():
    return pr.theta_curve()


# ------------------------------------------------------------------ sources

@pytest.mark.skipif(not HAVE_SOURCES, reason="pinned source files are not in this cache")
def test_sources_hash_and_citations():
    assert all(pr.verify_sources().values()), pr.verify_sources()
    assert pr.verify_citations() == []


# ------------------------------------------------------------- the counts

LAWS = [pr.PAPER_LAW, pr.GUO_LAW, pr.Law.slope(Fr(1, 2)), pr.Law.threshold(Fr(4, 5))]


def test_excess_is_the_minimisation_over_t():
    """price.excess equals min over t in [1, 3/2] of max{R_short, L} at 380 bins, 4 laws."""
    n = 0
    for law in LAWS:
        for i in range(1, 20):
            for j in range(0, 5):
                d, x = Fr(i, 24), Fr(j, 8)
                assert 1 - d + pr.excess(d, x, law, pr.C_PAPER) == pr.rstar_bruteforce(d, x, law, pr.C_PAPER)
                n += 1
    assert n == 380


def test_excess_reproduces_the_printed_counts():
    for i in range(1, 20):
        for j in range(0, 5):
            d, x = Fr(i, 24), Fr(j, 8)
            D, P = pr.counts(x, pr.C_PAPER)
            J = (Fr(5, 6) - d) * D + d * P
            # paper line 16019 and Liu line 8438 at kappa = 3/4
            assert pr.excess(d, x, pr.PAPER_LAW, pr.C_PAPER) == (Fr(5, 6) - d) * d * P / (2 * J)
            # Guo lines 73 to 75: T_99, and t_99 is the crossing
            J99 = (Fr(33, 40) - d) * D + d * P
            if d < Fr(97, 120):
                assert pr.excess(d, x, pr.GUO_LAW, pr.C_PAPER) == (Fr(97, 120) - d) * d * P / (2 * J99)
                t99 = 1 + (D / 120 + d * P / 2) / J99
                rshort = 1 - d + d * P / D * (Fr(3, 2) - t99)
                longc = Fr(1, 6) + (Fr(33, 40) - d) * t99
                assert rshort == longc == 1 - d + pr.excess(d, x, pr.GUO_LAW, pr.C_PAPER)
    # the paper's printed D_x, P_x at c = 4/9 (line 15192)
    assert pr.counts(Fr(1, 2), pr.C_PAPER) == (Fr(37, 18), Fr(7, 9))


def test_amplified_exponents():
    assert pr.PAPER_LAW.e(1) == 1 and pr.PAPER_LAW.e(Fr(9, 8)) == Fr(53, 48) and pr.PAPER_LAW.e(Fr(3, 2)) == Fr(17, 12)
    assert pr.GUO_LAW.alpha == Fr(33, 40) and pr.GUO_LAW.e0 == Fr(1, 6) and pr.GUO_LAW.delta_e == Fr(97, 120)
    assert (1 - pr.GUO_LAW.e0) / pr.GUO_LAW.alpha == Fr(100, 99)       # the kink of e_99
    th = pr.Law.threshold(Fr(2, 3))
    assert (1 - th.e0) / th.alpha == Fr(3, 2) and th.delta_e == 0     # ideal counts on r <= 3/2
    assert pr.Law.slope(0).delta_e == 0


# ---------------------------------------------------- system P, regime A

def test_regime_A_reproduces_B_alg(H):
    assert same(H["P_T"], (1507 - 2 * S921) / 1653)
    assert same(H["P_delta"], (49 - S921) / 48)
    assert same(H["P_ell"], sp.Rational(11, 551) + 8 * S921 / 1653)
    assert same(H["P_b"], sp.Rational(-4, 29) + 230 * S921 / 26709)     # Liu v1's b, FOLLOWUPS.md
    assert same(H["P_mu"], (73 + S921) / 551)
    assert same(H["P_d_alpha"], sp.Rational(7414, 303601) - 181690 * S921 / 279616521)
    assert same(H["P_d_eta"], (S921 - 478) / 551)
    assert same(H["P_d_theta"], sp.Rational(22490, 910803) + 99110 * S921 / 279616521)
    d = H["P_delta"]
    assert (288 * d * d - 588 * d + 185) == 0
    assert same(Fr(3, 4) + 3 * d / 2, (73 - S921) / 32)


def test_regime_A_derivatives_by_finite_differences(H):
    eps = Fr(1, 10 ** 9)
    for key, law_of in (("P_d_alpha", pr.Law.slope), ("P_d_theta", None)):
        if law_of is None:
            up = pr.regime_A_P(pr.Law.threshold(1 + eps)).target
            dn = pr.regime_A_P(pr.Law.threshold(1 - eps)).target
        else:
            up = pr.regime_A_P(law_of(Fr(5, 6) + eps)).target
            dn = pr.regime_A_P(law_of(Fr(5, 6) - eps)).target
        fd = (float(up.mp(40)) - float(dn.mp(40))) / (2 * float(eps))
        assert abs(fd - float(H[key])) < 1e-6
    up = pr.regime_A_P(pr.PAPER_LAW, eta=eps).target
    assert abs((float(up.mp(40)) - float(H["P_T"].mp(40))) / float(eps) - float(H["P_d_eta"])) < 1e-6


def test_alpha_eta_theta_needed_in_regime_A(H):
    a = H["P_alpha_record"]
    assert a == Fr(144263243506939, 179612914571532)
    ra = pr.regime_A_P(pr.Law.slope(a))
    assert ra.target == pr.Quad(L) and ra.notes["b_positive"] and ra.notes["gram_ok"]
    assert pr.regime_A_P(pr.Law.slope(H["P_alpha_xu_sang"])).target == pr.Quad(pr.LEVEL_XU_SANG)
    assert pr.regime_A_P(pr.PAPER_LAW, eta=Fr(0)).target - H["P_eta_record"] * (1 - H["P_mu"]) == pr.Quad(L)
    t = H["P_theta_record"]
    assert t == Fr(1292195122714234, 1297609308016905)
    assert pr.regime_A_P(pr.Law.threshold(t)).target == pr.Quad(L)


@pytest.mark.parametrize("frame", ["P0", "P2"])
def test_alpha_needed_is_bracketed_by_sandwiches(frame, H):
    a = H["P_alpha_record"]
    lo = pr.sandwich(pr.SystemP(frame, pr.Law.slope(a - Fr(1, 10 ** 9))))
    hi = pr.sandwich(pr.SystemP(frame, pr.Law.slope(a + Fr(1, 10 ** 9))))
    assert lo.ub <= L < hi.lb


def test_alpha_needed_in_P1_bracket():
    lo, hi = pr.P1_ALPHA_RECORD
    assert pr.sandwich(pr.SystemP("P1", pr.Law.slope(lo))).ub <= L < pr.sandwich(pr.SystemP("P1", pr.Law.slope(hi))).lb
    assert hi - lo < Fr(1, 10 ** 10)


def test_sandwich_brackets_B_alg_and_hunt_134_bounds(H):
    s = pr.sandwich(pr.SystemP("P0"))
    assert pr.Quad(s.lb) <= H["P_T"] <= pr.Quad(s.ub) and s.width < Fr(1, 10 ** 12)
    assert Fr(5655673, 6464057) < s.lb and Fr(44117, 50422) < s.lb < Fr(7, 8)
    ok, _ = pr.feasible(pr.SystemP("P0"), pr.PAPER_GEOMETRY)
    assert ok and pr.SystemP("P0").target(pr.PAPER_GEOMETRY) == Fr(7, 8)


# ------------------------------------------------------------ the price curve

CURVE_TABLE = {
    "P0": ["0.8749570698", "0.8748931216", "0.8747921786", "0.8745098039", "0.8739158273",
           "0.8722266776", "0.8704255897", "0.8667826048", "13/15"],
    "P1": ["0.8749570698", "0.8748931216", "0.8747946020", "0.8745531405", "0.8741661871",
           "0.8739028246", "0.8739028246", "0.8739028246", "84031/96156"],
    "P2": ["0.8749570698", "0.8748931216", "0.8747921786", "0.8745098039", "0.8739322471",
           "0.8727977179", "0.8723425934", "0.8723425934", "368153/422028"],
}


def _shown_ok(s, want) -> bool:
    """A table cell agrees with a sandwich: either an exact fraction equal to the lower end
    and met by the upper end to 10^-15, or 10 decimals on which both ends agree."""
    if "/" in want:
        return str(s.lb) == want and s.ub - s.lb < Fr(1, 10 ** 15)
    return pr.d10(s.lb) == pr.d10(s.ub) == want


def test_price_curve_table(CURVE):
    for fr, row in CURVE_TABLE.items():
        for al, want in zip(pr.CURVE_ALPHAS, row):
            s = CURVE[(fr, al)]
            assert s.width < Fr(1, 10 ** 12)
            assert _shown_ok(s, want), (fr, al, float(s.lb), want)
    assert pr.regime_A_P(pr.Law.slope(Fr(3, 4))).target == pr.Quad(Fr(223, 255))
    assert pr.regime_A_P(pr.Law.slope(Fr(3, 4))).delta == pr.Quad(Fr(37, 96))
    assert float(CURVE[("P0", Fr(1, 100))].lb) > 13 / 15


def test_thirteen_fifteenths(CURVE):
    assert CURVE[("P0", Fr(0))].lb == Fr(13, 15)
    s = pr.sandwich(pr.SystemP("P0", pr.Law.slope(Fr(1, 1000))))
    assert s.lb > Fr(13, 15)
    assert pr.sandwich(pr.SystemP("P0", pr.Law.threshold(Fr(2, 3)))).lb == Fr(13, 15)
    assert CURVE[("P1", Fr(0))].lb == Fr(84031, 96156) and CURVE[("P2", Fr(0))].lb == Fr(368153, 422028)
    # the minimiser of the floor relaxation fails the endpoint once alpha > 0
    S = pr.SystemP("P0", pr.Law.slope(Fr(1, 1000)))
    assert S.negE((Fr(1, 5), Fr(4, 5), Fr(0)), Fr(1, 2000), Fr(1, 2)) < 0


def test_liu_frames_near_thirteen_fifteenths():
    s = pr.sandwich(pr.SystemL("L1", pr.Law.slope(Fr(1, 2)), Fr(3, 4)))
    assert s.lb == Fr(437, 500) and float(s.ub) - 0.874 < 1e-12
    assert pr.sandwich(pr.SystemL("L1", pr.Law.slope(Fr(0)), Fr(3, 4))).lb == Fr(437, 500)
    assert pr.sandwich(pr.SystemL("L0", pr.Law.slope(Fr(1, 8)), Fr(3, 4))).lb == Fr(13, 15)
    assert pr.sandwich(pr.SystemL("L0", pr.Law.slope(Fr(1, 7)), Fr(3, 4))).lb > Fr(13, 15)


# ------------------------------------------------------------- Liu's system

def test_liu_reconstruction_is_exact():
    d, k, ell, b = sp.symbols("delta kappa ell b")
    c = 1 / (3 * k)
    D = 3 - (1 + 2 * c) / 2
    P = (2 - c) / 2
    J = (sp.Rational(5, 6) - d) * D + d * P
    X = (sp.Rational(5, 6) - d) * d * P / (2 * J)
    h = (1 + b + 3 * ell) / 2
    ly = (1 + b - ell) / 2
    E = (-sp.Rational(1, 4) + b / 6 + 5 * ell / 4 + d / 2 + (d / 2) * (ell + c * (h / 4 - ly / 2))
         - sp.Rational(3, 4) * h * (d - X))
    num = sp.numer(sp.together(sp.diff(E, b)))
    cr = pr.liu_cr(d, k)
    assert sp.simplify(num + 2 * cr) == 0
    mine = (5 - 6 * d) / (9 + 6 * d + 6 * c * d)
    diff = sp.numer(sp.together(pr.liu_ell_star_formula(d, k) - mine))
    assert sp.rem(sp.Poly(sp.expand(diff), d), sp.Poly(sp.expand(cr), d)).is_zero
    poly = pr._sym_liu_fixed_point_poly(pr.PAPER_LAW)
    kk = poly.gens[0]
    quartic = sp.Poly(16686 * kk ** 4 - 27405 * kk ** 3 + 9936 * kk ** 2 + 1290 * kk - 275, kk)
    assert sp.rem(poly, quartic).is_zero


def test_liu_fixed_point_and_prices(H):
    klo, khi, fac = pr.liu_fixed_point()
    Bq = lambda B: 133488 * B ** 4 - 376596 * B ** 3 + 384534 * B ** 2 - 167541 * B + 26231
    blo, bhi = (1 + klo) / 2, (1 + khi) / 2
    assert Bq(blo) * Bq(bhi) < 0 and bhi - blo < Fr(1, 10 ** 30)
    assert pr.d10(H["L_B"]) == "0.8748866470" and pr.d10(H["L_kappa"]) == "0.7497732941"
    assert 23 / 50 < float(H["L_delta"]) < 12 / 25                     # Liu, line 9707
    assert H["L_lambda"] >= 1.068 and 0 < H["L_F_kappa"] <= 0.0065 / 4  # Liu, lines 9763 and 9968
    one = pr.regime_A_L(pr.PAPER_LAW, Fr(3, 4))
    assert one.delta == pr.Quad(Fr(1519, 1434), Fr(-1, 1434), 715621)
    assert pr.liu_cr(one.delta, Fr(3, 4)) == 0
    assert pr.liu_ell_star_formula(one.delta, Fr(3, 4)) == one.ell


def test_liu_sandwich_matches_closed_form():
    ra = pr.regime_A_L(pr.PAPER_LAW, Fr(3, 4))
    for frame in ("L0", "L1"):
        s = pr.sandwich(pr.SystemL(frame, pr.PAPER_LAW, Fr(3, 4)))
        assert pr.Quad(s.lb) <= ra.target <= pr.Quad(s.ub)


def test_liu_alpha_needed(H):
    aL, kL = H["L_alpha_record"], H["L_kappa_record"]
    assert kL == Fr(3748087, 5000000) and kL < Fr(7497, 10000)
    assert pr.regime_A_L(pr.Law.slope(aL), kL).target == pr.Quad(L)
    a7 = H["L_alpha_record_7497"]
    assert pr.regime_A_L(pr.Law.slope(a7), Fr(7497, 10000)).target == pr.Quad(L)
    lo = pr.sandwich(pr.SystemL("L1", pr.Law.slope(a7 - Fr(1, 10 ** 9)), Fr(7497, 10000)))
    hi = pr.sandwich(pr.SystemL("L1", pr.Law.slope(a7 + Fr(1, 10 ** 9)), Fr(7497, 10000)))
    assert lo.ub <= L < hi.lb
    # the step at kappa = 7497/10000 is justified once a bound <= 17497/20000 is known:
    # one step at kappa = 3/4 already gives it at this alpha
    assert pr.regime_A_L(pr.Law.slope(a7), Fr(3, 4)).target <= Fr(17497, 20000)
    assert pr.regime_A_L(pr.Law.slope(H["L_alpha_record_3_4"]), Fr(3, 4)).target == pr.Quad(L)
    assert pr.regime_A_L(pr.Law.threshold(H["L_theta_record"]), 2 * L - 1).target == pr.Quad(L)
    eta = H["L_eta_record"]
    # eta enters ell* linearly at a fixed critical bin
    assert abs(float(pr.regime_A_L(pr.PAPER_LAW, 2 * L - 1, eta=Fr(str(float(eta)))).target) - float(L)) < 1e-12


# ------------------------------------------------------------- threshold door

THETA_TABLE = {
    "P0": ["0.8749570698", "0.8745999251", "0.8731166301", "0.8711593646", "0.8689826891", "0.8672523186", "13/15"],
    "P2": ["0.8749570698", "0.8745999251", "0.8731348699", "0.8723425934", "0.8723425934", "0.8723425934",
           "0.8723425934"],
}
TRIVIAL = ["11/12", "73/80", "43/48", "7/8", "61/72", "13/16", "7/9"]


def test_threshold_table(THETA, H):
    for fr, row in THETA_TABLE.items():
        for th, want in zip(pr.THETA_GRID, row):
            s = THETA[(fr, th)]
            assert s.width < Fr(1, 10 ** 12)
            assert _shown_ok(s, want), (fr, th, float(s.lb), want)
    assert [str(pr.trivial_route_abscissa(th)) for th in pr.THETA_GRID] == TRIVIAL
    assert pr.d10(H["L_guo_B"]) == "0.8744476409" and pr.d10(H["L_guo_kappa"]) == "0.7488952817"
    assert same(H["P_guo_T"], sp.Rational(2305, 2529) - 8 * sp.sqrt(22906) / 32877)


@pytest.mark.parametrize("frame", ["P0", "P2"])
def test_theta_needed_is_bracketed_by_sandwiches(frame, H):
    t = H["P_theta_record"]
    lo = pr.sandwich(pr.SystemP(frame, pr.Law.threshold(t - Fr(1, 10 ** 9))))
    hi = pr.sandwich(pr.SystemP(frame, pr.Law.threshold(t + Fr(1, 10 ** 9))))
    assert lo.ub <= L < hi.lb


def test_theta_crossover_brackets():
    for frame, (lo, hi) in (("P0", pr.THETA_CROSS_P0), ("P2", pr.THETA_CROSS_P2)):
        s_lo = pr.sandwich(pr.SystemP(frame, pr.Law.threshold(lo)))
        s_hi = pr.sandwich(pr.SystemP(frame, pr.Law.threshold(hi)))
        assert s_lo.lb > pr.trivial_route_abscissa(lo)      # trivial route smaller below
        assert s_hi.ub < pr.trivial_route_abscissa(hi)      # assembly smaller above
        assert hi - lo < Fr(1, 10 ** 8)


# ------------------------------------------------------------------ Guo

def test_guo_328_375():
    ell, b = pr.GUO_ELL, pr.GUO_B
    assert (1 - b - ell) / 2 == Fr(361, 1000) and (1 + b - ell) / 2 == Fr(471, 1000)
    assert (1 + b + 3 * ell) / 2 == Fr(807, 1000) and Fr(11, 12) - ell / 4 == Fr(328, 375)
    assert pr.guo_identity_holds()
    assert all(a == b for a, b in pr.GUO_SQUARES)
    assert pr.guo_bound_holds()
    rg = pr.regime_A_P(pr.GUO_LAW)
    assert Fr(1, 6) <= rg.ell.bracket(20)[0] and rg.ell.bracket(20)[1] <= Fr(17, 100)
    assert Fr(1, 10) <= rg.b.bracket(20)[0] and rg.b.bracket(20)[1] <= Fr(13, 100)
    assert rg.target < pr.Quad(Fr(328, 375))


def test_guo_bound_is_not_vacuous():
    """Planted fault: a margin far above the true minimum is refused."""
    h = (1 + pr.GUO_B + 3 * pr.GUO_ELL) / 2
    A0 = -(Fr(-1, 4) + pr.GUO_B / 6 + 5 * pr.GUO_ELL / 4)
    ok, _ = pr.rectangle_min_ok(A0, pr.GUO_B / 2 + pr.GUO_ELL / 2, -pr.GUO_ELL, h, pr.GUO_LAW, pr.C_PAPER,
                                Fr(0), Fr(3, 4), margin=Fr(1, 100))
    assert not ok


def test_trivial_route_values():
    assert pr.trivial_route_abscissa(1) == Fr(11, 12)
    assert pr.trivial_route_abscissa(Fr(99, 100)) == Fr(73, 80)
    assert pr.trivial_route_abscissa(Fr(9, 10)) == Fr(7, 8)
    assert pr.trivial_route_abscissa(Fr(2, 3)) == Fr(7, 9)
    assert Fr(1, 2) + Fr(99, 100) / 2 == Fr(199, 200) and 1 + Fr(99, 100) == Fr(199, 100)
    # the W_a contradiction threshold: 73/80 - a < 1/2
    assert Fr(73, 80) - Fr(33, 80) == Fr(1, 2) and Fr(3, 8) < Fr(33, 80)


# ------------------------------------------------------------ loss-map support

def test_maxplus_amplification_is_tight():
    for r, want in ((Fr(1), Fr(1)), (Fr(9, 8), Fr(53, 48)), (Fr(3, 2), Fr(17, 12))):
        dual, primal = pr.amplification_maxplus(r, 1)
        assert dual == primal == want == pr.PAPER_LAW.e(r)


def test_sixth_power_invariance_enumeration():
    r = pr.invariance_group_check(5000, 3000)
    assert r["elements"] == 18144 and r["sixth_powers"] == 3
    assert r["sixth_power_with_nontrivial_symbol"] == [] and r["non_sixth_power_without_witness"] == []


def test_ideal_count_ratio():
    assert pr.d10(pr.ideal_count_ratio(10 ** 4), 4) == "0.3027"


def test_rivals():
    assert pr.d10(pr.rival_Wa_diagonal(0.4, 20000), 1) == "8.6"
    assert pr.d10(pr.rival_Wa_diagonal(0.45, 20000), 1) == "7.3"
    a = pr.epstein_multiplicativity_defect()
    assert a[1] == 1 and a[6] == 2 and a[2] * a[3] == 0


def test_two_decision_procedures_agree_at_the_paper_point():
    S = pr.SystemP("P0")
    z = pr.PAPER_GEOMETRY
    A0, A1c, A1x, w = S.rectangle_data(z, "endpoint")
    for m, want in ((Fr(0), True), (Fr(49, 440640), True), (Fr(1, 4000), False)):
        a, _ = pr.rectangle_min_ok(A0, A1c, A1x, w, S.law, S.c, Fr(0), Fr(5, 6), margin=m)
        b, _ = pr.rectangle_min_ok_cells(A0, A1c, A1x, w, S.law, S.c, Fr(0), Fr(5, 6), margin=m)
        assert a == b == want
    assert pr.feasible(S, z, margin=Fr(228147, 10 ** 9))[0]
    assert not pr.feasible(S, z, margin=Fr(228148, 10 ** 9))[0]
    assert S.negE(z, Fr(79, 204), Fr(1, 2)) == Fr(7, 30672) > Fr(228148, 10 ** 9)


# ------------------------------------------------------------- planted faults

def test_planted_fault_wrong_slope_breaks_B_alg():
    bad = pr.regime_A_P(pr.Law.slope(Fr(5, 6) + Fr(1, 100))).target
    assert not same(bad, (1507 - 2 * S921) / 1653)


def test_planted_fault_wrong_weight_breaks_liu_cr():
    d, k, ell, b = sp.symbols("delta kappa ell b")
    c = 1 / (3 * k)
    D = 3 - (1 + 2 * c) / 2
    P = (2 - c) / 2
    J = (sp.Rational(5, 6) - d) * D + d * P
    X = (sp.Rational(5, 6) - d) * d * P / (2 * J)
    h = (1 + b + 3 * ell) / 2
    ly = (1 + b - ell) / 2
    E = (-sp.Rational(1, 4) + b / 6 + 5 * ell / 4 + d / 2 + (d / 2) * (ell + c * (h / 4 - ly / 2)) - h * (d - X))
    num = sp.numer(sp.together(sp.diff(E, b)))
    assert sp.simplify(num + 2 * pr.liu_cr(d, k)) != 0


# ------------------------------------------------------------- markdown gate

MD = [HERE / "LOSS_MAP.md", HERE / "guo_h11.md"]
TOKEN = re.compile(r"(?<![\w.^/])(\d+/10\^\d+|\d+\.\d+|\d+/\d+)(?![\w.^/])")

#: section, lemma and theorem labels (each occurrence must follow one of these words)
LABELS = {"2.1", "2.2", "2.3", "2.4", "2.5", "3.1", "1.3", "1.4", "11.1", "11.2", "17.1", "17.6", "18.1", "19.1"}
LABEL_WORDS = ("Lemma", "Proposition", "Theorem", "Hypothesis", "section", "###", "Section")

#: constants taken from the sources or from the task, each checked against a citation or the model
def _cited_constants() -> dict:
    c = pr.CITATIONS
    snip = lambda k: c[k][2]
    return {
        "5/6": pr.PAPER_LAW.alpha == Fr(5, 6) and r"\frac56" in snip("alpha_def"),
        "1/6": pr.GUO_LAW.e0 == Fr(1, 6) and "(H/U)^{1/6}" in snip("H_P"),
        "7/8": r"\frac78" in snip("E_d"),
        "11/12": pr.trivial_route_abscissa(1) == Fr(11, 12),
        "13/15": pr.LEVEL_13_15 == Fr(13, 15),
        "3/4": "3/4" in snip("guo_criterion"),
        "1/2": "1/2" in snip("guo_criterion"),
        "1/3": pr.regime_A_P().delta > Fr(1, 3),
        "2/3": "(KD)^{2/3}" in snip("sextic_large_sieve"),
        "1/4": "-1/4" in snip("guo_endpoint"),
        "1/5": pr.SystemL().linear_constraints()[1][1]((Fr(1, 5), Fr(0))) == 0,
        "1/8": r"\delta\ge1/8" in snip("liu_one_eighth"),
        "3/2": "(3/2-t)" in snip("R_short"),
        "4/9": pr.C_PAPER == Fr(4, 9),
        "1/50": Fr(1, 50) == pr.SystemP("P1").dmin,
        "51/100": Fr(51, 100) == (1 + pr.SystemP("P1").dmin) / 2,
        "76/75": r"\frac{76}{75}" in snip("intermediate_R"),
        "7/37": r"\frac7{37}" in snip("supply"),
        "437/500": "437/500" in snip("liu_admissible_1"),
        "0.874": Fr(437, 500) == Fr(874, 1000),
        "7497/10000": "7497/10000" in snip("liu_kappa_range"),
        "99/100": "D^{99/100}" in snip("guo_hypothesis_range"),
        "101/100": "D^{101/100}" in snip("guo_hypothesis_range"),
        "100/99": (1 - pr.GUO_LAW.e0) / pr.GUO_LAW.alpha == Fr(100, 99),
        "33/40": "33r/40" in snip("guo_e99"),
        "97/120": "97/120" in snip("guo_T99"),
        "21/125": "21/125" in snip("guo_geometry"),
        "11/100": "11/100" in snip("guo_geometry"),
        "361/1000": (1 - pr.GUO_B - pr.GUO_ELL) / 2 == Fr(361, 1000),
        "471/1000": (1 + pr.GUO_B - pr.GUO_ELL) / 2 == Fr(471, 1000),
        "807/1000": (1 + pr.GUO_B + 3 * pr.GUO_ELL) / 2 == Fr(807, 1000),
        "328/375": "328/375" in snip("guo_conditional"),
        "7/42768": "7/42768" in snip("guo_bound"),
        "1/10": "1/10" in snip("guo_family"),
        "13/100": r"\frac{13}{100}" in snip("guo_box_b"),
        "17/100": "17}{100" in snip("guo_box"),
        "49/440640": r"\frac{49}{440640}" in snip("endpoint_bound"),
        "79/204": True,  # hunt #134's worst point, checked in test_two_decision_procedures_agree
        "7/30672": True,  # checked in test_two_decision_procedures_agree_at_the_paper_point
        "5655673/6464057": True,  # hunt #134, checked in test_sandwich_brackets_B_alg
        "44117/50422": True,  # hunt #134, checked in test_sandwich_brackets_B_alg
        "9/10": pr.trivial_route_abscissa(Fr(9, 10)) == Fr(7, 8),
        "19/20": Fr(19, 20) in pr.THETA_GRID,
        "41/50": Fr(41, 50) in pr.CURVE_ALPHAS,
        "4/5": Fr(4, 5) in pr.CURVE_ALPHAS,
        "1/100": Fr(1, 100) in pr.CURVE_ALPHAS,
        "3/8": True,  # the rival gate's threshold, from the task
        "33/80": Fr(73, 80) - Fr(33, 80) == Fr(1, 2),
        "5/12": pr.trivial_route_abscissa(Fr(12, 5)) == 1 + Fr(1, 2),
        "73/80": True, "7/9": True, "43/48": True, "61/72": True, "13/16": True,  # test_trivial_route_values
        "199/200": True, "199/100": True,  # test_trivial_route_values
        "9/8": True, "53/48": True, "17/12": True,  # test_maxplus_amplification_is_tight
        "223/255": True, "37/96": True,  # test_price_curve_table
        "84031/96156": True, "368153/422028": True,  # test_thirteen_fifteenths
        "1/4000": True, "228147/10^9": True, "228148/10^9": True,  # test_two_decision_procedures
        "8748087/10^7": L == Fr(8748087, 10 ** 7),
        "0.8748087": L == Fr(8748087, 10 ** 7),
        "0.8748867": pr.LEVEL_XU_SANG == Fr(8748867, 10 ** 7),
        "3748087/5000000": 2 * L - 1 == Fr(3748087, 5000000),
        "5/3": "Q^{5/3}" in snip("by_cubic_bound"),
        "4/3": "Q^{4/3}" in snip("by_cubic_bound"),
        "11/9": "Q^{11/9}" in snip("by_cubic_bound"),
        "12/5": "M^{12/5}" in snip("by_cubic_bound"),
        "0.4": True, "0.45": True, "8.6": True, "7.3": True,  # test_rivals (measured)
        "0.3027": True,  # test_ideal_count_ratio
    }


def _computed_strings(H, CURVE, THETA) -> set:
    out = set()
    for v in H.values():
        for w in (v, -v):
            try:
                out.add(pr.d10(w))
            except Exception:
                pass
        if isinstance(v, Fr):
            out.add(str(abs(v)))
        if isinstance(v, pr.Quad):
            out.add(str(abs(v.p)))
    for s in list(CURVE.values()) + list(THETA.values()):
        out.add(pr.d10(s.lb))
    for lo, hi in (pr.P1_ALPHA_RECORD, pr.THETA_CROSS_P0, pr.THETA_CROSS_P2):
        out |= {pr.d10(lo), pr.d10(hi), str(lo), str(hi)}
    out.add(pr.d10(abs(H["P_ratio_eta_alpha"])))
    out.add(pr.d10(H["L_d_alpha"] / float(H["P_d_alpha"]), 2))
    out.add(pr.d10(pr.Quad(Fr(73, 32), Fr(-1, 32), 921)))
    return out


def _unpinned(texts, H, CURVE, THETA) -> list:
    computed = _computed_strings(H, CURVE, THETA)
    cited = {k for k, ok in _cited_constants().items() if ok}
    bad = []
    for text in texts:
        for m in TOKEN.finditer(text):
            tok = m.group(1)
            if tok in LABELS:
                before = text[max(0, m.start() - 14):m.start()]
                if any(wd in before for wd in LABEL_WORDS):
                    continue
            if tok in computed or tok in cited:
                continue
            bad.append(tok)
    return bad


def test_every_number_on_both_pages_is_pinned(H, CURVE, THETA):
    texts = [p.read_text(encoding="utf-8") for p in MD]
    assert _unpinned(texts, H, CURVE, THETA) == []


def test_planted_fault_md_gate_goes_red(H, CURVE, THETA):
    texts = [p.read_text(encoding="utf-8") for p in MD]
    assert _unpinned([texts[0] + "\nslope 0.0047006136\n"], H, CURVE, THETA) == ["0.0047006136"]
    assert _unpinned([texts[0].replace("0.8031897030", "0.8031897031", 1)], H, CURVE, THETA) == ["0.8031897031"]


def test_the_cited_constants_all_check():
    bad = [k for k, ok in _cited_constants().items() if not ok]
    assert bad == []


def test_no_reserved_word_and_no_long_dashes():
    for p in [HERE / "price.py", HERE / "test_price.py"] + MD:
        raw = p.read_bytes().lower()
        assert b"cert" + b"ified" not in raw and b"cert" + b"ificat" not in raw, p.name
        assert chr(0x2014).encode() not in raw and chr(0x2013).encode() not in raw, p.name


def test_pages_state_the_central_numbers():
    t = (HERE / "LOSS_MAP.md").read_text(encoding="utf-8")
    for s in ("(1507 - 2 sqrt 921)/1653", "0.0047006135", "-0.8124356047", "0.8031897030", "0.8028731275",
              "0.0073713973", "0.8229295767", "0.8229135719", "84031/96156", "368153/422028", "13/15"):
        assert s in t, s
    g = (HERE / "guo_h11.md").read_text(encoding="utf-8")
    for s in ("328/375", "73/80", "199/200", "0.8745999251", "45529856", "13108397936", "1763264"):
        assert s in g, s
