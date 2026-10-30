"""Hunt #136, assembly lane: every number ASSEMBLY.md states is pinned here.

Exact throughout: Fractions, the quadratic-field numbers `assembly.QF`, and sympy for
real-root isolation and Sturm counts.  The float LP in assembly.py only proposes active
sets; the brackets below are re-decided here from stored witnesses (a dual witness for
each lower end, a rational geometry checked on the whole (delta, x) rectangle for each
upper end).  Planted faults show that the reproductions, the sampler, the rectangle check,
the rows at d < h, the witnesses and the markdown gate can each go red.

Revised after verifier round 1 (2026-10-21): the intermediate row covers delta <= alpha
only, the sampler is Sturm-guarded, and the markdown gate reads signs and checks the
tables of ASSEMBLY.md sections 4 to 6 cell by cell.  Repair pass: every paper line the page
names is a checked citation, the alpha axis is compared with the verifier's recorded
independent LP values, the inner-row check is planted at d = d_min for the bins
delta >= alpha, and Lemma marked's second width condition is read at both amplitude ends.
"""
from __future__ import annotations

import math
import os
import random
import re
import sys
from dataclasses import replace
from fractions import Fraction as Fr

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import assembly as A  # noqa: E402

sp = pytest.importorskip("sympy")
from mpmath import mp, mpf  # noqa: E402

S921 = sp.sqrt(921)
S518 = sp.sqrt(518)
S22829 = sp.sqrt(22829)
SIGMA_STAR = (sp.Integer(1507) - 2 * S921) / 1653
X = sp.Symbol("x")


def qsym(v):
    """sympy value of a QF, Fraction or sympy number."""
    if isinstance(v, A.QF):
        return v.sympy()
    if isinstance(v, Fr):
        return sp.Rational(v.numerator, v.denominator)
    return v


def same(a, b):
    return sp.simplify(qsym(a) - qsym(b)) == 0


def close(v, x, tol):
    return abs(float(v) - x) < tol


def rat(v, q=10**14):
    """A rational close to an exact QF value."""
    return Fr(str(v.mp(30))).limit_denominator(q)


@pytest.fixture(scope="module")
def base():
    return A.regime_A()


# --------------------------------------------------------------- the controls

def test_every_printed_constant_is_reproduced():
    reps = A.reproductions()
    assert len(reps) == 72
    assert [r["name"] for r in reps if not r["ok"]] == []


def test_every_citation_names_a_line():
    assert len(A.CITATIONS) == 123
    for n, snip in A.CITATIONS.values():
        assert 1 <= n <= 16677 and snip


def _md_paper_lines(text):
    """Paper line numbers named in the text: 'line N', 'lines N to M', 'lines N, M and K',
    and the last column of the symbol table of section 1."""
    nums = set()
    for m in re.finditer(r"\blines? ((?:\d{3,5}(?:,? (?:and |to )?)?)+)", text):
        nums |= {int(v) for v in re.findall(r"\d{3,5}", m.group(1))}
    for row in text.splitlines():
        if row.startswith("| `") and row.count("|") >= 5:
            nums |= {int(v) for v in re.findall(r"\b\d{3,5}\b", row.strip().strip("|").split("|")[-1])}
    return nums


def test_every_line_the_md_cites_is_a_citation():
    """Each paper line ASSEMBLY.md names is a key line of assembly.CITATIONS, so
    test_citations_against_the_pinned_source checks it against the pinned file."""
    nums = _md_paper_lines(_md())
    assert len(nums) >= 40
    cited = {n for n, _ in A.CITATIONS.values()}
    assert sorted(n for n in nums if n not in cited) == []
    # planted: a line the page does not cite is caught, in prose and in a range
    for extra in ("\nsee line 16147.\n", "\n(lines 16146 to 16147)\n"):
        assert sorted(n for n in _md_paper_lines(_md() + extra) if n not in cited) == [16147]


@pytest.mark.skipif(not A.DEFAULT_PAPER.exists(), reason="pinned paper.tex not on this machine")
def test_citations_against_the_pinned_source():
    assert A.verify_citations(A.DEFAULT_PAPER) == []


def test_target_is_seven_eighths_at_the_paper_geometry():
    assert A.target(A.ELL_PAPER, A.M_PAPER, A.B_PAPER) == Fr(7, 8)
    # and the two stages lie on one formula: 11/12 with no slots
    assert A.target(Fr(0), Fr(1), Fr(0)) == Fr(11, 12)


def test_the_papers_own_bookkeeping_gives_exactly_seven_eighths():
    fr = A.FROZEN_PAPER_BOOKKEEPING
    cert = A.lower_bound_from(A.PAPER, fr, [("low",), ("int", Fr(5, 6)), ("end", Fr(899, 2250), Fr(1, 2)),
                                            ("per_summand",)])
    assert cert["lb"] == Fr(7, 8)
    assert A.achievable_upper(A.ELL_PAPER, A.M_PAPER, A.B_PAPER, A.PAPER, fr, slack=Fr(0)) == Fr(7, 8)


def test_endpoint_margin_and_worst_point():
    ell, M, b = A.ELL_PAPER, A.M_PAPER, A.B_PAPER
    worst = A.neg_E_star(Fr(79, 204), Fr(1, 2), ell, M, b)
    assert worst == Fr(7, 30672)
    assert Fr(49, 176256) / Fr(5, 2) == Fr(49, 440640) < worst
    # the witness's bound is a lower bound on a grid, never violated
    for i in range(1, 41):
        for j in range(0, 6):
            assert A.neg_E_star(Fr(5, 6) * Fr(i, 40), Fr(j, 10), ell, M, b) >= Fr(49, 440640)


def test_hunt_134_reoptimisation_controls():
    assert Fr(3, 25) == Fr("0.12")
    assert A.robust_single_point_bound(Fr(223, 576), Fr(1, 2)) == Fr(5655673, 6464057)
    assert close(Fr(5655673, 6464057), 0.8749417, 5e-8)
    assert A.gram_limited_single_point_bound(Fr(7, 18), Fr(1, 2)) == Fr(44117, 50422)
    s, ell, d = A.fixed_b_optimum_exact(Fr(3, 25))
    sv = sp.N(s, 40)
    assert abs(sv - sp.Rational(874958, 10**6)) < sp.Rational(5, 10**7)      # #134's scan at b = 0.12
    assert abs(sv - sp.Rational(8749576643, 10**10)) < sp.Rational(1, 10**10)
    sf, _, _ = A.fixed_b_optimum(Fr(3, 25))                                    # 40-digit float route
    assert abs(float(sf) - float(sv)) < 1e-14


def test_perfect_count_ceiling():
    assert A.perfect_count_ceiling(Fr(0))["sigma"] == Fr(13, 15)
    pc = A.perfect_count_ceiling(Fr(1, 50))
    assert pc["sigma"] == Fr(167, 192)
    assert pc["checks"]["floor"] == 0
    assert A.ceiling_no_intermediate(Fr(0))["lb"] == Fr(13, 15)
    assert A.ceiling_no_intermediate(Fr(1, 50))["lb"] == Fr(167, 192)
    # the decimal renderings ASSEMBLY.md prints
    assert close(Fr(167, 192), 0.8697916667, 5e-11) and close(Fr(13, 15), 0.8666666667, 5e-11)
    assert close(SIGMA_STAR, 0.8749570698, 5e-11)
    assert round(float(SIGMA_STAR), 5) == 0.87496                                # "a target near 0.87496"


# ------------------------------------------------------- the exact optimum

def test_regime_A_closed_form(base):
    assert same(base["sigma"], SIGMA_STAR)
    assert same(base["delta"], (49 - S921) / 48)
    assert same(base["ell"], sp.Rational(11, 551) + 8 * S921 / 1653)
    assert same(base["b"], sp.Rational(-4, 29) + 230 * S921 / 26709)
    assert same(base["K"], sp.Rational(11, 8) - S921 / 24)
    assert close(base["sigma"], 0.8749570698, 5e-11)
    assert close(base["ell"], 0.1668383875, 5e-11) and close(base["b"], 0.1234054370, 5e-11)
    assert close(base["h"], 0.8119602997, 5e-11)
    assert close(base["mu"], 0.1875643953, 5e-11) and close(base["nu"], 0.0625214651, 5e-11)
    # the row-norm reading it needs: M - 2 ell below 1/2 (so the per-summand reading fails)
    assert base["M"] - 2 * base["ell"] < Fr(1, 2)
    assert close(base["M"] - 2 * base["ell"], 0.4994848376, 5e-11)
    # the closed form for the row inputs alone agrees
    rho, coeffs, sg = A.regime_A_formula_row_inputs()
    assert rho == Fr(37, 14) and coeffs == (Fr(-16, 7), Fr(14, 3), Fr(-185, 126))
    assert same(sg, SIGMA_STAR)
    # the rho form holds away from the paper's inputs too
    for th in (A.Inputs(c_M=Fr(51, 100), c_P=Fr(1, 4), alpha=Fr(4, 5)), A.Inputs(c_P=Fr(1, 3))):
        assert same(A.regime_A_formula_row_inputs(th)[2], A.regime_A(th)["sigma"])


def test_regime_A_is_the_optimum_exactly(base):
    cert = A.regime_A_witness(base)
    assert cert["lb"] == base["sigma"]                       # an exact lower bound
    assert all(r == 0 for r in cert["residual"])
    assert all(w > 0 for w in cert["weights"])
    ell = Fr(str(base["ell"].mp(30))).limit_denominator(10**15)
    b = Fr(str(base["b"].mp(30))).limit_denominator(10**15)
    ub = A.achievable_upper(ell, 1 - ell, b, A.PAPER, A.FROZEN, slack=Fr(1, 10**14))
    assert ub is not None and ub > base["sigma"] and ub - base["sigma"] < Fr(2, 10**14)
    # the rows at d < h have room there too, although n = 1/2 does not need the check
    assert A.inner_rows_ok(ell, 1 - ell, b, ub)
    sl = A.regime_A_slacks(base)
    assert all(v > 0 for v in sl.values())
    for key, val in (("x_boundary", 0.0091161574), ("floor", 0.0058792912),
                     ("intermediate", 0.0026581589), ("supply", 0.0132242767)):
        assert close(sl[key], val, 5e-10)


def test_float_proposals_and_exact_sandwich_agree(base):
    sw = A.sandwich()
    assert sw["lb"] <= base["sigma"] <= sw["ub"]
    assert sw["ub"] - sw["lb"] < Fr(2, 10**8)


def test_tied_capacity_reproduces_guo():
    lo, hi = A.tied_capacity_fixed_point()
    assert hi - lo <= Fr(1, 10**18)
    assert Fr(8749570194200989453, 10**19) < lo < hi < Fr(8749570194200989463, 10**19)
    assert int(lo * 10**10) == 8749570194 == int(A.GUO * 10**10)
    assert close(lo, 0.87495701942, 5e-12)                       # the rendering ASSEMBLY.md prints


# ------------------------------------------------------------ shadow prices

SHADOW = {
    "z_p": (sp.Rational(-254, 551) - 5869 * S921 / 507471, -0.8119602997),
    "n_num": (sp.Rational(66721, 1821606) + 623353 * S921 / 838849563, 0.0591792953),
    "g": (sp.Rational(-1071, 15979) + 56812 * S921 / 14716659, 0.0501294854),
    "c_M": (sp.Rational(-12348, 303601) + 286552 * S921 / 279616521, -0.0095710837),
    "alpha": (sp.Rational(7414, 303601) - 181690 * S921 / 279616521, 0.0047006135),
    "c_P": (sp.Rational(-5103, 607202) + 19737 * S921 / 93205507, -0.0019776984),
    "R_fl": (sp.Integer(0), 0.0),
}
ELASTICITY = {"z_p": -0.135327, "g": 0.008355, "c_M": -0.004786, "alpha": 0.003917,
              "c_P": -0.000439, "R_fl": 0.0, "n_num": 0.029590}


def test_shadow_prices_exact(base):
    sh = A.regime_A_shadow_prices(base)
    for k, (exact, val) in SHADOW.items():
        assert same(sh[k], exact), k
        assert close(sh[k], val, 5e-11), k
        assert close(Fr(getattr(A.PAPER, k)) * sh[k], ELASTICITY[k], 5e-7), k
    assert same(sh["z_p"], -base["h"])
    assert same(sh["n_num"], base["mu"] * base["h"] * base["delta"])
    # "the numerator cost is worth about six times more per unit (ratio 6.18)"
    ratio = abs(float(sh["n_num"]) / float(sh["c_M"]))
    assert 6 < ratio < 6.5 and round(ratio, 2) == 6.18


def _sigma_mp(th):
    return A.regime_A(th)["sigma"].mp(50)


@pytest.mark.parametrize("name", ["c_M", "c_P", "alpha", "g", "z_p", "n_num"])
def test_shadow_prices_by_finite_differences(base, name):
    """Independent route: re-solve the closed form at the input plus and minus 10^-9."""
    eps = Fr(1, 10**9)
    v = Fr(getattr(A.PAPER, name))
    with mp.workdps(50):
        fd = (_sigma_mp(A.with_input(name, v + eps)) - _sigma_mp(A.with_input(name, v - eps))) / (2 * mpf(1e-9))
    assert abs(float(fd) - float(A.regime_A_shadow_prices(base)[name])) < 1e-8


def test_ranking(base):
    sh = A.regime_A_shadow_prices(base)
    ranked = sorted(sh, key=lambda k: -abs(float(sh[k])))
    assert ranked == ["z_p", "n_num", "g", "c_M", "alpha", "c_P", "R_fl"]


# --------------------------------------------- the first break on each axis

BREAKS = {   # name: (value, failing constraint, sigma there)
    "z_p": (0.1751510556, ["floor"], 0.8679871838),
    "n_num": (0.4908887159, ["intermediate"], 0.8744203215),
    "g": (0.1567188215, ["floor"], 0.8743819388),
    "c_M": (0.5361872194, ["supply"], 0.8745985237),
    "alpha": (0.6098049914, ["b_nonneg"], 0.8733861759),
    "c_P": (0.5261221985, ["x_boundary"], 0.8740683460),
}
BREAK_WORDS = {"z_p": "the floor bin", "n_num": "the intermediate range", "g": "the floor bin",
               "c_M": "the supply hypothesis", "alpha": "b reaches 0", "c_P": "x leaves 1/2"}


@pytest.mark.parametrize("name", list(BREAKS))
def test_regime_A_break(name):
    ok, bad, failing = A.regime_A_break(name)
    v, fail, s_there = BREAKS[name]
    assert failing == fail
    assert abs(bad - ok) <= Fr(1, 10**10)
    assert close(ok, v, 2e-10)
    assert close(A.regime_A(A.with_input(name, ok))["sigma"], s_there, 5e-10)


def test_c_M_break_without_the_uniform_supply_hypothesis():
    ok, bad, failing = A.regime_A_break("c_M", A.Frozen(supply="off"))
    assert failing == ["x_boundary"] and close(ok, 0.5468059250, 2e-10)


# ------------------------------------------------ what each input must reach

CROSS_A = {  # (name, level): input value where sigma_A crosses the level (regime A)
    ("z_p", "xu_sang"): 0.1667533220,
    ("n_num", "xu_sang"): 0.4988101977,
    ("g", "xu_sang"): 0.1652928246,
    ("c_M", "xu_sang"): 0.5073016702,
    ("alpha", "xu_sang"): 0.8186903585,
    ("c_P", "xu_sang"): 0.2565018832,
    ("z_p", "0.87"): 0.1727198769,
}


@pytest.mark.parametrize("key", list(CROSS_A))
def test_regime_A_crossings(key):
    name, lab = key
    level = A.LEVELS[lab]
    ok, _, _ = A.regime_A_break(name)
    va, vb = A.regime_A_crossing(name, level, ok)
    assert abs(vb - va) <= Fr(1, 10**12)
    assert close(va, CROSS_A[key], 1e-10)
    for v in (va, vb):                        # regime A is the optimum at both ends
        _, sol, sl = A.regime_A_on_axis(name, v)
        assert all(x >= 0 for x in sl.values())
    assert A.regime_A(A.with_input(name, va))["sigma"] > level > A.regime_A(A.with_input(name, vb))["sigma"]


XU_SANG_CHANGE = {"z_p": 0.0000866553, "n_num": -0.0011898023, "g": -0.0013738421,
                  "c_M": 0.0073016702, "alpha": -0.0146429748, "c_P": 0.0342796610}


def test_xu_sang_improvements_needed():
    """The changes alone that beat 0.8748867, as stated in ASSEMBLY.md."""
    for k, want in XU_SANG_CHANGE.items():
        assert close(CROSS_A[(k, "xu_sang")] - float(getattr(A.PAPER, k)), want, 2e-10), k


#: stored witnesses for the crossings past regime A (assembly.verified_crossing output)
CERTS = {
    ("n_num", "0.87"): {
        "va": Fr(746673726362557, 2013625570000000),
        "tags": [("low",), ("floor",), ("int", Fr(5, 6)), ("dual_length",)],
        "vb": Fr(716308399326243, 1931737570000000),
        "geo": (Fr(933333393757, 5 * 10**12), Fr(4066666606243, 5 * 10**12), Fr(186365117427, 10**13)),
    },
    ("z_p", "13/15"): {
        "va": Fr(75980771510193, 429898070000000),
        "tags": [("low",), ("floor",), ("end", Fr(51251, 150000), Fr(1, 2)), ("dual_length",)],
        "vb": Fr(886918321816491, 5018164910000000),
        "geo": (Fr(416349187703, 2500000000000), Fr(2083650812297, 2500000000000), Fr(1609752953767, 10**13)),
    },
    ("g", "0.87"): {
        "va": Fr(4474556787173, 50271730000000),
        "tags": [("low",), ("floor",), ("end", Fr(5125039, 15000000), Fr(1, 2)), ("dual_length",)],
        "vb": Fr(736577722451671, 8275483290000000),
        "geo": (Fr(1618964306001, 10**13), Fr(8381035693999, 10**13), Fr(1594800203191, 10**13)),
    },
    ("g", "13/15"): {
        "va": Fr(173346360858629, 4108586290000000),
        "tags": [("low",), ("floor",), ("dual_length",), ("supply",)],
        "vb": Fr(334387507444299, 7925557010000000),
        "geo": (Fr(52028608536489907, 334330704489652153), Fr(282302095953162246, 334330704489652153),
                Fr(59600188715200000, 334330704489652153)),
    },
}
CERT_BRACKETS = {("n_num", "0.87"): (0.3708106102, 0.3708104095),
                 ("z_p", "13/15"): (0.1767413646, 0.1767415654),
                 ("g", "0.87"): (0.0890074160, 0.0890072152),
                 ("g", "13/15"): (0.0421912426, 0.0421910418)}


@pytest.mark.parametrize("key", list(CERTS))
def test_crossings_past_regime_A(key):
    """Each upper end is decided by the repaired (Sturm-guarded) rectangle check."""
    name, lab = key
    level = A.LEVELS[lab]
    c = CERTS[key]
    lb = A.lower_bound_from(A.with_input(name, c["va"]), A.FROZEN, c["tags"])["lb"]
    ub = A.achievable_upper(*c["geo"], A.with_input(name, c["vb"]), A.FROZEN)
    assert lb > level > ub
    assert close(c["va"], CERT_BRACKETS[key][0], 1e-10) and close(c["vb"], CERT_BRACKETS[key][1], 1e-10)


N_POINTS = (Fr(0), Fr(1, 10), Fr(1, 5), Fr(13, 50), Fr(3, 10), Fr(1, 3))


def test_numerator_regimes():
    n = sp.Symbol("n")
    nr = A.n_num_regimes()
    assert sp.simplify(nr["floor_int_sigma"] - (2250 * n**2 + 76293 * n + 1137725) / (72 * (600 * n + 18397))) == 0
    assert nr["floor_int_sigma"].subs(n, sp.Rational(1, 2)) == sp.Rational(84031, 96156)
    assert sp.simplify(nr["n_087"] - (sp.Rational(-4301, 500) + sp.sqrt(181150489) / 1500)) == 0
    assert close(sp.N(nr["n_087"], 30), 0.3708105098, 5e-11)
    hi, lo = CERT_BRACKETS[("n_num", "0.87")]
    assert lo < float(sp.N(nr["n_087"], 30)) < hi
    assert close(sp.N(nr["floor_int_b0_at"], 30), 0.3484739370, 5e-11)
    assert sp.simplify(nr["floor_b0_sigma"] - (18 * n + 659) / (3 * (6 * n + 253))) == 0
    # every n >= 0: the n = 0 dual witness holds because the floor rows only weaken as n falls
    assert nr["ceiling_all_n"] == Fr(659, 759) > A.THIRTEEN_FIFTEENTHS
    assert close(Fr(659, 759), 0.8682476943, 5e-11)
    for geo in ((Fr(1, 6), Fr(5, 6), Fr(1, 8)), (Fr(1, 5), Fr(4, 5), Fr(0))):
        vals = [A.E_floor(*geo, A.Inputs(n_num=v)) for v in (Fr(0), Fr(1, 4), Fr(1, 2))]
        assert vals[0] < vals[1] < vals[2]


def test_n_slope_threshold_and_the_rows_below_h():
    """Below n = 26/125 a row at d < h may exceed its d = h end; the last n-axis formula is
    the exact optimum at six points with those rows checked (verifier issue 7)."""
    assert A.n_slope_threshold() == Fr(26, 125)
    # the slope bound behind it: (1 - z_0) - (1 - n) delta_max vanishes at 26/125
    assert (1 - A.FROZEN.z0) - (1 - Fr(26, 125)) * A.FROZEN.delta_max == 0
    # the intermediate range keeps a positive slope for every n >= 0: 101/150 - (2/3)(5/6)
    assert Fr(101, 150) - Fr(2, 3) * Fr(5, 6) == Fr(53, 450) > 0
    tags = [("low",), ("floor",), ("dual_length",), ("b_nonneg",)]
    for nv in N_POINTS:
        th = A.with_input("n_num", nv)
        lb = A.lower_bound_from(th, A.FROZEN, tags)
        assert lb["lb"] == (18 * nv + 659) / (3 * (6 * nv + 253))
        ell, M, b = lb["w"][:3]
        assert b == 0
        assert A.achievable_upper(ell, M, b, th, A.FROZEN, slack=Fr(0), inner=True) == lb["lb"]
        assert A.inner_rows_ok(ell, M, b, lb["lb"], th)


def test_z_p_floor_regime_closed_form():
    v = A.zp_floor_regime()
    assert same(v["delta"], sp.Rational(-740, 5573) + 35 * S22829 / 11146)
    assert same(v["h"], sp.Rational(23762198, 27128539) - 8190 * S22829 / 27128539)
    assert same(v["const"], sp.Rational(83492716, 81385617) - 2240 * S22829 / 27128539)
    assert same(v["z_13_15"], sp.Rational(28260493, 155678520) - 329 * S22829 / 10378568)
    assert close(v["z_13_15"], 0.1767414708, 5e-11)
    lo, hi = CERT_BRACKETS[("z_p", "13/15")]
    assert lo < float(v["z_13_15"]) < hi
    # the vertex is z_p-free and the generic vertex solver agrees with the Q(sqrt) solve
    w = A.vertex_on_axis("z_p", Fr(2, 10))
    assert abs(float(sp.N(w["ell"], 30)) - float(v["ell"])) < 1e-14
    assert abs(float(sp.N(w["b"], 30)) - float(v["b"])) < 1e-14


def test_z_p_floor_regime_range():
    lo, hi = A.zp_floor_vertex_end()
    assert close(lo, 0.2735042735, 2e-10) and hi - lo <= Fr(1, 10**10)
    m = A.floor_vertex_multipliers(A.with_input("z_p", Fr(18, 100)))
    assert all(m[k] > 0 for k in ("low", "floor", "end", "nu"))


def test_g_regimes():
    g = sp.Symbol("g")
    lo, hi = A.g_floor_to_gram()
    assert close(lo, 0.0857605178, 2e-10)
    gg = A.g_gram_regime()
    assert sp.simplify(gg["sigma_of_g"] - (418 * g - 1601) / (6 * (106 * g - 309))) == 0
    assert gg["g_supply"] == [sp.Rational(4, 53)]
    gs = A.g_supply_regime()
    assert sp.simplify(gs["sigma_of_g"] - (12922 * g - 11513) / (6 * (2650 * g - 2221))) == 0
    assert gs["g_13_15"] == sp.Rational(181, 4290)
    lo2, hi2 = CERT_BRACKETS[("g", "13/15")]
    assert hi2 < 181 / 4290 < lo2
    assert close(Fr(181, 4290), 0.0421911422, 5e-11)


# ------------------------------------------- the alpha axis: regime B (verifier issue 1)

ALPHA_B = sp.Rational(247, 573) + 3 * S518 / 382
ALPHA_F = sp.Rational(51, 350) + S518 / 175
ALPHA_087 = sp.Rational(85, 546) + 5 * S518 / 819
SIGMA_AT_ALPHA_B = sp.Rational(18589, 20919) - 14 * S518 / 20919
REGIME_B_POINTS = (Fr(3, 5), Fr(1, 2), Fr(2, 5), Fr(3, 10), Fr(7, 25))


def test_regime_B_closed_form():
    af, ab = A.regime_B_ends()
    assert same(ab, ALPHA_B) and same(af, ALPHA_F)
    assert same(A.regime_B_level(A.TARGET_087), ALPHA_087)
    assert same(A.regime_B_level(Fr(167, 192)), ALPHA_F)
    assert close(ab, 0.6098049914, 5e-11) and close(af, 0.2757692192, 5e-11)
    assert close(A.regime_B_level(A.TARGET_087), 0.2946252341, 5e-11)
    # delta_B and K_B are proportional to alpha (exact field Q(sqrt 518): D P = 259/162)
    sol = A.regime_B(A.with_input("alpha", Fr(1, 2)))
    assert sol["D"] * sol["P"] == Fr(259, 162)
    assert same(sol["delta"], (37 - S518) / 23 / 2) and same(sol["K"], (714 - 28 * S518) / 529 / 2)
    assert close(sol["sigma"], 0.8722266776, 5e-11)
    # the regime-A break is where b reaches 0, and both closed forms meet there
    ok, bad, failing = A.regime_A_break("alpha")
    assert failing == ["b_nonneg"] and bad < ab < ok
    D, P = sol["D"], sol["P"]
    K = ab * P / (D + P + 2 * A.QF(0, 1, D * P))
    assert same(Fr(11, 12) - (1 - K) / (4 * (5 + 3 * K)), SIGMA_AT_ALPHA_B)
    assert close(SIGMA_AT_ALPHA_B, 0.8733861759, 5e-11)
    assert abs(float(A.regime_A(A.with_input("alpha", ok))["sigma"]) - float(SIGMA_AT_ALPHA_B)) < 1e-9


@pytest.mark.parametrize("a", REGIME_B_POINTS)
def test_regime_B_is_the_optimum_exactly(a):
    th = A.with_input("alpha", a)
    sol = A.regime_B(th)
    w = A.regime_B_witness(sol, th)
    assert w["lb"] == sol["sigma"]                                   # exact lower bound
    assert all(v > 0 for v in w["y"].values())
    assert all(v > 0 for v in A.regime_B_slacks(sol, th).values())
    ell = rat(sol["ell"])
    ub = A.achievable_upper(ell, 1 - ell, Fr(0), th, A.FROZEN, slack=Fr(1, 10**13))
    assert ub is not None and sol["sigma"] < ub and ub - sol["sigma"] < Fr(2, 10**13)


def test_regime_B_generic_vertex_solver_agrees():
    for a in (Fr(1, 2), Fr(3, 10)):
        v = A.vertex_on_axis("alpha", a)
        assert abs(sp.N(v["sigma"], 40) - sp.N(qsym(A.regime_B(A.with_input("alpha", a))["sigma"]), 40)) < 1e-30


def test_alpha_reaches_087():
    """Exact bracket of the alpha that reaches 0.87: a dual witness above, a checked geometry below."""
    va, vb = Fr(29462524, 10**8), Fr(29462523, 10**8)
    assert vb < qsym(ALPHA_087) < va
    th_a = A.with_input("alpha", va)
    sa = A.regime_B(th_a)
    wa = A.regime_B_witness(sa, th_a)
    assert all(v > 0 for v in wa["y"].values()) and wa["lb"] > A.TARGET_087
    th_b = A.with_input("alpha", vb)
    sb = A.regime_B(th_b)
    ell = rat(sb["ell"], 10**15)
    ub = A.achievable_upper(ell, 1 - ell, Fr(0), th_b, A.FROZEN, slack=Fr(1, 10**13))
    assert ub is not None and ub < A.TARGET_087


def test_alpha_floor_limited_stretch():
    """167/192 holds for every alpha (its rows involve no alpha) and is attained below the floor point."""
    geo = (Fr(3, 16), Fr(13, 16), Fr(0))
    for a in (Fr(1, 4), Fr(1, 5), Fr(27, 100)):
        assert A.achievable_upper(*geo, A.with_input("alpha", a), A.FROZEN, slack=Fr(0)) == Fr(167, 192)
    assert Fr(27, 100) < qsym(ALPHA_F) < Fr(7, 25)
    assert A.achievable_upper(*geo, A.with_input("alpha", Fr(7, 25)), A.FROZEN, slack=Fr(0)) is None
    # the endpoint rows only weaken as alpha falls: K increases with alpha at every bin
    for dv, xv in ((Fr(1, 10), Fr(0)), (Fr(1, 5), Fr(1, 2)), (Fr(1, 4), Fr(1, 4))):
        ks = [A.K_of(dv, xv, A.with_input("alpha", a)) for a in (Fr(27, 100), Fr(3, 10), Fr(1, 2))]
        assert ks[0] < ks[1] < ks[2]


def test_intermediate_row_does_not_bind_on_the_alpha_axis():
    """Its slack is 0.0026581589 at the paper's alpha and larger at every other point checked.

    The slacks live in different quadratic fields, so they are compared through 50-digit
    values of the exact numbers; every gap below exceeds 10^-3."""
    def v50(q):
        return q.mp(50) if isinstance(q, A.QF) else A.mpf_of(q, 50)
    paper_slack = A.regime_A_slacks(A.regime_A())["intermediate"]
    assert close(paper_slack, 0.0026581589, 5e-10)
    p50 = v50(paper_slack)
    others = []
    for a in (Fr(4, 5), Fr(7, 10), Fr(31, 50)):
        th = A.with_input("alpha", a)
        others.append(A.regime_A_slacks(A.regime_A(th), th)["intermediate"])
    for a in REGIME_B_POINTS:
        th = A.with_input("alpha", a)
        others.append(A.regime_B_slacks(A.regime_B(th), th)["intermediate"])
    geo = (Fr(3, 16), Fr(13, 16), Fr(0))
    for a in (Fr(27, 100), Fr(1, 5), Fr(1, 10)):
        th = A.with_input("alpha", a)
        others += [Fr(167, 192) - A.target(*geo, th) - A.E_intermediate(dv, *geo, th) for dv in A.int_deltas(th)]
    assert len(others) == 3 + 5 + 6
    assert all(v50(v) - p50 > mpf("0.001") for v in others)
    # and it is imposed only up to min(alpha, 5/6) (line 16146)
    assert A.int_deltas(A.with_input("alpha", Fr(1, 2))) == [Fr(1, 50), Fr(1, 2)]
    with pytest.raises(ValueError):
        A.lower_bound_from(A.with_input("alpha", Fr(1, 2)), A.FROZEN, [("low",), ("int", Fr(5, 6))])


#: the verifier's independent grid LP (round 1, its own model built from paper.tex), with
#: the intermediate row imposed only for delta <= alpha: recorded values, not recomputed here
VERIFIER_LP = {Fr(4, 5): 0.8747921689, Fr(6076005515, 10**10): 0.8733630954,
               Fr(1, 2): 0.8722266748, Fr(3, 10): 0.8700592617}


def test_the_alpha_axis_agrees_with_the_verifiers_independent_lp():
    """A grid relaxation lies below the exact optimum, so each recorded value must sit
    below the closed form (regime A at 4/5, regime B at the others), by less than 10^-8."""
    for a, v in VERIFIER_LP.items():
        th = A.with_input("alpha", a)
        sa = A.regime_A(th)
        if sa is not None and all(x >= 0 for x in A.regime_A_slacks(sa, th).values()):
            s = sa["sigma"]
            assert a == Fr(4, 5)
        else:
            sb = A.regime_B(th)
            assert all(x >= 0 for x in A.regime_B_slacks(sb, th).values())
            s = sb["sigma"]
        assert 0 < float(s) - v < 1e-8, (a, float(s), v)


def test_the_withdrawn_frame_reproduces_the_withdrawn_claims():
    """The 14:36Z version imposed the intermediate row at delta = 5/6 for every alpha."""
    old = A.Frozen(intermediate="at_delta_max")
    for a in (Fr(1, 3), Fr(1, 2)):
        assert A.ceiling_four_rows(A.with_input("alpha", a), old)["lb"] == Fr(84031, 96156)
    geo = (Fr(1710553683597, 10**13), Fr(8289446316403, 10**13), Fr(1262947709971, 10**13))
    ub = A.achievable_upper(*geo, A.with_input("alpha", Fr(1, 2)), old)
    assert Fr(84031, 96156) < ub < Fr(84031, 96156) + Fr(1, 10**9)
    # in the corrected frame alpha = 1/2 goes well below it
    assert A.regime_B(A.with_input("alpha", Fr(1, 2)))["sigma"] < Fr(84031, 96156) - Fr(1, 1000)


# --------------------------------------------------------------- the ceilings

def test_ceiling_for_every_row_input():
    """167/192 holds for every (c_M, c_P, alpha): its rows do not involve them."""
    for th in (A.PAPER, A.Inputs(c_M=Fr(9, 10), c_P=Fr(7, 10), alpha=Fr(1, 3)),
               A.Inputs(c_M=Fr(1, 3), alpha=Fr(99, 100)), A.Inputs(alpha=Fr(1, 10))):
        r = A.lower_bound_from(th, A.FROZEN, A.ROW_INPUT_FREE_TAGS)
        assert r["lb"] == Fr(167, 192)
        assert set(r["rows"]) == {("low",), ("floor",), ("dual_length",), ("b_nonneg",)}
    assert A.ceiling_row_inputs()["lb"] == Fr(167, 192) > A.THIRTEEN_FIFTEENTHS


def test_four_row_bound_and_the_bin_ceiling():
    """84031/96156 for every (c_M, c_P) at alpha >= 5/6; 368153/422028 with the bin ceiling at 3/4."""
    for th in (A.PAPER, A.Inputs(c_M=Fr(9, 10), c_P=Fr(7, 10)), A.Inputs(alpha=Fr(9, 10), c_P=Fr(1, 3))):
        assert A.ceiling_four_rows(th)["lb"] == Fr(84031, 96156)
    assert close(Fr(84031, 96156), 0.8739028246, 5e-11)
    r = A.ceiling_four_rows(A.PAPER, A.Frozen(delta_max=Fr(3, 4)))
    assert r["lb"] == Fr(368153, 422028) and close(r["lb"], 0.8723425934, 5e-11)
    assert ("int", Fr(3, 4)) in r["rows"]
    # below alpha = 5/6 the intermediate row sits at delta = alpha and the bound moves
    assert A.ceiling_four_rows(A.with_input("alpha", Fr(1, 2)))["lb"] < Fr(84031, 96156)


def test_ceiling_for_every_capacity():
    """At alpha = 5/6 the rows with no prime amplitude (x = 0) and the intermediate range
    bound the abscissa for every (c_M, c_P); in the model the bound is attained at
    c_M = 9/10 with the supply hypothesis off (Lemma marked's second width condition fails
    there: test_marked_width_condition)."""
    cc = A.ceiling_capacities()
    assert close(cc["lb"], 0.8740524834, 5e-11)
    assert all(t[0] != "end" or t[2] == 0 for t in cc["rows"])
    for th in (A.Inputs(c_M=Fr(9, 10)), A.Inputs(c_P=Fr(7, 10)), A.Inputs(c_M=Fr(3, 4), c_P=Fr(1, 2))):
        assert A.lower_bound_from(th, A.FROZEN, cc["rows"])["lb"] == cc["lb"]
    assert close(sp.N(cc["vertex"]["sigma"], 30), 0.8740524834, 5e-11)
    geo = (Fr(1704567331663, 10**13), Fr(8295432668337, 10**13), Fr(312173303191, 2500000000000))
    ub = A.achievable_upper(*geo, A.with_input("c_M", Fr(9, 10)), A.Frozen(supply="off"))
    assert cc["lb"] < ub < cc["lb"] + Fr(1, 10**9)


def test_marked_width_condition():
    """Lemma marked (line 9254): 2r + 8z <= 3m - c_2 over the requested r holds only for
    c_M <= (5 - 4 c_P)/(9 - 8 c_P) (the end x = 1/2) and c_M <= 5/8 (the end x = 0, r = 2/3);
    37/65 at c_P = 2/9 (verifier issue 6)."""
    assert A.marked_width_cM_max() == Fr(37, 65)
    # the end x = 0 binds once c_P > 5/8: there r_*(1, 0) = 2/3 is the smallest requested r
    assert A.r_cross(Fr(1), Fr(0), A.Inputs(c_P=Fr(9, 10))) == Fr(2, 3)
    assert A.marked_width_cM_max(A.Inputs(c_P=Fr(9, 10))) == Fr(5, 8)
    assert A.marked_width_cM_max(A.Inputs(c_P=Fr(5, 8))) == Fr(5, 8) == (5 - 4 * Fr(5, 8)) / (9 - 8 * Fr(5, 8))
    assert A.marked_width_excess(A.Inputs(c_P=Fr(9, 10))) == Fr(-1, 3)
    assert A.marked_width_excess(A.Inputs(c_M=Fr(5, 8), c_P=Fr(9, 10))) == 0
    assert A.marked_width_excess(A.Inputs(c_M=Fr(13, 20), c_P=Fr(9, 10))) > 0
    for cM, cP in ((Fr(1, 2), Fr(2, 9)), (Fr(3, 5), Fr(2, 9)), (Fr(1, 2), Fr(1, 3)), (Fr(37, 65), Fr(2, 9)),
                   (Fr(7, 10), Fr(1, 10))):
        th = A.Inputs(c_M=cM, c_P=cP)
        ex, bound = A.marked_width_excess(th), A.marked_width_cM_max(th)
        assert (ex > 0) == (cM > bound) and (ex == 0) == (cM == bound)
    assert A.marked_width_excess(A.PAPER) == Fr(-9, 37)
    assert A.marked_width_excess(A.with_input("c_M", Fr(9, 10))) == Fr(215, 149)
    # every regime-A statement along c_M sits below 37/65
    for v in (0.5361872194, 0.5468059250, float(Fr(3023, 5625)), 0.5073016702):
        assert v < 37 / 65
    # along c_P (c_M = 1/2) the condition never fails: 1/2 < (5 - 4c)/(9 - 8c) iff 9 < 10,
    # and 1/2 < 5/8
    c = sp.Symbol("c")
    assert sp.simplify((5 - 4 * c) / (9 - 8 * c) - sp.Rational(1, 2) - 1 / (2 * (9 - 8 * c))) == 0
    assert Fr(1, 2) < Fr(5, 8)
    for cP in (Fr(1, 4), Fr(1, 2), Fr(9, 10), Fr(99, 100)):
        assert A.marked_width_excess(A.with_input("c_P", cP)) < 0


def test_c_M_envelope_under_the_uniform_supply_hypothesis():
    geo = (Fr(1124092560507492556197035, 6678351917362194152545479),
           Fr(5554259356854701596348444, 6678351917362194152545479),
           Fr(267964722868491699447192, 2226117305787398050848493))
    ub = A.achievable_upper(*geo, A.with_input("c_M", Fr(3023, 5625)), A.FROZEN)
    assert Fr(8745869524, 10**10) < ub < Fr(8745869525, 10**10) and close(Fr(3023, 5625), 0.537422, 5e-7)
    assert close(ub, 0.8745869525, 5e-11)                        # the rendering ASSEMBLY.md prints


def test_reachable_and_unreachable_levels():
    """As written: c_M and c_P cannot reach 0.87 (alpha = 5/6); alpha alone can; no row-count
    input reaches 13/15; the numerator cost alone cannot reach 13/15."""
    assert A.ceiling_capacities()["lb"] > A.TARGET_087
    assert A.ceiling_row_inputs()["lb"] > A.THIRTEEN_FIFTEENTHS
    assert A.ceiling_row_inputs()["lb"] < A.TARGET_087
    af, ab = A.regime_B_ends()
    assert af < A.regime_B_level(A.TARGET_087) < ab
    assert A.n_num_regimes()["ceiling_all_n"] > A.THIRTEEN_FIFTEENTHS


# ------------------------------------- the sampler and the rectangle check (issues 3, 5)

CUBIC = sp.Poly(sp.expand(((X - sp.Rational(71, 250))**2 - sp.Rational(2, 10**6)) * (X + 1)), X)


def test_sampler_catches_a_dip_between_close_roots():
    """The verifier's cubic: negative between two roots 0.0028 apart whose isolating
    intervals share an endpoint; the 14:36Z sampler skipped that gap."""
    ivs = [iv for iv, _ in CUBIC.intervals() if iv[0] >= 0]
    assert any(a[1] == b[0] for a, b in zip(ivs, ivs[1:]))          # a shared endpoint
    assert CUBIC.eval(sp.Rational(71, 250)) < 0
    assert 0.0028 < 2 * math.sqrt(2e-6) < 0.0029
    assert not A._nonneg_on(CUBIC, 0, sp.Rational(1, 2))
    # the shared endpoint itself is now a sample, and it lies in the dip
    pts = A._sample_points([CUBIC], 0, sp.Rational(1, 2))
    assert any(CUBIC.eval(p) < 0 for p in pts)


def test_sampler_rational_roots_and_double_roots():
    assert not A._nonneg_on(sp.Poly((X - sp.Rational(1, 5)) * (X - sp.Rational(2, 5)), X), 0, sp.Rational(1, 2))
    assert A._nonneg_on(sp.Poly((X - sp.Rational(1, 5))**2 * (X + 1), X), 0, sp.Rational(1, 2))
    assert A._nonneg_on(sp.Poly((X - sp.Rational(1, 5)) * (X - sp.Rational(2, 5)), X), sp.Rational(2, 5), 1)


def test_sampler_random_dips_and_bumps():
    rng = random.Random(20261021)
    for _ in range(40):
        c = sp.Rational(rng.randint(1, 499), 1000)
        e = sp.Rational(rng.randint(1, 100), 10**7)
        assert not A._nonneg_on(sp.Poly(sp.expand(((X - c)**2 - e) * (X + 1)), X), 0, sp.Rational(1, 2))
        assert A._nonneg_on(sp.Poly(sp.expand(((X - c)**2 + e) * (X + 1)), X), 0, sp.Rational(1, 2))


def test_sturm_guard_alone_decides(monkeypatch):
    """With the interval proposal emptied the Sturm guard still finds the dip; with the
    guard switched off as well (a planted fault) the dip is missed."""
    monkeypatch.setattr(sp.Poly, "intervals", lambda self, *a, **k: [])
    assert not A._nonneg_on(CUBIC, 0, sp.Rational(1, 2))
    monkeypatch.setattr(A, "_STURM_GUARD", False)
    assert A._nonneg_on(CUBIC, 0, sp.Rational(1, 2))                 # the planted fault goes through


def _grid_min_room(ell, M, b, s, th=A.PAPER, fr=A.FROZEN, nd=60, nx=8):
    room = s - A.target(ell, M, b, th)
    return min(room + A.neg_E_star_closed(Fr(fr.delta0) + (Fr(fr.delta_max) - Fr(fr.delta0)) * Fr(i, nd),
                                          Fr(j, 2 * nx), ell, M, b, th, fr)
               for i in range(nd + 1) for j in range(nx + 1))


def test_rectangle_check_agrees_with_an_exact_grid(base):
    """Soundness direction on random targets near the optimum: an exact grid violation
    forces a refusal, and an acceptance leaves the grid clean."""
    rng = random.Random(136)
    ell0 = Fr(str(base["ell"].mp(30))).limit_denominator(10**12)
    b0 = Fr(str(base["b"].mp(30))).limit_denominator(10**12)
    s0 = Fr(str(base["sigma"].mp(30))).limit_denominator(10**12)
    seen = {True: 0, False: 0}
    for _ in range(10):
        ell = ell0 + Fr(rng.randint(-30, 30), 10**6)
        b = b0 + Fr(rng.randint(-300, 300), 10**6)
        s = s0 + Fr(rng.randint(-50, 400), 10**6)
        ok = A.endpoint_room_ok(ell, 1 - ell, b, s)
        if _grid_min_room(ell, 1 - ell, b, s) < 0:
            assert not ok
        if ok:
            assert _grid_min_room(ell, 1 - ell, b, s) >= 0
        seen[ok] += 1
    assert seen[True] and seen[False]


BILINEAR_CASE = (A.Inputs(alpha=Fr(1, 2), n_num=Fr(3, 5)), (Fr(3, 16), Fr(13, 16), Fr(0)))


def test_planted_fault_bilinear_branch_goes_red(monkeypatch):
    """A target violated only in the bins delta >= alpha: refused by the full check,
    accepted with delta_max = alpha, and accepted (wrongly) with that branch skipped."""
    th, geo = BILINEAR_CASE
    s = A.target(*geo, th) - A.neg_E_star_closed(Fr(5, 6), Fr(1, 2), *geo, th) - Fr(1, 10**4)
    assert not A.endpoint_room_ok(*geo, s, th, A.FROZEN)
    assert A.endpoint_room_ok(*geo, s, th, A.Frozen(delta_max=Fr(1, 2)))
    monkeypatch.setattr(A, "_BILINEAR_BRANCH", False)
    assert A.endpoint_room_ok(*geo, s, th, A.FROZEN)                  # the planted fault goes through


def test_planted_fault_inner_rows_go_red():
    """A target violated only by a slot row at d = 1/2 (n = 0, alpha = 1/2)."""
    th = A.Inputs(n_num=Fr(0), alpha=Fr(1, 2))
    geo = (Fr(49, 253), Fr(204, 253), Fr(0))
    ell, M, b = geo
    h = A.geometry(*geo)[2]
    worst = max(-A.neg_E_star_closed(dv, xv, *geo, th)
                - (h - Fr(1, 2)) * (A.R_star(dv, xv, th) + th.n_num * dv - A.FROZEN.z0)
                for dv in (Fr(k, 100) for k in range(2, 51)) for xv in (Fr(0), Fr(1, 4), Fr(1, 2)))
    s = A.target(*geo, th) + worst - Fr(1, 10**6)
    room = s - A.target(*geo, th)
    dmin = A.FROZEN.d_min
    others = [A.high_exponent(dmin, dv, dv / 2, A.R_intermediate(dv, th), *geo, th) for dv in A.int_deltas(th)]
    others += [A.high_exponent(dmin, A.FROZEN.delta0, A.FROZEN.delta0 / 2, th.R_fl, *geo, th)]
    others += [A.high_exponent(dmin, dv, xv * dv, 1 - dv, *geo, th) for dv in (Fr(1, 2), Fr(5, 6))
               for xv in (Fr(0), Fr(1, 2))]
    assert all(room - E > 0 for E in others)                          # only the slot family is violated
    assert not A.inner_rows_ok(*geo, s, th)
    # and it reads the rows at d < h, not the endpoint: a target 1/100 above the slot rows
    # but below the endpoint maximum passes it, while the endpoint check refuses it
    s_up = s + Fr(1, 100) + Fr(1, 10**6)
    assert A.inner_rows_ok(*geo, s_up, th)
    assert not A.endpoint_room_ok(*geo, s_up, th)


def test_planted_fault_inner_large_delta_rows_go_red():
    """The bins delta >= alpha carry the count 1 - delta at every d <= h.  At n = 0 their
    d-slope 1 - z_0 - delta is negative for delta > 33/50, so their d_min end lies above the
    d = h end.  With alpha = 2/3 and the geometry (11/50, 39/50, 0) the check of the rows at
    d < h, taken on its own, refuses a target violated among them only there and passes one
    just above; reading those rows at d = h instead (a scratch-copy fault of this repair)
    passed both."""
    th = A.Inputs(n_num=Fr(0), alpha=Fr(2, 3))
    geo = (Fr(11, 50), Fr(39, 50), Fr(0))
    h, dmin = A.geometry(*geo)[2], A.FROZEN.d_min
    corners = [(dv, xv) for dv in (Fr(2, 3), Fr(5, 6)) for xv in (Fr(0), Fr(1, 2))]
    at_dmin = max(A.high_exponent(dmin, dv, xv * dv, 1 - dv, *geo, th) for dv, xv in corners)
    at_h = max(A.high_exponent(h, dv, xv * dv, 1 - dv, *geo, th) for dv, xv in corners)
    assert at_dmin > at_h + Fr(1, 20)
    assert Fr(33, 50) == 1 - A.FROZEN.z0
    s = A.target(*geo, th) + at_dmin - Fr(1, 10**6)
    room = s - A.target(*geo, th)
    others = [A.high_exponent(dmin, dv, dv / 2, A.R_intermediate(dv, th), *geo, th) for dv in A.int_deltas(th)]
    others.append(A.high_exponent(dmin, A.FROZEN.delta0, A.FROZEN.delta0 / 2, th.R_fl, *geo, th))
    assert all(room - E > 0 for E in others)            # of the rows at d < h only these fail:
    assert A._room_rect_ok(*geo, s, th, A.FROZEN, d_row=Fr(1, 2), quad=True, bilin=False)   # slot rows fit
    assert not A.inner_rows_ok(*geo, s, th)
    assert A.inner_rows_ok(*geo, s + Fr(2, 10**6), th)


# ---------------------------------------------------------- planted faults

@pytest.mark.parametrize("name,value", [("g", Fr(1, 12)), ("z_p", Fr(1, 5)), ("alpha", Fr(4, 5)),
                                        ("c_M", Fr(1, 3)), ("c_P", Fr(1, 4)), ("R_fl", Fr(99, 100)),
                                        ("n_num", Fr(1, 3))])
def test_planted_wrong_exponent_breaks_a_reproduction(monkeypatch, name, value):
    monkeypatch.setattr(A, "PAPER", replace(A.PAPER, **{name: value}))
    assert any(not r["ok"] for r in A.reproductions())


@pytest.mark.parametrize("name,value", [("g", Fr(1, 12)), ("z_p", Fr(1, 5)), ("alpha", Fr(4, 5)),
                                        ("c_M", Fr(9, 20)), ("c_P", Fr(1, 4)), ("n_num", Fr(49, 100))])
def test_planted_wrong_exponent_changes_the_optimum(base, name, value):
    other = A.regime_A(A.with_input(name, value))
    assert other is None or float(other["sigma"]) != pytest.approx(float(base["sigma"]), abs=1e-9)


def test_planted_fault_feasibility_check_goes_red(base):
    ell = Fr(str(base["ell"].mp(30))).limit_denominator(10**15)
    b = Fr(str(base["b"].mp(30))).limit_denominator(10**15)
    beyond = ell + Fr(1, 10**6)                      # past the optimum along M + ell = 1
    assert not A.endpoint_room_ok(beyond, 1 - beyond, b, A.target(beyond, 1 - beyond, b) + Fr(1, 10**13))
    s_below = Fr(str(base["sigma"].mp(30))).limit_denominator(10**16) - Fr(1, 10**10)
    assert not A.endpoint_room_ok(ell, 1 - ell, b, s_below)
    assert A.achievable_upper(ell, 1 - ell + Fr(1, 100), b) is None          # M + ell > 1
    assert A.achievable_upper(ell, 1 - ell, Fr(-1, 100)) is None             # b < 0


def test_planted_fault_witness_goes_red(base):
    cert = A.regime_A_witness(base)
    mu = base["mu"] + Fr(1, 1000)
    bad = dict(base, mu=mu)
    assert any(r != 0 for r in A.regime_A_witness(bad)["residual"])
    rows = A._exact_rows_for(A.PAPER, A.FROZEN, [("low",), ("end", Fr(1, 10), Fr(0)), ("dual_length",),
                                                 ("b_nonneg",)])
    assert A._exact_basis(rows, [0, 1, 2, 3]) is None or A._exact_basis(rows, [0, 1, 2, 3])["lb"] < cert["lb"]
    # the stored witnesses are not vacuous: used at the wrong end they must fail
    c = CERTS[("g", "0.87")]
    lb_wrong = A.lower_bound_from(A.with_input("g", c["vb"]), A.FROZEN, c["tags"])["lb"]
    assert lb_wrong < A.TARGET_087
    ub_wrong = A.achievable_upper(*c["geo"], A.with_input("g", c["va"]), A.FROZEN)
    assert ub_wrong is None or ub_wrong > A.TARGET_087
    # a regime-B witness at an alpha above alpha_b has a negative weight on b >= 0
    th = A.with_input("alpha", Fr(61, 100))
    assert A.regime_B_witness(A.regime_B(th), th)["y"]["b_nonneg"] < 0


# ----------------------------------------------------- ASSEMBLY.md is pinned

def _md():
    with open(os.path.join(HERE, "ASSEMBLY.md"), encoding="utf-8") as fh:
        return fh.read()


def _f(v, digits=10, sign=False):
    return f"{float(v):{'+' if sign else ''}.{digits}f}"


#: every decimal and fraction ASSEMBLY.md may print, sign included; each is pinned by a
#: test above, or is a cited constant of the paper (line-numbered in assembly.CITATIONS),
#: or an input value used by the tests
ALLOWED = {
    # the optimum, its multipliers and slacks
    "0.8749570698", "0.8749570194", "0.87495701942", "0.8749417", "0.874958", "0.8749576643", "0.87496",
    "0.1668383875", "0.1234054370", "0.8119602997", "0.1875643953", "0.0625214651", "0.4994848376",
    "0.0091161574", "0.0058792912", "0.0026581589", "0.0132242767",
    # shadow prices and elasticities (signed)
    "-0.8119602997", "+0.0591792953", "+0.0501294854", "-0.0095710837", "+0.0047006135", "-0.0019776984",
    "-0.135327", "+0.029590", "+0.008355", "-0.004786", "+0.003917", "-0.000439", "6.18",
    "-254/551", "66721/1821606", "-1071/15979", "-12348/303601", "7414/303601", "-5103/607202",
    # changes to beat Xu and Sang (signed) and the crossing values
    "+0.0000866553", "-0.0011898023", "-0.0013738421", "+0.0073016702", "-0.0146429748", "+0.0342796610",
    "0.1667533220", "0.4988101977", "0.1652928246", "0.5073016702", "0.8186903585", "0.2565018832",
    "0.1727198769", "0.3708105098", "0.0890072152", "0.0890074160", "0.2946252341",
    "0.1767414708", "0.1767413646", "0.1767415654", "0.3708106102", "0.3708104095",
    "0.0421911422",
    # breaks and regimes
    "0.1751510556", "0.1567188215", "0.5361872194", "0.4908887159", "0.6098049914", "0.5261221985",
    "0.8679871838", "0.8744203215", "0.8743819388", "0.8745985237", "0.8733861759", "0.8740683460",
    "0.5468059250", "0.2735042735", "0.0857605178", "0.3484739370", "0.2757692192", "0.8722266776",
    "28260493/155678520", "83492716/81385617", "-740/5573", "-4301/500", "4/53", "181/4290",
    "247/573", "18589/20919", "85/546", "51/350", "3023/5625", "0.537422", "0.8745869525",
    "0.6076005515",                          # the verifier's sample point (VERIFIER_LP)
    # ceilings
    "167/192", "0.8697916667", "0.8740524834", "84031/96156", "0.8739028246", "368153/422028",
    "0.8723425934", "13/15", "0.8666666667", "659/759", "0.8682476943",
    # the marked width condition and the slope threshold
    "37/65", "215/149", "5/8", "26/125",
    # controls
    "5655673/6464057", "44117/50422", "49/440640", "7/30672", "37/14", "223/576", "7/18", "3/25",
    "899/2250", "79/204", "0.0028",
    # input values used by the tests (#134's b = 0.12 is 3/25; planted faults; sample points)
    "0.12", "9/10", "99/100", "3/5", "2/5", "3/10", "7/25", "27/100", "13/50",
    # reference lines (external map and FOLLOWUPS.md, not checked here)
    "0.8748867", "0.87", "0.874957", "0.874887", "0.8748087",
    # the paper's constants and inputs, cited by line
    "7/8", "11/12", "1/2", "2/9", "5/6", "1/6", "1/50", "17/50", "1/100", "3/4", "1/12", "1/8",
    "5/16", "3/16", "11/16", "13/16", "17/48", "23/48", "7/37", "8/39", "23/37", "2/27", "51/64",
    "49/14400", "529/2400", "25/96", "7/1200", "1/48", "63/800", "79/800", "76/75", "2/3", "3/2",
    "1/24", "1/4", "1/3", "9/2", "11/6", "1/5", "4/5", "35/54", "5/2", "37/18", "7/9", "51/100",
    "1/10",
}

_TOKEN = re.compile(r"(?<![\w./#])([+-]?\d+\.\d+|[+-]?\d+/\d+)(?![\w/])")


def _unpinned(text):
    return sorted({t for t in _TOKEN.findall(text) if t not in ALLOWED})


def test_every_number_in_the_md_is_pinned():
    unknown = _unpinned(_md())
    assert unknown == [], f"numbers in ASSEMBLY.md with no pin: {unknown}"


def _table(text, header_start):
    """The body rows of the markdown table whose header line starts with `header_start`."""
    lines = text.splitlines()
    i = next(k for k, ln in enumerate(lines) if ln.startswith(header_start))
    rows = []
    for ln in lines[i + 2:]:
        if not ln.startswith("|"):
            break
        rows.append([c.strip() for c in ln.strip().strip("|").split("|")])
    return rows


def _price_table():
    names = ["z_p", "n_num", "g", "c_M", "alpha", "c_P"]
    label = {"n_num": "n"}
    rows = []
    for rank, k in enumerate(names, 1):
        rows.append([str(rank), label.get(k, k), _f(SHADOW[k][1], sign=True), None,
                     _f(ELASTICITY[k], 6, sign=True), _f(XU_SANG_CHANGE[k], sign=True)])
    rows.append(["7", "R_fl", "0", "the floor has slack", "0", "none"])
    return rows


def _break_table():
    order = [("z_p", "z_p (raised)"), ("n_num", "n (lowered)"), ("g", "g (lowered)"), ("c_M", "c_M (raised)"),
             ("alpha", "alpha (lowered)"), ("c_P", "c_P (raised)")]
    return [[lab, _f(BREAKS[k][0]), BREAK_WORDS[k], _f(BREAKS[k][2])] for k, lab in order]


def _reach_table():
    g87 = CERT_BRACKETS[("g", "0.87")]
    return [
        ["z_p (1/6)", _f(CROSS_A[("z_p", "xu_sang")]), _f(CROSS_A[("z_p", "0.87")]), _f(0.1767414708)],
        ["n (1/2)", _f(CROSS_A[("n_num", "xu_sang")]), _f(0.3708105098), "no: every n >= 0 stays at or above 659/759"],
        ["g (1/6)", _f(CROSS_A[("g", "xu_sang")]), f"{_f(g87[1])} to {_f(g87[0])}", "181/4290"],
        ["c_M (1/2)", _f(CROSS_A[("c_M", "xu_sang")]), "no: ceiling " + _f(0.8740524834), "no"],
        ["alpha (5/6)", _f(CROSS_A[("alpha", "xu_sang")]), _f(qsym(ALPHA_087)),
         "no: every alpha stays at or above 167/192"],
        ["c_P (2/9)", _f(CROSS_A[("c_P", "xu_sang")]), "no: ceiling " + _f(0.8740524834), "no"],
        ["R_fl (1)", "no (zero price)", "no", "no"],
    ]


def test_md_tables_match_the_pinned_values():
    """Sections 4, 5 and 6: every cell, so two values swapped between rows go red."""
    text = _md()
    from sympy.parsing import sympy_parser as tr
    got = _table(text, "| rank | input |")
    want = _price_table()
    assert len(got) == len(want)
    for g_row, w_row in zip(got, want):
        for k, (gc, wc) in enumerate(zip(g_row, w_row)):
            if k == 3 and wc is None:              # the exact column, parsed and compared exactly
                expr = tr.parse_expr(gc.strip("`"), transformations=tr.standard_transformations
                                     + (tr.implicit_multiplication_application,))
                name = {"n": "n_num"}.get(g_row[1], g_row[1])
                assert sp.simplify(expr - SHADOW[name][0]) == 0, g_row
            else:
                assert gc == wc, (g_row, w_row)
    assert _table(text, "| input | regime A holds to |") == _break_table()
    assert _table(text, "| input (paper value) |") == _reach_table()


def test_planted_fault_md_pin_goes_red():
    """A number with no pin, a pinned number with one digit changed, a negative number with
    one digit changed, and two table values swapped between rows are all caught."""
    text = _md()
    assert _unpinned(text + "\nsigma = 0.8749570699\n") == ["0.8749570699"]
    assert _unpinned(text.replace("84031/96156", "84031/96157", 1)) == ["84031/96157"]
    assert _unpinned(text.replace("-0.8119602997", "-0.8119602998", 1)) == ["-0.8119602998"]
    swapped = text.replace("| 0.1727198769 | 0.1767414708 |", "| 0.1767414708 | 0.1727198769 |", 1)
    assert swapped != text
    assert _table(swapped, "| input (paper value) |") != _reach_table()


def test_no_reserved_word_and_no_em_dash():
    for name in ("ASSEMBLY.md", "assembly.py", "test_assembly.py"):
        with open(os.path.join(HERE, name), "rb") as fh:
            raw = fh.read().lower()
        assert b"cert" + b"ified" not in raw and b"cert" + b"ificat" not in raw, name
        assert chr(0x2014).encode() not in raw and chr(0x2013).encode() not in raw, name
        assert all(c < 128 for c in raw), name                       # ASCII only


def test_the_md_states_the_central_numbers_and_readings():
    text = _md()
    for s in ("(1507 - 2 sqrt 921)/1653", "0.8749570698", "0.8749570194", "167/192", "0.8740524834",
              "13/15", "181/4290", "0.1751510556", "0.5073016702", "0.2946252341", "0.6098049914",
              "37/65", "84031/96156", "368153/422028"):
        assert s in text, s
    # the two readings are defined, and every sub-7/8 section and the doors cite them
    assert "**R1, total accounting**" in text and "**R2, the shared lemmas below their range.**" in text
    for anchor in ("## 3. The optimum", "## 5. The abscissa", "## 6. What each input", "## 7. Ceilings",
                   "## The doors"):
        section = text.split(anchor, 1)[1].split("\n## ", 1)[0]
        assert "R1" in section and "R2" in section, anchor
