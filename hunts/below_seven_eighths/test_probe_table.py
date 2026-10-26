"""Tests for hunt #136's probe lane (`probe_table.py`, `PROBE.md`).

The values PROBE.md prints are pinned here: exact ones as fractions, measured ones (float
optimisations) with a stated tolerance.  `prose_problems` reads the page itself: every
decimal must sit in a phrase computed or quoted here, every fraction must be a computed,
cited or quoted value, every line reference must name a line that a citation check
reads, and the tables of sections 1, 3, 4 and 5 and the walls of section 6 are rendered
from the computation.  It cannot catch a swap of two allowed fractions outside the
rendered tables and phrases, or a changed integer that no phrase carries.  The module is
loaded by path under a unique name, because other lanes of this hunt may put a
`probe.py` in the same directory.  Nothing here writes a file.
"""
from __future__ import annotations

import importlib.util
import itertools
import math
import random
import re
import types
from collections import Counter
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("b78_probe_table", HERE / "probe_table.py")
pt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(pt)

KS = (2, 3, 4, 5, 6, 8, 12)
HELD, LIMIT = pt.FLOOR_HELD, pt.FLOOR_LIMIT
PROBE_MD = HERE / "PROBE.md"

_MEMO: dict = {}


def opt(k, variant, d0=HELD, **kw):
    """Memoised endpoint_optimum (the float route is deterministic and touches no patch)."""
    key = (k, variant, d0, tuple(sorted(kw.items())))
    if key not in _MEMO:
        _MEMO[key] = pt.endpoint_optimum(k, variant, floor_delta0=float(d0), **kw)
    return _MEMO[key]


# ----------------------------------------------------------------- the source
@pytest.mark.skipif(not pt.PAPER.exists(), reason="pinned paper.tex not on this machine")
def test_every_citation_sits_on_its_line():
    assert pt.verify_citations() == []
    assert len(pt.CITATIONS) == 91


@pytest.mark.skipif(not pt.FOLLOWUPS_DIR.exists(), reason="cached follow-ups not on this machine")
def test_outside_citations_sit_on_their_lines():
    """Liu's cached sources: sha256 pinned, every quoted line checked."""
    assert pt.verify_outside_citations() == []
    assert len(pt.OUTSIDE_CITATIONS) == 22


def test_provenance_lines_are_cited_lines():
    """Every line a provenance row names is a line some citation checks; grades as stated."""
    cited = {n for n, _ in pt.CITATIONS.values()}
    for row in pt.PROVENANCE:
        for n in row["lines"]:
            assert n in cited, (row["key"], n)
    assert {r["origin"] for r in pt.PROVENANCE} == {"sextic", "cubic-theta", "generic", "choice"}
    sextic = sorted(r["key"] for r in pt.PROVENANCE if r["origin"] == "sextic")
    assert sextic == ["alpha", "gram_cap", "gram_exceptional", "gram_low", "plain_capacity",
                      "pole", "slot_weight"]
    # the reading of each sextic 6 as k is never graded above inferred
    assert all("inferred" in r["grade"] for r in pt.PROVENANCE if r["origin"] == "sextic")
    grade = {r["key"]: r["grade"] for r in pt.PROVENANCE}
    assert grade["mellin_positive"].startswith("cited")
    assert grade["dual_length"].startswith("derived") and "inferred" in grade["dual_length"]
    assert "BGL Theorem 1.3" in grade["sextic_sieve"]
    tmpl = {r["key"]: r["template"] for r in pt.PROVENANCE}
    assert "for k >= 7" in tmpl["euler_regions"]
    assert len({r["key"] for r in pt.PROVENANCE}) == len(pt.PROVENANCE) == 23


# ------------------------------------------------------- k = 6 gives the paper
def test_template_reproduces_the_paper_at_k6():
    reps = pt.reproductions()
    assert [r["name"] for r in reps if r["got"] != r["want"]] == []
    assert len(reps) == 14
    assert Counter(r["source"] for r in reps) == Counter({"paper": 12, "hunt134": 2})


@pytest.mark.skipif(not pt.PAPER.exists(), reason="pinned paper.tex not on this machine")
def test_reproduction_sources_are_honest():
    """A value said to be printed is on its line; a value said to be hunt 134's is absent."""
    text = pt.PAPER.read_text(encoding="utf-8")
    lines = text.splitlines()
    cited_lines = {n for n, _ in pt.CITATIONS.values()}
    for r in pt.reproductions():
        if r["source"] == "paper":
            assert r["line"] in cited_lines, r["name"]
            assert r["tex"] in lines[r["line"] - 1], r["name"]
        else:
            assert r["line"] is None
            for s in r["absent"]:
                assert s not in text, (r["name"], s)


def test_paper_completed_square_identity_on_a_grid():
    pts = [(Fr(i, 24), Fr(j, 8)) for i in range(0, 21) for j in range(0, 5)]
    assert len(pts) == 105
    assert all(pt.paper_completed_square_identity(d, x) for d, x in pts)


def test_paper_margin_and_worst_point():
    w = pt.endpoint_neg_e(6, pt.ELL_P, pt.M_P, pt.B_P, Fr(79, 204), Fr(1, 2), pt.ALPHA_P, pt.C_P)
    assert w == Fr(7, 30672) and w >= Fr(49, 440640)


#: hunt #134's exact bounds and witness points (its results.json, robust_bound and
#: gram_limited_bound), read from origin/claude/hunt-134-seven-eighths-pin
H134_ROBUST, H134_ROBUST_AT = Fr(5655673, 6464057), Fr(223, 576)
H134_GRAM, H134_GRAM_AT = Fr(44117, 50422), Fr(7, 18)


def test_hunt_134_exact_bounds_at_their_witness_points():
    """The mission's kill condition 1 names the re-optimised 0.8749417: both of hunt #134's
    exact bounds come back exactly at its witness points, x = 1/2, with no floor row."""
    half = Fr(1, 2)
    assert pt.single_point_bound(6, H134_ROBUST_AT, half, pt.ALPHA_P, pt.C_P,
                                 delta0=None) == H134_ROBUST
    assert pt.single_point_bound(6, H134_GRAM_AT, half, pt.ALPHA_P, pt.C_P,
                                 delta0=None) == H134_GRAM
    assert f"{float(H134_ROBUST):.7f}" == "0.8749417"

    def coeffs(delta):
        def f(ell, b):
            return pt.endpoint_neg_e_closed(6, ell, 1 - ell, b, delta, half, pt.ALPHA_P, pt.C_P)
        A = f(Fr(0), Fr(0))
        return A, f(Fr(1), Fr(0)) - A, f(Fr(0), Fr(1)) - A
    # at 223/576 -E_* does not increase with b: b = 0 is best and no Gram cap is used
    A, A_l, A_b = coeffs(H134_ROBUST_AT)
    assert A_b <= 0 and Fr(11, 12) - (-A / A_l) / 4 == H134_ROBUST
    # at 7/18 it increases with b, so the Gram cap b = 3(1 - 3 ell)/8 binds
    A, A_l, A_b = coeffs(H134_GRAM_AT)
    ell_star = -(A + A_b * Fr(3, 8)) / (A_l - A_b * Fr(9, 8))
    assert A_b > 0 and Fr(11, 12) - ell_star / 4 == H134_GRAM
    assert H134_ROBUST < H134_GRAM < pt.best_exact_bound(6, "A")["sigma0_lower"]


def test_liu_count_equation_is_the_template_count():
    """Liu v2's count equation R_kappa = 2/3 (cached source lines 296 and 298) is the
    template's R_* = 2/3 at x = 1/2, alpha = 5/6, c = 1/(3 kappa), identically in kappa;
    at the measured binding point of the tied optimum R_* is 2/3 to 1e-6."""
    xi, ka = sp.symbols("xi kappa", positive=True)
    c = pt.plain_coeff(6, ka)
    assert sp.simplify(c - 1 / (3 * ka)) == 0
    x, al = sp.Rational(1, 2), sp.Rational(5, 6)
    Dx, Px = pt.d_x(x, c), pt.p_x(x, c)
    J = (al - xi) * Dx + xi * Px
    R = 1 - xi + (al - xi) * xi * Px / (2 * J)
    liu = (216 * ka - 18) * xi ** 2 - (468 * ka - 57) * xi + 150 * ka - 20
    ratio = sp.simplify(sp.numer(sp.together(R - sp.Rational(2, 3))) / liu)
    assert ratio.free_symbols == set() and ratio != 0
    for v in ("C", "A"):
        r = opt(6, v)
        rb = pt.r_star(Fr(r["delta_bind"]).limit_denominator(10 ** 9), Fr(1, 2), pt.ALPHA_P,
                       Fr(r["c"]).limit_denominator(10 ** 12))
        assert abs(float(rb) - 2 / 3) < 1e-6


# --------------------------------------------------- general k, exact algebra
def test_closed_forms_symbolically_for_every_k():
    """Independent sympy re-derivation of the target, C_0 and -E_* for symbolic k."""
    k, ell, M, b, dl, x, al, c, zc = sp.symbols("k ell M b delta x alpha c zc", positive=True)
    z = 1 / k
    lx, ly = (M - b) / 2, (M + b) / 2
    h = 1 - lx + ell
    low = lx / 2 + b / (2 * k)
    shift = 1 - lx / 2 - h * z
    sigma = low + shift
    assert sp.simplify(sigma - (1 - 1 / k + (M - 2 * ell) / (2 * k))) == 0
    q = x * dl
    Dx = 3 - (1 + 2 * c) * x
    Px = (2 - 2 * c * x) * (1 - x)
    J = (al - dl) * Dx + dl * Px
    K = (al - dl) * dl * Px / J
    R = 1 - dl + K / 2

    def E(d, delta, qq, RR):
        aa = (1 + delta) / 2
        return (aa - sigma + h * (zc - z) - aa * ly - (1 - aa) * ell - (delta / 2 - qq) * ell
                + d * (RR + delta / 2 - zc))
    C0 = sp.Rational(1, 2) + ell / 2 - sp.Rational(3, 4) * M + b * (sp.Rational(1, 4) - 1 / (2 * k))
    assert sp.simplify(E(h, 0, 0, 1) - C0) == 0
    closed = -C0 + dl * (ell + b) / 2 - ell * x * dl - h / 2 * K
    assert sp.simplify(-E(h, dl, q, R) - closed) == 0
    d0 = sp.symbols("d0", positive=True)
    assert sp.simplify(E(h, d0, d0 / 2, 1) - (C0 + (1 + ell - M / 2) * d0)) == 0
    # the balancing t equalises R_short and L, and both equal R_*
    t = 1 + dl * Px / (2 * J)
    r_short = 1 - dl + dl * Px / Dx * (sp.Rational(3, 2) - t)
    long_ = 1 - dl + (al - dl) * (t - 1)
    assert sp.simplify(r_short - long_) == 0 and sp.simplify(long_ - R) == 0
    # the constant-target slope is positive and free of k
    slope = sp.diff(closed.subs(M, 2 * ell + sp.Symbol("m0")), ell)
    assert sp.simplify(slope - (1 + dl * (sp.Rational(1, 2) - x))) == 0
    # E(h) does not see the contour; the pole enters the endpoint only through b
    assert sp.simplify(sp.diff(E(h, dl, q, R), zc)) == 0
    # at b = 0 the endpoint and the floor rows are free of k, and 1 - sigma_0 scales as 1/k
    assert sp.simplify(sp.diff(closed.subs(b, 0), k)) == 0
    assert sp.simplify(sp.diff((C0 + (1 + ell - M / 2) * d0).subs(b, 0), k)) == 0
    assert sp.simplify(1 - sigma - (1 - (M - 2 * ell) / 2) / k) == 0
    # the plain coefficient: D_x/P_x increases with c, so every bound decreases in c
    assert sp.simplify(sp.diff(Dx / Px, c) - 2 * x * (1 - x) ** 2 / Px ** 2) == 0


def test_floor_wall_dual_identity_symbolically_in_k_and_the_floor_bin():
    """M - 2 ell - m = y1 (-floor) + y2 (1 - M - ell) + y3 b for symbolic k and delta_0."""
    k, ell, M, b, d0 = sp.symbols("k ell M b d0", positive=True)
    C0 = sp.Rational(1, 2) + ell / 2 - sp.Rational(3, 4) * M + b * (sp.Rational(1, 4) - 1 / (2 * k))
    floor = C0 + (1 + ell - M / 2) * d0
    s = 5 + 6 * d0
    y1, y2 = 12 / s, 4 / s
    y3 = y1 * (sp.Rational(1, 4) - 1 / (2 * k))
    m = (2 + 12 * d0) / s
    assert sp.simplify(M - 2 * ell - m - (y1 * (-floor) + y2 * (1 - M - ell) + y3 * b)) == 0
    assert sp.solve(sp.Eq(y3, 0), k) == [2]
    # the wall and the vertex where it is attained
    wall = 1 - 1 / k + m / (2 * k)
    assert sp.simplify(wall - (1 - 1 / k + (1 + 6 * d0) / (k * (5 + 6 * d0)))) == 0
    ell_star = (sp.Rational(1, 4) - d0 / 2) / (sp.Rational(5, 4) + 3 * d0 / 2)
    on_line = floor.subs({M: 1 - ell, b: 0}).subs(ell, ell_star)
    assert sp.simplify(on_line) == 0
    assert sp.simplify((1 - 3 * ell).subs(ell, ell_star) - m) == 0
    # the losslessness ell <= 1/5 holds there for every delta_0 >= 0
    slack = (sp.Rational(4, 5) * d0) / (sp.Rational(5, 4) + 3 * d0 / 2)
    assert sp.simplify(sp.Rational(1, 5) - ell_star - slack) == 0
    assert all(ell_star.subs(d0, v) <= sp.Rational(1, 5) for v in (0, sp.Rational(1, 50), 1))
    # the vertex has ell >= 0 exactly for delta_0 <= 1/2
    assert sp.solve(sp.Eq(ell_star, 0), d0) == [sp.Rational(1, 2)]


def test_floor_wall_holds_for_floor_bins_up_to_one_half_and_not_beyond():
    """The wall formula holds for 0 <= delta_0 <= 1/2; at 1/2 it is the balanced probe and
    above it the floor rows cannot be met: their smallest value is -1/4 + delta_0/2."""
    for k in KS:
        for d0 in (LIMIT, HELD, Fr(1, 10), Fr(1, 4), Fr(1, 2)):
            assert pt.floor_ceiling(k, delta0=d0)["sigma0"] == pt.floor_wall_closed(k, d0)
        top = pt.floor_ceiling(k, delta0=Fr(1, 2))
        assert top["sigma0"] == pt.part_one_target(k) and (top["ell"], top["M"]) == (0, 1)
        with pytest.raises(ValueError):
            pt.floor_ceiling(k, delta0=Fr(51, 100))
        for d0 in (Fr(0), Fr(1, 2), Fr(51, 100)):
            low = pt.c0_closed(k, Fr(0), Fr(1), Fr(0)) + (1 + Fr(0) - Fr(1, 2)) * d0
            assert low == -Fr(1, 4) + d0 / 2
            # and no admissible point does better (coefficients of ell, M, b in the rows)
            assert Fr(1, 2) + d0 > 0 and -Fr(3, 4) - d0 / 2 < 0 and Fr(1, 4) - Fr(1, 2 * k) >= 0


def test_dual_length_subtraction_leaves_m_plus_ell_minus_one():
    """Line 8246 with general parameters: the extra term is M + ell - 1."""
    H, A0, za, N0, B0, th, M, ell, d = sp.symbols("H A0 za N0 B0 th M ell d")
    Mp, lp = M - 2 * d, ell - d
    T_d = 2 * H + 2 * A0 + 2 * za - 1 - lp - th - N0 - 3 * B0
    printed = H - Mp + 2 * A0 + 2 * (za - lp) - N0 - 3 * B0 - th
    assert sp.expand(T_d - (H - 3 * d) - printed - (M + ell - 1)) == 0
    # at the paper's geometry the extra term vanishes, as line 8246 uses
    assert pt.M_P + pt.ELL_P - 1 == 0


def test_two_routes_agree_exactly_on_random_rational_points():
    rng = random.Random(136)
    for k in range(2, 13):
        for _ in range(40):
            ell = Fr(rng.randint(0, 60), 300)
            M = Fr(rng.randint(150, 300), 300)
            b = Fr(rng.randint(0, 60), 300)
            dl = Fr(rng.randint(7, 299), 360)
            x = Fr(rng.randint(0, 50), 100)
            al, c = pt.alpha_amp(k), Fr(rng.randint(1, 30), 30)
            assert pt.target(k, ell, M, b) == pt.target_closed(k, ell, M)
            assert pt.c0(k, ell, M, b) == pt.c0_closed(k, ell, M, b)
            assert (pt.endpoint_neg_e(k, ell, M, b, dl, x, al, c)
                    == pt.endpoint_neg_e_closed(k, ell, M, b, dl, x, al, c))
            if dl < al:
                _, rs, lg = pt.short_and_long(dl, x, al, c)
                assert rs == lg == pt.r_star(dl, x, al, c)
                # the polynomial of the upper bounds is J (-E_*) on M = 1 - ell
                F = pt.endpoint_polynomial(k, ell, b, al, c)
                J = (al - dl) * pt.d_x(x, c) + dl * pt.p_x(x, c)
                assert pt._peval(F, dl, x) == J * pt.endpoint_neg_e_closed(
                    k, ell, 1 - ell, b, dl, x, al, c)
                assert pt._peval(pt.endpoint_denominator(al, c), dl, x) == J


def test_walls_have_the_closed_forms():
    for k in KS:
        assert pt.part_one_target(k) == 1 - Fr(1, 2 * k)
        assert pt.corner_target(k) == 1 - Fr(3, 4 * k)
        fh = pt.floor_ceiling(k)                       # default: the paper's floor bin
        assert fh["delta0"] == HELD and fh["sigma0"] == 1 - Fr(25, 32 * k)
        assert (fh["ell"], fh["M"], fh["b"]) == (Fr(3, 16), Fr(13, 16), Fr(0))
        fl = pt.floor_ceiling(k, delta0=LIMIT)
        assert fl["sigma0"] == 1 - Fr(4, 5 * k)
        assert (fl["ell"], fl["M"], fl["b"]) == (Fr(1, 5), Fr(4, 5), Fr(0))
        for d0 in (HELD, LIMIT):
            assert pt.floor_ceiling(k, delta0=d0)["sigma0"] == pt.floor_wall_closed(k, d0)
            # with the per-summand loss the floor wall is the corner itself
            assert pt.floor_ceiling(k, "per_summand", delta0=d0)["sigma0"] == 1 - Fr(3, 4 * k)
    table = {k: (pt.part_one_target(k), pt.corner_target(k), pt.system_prices(k)["floor_held"],
                 pt.system_prices(k)["floor_limit"]) for k in KS}
    assert table == WALLS


#: section 3 of PROBE.md: (balanced, corner, floor at 1/50, floor in the limit)
WALLS = {2: (Fr(3, 4), Fr(5, 8), Fr(39, 64), Fr(3, 5)),
         3: (Fr(5, 6), Fr(3, 4), Fr(71, 96), Fr(11, 15)),
         4: (Fr(7, 8), Fr(13, 16), Fr(103, 128), Fr(4, 5)),
         5: (Fr(9, 10), Fr(17, 20), Fr(27, 32), Fr(21, 25)),
         6: (Fr(11, 12), Fr(7, 8), Fr(167, 192), Fr(13, 15)),
         8: (Fr(15, 16), Fr(29, 32), Fr(231, 256), Fr(9, 10)),
         12: (Fr(23, 24), Fr(15, 16), Fr(359, 384), Fr(14, 15))}


def test_floor_wall_dual_multipliers_for_every_k():
    """The identity holds exactly at grid points for k = 2 to 39 and three floor bins."""
    for d0 in (LIMIT, HELD, Fr(1, 10)):
        for k in range(2, 40):
            y1, y2, y3, m = pt.floor_dual_multipliers(k, d0)
            assert min(y1, y2, y3) >= 0
            for ell, M, b in itertools.product([Fr(0), Fr(1, 7), Fr(1, 3)], repeat=3):
                lhs = M - 2 * ell - m
                fl = pt.c0_closed(k, ell, M, b) + (1 + ell - M / 2) * d0
                assert lhs == y1 * (-fl) + y2 * (1 - M - ell) + y3 * b
    y_held = pt.floor_dual_multipliers(6, HELD)
    assert y_held == (Fr(75, 32), Fr(25, 32), Fr(75, 32) * Fr(1, 6), Fr(7, 16))
    y_lim = pt.floor_dual_multipliers(6, LIMIT)
    assert (y_lim[0], y_lim[1], y_lim[3]) == (Fr(12, 5), Fr(4, 5), Fr(2, 5))
    # the held floor bin is the paper's a = 51/100
    assert HELD == 2 * Fr(51, 100) - 1


def test_bootstrap_ceiling_equals_the_amplification_slope():
    """2 sigma_I(k) - 1 = 1 - 1/k = alpha(k): the paper's kappa <= 5/6 = alpha at k = 6."""
    for k in range(2, 40):
        assert 2 * pt.part_one_target(k) - 1 == pt.alpha_amp(k)


def test_gram_coefficient_is_half_the_pole_so_b_cancels():
    for k in KS:
        assert pt.gram_low(k) == pt.z_pole(k) / 2
        for b in (Fr(0), Fr(1, 8), Fr(1, 5)):
            assert pt.target(k, pt.ELL_P, pt.M_P, b) == pt.corner_target(k)
    assert pt.gram_cap_slope(6) == Fr(8, 3)        # the paper's b <= 3(M - 2 ell)/8


def test_shadow_prices_at_the_paper_geometry():
    """d sigma/dz = -(h - b/2) = -3/4 with g = z/2 tied, -h = -13/16 with g held."""
    _, _, h = pt.geometry(pt.ELL_P, pt.M_P, pt.B_P)
    assert -(h - pt.B_P / 2) == Fr(-3, 4) and -h == Fr(-13, 16)
    # d sigma/dg = b = 1/8
    t0 = pt.target(6, pt.ELL_P, pt.M_P, pt.B_P, g=Fr(1, 12))
    t1 = pt.target(6, pt.ELL_P, pt.M_P, pt.B_P, g=Fr(0))
    assert t0 - t1 == Fr(1, 96)


def test_reflection_twist_map_and_pole_per_twist():
    """Line 1790 on the uniform-exponent reading: a twist chi^j has dual chi^(-(j+2)), and
    the pole is 1/order(chi^j).  Only the arithmetic of the map is checked."""
    dual = {j: (-(j + 2)) % 6 for j in range(1, 6)}
    assert dual == {1: 3, 2: 2, 3: 1, 4: 0, 5: 5}
    order = {j: 6 // math.gcd(6, j) for j in range(1, 6)}
    assert order == {1: 6, 2: 3, 3: 2, 4: 3, 5: 6}
    # only j = 1 (and its conjugate j = 5) keeps the pole at 1/6; j = 4 gives a
    # principal (Ramanujan) dual, line 1791
    assert [j for j in dual if dual[j] == 0] == [4]


def test_held_inputs_fit_per_k():
    """Where the held contour 17/50 and the Euler regions stop fitting (section 1)."""
    fit = {k: pt.held_inputs_fit(k) for k in KS}
    assert [k for k in KS if fit[k]["contour_right_of_pole"]] == [3, 4, 5, 6, 8, 12]
    assert [k for k in KS if fit[k]["residue_in_region_two"]] == [2, 3, 4, 5, 6]
    assert fit[2]["window"] == (Fr(1, 2), Fr(3, 4)) and fit[2]["window_open_below"]
    assert all(fit[k]["held_contour_in_window"] for k in KS if k >= 3)
    # inside the k = 2 window the frequency slope of every row priced here stays positive
    for zc in (Fr(51, 100), Fr(5, 8), Fr(74, 100)):
        assert pt.frequency_slope_lower(2, zc) > 0
    assert pt.frequency_slope_lower(2, Fr(3, 4)) == 0
    assert pt.frequency_slope_lower(6, pt.ZC_P) == Fr(73, 300)
    # the paper's own floor row: R + delta_0/2 - 17/50 > 0 (line 15849)
    assert 1 + HELD / 2 - pt.ZC_P > 0


def test_region_two_holds_the_residue_exactly_for_k_up_to_6():
    """The principal residue 1/k lies in region two (z_r >= 33/200) for k <= 6 only, so the
    held region fails from k = 7 on, not only for the k = 8 and 12 of the tables."""
    assert [k for k in range(2, 40) if pt.held_inputs_fit(k)["residue_in_region_two"]] \
        == [2, 3, 4, 5, 6]
    assert Fr(1, 7) < pt.REGION_TWO_Z <= Fr(1, 6)


def test_capacities_and_supply():
    assert pt.inverse_capacity_max(pt.C_P) == Fr(7, 37)
    assert pt.supply_needed(pt.C_P) == Fr(7, 37)
    assert abs(pt.supply_needed_float(4 / 9) - 7 / 37) < 1e-15
    # closed form and grid route agree, either side of c = 1
    for i in range(0, 20):
        c = Fr(i, 10)
        assert abs(float(pt.supply_needed(c)) - pt.supply_needed_float(float(c))) < 1e-14
    assert pt.plain_count_decreasing(Fr(199, 100)) and not pt.plain_count_decreasing(Fr(2))
    assert pt.tied_c(6, Fr(7, 8)) == Fr(4, 9) == pt.C_P == pt.plain_coeff(6, pt.KAPPA_P)
    assert pt.tied_c(2, Fr(3, 5)) == 5 and pt.tied_c(2, Fr(39, 64)) == Fr(32, 7)


def test_capacity_closed_forms_symbolically():
    """(1 - r_*(1))/2 = (1 - cx)/(2 D_x) and c(1 - 2 m_min)/2 = c(1 - x)/(2 D_x), with
    x-derivatives of sign 1 - c and c - 1: the maxima sit at x = 0 or x = 1/2."""
    x, c = sp.symbols("x c", positive=True)
    D = 3 - (1 + 2 * c) * x
    r1 = (2 - 2 * c * x - x * (1 - c)) / D
    m1 = (1 - c * x) / D
    assert sp.simplify((1 - r1) / 2 - (1 - c * x) / (2 * D)) == 0
    assert sp.simplify(c * (1 - 2 * m1) / 2 - c * (1 - x) / (2 * D)) == 0
    assert sp.simplify(sp.diff((1 - c * x) / D, x) - (1 - c) / D ** 2) == 0
    assert sp.simplify(sp.diff((1 - x) / D, x) - (2 * c - 2) / D ** 2) == 0


def test_slot_supply_beyond_two_thirds_is_infeasible():
    """The defect fixed in the first revision: a capacity of at least 2/3 cannot be
    supplied, since ell/h < 2/3 for h = 1/2 + 3 ell/2 + b/2; the old test passed such points."""
    s = pt.supply_needed(Fr(19, 10))
    assert s == Fr(19, 24) and s >= Fr(2, 3)
    r = pt.endpoint_optimum(6, "A", c=1.9)
    assert not r["valid"] and r["reason"] == "requested capacity exceeds the slot supply"
    # the old acceptance rule ell >= s(1 + b)/(2 - 3s) accepts every ell >= 0 here
    old_threshold = s * (1 + Fr(1, 8)) / (2 - 3 * s)
    assert old_threshold < 0
    # and the true condition fails for every admissible ell and b
    for ell in (Fr(0), Fr(1, 10), Fr(1, 5)):
        for b in (Fr(0), Fr(1, 8)):
            assert ell / (Fr(1, 2) + Fr(3, 2) * ell + b / 2) < s


def test_k2_tie_asks_for_c_at_least_two_for_every_target():
    """At k = 2 every template target is at most 3/4 and the equality tie's
    1/(2 sigma - 1) >= 2 there: a statement about the equality tie only."""
    sig = sp.symbols("sigma", positive=True)
    assert sp.simplify(2 / (2 * (2 * sig - 1)) - 2 - (3 - 4 * sig) / (2 * sig - 1)) == 0
    assert pt.part_one_target(2) == Fr(3, 4) and pt.tied_c(2, Fr(3, 4)) == 2
    rng = random.Random(2)
    for _ in range(50):
        ell, M = Fr(rng.randint(0, 50), 100), Fr(rng.randint(50, 100), 100)
        if M + ell <= 1:
            assert pt.target_closed(2, ell, M) <= Fr(3, 4)


def test_lemma_plain_kappa_per_variant():
    """On the k kappa reading, the held c = 4/9 is kappa = 9/(2k) (section 4)."""
    kap = {k: pt.kappa_of_c(k, pt.C_P) for k in KS}
    assert kap == {2: Fr(9, 4), 3: Fr(3, 2), 4: Fr(9, 8), 5: Fr(9, 10), 6: Fr(3, 4),
                   8: Fr(9, 16), 12: Fr(3, 8)}
    # above 1 for k <= 4: admissible through kappa = 1, whose c = 2/k is at least 4/9
    assert all(kap[k] > 1 and pt.plain_coeff(k, Fr(1)) >= pt.C_P for k in (2, 3, 4))
    # k = 5: inside the range, hypothesis 19/20, which the order-5 Part I analogue supplies
    assert pt.KAPPA_P <= kap[5] <= 1 and (1 + kap[5]) / 2 == Fr(19, 20)
    assert pt.part_one_target(5) == Fr(9, 10) < Fr(19, 20)
    # k = 6: kappa = 3/4, hypothesis 7/8 (the paper's theorem, as Liu v1 uses it)
    assert kap[6] == pt.KAPPA_P and (1 + kap[6]) / 2 == Fr(7, 8)
    # k = 8 and 12: below the stated range
    assert kap[8] < pt.KAPPA_P and kap[12] < pt.KAPPA_P
    assert (float(kap[8]), float(kap[12])) == (0.5625, 0.375)
    # a c inside the range (kappa = 3/4) only raises the A and B values at k = 8 and 12
    for k, c_in in ((8, Fr(1, 3)), (12, Fr(2, 9))):
        assert pt.plain_coeff(k, pt.KAPPA_P) == c_in < pt.C_P
        for v in "AB":
            assert opt(k, v, c=float(c_in))["sigma0"] > MEASURED[(k, v)]
    # a larger kappa only shrinks the condition n_1 + n_2 + 6 kappa z <= M (line 12561)
    n1, n2, z, k1, dk = sp.symbols("n1 n2 z k1 dk", nonnegative=True)
    assert sp.expand((n1 + n2 + 6 * (k1 + dk) * z) - (n1 + n2 + 6 * k1 * z)) == 6 * dk * z


# -------------------------------------------------------------- the endpoint
def test_k6_tied_variant_reproduces_liu():
    """The template at k = 6 with c tied to the target is Liu's comparison system."""
    for d0 in (HELD, LIMIT):
        r = opt(6, "C", d0)
        assert r["valid"] and abs(r["sigma0"] - pt.LIU_B_NEW) < 1e-12
        lb = pt.best_exact_bound(6, "C", delta0=d0)["sigma0_lower"]
        assert lb <= Fr(pt.LIU_B_NEW) and float(lb) > pt.LIU_B_NEW - 1e-8
        assert abs(r["delta_bind"] - 0.38858) < 1e-5 and r["x_bind"] == 0.5
        assert abs(r["ell"] - 0.166839) < 1e-6 and abs(r["b"] - 0.123406) < 1e-6


def test_k6_tied_variant_matches_liu_closed_forms():
    """Liu's closed forms (arXiv 2610.12234v2, cached source lines 130 to 135 and 302 to
    304): the root xi of 1188 xi^3 - 2160 xi^2 + 171 xi + 190 in (0.38858, 0.38859)
    gives B, ell, b, kappa."""
    lo, hi = Fr(38858, 100000), Fr(38859, 100000)

    def f(t):
        return 1188 * t ** 3 - 2160 * t ** 2 + 171 * t + 190
    assert f(lo) * f(hi) < 0
    for _ in range(80):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(lo) * f(mid) > 0 else (lo, mid)
    xi = float(lo)
    B = (18 * xi + 7) / (18 * xi + 9)
    ell = (5 - 6 * xi) / (9 + 18 * xi)
    b = 8 * (3 * xi - 1) * (12 * xi ** 2 - 40 * xi + 15) / (
        9 * (2 * xi + 1) * (24 * xi ** 2 - 20 * xi + 5))
    assert abs(B - pt.LIU_B_NEW) < 1e-15
    r = opt(6, "C")
    assert abs(r["sigma0"] - B) < 1e-12
    assert abs(r["delta_bind"] - xi) < 1e-5          # Liu's xi is the binding delta
    assert abs(r["ell"] - ell) < 1e-6 and abs(r["b"] - b) < 1e-6
    assert abs(r["kappa0"] - (2 * B - 1)) < 1e-12


def test_k6_fixed_capacity_matches_hunt_134():
    r = opt(6, "A")
    assert abs(r["sigma0"] - 0.8749570698) < 1e-9
    # Liu's first closed form, kappa = 3/4 held (arXiv 2610.12234v1, cached source)
    assert abs(r["sigma0"] - (1507 - 2 * 921 ** 0.5) / 1653) < 1e-12
    lb = pt.best_exact_bound(6, "A")["sigma0_lower"]
    assert lb > H134_ROBUST and lb > H134_GRAM
    assert float(lb) > 0.874957066 and lb < Fr(7, 8)
    assert opt(6, "A", loss="per_summand")["sigma0"] == pytest.approx(0.875, abs=1e-12)


#: measured optimum (float scan) per (k, variant); PROBE.md prints these to 7 places.
#: MEASURED is the paper's floor bin 1/50, MEASURED_LIMIT the limit delta_0 -> 0.
MEASURED = {
    (2, "A"): 0.6093750, (2, "B"): 0.6093750,
    (3, "A"): 0.7449310, (3, "B"): 0.7441280,
    (4, "A"): 0.8106425, (4, "B"): 0.8102393, (4, "C"): 0.8096920,
    (5, "A"): 0.8494278, (5, "B"): 0.8492734, (5, "C"): 0.8491144,
    (6, "A"): 0.8749571, (6, "B"): 0.8749571, (6, "C"): 0.8749570,
    (8, "A"): 0.9065214, (8, "B"): 0.9067045, (8, "C"): 0.9068015,
    (12, "A"): 0.9378033, (12, "B"): 0.9381005, (12, "C"): 0.9382153,
}
MEASURED_LIMIT = dict(MEASURED)
MEASURED_LIMIT.update({(2, "A"): 0.6060442, (2, "B"): 0.6038808, (3, "A"): 0.7442838,
                       (3, "B"): 0.7434565, (4, "A"): 0.8105686, (4, "B"): 0.8102025,
                       (4, "C"): 0.8096034})
BRACKET_ROWS = sorted([(k, v, HELD) for k, v in MEASURED]
                      + [(k, v, LIMIT) for k, v in MEASURED_LIMIT])
#: the first pass's table (its PROBE.md section 4, limit convention, scan from 1/50)
FIRST_PASS = {
    (2, "A"): 0.6060442, (2, "B"): 0.6038808, (3, "A"): 0.7442838, (3, "B"): 0.7434565,
    (4, "A"): 0.8105686, (4, "B"): 0.8102025, (4, "C"): 0.8096034,
    (5, "A"): 0.8494278, (5, "B"): 0.8492734, (5, "C"): 0.8491144,
    (6, "A"): 0.8749571, (6, "B"): 0.8749571, (6, "C"): 0.8749570,
    (8, "A"): 0.9065214, (8, "B"): 0.9067045, (8, "C"): 0.9068015,
    (12, "A"): 0.9378033, (12, "B"): 0.9381005, (12, "C"): 0.9382153,
}


def test_the_limit_column_is_the_first_pass_table():
    """Scanning the endpoint from 0 instead of 1/50 moved no printed value of the first pass
    (each limit row is also checked against the live scan in the bracket test)."""
    assert MEASURED_LIMIT == FIRST_PASS
    for k, v in ((2, "A"), (4, "C"), (6, "A")):
        assert abs(opt(k, v, LIMIT)["sigma0"] - FIRST_PASS[(k, v)]) < 6e-8


@pytest.mark.parametrize("row", BRACKET_ROWS, ids=lambda r: f"{r[0]}{r[1]}-{r[2]}")
def test_endpoint_optimum_and_exact_bracket(row):
    k, v, d0 = row
    table = MEASURED if d0 == HELD else MEASURED_LIMIT
    r = opt(k, v, d0)
    assert r["valid"]
    assert abs(r["sigma0"] - table[(k, v)]) < 6e-8
    lb = pt.best_exact_bound(k, v, delta0=d0)["sigma0_lower"]
    ub = pt.exact_upper_bound(k, v, delta0=d0, measured=r)
    assert ub["valid"], ub
    # exact on both sides, the measured value inside, and narrower than 2e-8
    assert lb <= ub["sigma0_upper"]
    assert float(lb) <= r["sigma0"] + 1e-12 and r["sigma0"] <= float(ub["sigma0_upper"]) + 1e-12
    assert ub["sigma0_upper"] - lb < Fr(2, 10 ** 8)


def test_k2_paper_bin_rows_are_the_floor_exactly():
    """At k = 2 the floor rows carry no b (1/4 - 1/(2k) = 0) and bind: 39/64 for A and B."""
    for v in ("A", "B"):
        assert pt.best_exact_bound(2, v)["sigma0_lower"] == Fr(39, 64)
        assert abs(opt(2, v)["sigma0"] - 39 / 64) < 1e-12


def test_k6_exact_bound_and_slacks_at_the_optimum():
    lb = pt.best_exact_bound(6, "A")
    assert lb["sigma0_lower"] == Fr(4995360671043583, 5709263753593183)
    assert (lb["delta"], lb["x"]) == (Fr(384312, 989005), Fr(1, 2))
    ub = pt.exact_upper_bound(6, "A", measured=opt(6, "A"))
    assert ub["valid"] and ub["sigma0_upper"] <= Fr(8749570699, 10 ** 10)
    # the old single point of the first pass is still a valid, weaker bound
    old = pt.single_point_bound(6, Fr(89551, 230455), Fr(1, 2), pt.ALPHA_P, pt.C_P)
    assert old == Fr(97643690184149, 111598264488819) < lb["sigma0_lower"]
    r = opt(6, "A")
    c0 = 0.5 + r["ell"] / 2 - 0.75 * r["M"] + r["b"] * (0.25 - 1 / 12)
    assert abs(c0 - (-0.0209)) < 1e-4                       # floor rows slack
    assert abs(c0 + (1 + r["ell"] - r["M"] / 2) / 50 - (-0.0059)) < 1e-4
    assert abs((1 - 3 * r["ell"]) * 3 / 8 - 0.1873) < 1e-4  # Gram cap, b = 0.1234
    assert abs(r["b"] - 0.1234) < 1e-4
    assert abs(r["supply_ratio"] - 0.2055) < 1e-4 and r["supply_ratio"] > 7 / 37


def test_exact_upper_bound_checker_is_sharp(monkeypatch):
    """A point 1e-6 beyond the measured optimum must fail the exact check, and a planted
    fault (K dropped from the endpoint polynomial) must make it pass: a check that cannot
    fail is not a check."""
    r = opt(6, "A")
    b = Fr(r["b"]).limit_denominator(10 ** 9)
    bad = Fr(r["ell"]).limit_denominator(10 ** 12) + Fr(1, 10 ** 6)
    checks = pt.point_is_feasible(6, bad, b, pt.ALPHA_P, pt.C_P)
    assert not checks["endpoint, delta < alpha"] and checks["J > 0"]
    ok, corner = pt.positive_on_box(pt.endpoint_polynomial(6, bad, b, pt.ALPHA_P, pt.C_P),
                                    (HELD, pt.ALPHA_P, Fr(0), Fr(1, 2)))
    assert not ok and corner is not None          # a concrete point with -E_* <= 0
    assert pt.endpoint_neg_e_closed(6, bad, 1 - bad, b, corner[0], corner[1], pt.ALPHA_P,
                                    pt.C_P) <= 0
    good = pt.exact_upper_bound(6, "A", measured=r)
    assert all(pt.point_is_feasible(6, good["ell"], good["b"], pt.ALPHA_P, pt.C_P).values())
    # an independent sanity check of the subdivision: -E_* > 0 on an exact 21 x 11 grid
    for i in range(21):
        dl = HELD + (pt.ALPHA_P - HELD) * Fr(i, 20)
        for j in range(11):
            assert pt.endpoint_neg_e_closed(6, good["ell"], 1 - good["ell"], good["b"], dl,
                                            Fr(j, 20), pt.ALPHA_P, pt.C_P) > 0
    with monkeypatch.context() as m:
        def no_k(k, ell, b, alpha, c):
            beta = Fr(1, 4) - Fr(1, 2 * k)
            L = {(0, 0): Fr(1, 4) - beta * b - Fr(5, 4) * ell, (1, 0): (ell + b) / 2, (1, 1): -ell}
            return pt._pmul(pt.endpoint_denominator(alpha, c), L)
        m.setattr(pt, "endpoint_polynomial", no_k)
        assert pt.point_is_feasible(6, bad, b, pt.ALPHA_P, pt.C_P)["endpoint, delta < alpha"]


# ------------------------------------- the exact checker against an independent route
N_FEAS = 400


def _exact_supply(c: Fr) -> Fr:
    """Independent route to the slot-supply threshold: the largest requested capacity on an
    exact grid of 101 values of x (both maxima sit at x = 0 or 1/2, which it contains)."""
    best = Fr(0)
    for i in range(101):
        x = Fr(i, 200)
        dx = 3 - (1 + 2 * c) * x
        r1 = (2 - 2 * c * x - x * (1 - c)) / dx
        m1 = (1 - c * x) / dx
        best = max(best, (1 - r1) / 2, c * (1 - 2 * m1) / 2)
    return best


def _feasibility_route(k, ell, b, alpha, c, delta0) -> dict:
    """Each non-subdivision check of point_is_feasible, computed another way."""
    M = 1 - ell
    _, _, h = pt.geometry(ell, M, b)
    dmax = 1 - Fr(1, k)
    out = {
        "ell >= 0": ell >= 0,
        "b >= 0": b >= 0,
        "gram cap": (3 - 4 * Fr(1, 2 * k)) * b <= M - 2 * ell,
        "loss": 2 * M >= 1 + 3 * ell,
        "floor": pt.floor_exponent(k, ell, M, b, delta0) < 0,     # the transcribed E(h)
        "plain count decreasing": c / 2 < 1,
        "slot supply": ell / h > _exact_supply(c),
    }
    if alpha < dmax:
        # K = 0 for delta >= alpha, so -E_* is bilinear in (delta, x): its corners decide
        out["endpoint, delta >= alpha"] = all(
            pt.endpoint_neg_e_closed(k, ell, M, b, dl, x, alpha, c) > 0
            for dl in (alpha, dmax) for x in (Fr(0), Fr(1, 2)))
    return out


def _feasibility_sample() -> list[tuple]:
    rng = random.Random(1136)
    pts = []
    for _ in range(N_FEAS):
        k = rng.choice(KS)
        pts.append((k, Fr(rng.randint(-3, 33), 132), Fr(rng.randint(-2, 40), 160),
                    rng.choice((pt.ALPHA_P, pt.alpha_amp(k))), Fr(rng.randint(1, 44), 20),
                    rng.choice((LIMIT, HELD, Fr(1, 10)))))
    return pts


def _disagreements(mod) -> list:
    bad = []
    for k, ell, b, alpha, c, d0 in _feasibility_sample():
        got = mod.point_is_feasible(k, ell, b, alpha, c, d0, endpoint=False)
        want = _feasibility_route(k, ell, b, alpha, c, d0)
        if got != want:
            bad.append((k, ell, b, alpha, c, d0, got, want))
    return bad


def test_point_is_feasible_agrees_with_an_independent_route():
    """Constraint by constraint, on points where every constraint is both met and missed."""
    assert _disagreements(pt) == []
    seen = {}
    for k, ell, b, alpha, c, d0 in _feasibility_sample():
        for key, v in _feasibility_route(k, ell, b, alpha, c, d0).items():
            seen.setdefault(key, set()).add(v)
    assert len(seen) == 8 and all(v == {True, False} for v in seen.values()), seen


#: source mutants of probe_table.point_is_feasible: each makes one check vacuous or wrong
MUTANTS = [
    ("(Fr(1, 2) + Fr(3, 2) * ell) * delta0 < 0,", "(Fr(1, 2) + Fr(3, 2) * ell) * delta0 < 1,"),
    ('"slot supply": ell / h > supply_needed(c),', '"slot supply": ell / h > 0,'),
    ('"gram cap": gram_cap_slope(k) * b <= 1 - 3 * ell,', '"gram cap": gram_cap_slope(k) * b <= 2 - 3 * ell,'),
    ('"loss": ell <= (Fr(1, 5) if loss', '"loss": ell <= (Fr(1, 4) if loss'),
    ("+ dl * (ell + b) / 2 - ell * x * dl", "+ dl * (ell + b) / 2"),
    ('"plain count decreasing": plain_count_decreasing(c),', '"plain count decreasing": True,'),
]


def _mutant(old: str, new: str):
    src = (HERE / "probe_table.py").read_text(encoding="utf-8")
    assert src.count(old) == 1, old
    mod = types.ModuleType("b78_probe_table_mutant")
    exec(compile(src.replace(old, new), str(HERE / "probe_table.py"), "exec"), mod.__dict__)
    return mod


@pytest.mark.parametrize("mutant", MUTANTS, ids=lambda m: m[1][:28])
def test_point_is_feasible_mutants_are_caught(mutant):
    """The verifier made the floor and slot-supply checks vacuous and every test stayed
    green; each such mutant must now disagree with the independent route."""
    assert _disagreements(_mutant(*mutant)) != []


# ---------------------------------------------------------- the tied variant
def test_per_summand_reading_returns_the_corner_for_k_up_to_6():
    """The endpoint allows ell > 1/6 exactly for k <= 6, so the per-summand optimum is
    the corner 1 - 3/(4k) there; for k >= 8 the endpoint binds below ell = 1/6."""
    for d0 in (HELD, LIMIT):
        for k in KS:
            r = opt(k, "A", d0)
            assert (r["ell"] > 1 / 6) == (k <= 6)
            ps = opt(k, "A", d0, loss="per_summand")["sigma0"]
            if k <= 6:
                assert abs(ps - float(pt.corner_target(k))) < 1e-12
            else:
                assert abs(ps - r["sigma0"]) < 1e-12


def test_optimum_geometry_ranges_quoted_in_probe_md():
    for d0, table in ((HELD, MEASURED), (LIMIT, MEASURED_LIMIT)):
        for (k, v) in table:
            r = opt(k, v, d0)
            assert 0.16 < r["ell"] < 0.20, (k, v, d0)
    assert abs(opt(6, "A")["delta_bind"] - 0.3886) < 1e-4


def test_equality_tie_has_no_fixed_point_for_k2_and_k3():
    tie = "no fixed point of the equality tie: "
    for d0 in (HELD, LIMIT):
        r2, r3 = opt(2, "C", d0), opt(3, "C", d0)
        assert not r2["valid"] and r2["reason"].startswith(tie + "it asks for c = ")
        assert not r3["valid"] and r3["reason"] == (
            tie + "the requested capacity exceeds the slot supply")


#: relaxed ties (probe_table.RELAXED_TIES), measured, per bin; PROBE.md prints 7 places
RELAXED = {("k2 kappa 1", HELD): 0.6093750, ("k2 kappa 1", LIMIT): 0.6033313,
           ("k3 kappa 3/4", HELD): 0.7435200, ("k3 kappa 3/4", LIMIT): 0.7428264,
           ("k3 kappa 3/5", HELD): 0.7430799, ("k3 kappa 3/5", LIMIT): 0.7425970}


def relaxed_opt(key, d0):
    k, kappa, _, _ = pt.RELAXED_TIES[key]
    return opt(k, "C", d0, c=float(pt.plain_coeff(k, kappa)))


@pytest.mark.parametrize("row", sorted(RELAXED), ids=lambda r: f"{r[0]}-{r[1]}")
def test_relaxed_tie_points_and_their_exact_brackets(row):
    key, d0 = row
    k, kappa, _, _ = pt.RELAXED_TIES[key]
    c = pt.plain_coeff(k, kappa)
    r = relaxed_opt(key, d0)
    assert r["valid"] and abs(r["sigma0"] - RELAXED[row]) < 6e-8
    lb = pt.best_exact_bound(k, "C", delta0=d0, c=c, cuts=16)["sigma0_lower"]
    ub = pt.exact_upper_bound(k, "C", delta0=d0, measured=r, c=c)
    assert ub["valid"], ub
    assert lb <= ub["sigma0_upper"] and ub["sigma0_upper"] - lb < Fr(1, 10 ** 8)
    assert float(lb) <= r["sigma0"] + 1e-12 and r["sigma0"] <= float(ub["sigma0_upper"]) + 1e-12


def test_relaxed_ties_are_admissible_and_help():
    """Lemma plain at kappa needs beta_* <= (1 + kappa)/2, none at kappa = 1 (line 12565)."""
    for key, (k, kappa, need, _) in pt.RELAXED_TIES.items():
        assert (need is None) == (kappa == 1)
        assert need is None or need == (1 + kappa) / 2
        assert pt.plain_count_decreasing(pt.plain_coeff(k, kappa))
    # what supplies each hypothesis: the order-3 Part I analogue 5/6 < 7/8, and the
    # kappa = 3/4 point (below 4/5 at both bins) for kappa = 3/5
    assert pt.part_one_target(3) == Fr(5, 6) < pt.RELAXED_TIES["k3 kappa 3/4"][2]
    assert all(RELAXED[("k3 kappa 3/4", d0)] < pt.RELAXED_TIES["k3 kappa 3/5"][2]
               for d0 in (HELD, LIMIT))
    # stated range 3/4 <= kappa <= 1: the first two inside, the third below it and below
    # Liu's 13/18
    k1, k2, k3 = (pt.RELAXED_TIES[key][1] for key in ("k2 kappa 1", "k3 kappa 3/4",
                                                       "k3 kappa 3/5"))
    assert pt.KAPPA_P <= k1 <= 1 and pt.KAPPA_P <= k2 <= 1 and k3 < pt.LIU_KAPPA_FLOOR
    # the k = 2 point at the paper's bin is the floor wall exactly
    assert pt.best_exact_bound(2, "C", c=Fr(1), cuts=16)["sigma0_lower"] == Fr(39, 64)
    # a larger c helps (each value below the variant-B value at the same k and bin) ...
    for key, d0 in RELAXED:
        k = pt.RELAXED_TIES[key][0]
        table = MEASURED if d0 == HELD else MEASURED_LIMIT
        assert RELAXED[(key, d0)] <= table[(k, "B")] + 1e-12
    # ... until the slot supply binds: at k = 2, kappa = 3/4 (c = 4/3) it already fails
    assert pt.plain_coeff(2, Fr(3, 4)) == Fr(4, 3)
    r = opt(2, "C", HELD, c=float(Fr(4, 3)))
    assert not r["valid"] and r["reason"] == "requested capacity exceeds the slot supply"


def test_variant_c_moment_requirements():
    """Only the tied variant asks for kappa_0 = 2 sigma_0 - 1 below 3/4 (section 4)."""
    k6, k5, k4 = (opt(k, "C")["kappa0"] for k in (6, 5, 4))
    assert float(pt.LIU_KAPPA_FLOOR) < k6 < float(pt.KAPPA_P)
    assert k5 < float(pt.LIU_KAPPA_FLOOR) and k4 < float(pt.LIU_KAPPA_FLOOR)
    assert (f"{k6:.4f}", f"{k5:.4f}", f"{k4:.4f}") == ("0.7499", "0.6982", "0.6194")
    # variants A and B: c = 4/9 is Lemma plain at kappa = 3/4, whose hypothesis is 7/8
    assert pt.plain_coeff(6, pt.KAPPA_P) == pt.C_P and (1 + pt.KAPPA_P) / 2 == Fr(7, 8)


def test_thresholds_per_wall():
    """Which orders k beat 13/15, Xu and Sang's 0.8748867 and 0.8748087, wall by wall."""
    def below(th, f):
        return [k for k in KS if f(k) < th]
    floors = (lambda k: WALLS[k][2], lambda k: WALLS[k][3])
    for th in (pt.THIRTEEN_FIFTEENTHS, pt.XU_SANG, pt.NEWER_RECORD):
        assert below(th, pt.corner_target) == [2, 3, 4, 5]
        assert below(float(th), lambda k: MEASURED[(k, "A")]) == [2, 3, 4, 5]
        assert below(float(th), lambda k: MEASURED_LIMIT[(k, "A")]) == [2, 3, 4, 5]
        assert all(below(th, f)[:4] == [2, 3, 4, 5] for f in floors)
        assert all(v < float(th) for v in RELAXED.values())
    assert below(pt.XU_SANG, pt.part_one_target) == [2, 3]
    assert pt.part_one_target(4) == Fr(7, 8)
    for th in (pt.XU_SANG, pt.NEWER_RECORD):
        assert all(below(th, f) == [2, 3, 4, 5, 6] for f in floors)
    assert below(pt.THIRTEEN_FIFTEENTHS, floors[0]) == [2, 3, 4, 5]
    # k >= 8 is worse than the paper's own 7/8 at every wall
    assert all(pt.corner_target(k) > Fr(7, 8) for k in (8, 12))
    assert all(MEASURED[(k, v)] > 0.875 for k in (8, 12) for v in "ABC")
    # the room FOLLOWUPS.md measures against 13/15, and the same room against 167/192
    assert f"{float(pt.NEWER_RECORD - Fr(13, 15)):.7f}" == "0.0081420"
    assert f"{float(pt.NEWER_RECORD - Fr(167, 192)):.7f}" == "0.0050170"


def test_perfect_row_counts_meet_the_floor_wall():
    """With the row-count excess removed (alpha = 0, so K = 0) the scan hits the floor wall."""
    for d0 in (HELD, LIMIT):
        for k in (4, 6, 12):
            r = opt(k, "A", d0, alpha=0.0)
            assert abs(r["sigma0"] - float(pt.floor_wall_closed(k, d0))) < 1e-12


#: section 5 of PROBE.md: variant A at k = 6, (paper's floor bin, limit), measured
PRICES = {
    "none": (0.8749571, 0.8749571),
    "k5": (0.8494278, 0.8494278),
    "gram 1/18": (0.8714226, 0.8710590),
    "gram 1/24": (0.8696095, 0.8690251),
    "gram 0": (0.8639502, 0.8633974),
    "alpha 3/4": (0.8745098, 0.8745098),
    "alpha 1/2": (0.8722267, 0.8722267),
    "alpha 0": (167 / 192, 13 / 15),
    "c 1": (0.8741768, 0.8741768),
    "c 1.144": (0.8738710, 0.8738710),
}
PRICE_KW = {"none": {}, "gram 1/18": dict(gram=1 / 18), "gram 1/24": dict(gram=1 / 24),
            "gram 0": dict(gram=0.0), "alpha 3/4": dict(alpha=0.75), "alpha 1/2": dict(alpha=0.5),
            "alpha 0": dict(alpha=0.0), "c 1": dict(c=1.0), "c 1.144": dict(c=1.144)}


def price(name, d0):
    if name == "k5":
        return opt(5, "A", d0)["sigma0"]
    return opt(6, "A", d0, **PRICE_KW[name])["sigma0"]


def pole_slope(d0):
    lo, hi = opt(5.99, "A", d0)["sigma0"], opt(6.01, "A", d0)["sigma0"]
    return (hi - lo) / (1 / 6.01 - 1 / 5.99)


def test_prices_of_single_constants_at_k6():
    for i, d0 in enumerate((HELD, LIMIT)):
        for name in PRICES:
            assert abs(price(name, d0) - PRICES[name][i]) < 1e-6, (name, d0)
        assert f"{pole_slope(d0):.4f}" == "-0.7618"
        # Gram exponent at 0: the slot supply binds at 7/37
        assert abs(opt(6, "A", d0, gram=0.0)["supply_ratio"] - 7 / 37) < 1e-9
        # c = 1.144 is a local best on the grid of step 0.001 and the supply binds there
        assert price("c 1.144", d0) < opt(6, "A", d0, c=1.143)["sigma0"]
        assert price("c 1.144", d0) < opt(6, "A", d0, c=1.145)["sigma0"]
        cb = opt(6, "A", d0, c=1.144)
        assert abs(cb["supply_ratio"] - pt.supply_needed_float(1.144)) < 1e-9
        assert not opt(6, "A", d0, c=1.2)["valid"]
    assert pt.floor_ceiling(6, delta0=LIMIT, g=Fr(0))["sigma0"] == Fr(31, 36)
    assert pt.floor_ceiling(6, delta0=HELD, g=Fr(0))["sigma0"] == Fr(1601, 1854)
    # the rounded gains PROBE.md quotes (paper's bin; then the limit)
    g = gains()
    assert g == {"k": "0.0255", "gram": "0.0110", "alpha": "0.0052", "c": "0.0011",
                 "a34": "0.0004", "a12": "0.0027", "c1": "0.0008",
                 "gram_l": "0.0116", "alpha_l": "0.0083"}


def gains() -> dict:
    base = price("none", HELD)
    out = {"k": base - price("k5", HELD), "gram": base - price("gram 0", HELD),
           "alpha": base - price("alpha 0", HELD), "c": base - price("c 1.144", HELD),
           "a34": base - price("alpha 3/4", HELD), "a12": base - price("alpha 1/2", HELD),
           "c1": base - price("c 1", HELD),
           "gram_l": price("none", LIMIT) - price("gram 0", LIMIT),
           "alpha_l": price("none", LIMIT) - price("alpha 0", LIMIT)}
    return {key: f"{v:.4f}" for key, v in out.items()}


# --------------------------------------------------------------- planted faults
FAULT_SIGNAL, FAULT_PX, FAULT_FLOOR = Fr(1, 1000), Fr(1, 100), Fr(1, 100)


def test_planted_faults_turn_the_reproductions_red(monkeypatch):
    """A check that cannot fail is not a check: four faults, each must be caught."""
    faults = [
        ("gram_low", lambda k: Fr(1, k)),            # forget the Cauchy-Schwarz half
        ("z_pole", lambda k: Fr(1, k + 1)),          # move the pole
        ("signal_shift", lambda k, ell, M, b: Fr(11, 16) + FAULT_SIGNAL),
        ("FLOOR_HELD", FAULT_FLOOR),                 # move the floor bin
    ]
    for name, fake in faults:
        with monkeypatch.context() as m:
            m.setattr(pt, name, fake)
            bad = [r["name"] for r in pt.reproductions() if r["got"] != r["want"]]
            assert bad, f"planted fault in {name} was not caught"


#: PROBE.md section 7: the Gram coefficient set to 1/k gives exactly these values
HAND_FAULT = {"low exponent 3/16": Fr(19, 96), "target 7/8": Fr(85, 96),
              "C_0 = -1/48": Fr(-1, 32), "worst point 79/204: -E_* = 7/30672": Fr(653, 61344)}


def test_the_hand_planted_gram_fault_gives_the_recorded_fail_lines(monkeypatch):
    with monkeypatch.context() as m:
        m.setattr(pt, "gram_low", lambda k: Fr(1, k))
        bad = {r["name"]: r["got"] for r in pt.reproductions() if r["got"] != r["want"]}
    assert bad == HAND_FAULT


def test_planted_fault_in_the_row_counts_is_caught(monkeypatch):
    with monkeypatch.context() as m:
        m.setattr(pt, "p_x", lambda x, c: (2 - 2 * c * x) * (1 - x) + FAULT_PX)
        assert not pt.paper_completed_square_identity(Fr(1, 3), Fr(1, 4))
        w = pt.endpoint_neg_e(6, pt.ELL_P, pt.M_P, pt.B_P, Fr(79, 204), Fr(1, 2),
                              pt.ALPHA_P, pt.C_P)
        assert w != Fr(7, 30672)


# ---------------------------------------------------------- the lexical rules
def test_lane_files_obey_the_lexical_rules():
    stem = "cert" + "if"
    for name in ("probe_table.py", "test_probe_table.py", "PROBE.md"):
        path = HERE / name
        if not path.exists():
            continue
        data = path.read_bytes().decode("utf-8")
        assert stem not in data.lower(), name
        assert data.isascii(), name          # so no em dash, en dash or other dash either


# ------------------------------------------------------------ the page itself
_ARXIV = re.compile(r"\b\d{4}\.\d{4,5}(?:v\d+)?\b")
_NUMBER = re.compile(r"(?<![\w.])-?\d+\.\d+|(?<![\w.])\d+e-\d+")
_FRACTION = re.compile(r"(?<![\w/.])\d+/\d+(?![\w/(]|\.\d)")
_LINE_REF = re.compile(r"\b((?:cached |v[12] |its )?source )?lines? (\d+(?:(?:,? and |, | to )\d+)*)")


def _tokens(s: str) -> Counter:
    return Counter(_NUMBER.findall(_ARXIV.sub(" ", s)))


def _fractions(s: str) -> set:
    return set(_FRACTION.findall(_ARXIV.sub(" ", s)))


def _tex_fractions(snippet: str) -> set:
    """Fractions of a LaTeX snippet, with \\frac{a}{b}, \\frac ab and mixed forms as a/b."""
    s = re.sub(r"\\frac\{(\d+)\}\{(\d+)\}", r" \1/\2 ", snippet)
    s = re.sub(r"\\frac(\d)\{(\d+)\}", r" \1/\2 ", s)
    s = re.sub(r"\\frac\{(\d+)\}(\d)", r" \1/\2 ", s)
    s = re.sub(r"\\frac(\d)(\d)", r" \1/\2 ", s)
    return _fractions(s)


def _f(v) -> str:
    return str(Fr(v))


def page_phrases() -> list[str]:
    """Every phrase of PROBE.md that carries a decimal, a load-bearing fraction or a
    load-bearing line number, with the value computed or quoted.  The tables of sections
    1, 3, 4 and 5 are rendered whole."""
    m7 = {key: f"{v:.7f}" for key, v in MEASURED.items()}
    l7 = {key: f"{v:.7f}" for key, v in MEASURED_LIMIT.items()}
    p7 = {key: (f"{a:.7f}", f"{b:.7f}") for key, (a, b) in PRICES.items()}
    x7 = {key: f"{v:.7f}" for key, v in RELAXED.items()}
    g = gains()
    c6 = f"{opt(6, 'C')['sigma0']:.10f}"
    lb = pt.best_exact_bound(6, "A")["sigma0_lower"]
    ub = pt.exact_upper_bound(6, "A", measured=opt(6, "A"))["sigma0_upper"]
    ub10 = f"{math.ceil(ub * 10 ** 10) / 10 ** 10:.10f}"
    r6 = opt(6, "A")
    c0 = r6["ell"] / 2 + 0.5 - 0.75 * r6["M"] + r6["b"] * (0.25 - 1 / 12)
    fl6 = c0 + (1 + r6["ell"] - r6["M"] / 2) * float(HELD)
    kap = [f"{opt(k, 'C')['kappa0']:.4f}" for k in (6, 5, 4)]
    slope = f"{pole_slope(HELD):.4f}"
    room13 = f"{float(pt.NEWER_RECORD - Fr(13, 15)):.7f}"
    room167 = f"{float(pt.NEWER_RECORD - Fr(167, 192)):.7f}"
    liu, xs, ys = "0.874957019420098946", "0.8748867", "0.8748087"
    C = {key: n for key, (n, _) in pt.CITATIONS.items()}
    W = {k: pt.system_prices(k) for k in KS}

    def row(k, cells):
        return f"| {k} | " + " | ".join(cells) + " |"
    table1 = [pt.provenance_row(r) for r in pt.PROVENANCE]
    table3 = [row(k, [_f(W[k]["part_one"]), _f(W[k]["corner"]), _f(W[k]["floor_held"]),
                      _f(W[k]["floor_limit"])]) for k in KS]
    table4 = [
        row(2, [f"{m7[(2, 'A')]} = 39/64 (the floor binds)", f"{m7[(2, 'B')]} = 39/64 (the floor binds)",
                "no fixed point of the tie (c >= 2)", f"{l7[(2, 'A')]}, {l7[(2, 'B')]}, no fixed point"]),
        row(3, [m7[(3, "A")], m7[(3, "B")], "no fixed point of the tie (slot supply)",
                f"{l7[(3, 'A')]}, {l7[(3, 'B')]}, no fixed point"]),
        row(4, [m7[(4, "A")], m7[(4, "B")], m7[(4, "C")],
                f"{l7[(4, 'A')]}, {l7[(4, 'B')]}, {l7[(4, 'C')]}"]),
    ] + [row(k, [m7[(k, "A")], m7[(k, "B")], m7[(k, "C")], "unchanged"]) for k in (5, 6, 8, 12)]
    relaxed_rows = []
    for key, supplied in (("k2 kappa 1", "kappa = 1"),
                          ("k3 kappa 3/4", f"the order-3 Part I analogue {pt.part_one_target(3)}"),
                          ("k3 kappa 3/5", "the row above")):
        k, kappa, need, _ = pt.RELAXED_TIES[key]
        inside = pt.KAPPA_P <= kappa <= 1
        hyp = "none" if need is None else f"beta_* <= {need}"
        rng = "inside" if inside else f"below it, and below Liu's {pt.LIU_KAPPA_FLOOR}"
        held = x7[(key, HELD)]
        if pt.best_exact_bound(k, "C", c=pt.plain_coeff(k, kappa), cuts=16)["sigma0_lower"] \
                == WALLS[k][2]:
            held += f" = {WALLS[k][2]} (the floor binds)"
        relaxed_rows.append(row(k, [_f(kappa), _f(pt.plain_coeff(k, kappa)), hyp, supplied, rng,
                                    held, x7[(key, LIMIT)]]))
    table5 = [
        f"| none | {p7['none'][0]} | {p7['none'][1]} |",
        f"| pole, slope in 1/k near 1/6 | {slope} per unit | {pole_slope(LIMIT):.4f} per unit |",
        f"| row order k = 6 to 5 | {p7['k5'][0]} | {p7['k5'][1]} |",
        f"| Gram exponent 1/12 to 1/18 (cap moved with it) | {p7['gram 1/18'][0]} | {p7['gram 1/18'][1]} |",
        f"| Gram exponent to 1/24 | {p7['gram 1/24'][0]} | {p7['gram 1/24'][1]} |",
        f"| Gram exponent to 0 (slot supply binds at 7/37) | {p7['gram 0'][0]} | {p7['gram 0'][1]} |",
        f"| alpha 5/6 to 3/4 | {p7['alpha 3/4'][0]} | {p7['alpha 3/4'][1]} |",
        f"| alpha to 1/2 | {p7['alpha 1/2'][0]} | {p7['alpha 1/2'][1]} |",
        f"| alpha to 0 (no row-count excess) | 167/192 = {p7['alpha 0'][0]} | 13/15 = {p7['alpha 0'][1]} |",
        f"| plain capacity c 4/9 to 1 | {p7['c 1'][0]} | {p7['c 1'][1]} |",
        "| c near 1.144 (a local best on a grid of step 0.001; the slot supply binds) | "
        f"{p7['c 1.144'][0]} | {p7['c 1.144'][1]} |",
    ]
    # exact values behind the prose
    _, _, h6 = pt.geometry(pt.ELL_P, pt.M_P, pt.B_P)
    yh, yl = pt.floor_dual_multipliers(6, HELD), pt.floor_dual_multipliers(6, LIMIT)
    fh, fl = pt.floor_ceiling(6, delta0=HELD), pt.floor_ceiling(6, delta0=LIMIT)
    g0h = pt.floor_ceiling(6, delta0=HELD, g=Fr(0))["sigma0"]
    g0l = pt.floor_ceiling(6, delta0=LIMIT, g=Fr(0))["sigma0"]
    dg = (pt.target(6, pt.ELL_P, pt.M_P, pt.B_P, g=Fr(1, 12))
          - pt.target(6, pt.ELL_P, pt.M_P, pt.B_P, g=Fr(0)))
    kapc = {k: pt.kappa_of_c(k, pt.C_P) for k in KS}
    want = {r["name"]: r["want"] for r in pt.reproductions()}
    reg2 = [k for k in range(2, 40) if pt.held_inputs_fit(k)["residue_in_region_two"]]
    prose = [
        # summary
        f"The paper's floor bin is a = {(1 + HELD) / 2}, delta_0 = {HELD} (line {C['floor_bin']})",
        f"At k = 6: {W[6]['part_one']}, {W[6]['corner']}, and {W[6]['floor_held']} at the paper's "
        f"bin, {W[6]['floor_limit']} in the limit.",
        f"the paper follows their Section 3 recursion, line {C['bgl_recursion']})",
        f"the template returns {c6}, the optimum Liu states",
        f"(2610.12234v2, {liu}, cached source line 131) to 1e-12, together with his binding "
        "point xi in (0.38858, 0.38859) and his ell and b",
        "(1507 - 2 sqrt 921)/1653 (2610.12234v1, cached source line 104) to 1e-12.",
        f"the endpoint at x = 1/2 near delta = {r6['delta_bind']:.4f} and the tie.",
        f"One step of the row order, 6 to 5, is worth {g['k']}.",
        f"removing the Gram exceptional term outright {g['gram']}, removing the row-count "
        f"excess outright (alpha -> 0) {g['alpha']}, the plain capacity at its best (c near "
        f"1.144, a local best on a grid of step 0.001, where the slot supply binds) {g['c']}.",
        f"alpha from 5/6 to 3/4 buys {g['a34']} and to 1/2 buys {g['a12']}, c from 4/9 to 1 "
        f"buys {g['c1']}.",
        f"endpoint below 13/15, {xs} and {ys}; k = 8",
        f"The balanced probe is below {xs} only for k <= 3",
        f"(lines {C['twist_exponents']} and {C['twist']}); in Part II the twist is the row "
        f"character, whose exponent at p is the valuation j_p of the row u (line "
        f"{C['row_valuations']}).",
        f"admissible points: {x7[('k2 kappa 1', HELD)]} at k = 2 (the floor wall {WALLS[2][2]}) "
        f"and {x7[('k3 kappa 3/4', HELD)]} at k = 3",
        "Goldmakher and Louvel, Theorem 1.3, read here from the arXiv copy",
        # section 1
        f"lies in region two (z_r >= {pt.REGION_TWO_Z}) exactly for k <= {max(reg2)}, so every "
        f"k >= {max(reg2) + 1}",
        "Their Theorem 1.3 has the same term for n-th order characters",
        # section 3
        "0 <= delta_0 <= 1/2 the minimum of M - 2 ell is",
        # the vertex test_floor_wall_dual_identity_symbolically... checks in sympy
        "attained at b = 0 and ell = (1/4 - delta_0/2)/(5/4 + 3 delta_0/2)",
        f"At the paper's bin m = {yh[3]} at ell = {fh['ell']}, M = {fh['M']} (multipliers "
        f"{yh[0]} and {yh[1]}); in the limit m = {yl[3]} at ell = {fl['ell']}, M = {fl['M']} "
        f"(multipliers {yl[0]} and {yl[1]}).",
        "(derived; the LP is infeasible at delta_0 = 51/100)",
        f"both floors are below 13/15 and {xs} for every k <= 5",
        f"at k = 6 both floors (167/192 and 13/15) are below {xs};",
        f"the balanced probe is below {xs} only for k <= 3",
        f"reports a newer record of {ys} for Dirichlet",
        f"against 13/15 ({room13})",
        f"the same room is {room167}, the distance from {ys} to 167/192",
        # section 4
        f"is narrower than 2e-8 (`test_endpoint_optimum_and_exact_bracket`, {len(BRACKET_ROWS)} rows",
        f"which this hunt has at {xs} and {ys} from other inputs",
        f"Variant C at k = 6 gives {c6}, matching Liu v2's {liu} to 1e-12, with binding delta "
        "in Liu's interval (0.38858, 0.38859) and his ell and b (v2 source lines 302 to 304) to 1e-6",
        f"Variant A gives {m7[(6, 'A')]}, Liu v1's closed form (1507 - 2 sqrt 921)/1653 to 1e-12",
        f"`{lb.numerator}/{lb.denominator} <= sigma_0 <= {ub10}`",
        f"above hunt #134's exact bounds {H134_ROBUST} and {H134_GRAM}, which `single_point_bound` "
        f"without the floor reproduces exactly at hunt #134's witness points delta = "
        f"{H134_ROBUST_AT} (no Gram cap) and delta = {H134_GRAM_AT} (Gram cap), x = 1/2.",
        "a float optimum of 0.874958 in its RESULTS.md, from a b-grid of step 0.01;",
        "and at the measured binding point the template's R_* is 2/3 to 1e-6.",
        "largest ell stays between 0.16 and 0.20 in every row",
        "returns the floor wall of section 3 to 1e-12 for k = 4, 6, 12",
        "(measured, each bracketed exactly on both sides, narrower than 1e-8, the lower end with "
        "cutting planes; `test_relaxed_tie_points_and_their_exact_brackets`)",
        f"which it already does at k = 2 with kappa = 3/4 (c = {pt.plain_coeff(2, Fr(3, 4))}).",
        f"Variants A and B hold c = {pt.C_P}, which is kappa = 9/(2k): {kapc[2]}, {kapc[3]} and "
        f"{kapc[4]} at k = 2, 3 and 4, above 1",
        f"{kapc[5]} at k = 5, inside the stated range 3/4 <= kappa <= 1 (line "
        f"{C['plain_kappa']}), with hypothesis beta_* <= {(1 + kapc[5]) / 2} (line "
        f"{C['plain_hypothesis']}), which the order-5 Part I analogue {pt.part_one_target(5)} "
        "supplies;",
        f"{kapc[6]} at k = 6, with hypothesis beta_* <= {(1 + kapc[6]) / 2}, which the paper's "
        "theorem supplies.",
        f"kappa = {kapc[8]} = {float(kapc[8])} and {kapc[12]} = {float(kapc[12])}, below the "
        "stated range;",
        f"the c of kappa = 3/4 ({pt.plain_coeff(8, pt.KAPPA_P)} and "
        f"{pt.plain_coeff(12, pt.KAPPA_P)}) only raises their A and B values (measured).",
        f"below 3/4: {kap[0]} at k = 6, inside Liu v2's extension",
        f"and {kap[1]} at k = 5 and {kap[2]} at k = 4, below it.",
        # section 5
        f"the step in k {g['k']}; the Gram term removed {g['gram']}; the row-count excess "
        f"removed {g['alpha']}; c at its best {g['c']} (in the limit the second and third are "
        f"{g['gram_l']} and {g['alpha_l']}).",
        f"d sigma_0 / d z_* = -(h - b/2) = {-(h6 - pt.B_P / 2)} with the Gram term tied to the "
        f"pole, -h = {-h6} with it held;",
        f"would be worth {dg} there.",
        f"the perfect-row-count wall drops to {g0h} at the paper's bin and to {g0l} in the limit",
        # section 6
        f"(line {C['dual_character']}; principal Ramanujan factors at j_p = 4, line "
        f"{C['dual_ramanujan']})",
        f"gamma_2(c) alpha-bar(cn^3) (line {C['coefficient_alpha']})",
        f"`gamma_1 gamma_2 = -alpha(p) chi_p(4)^- gamma_3` (line {C['gauss_pair']})",
        f"the quadratic large sieve (line {C['quadratic_sieve']})",
        f"gamma_2 gamma_4 = 1 (line {C['gamma24']})",
        "his B-flat is stated as 0.874886647 (source line 122)",
        f"(section 4): {kap[1]} at k = 5, below the 13/18",
        "Blomer, Goldmakher and Louvel, arXiv 1112.1650, Theorem 1.3, read here from the arXiv PDF",
        # section 7
        f"{want['C_II shift 11/16']}, {want['low exponent 3/16']}, {want['target 7/8']}, "
        f"{want['Part I shift 2/3']}, {want['Part I low 1/4']}, {want['Part I target 11/12']} "
        f"(line {C['part_I_target']}), h = {want['h = 13/16']}, C_0 = {want['C_0 = -1/48']}, "
        f"the floor {want['floor -7/1200']}, the large-delta formula {want['C_0 = -1/48']} - "
        f"delta/16, the supply {want['supply 8/39']} and the inverse capacity "
        f"{want['inverse capacity 7/37']}.",
        f"the worst point {want['worst point 79/204: -E_* = 7/30672']} at delta = 79/204, and "
        f"{want['floor ceiling 13/15 in the limit delta_0 -> 0']}.",
        f"hunt #134's exact bounds {H134_ROBUST} and {H134_GRAM}, reproduced exactly at its "
        "witness points",
        f"shifting the signal by {FAULT_SIGNAL}, adding {FAULT_PX} to P_x, or moving the floor "
        f"bin to {FAULT_FLOOR}",
        f"(low exponent {HAND_FAULT['low exponent 3/16']}, target {HAND_FAULT['target 7/8']}, "
        f"C_0 = {HAND_FAULT['C_0 = -1/48']}, worst point "
        f"{HAND_FAULT['worst point 79/204: -E_* = 7/30672']}).",
        # open issues
        f"Liu's B-flat 0.874886647 and the record {ys} that `FOLLOWUPS.md` reports",
        # the doors
        f"at delta = {r6['delta_bind']:.4f}, x = 1/2** (binding, with the offset b = "
        f"{r6['b']:.4f} interior where -E_* is flat in b). Its pole price is {slope} per unit "
        f"of 1/k; its row-count prices are alpha ({g['a34']} from 5/6 to 3/4, {g['alpha']} to "
        f"0) and c ({g['c1']} from 4/9 to 1, {g['c']} at its best).",
        f"ell/h = {r6['supply_ratio']:.4f} against 7/37: slack here, binding once the Gram "
        "exponent is lowered or c reaches 1.144 (section 5).",
        f"b <= 3(1 - 3 ell)/8 = {(1 - 3 * r6['ell']) * 3 / 8:.4f} against b = {r6['b']:.4f}: slack.",
        f"C_0 = {c0:.4f}, and {fl6:.4f} with the paper's bin: slack;",
        f"the largest lever ({g['k']} for the step to k = 5)",
        f"| row excess K | {g['a34']} to 3/4, {g['a12']} to 1/2, {g['alpha']} to 0 |",
        f"| row excess K; slot supply | {g['c1']} to 1, {g['c']} at its best |",
        f"the k = 6 template optimum is {m7[(6, 'A')]} with fixed capacity and {c6} with the tied one",
        f"the row-count lever is worth at most {g['alpha']} at the paper's bin ({g['alpha_l']} in "
        f"the limit), single steps of alpha and c {g['a34']} to {g['a12']}; the Gram exponent "
        f"would buy up to {g['gram']} but",
        # section labels of cited works
        "(section 1.2); after Hecke theory",
        "for even (odd) n (section 1.2);",
        'generality" (section 4.5);',
        "(Remark 4.6).",
    ]
    counts = [
        f"checked by `verify_citations` (all {len(pt.CITATIONS)} on their stated line)",
        f"(`OUTSIDE_CITATIONS`, all {len(pt.OUTSIDE_CITATIONS)} checked",
        f"{len(pt.reproductions())} values rebuilt from the general-k formulas. Twelve are printed",
        "The paper's completed-square identity holds on 105 points.",
        "checked in sympy, symbolic in k and delta_0, and exactly for k = 2 to 39)",
        f"on {N_FEAS} random rational points on which every constraint is both met and missed",
    ]
    return table1 + table3 + table4 + relaxed_rows + table5 + prose + counts


def allowed_fractions() -> set:
    """Fractions the page may print: those of the computed or quoted phrases, those of the
    cited lines (paper and outside sources), and the module's pinned constants."""
    allowed = set().union(*(_fractions(p) for p in page_phrases()))
    for _, snip in pt.CITATIONS.values():
        allowed |= _tex_fractions(snip)
    for _, _, snip in pt.OUTSIDE_CITATIONS.values():
        allowed |= _tex_fractions(snip)
    consts = [pt.ELL_P, pt.M_P, pt.B_P, pt.ALPHA_P, pt.KAPPA_P, pt.C_P, pt.ZC_P, pt.FLOOR_HELD,
              pt.REGION_TWO_X, pt.REGION_TWO_Z, pt.LIU_KAPPA_FLOOR, pt.THIRTEEN_FIFTEENTHS,
              (1 + pt.FLOOR_HELD) / 2, pt.supply_needed(pt.C_P)]
    consts += [pt.z_pole(k) for k in KS] + [abs(pt.c0_closed(6, pt.ELL_P, pt.M_P, pt.B_P))]
    for key, (k, kappa, need, _) in pt.RELAXED_TIES.items():
        consts += [kappa, pt.plain_coeff(k, kappa)] + ([need] if need else [])
    return allowed | {str(Fr(v)) for v in consts if Fr(v).denominator != 1}


def line_problems(flat: str) -> list[str]:
    """Every 'line N' must be a paper line a citation checks; every 'source line N' a line
    of an outside source that a citation checks; a range 'N to M' must be short and hold
    a checked line."""
    cited = {n for n, _ in pt.CITATIONS.values()}
    outside = {n for _, n, _ in pt.OUTSIDE_CITATIONS.values()}
    out = []
    for m in _LINE_REF.finditer(flat):
        pool = outside if m.group(1) else cited
        for item in re.split(r",? and |, ", m.group(2)):
            if " to " in item:
                a, b = (int(v) for v in item.split(" to "))
                if not (a < b <= a + 40 and any(a <= n <= b for n in pool)):
                    out.append(f"bad line range: {m.group(0)}")
            elif int(item) not in pool:
                out.append(f"unchecked line: {m.group(0)}")
    return out


def _section_tables(text: str, heading: str) -> list[list[list[str]]]:
    """The markdown tables of one section of the raw page, as rows of stripped cells."""
    lines = text.splitlines()
    start = next(i for i, ln in enumerate(lines) if ln.startswith(heading))
    tables, cur = [], None
    for ln in lines[start + 1:]:
        s = ln.strip()
        if ln.startswith("## "):
            break
        if s.startswith("|"):
            cells = [c.strip() for c in s.strip("|").split("|")]
            if cur is None:
                cur = []
                tables.append(cur)
            if not set("".join(cells)) <= set("-: "):
                cur.append(cells)
        else:
            cur = None
    return tables


def table_problems(text: str) -> list[str]:
    """Row counts of the rendered tables, and the walls of the section 6 systems table."""
    out = []
    t1 = _section_tables(text, "## 1.")
    if len(t1) != 1 or len(t1[0]) - 1 != len(pt.PROVENANCE):
        out.append("section 1 table does not have one row per PROVENANCE entry")
    t3 = _section_tables(text, "## 3.")
    if len(t3) != 1 or [r[0] for r in t3[0][1:]] != [str(k) for k in KS]:
        out.append("section 3 table rows are not k = " + ", ".join(map(str, KS)))
    t4 = _section_tables(text, "## 4.")
    if len(t4) != 2 or len(t4[0]) - 1 != len(KS) or len(t4[1]) - 1 != len(pt.RELAXED_TIES):
        out.append("section 4 tables have the wrong number of rows")
    t6 = _section_tables(text, "## 6.")
    if len(t6) != 1 or len(t6[0]) - 1 != len(pt.SYSTEMS):
        out.append("section 6 table does not have one row per system")
        return out
    names = {s["name"].split()[0]: s["k"] for s in pt.SYSTEMS}
    for cells in t6[0][1:]:
        tag, kcell, walls = cells[0].split()[0], cells[3], cells[4]
        if walls in ("as S0", "worse"):
            continue
        k = int(kcell)
        p = pt.system_prices(k)
        if names.get(tag) != k or walls != f"{p['part_one']} / {p['corner']} / {p['floor_held']}":
            out.append(f"section 6 walls of {tag}: {walls}")
    return out


def prose_problems(text: str) -> list[str]:
    """Problems with the page's numbers: a phrase missing, a decimal no phrase covers, a
    fraction that is neither computed nor cited, an unchecked line, a table out of shape."""
    flat = " ".join(text.split())
    phrases = page_phrases()
    problems = [f"missing phrase: {p}" for p in phrases if p not in flat]
    want = sum((_tokens(p) for p in phrases), Counter())
    got = _tokens(flat)
    if got != want:
        problems.append(f"decimals differ: unpinned {dict(got - want)}, missing {dict(want - got)}")
    stray = _fractions(flat) - allowed_fractions()
    if stray:
        problems.append(f"fractions neither computed nor cited: {sorted(stray)}")
    return problems + line_problems(flat) + table_problems(text)


def test_probe_md_numbers_are_the_pinned_ones():
    """Every decimal, fraction, line reference and table of PROBE.md is pinned."""
    assert prose_problems(PROBE_MD.read_text(encoding="utf-8")) == []


PROSE_FAULTS = [
    ("is worth 0.0255.", "is worth 0.0355."),                     # the k-step price, summary
    ("ell/h = 0.2055", "ell/h = 0.2155"),                         # the doors
    ("C_0 = -0.0209", "C_0 = -0.0309"),                           # the doors
    ("below 3/4: 0.7499 at k = 6", "below 3/4: 0.7999 at k = 6"), # a kappa_0 of section 4
    ("record of 0.8748087", "record of 0.8748088"),               # a quoted threshold
    ("alpha from 5/6 to 3/4 buys 0.0004", "alpha from 5/6 to 3/4 buys 0.0008"),  # a swap
    # the verifier's four typos of the first revision, which every test let through
    ("drops to 1601/1854", "drops to 1601/1845"),
    ("| 5 | 9/10 | 17/20 | 27/32 | 21/25 |", "| 5 | 9/10 | 17/20 | 27/32 | 21/52 |"),
    ("| 3 | 5/6 / 3/4 / 71/96 |", "| 3 | 5/6 / 3/4 / 17/96 |"),
    ("(line 4118)", "(line 4181)"),
    # a line of the section 1 table, two pinned fractions swapped, a relaxed-tie value,
    # one cited line swapped for another, an outside source line, a kappa of section 4
    ("| 8353, 8535, 8541 |", "| 8353, 8553, 8541 |"),
    ("| 3 | 5/6 | 3/4 | 71/96 | 11/15 |", "| 3 | 5/6 | 3/4 | 71/96 | 13/15 |"),
    ("| 0.7430799 | 0.7425970 |", "| 0.7430799 | 0.7425790 |"),
    ("gamma_2 gamma_4 = 1 (line 4124)", "gamma_2 gamma_4 = 1 (line 4118)"),
    ("v2 source line 298", "v2 source line 289"),
    ("9/4, 3/2 and 9/8 at k = 2, 3 and 4", "9/4, 3/2 and 9/7 at k = 2, 3 and 4"),
]


def _plant(text: str, old: str, new: str) -> str:
    """Replace the first occurrence of `old` in the raw page, matching any whitespace."""
    pattern = r"\s+".join(re.escape(w) for w in old.split())
    planted, n = re.subn(pattern, lambda _m: new, text, count=1)
    assert n == 1, old
    return planted


@pytest.mark.parametrize("fault", PROSE_FAULTS, ids=lambda f: f[0][:24])
def test_prose_faults_are_caught(fault):
    """Each planted edit of the page must turn prose_problems red."""
    text = PROBE_MD.read_text(encoding="utf-8")
    planted = _plant(text, *fault)
    assert planted != text and prose_problems(planted) != []
