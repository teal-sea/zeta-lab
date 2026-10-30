"""Pin identities X1 to X18 of FOLLOWUPS.md, and X19 to X22 of its tracker table.

Until 2026-10-26 these were "scratch-exact only" (FOLLOWUPS.md section 13): checked in
session scratch storage that was swept, pinned by no test in the tree. Every check here
reads its polynomials, isolating intervals, catalogue rows and table keys from
`followups.json`, so a changed value in the JSON is caught; constants that the JSON does
not carry are written here with the line of FOLLOWUPS.md they come from.

X3 (Liu's b_new against Guo's b_dagger modulo F) cannot be pinned: Guo's b_dagger formula
is recorded nowhere in the tree. Its test is an explicit xfail that says so.

Exact arithmetic only: fractions.Fraction and sympy. No outside source is read.
"""

from __future__ import annotations

import json
from datetime import datetime
from fractions import Fraction as Fr
from pathlib import Path

import pytest
import sympy as sp

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE / "followups.json").read_text())
X = {x["id"]: x for x in DATA["identities_checked_in_scratch"]}
ALG = {a["id"]: a for a in DATA["algebraic_numbers"]}
REC = {r["id"]: r for r in DATA["records_improvements"]}

s, u, e, l, B, xi, d = sp.symbols("s u e l B xi d")


def _poly(coeffs, var):
    """Polynomial from a coefficient list, highest degree first."""
    return sum(sp.Integer(c) * var ** (len(coeffs) - 1 - i) for i, c in enumerate(coeffs))


def _interval(aid):
    lo, hi = ALG[aid]["interval"]
    return sp.Rational(sp.sympify(lo)), sp.Rational(sp.sympify(hi))


def _root_in(poly, var, lo, hi):
    """The unique real root of poly in (lo, hi), as an exact sympy root object."""
    roots = [r for r in sp.Poly(poly, var).real_roots() if lo < r < hi]
    assert len(roots) == 1, (poly, lo, hi, roots)
    return roots[0]


G = _poly(ALG["B_new"]["poly_in_s"], s)          # Guo's G(s)
F = 1188 * u**3 - 2160 * u**2 + 171 * u + 190     # Liu's cubic in xi (X1 claim text)
Q_FLAT = _poly(ALG["B_flat"]["poly_in_s"], B)      # Liu's quartic in B

B_NEW = _root_in(G, s, *_interval("B_new"))
B_FLAT = _root_in(Q_FLAT, B, *_interval("B_flat"))
B_ALG = (1507 - 2 * sp.sqrt(921)) / 1653
XU_SANG = sp.Rational(DATA["records_improvements"][[r["id"] for r in DATA["records_improvements"]].index("xu_sang_2026_10_11")]["abscissa"]["exact"])
NEWTON = sp.Rational(REC["newton_2026_10_16"]["abscissa"]["exact"])
PR68 = sp.Rational(DATA["frontier"]["best_dirichlet_on_record"]["value"])
PR69 = sp.Rational(DATA["frontier"]["smallest_claim_open_draft"]["value"])


def _b_lim():
    """Newton's B_lim from the construction recorded in followups.json."""
    q = 71656266561 * d**2 - 151802815309 * d + 55463106075
    delta0 = _root_in(q, d, sp.Rational(1, 8), sp.Rational(5, 6))
    c0 = sp.Rational(40000, 89973)
    ell0 = (5 - 6 * delta0) / (9 + 6 * (1 + c0) * delta0)
    return sp.Rational(11, 12) - ell0 / 4


def test_x1_guo_cubic_is_liu_cubic():
    assert "1188u^3 - 2160u^2 + 171u + 190" in X["X1"]["claim"]
    lhs = sp.expand(sp.cancel(G.subs(s, (7 + 18 * u) / (9 + 18 * u)) * (9 + 18 * u) ** 3))
    assert sp.expand(lhs - 108 * F) == 0


def test_x2_nielstron_cubic():
    cubic = 657 * e**3 - 954 * e**2 + 21 * e + 20
    assert sp.expand(cubic.subs(e, sp.Rational(11, 3) - 4 * s) + sp.Rational(16, 3) * G) == 0
    # and nielstron's root in [1/6, 1/5] gives B_new through 11/12 - e/4
    e0 = _root_in(cubic, e, sp.Rational(1, 6), sp.Rational(1, 5))
    lo, hi = _interval("B_new")
    assert lo < sp.Rational(11, 12) - e0 / 4 < hi


@pytest.mark.xfail(strict=True, reason="Guo's b_dagger formula is not recorded in the tree; X3 stays scratch-only")
def test_x3_b_new_matches_guo_b_dagger():
    assert "b_dagger_formula" in DATA["algebraic_numbers"][1]


def test_x4_collet_quartic_is_liu_quartic():
    collet = 927 * l**4 - 3135 * l**3 + 2433 * l**2 + 275 * l - 100
    assert sp.expand(collet.subs(l, 4 * (sp.Rational(11, 12) - B)) - sp.Rational(16, 9) * Q_FLAT) == 0


def test_x5_ordering():
    chain = [B_FLAT, _b_lim(), NEWTON, XU_SANG, B_NEW, B_ALG, sp.Rational(7, 8)]
    for a, b in zip(chain, chain[1:]):
        assert sp.simplify(b - a) > 0, (a, b)


def test_x5_intervals_isolate():
    for aid in ("B_new", "B_flat"):
        lo, hi = _interval(aid)
        poly = _poly(ALG[aid]["poly_in_s"], s)
        assert sum(1 for r in sp.Poly(poly, s).real_roots() if lo < r < hi) == 1
    lo, hi = _interval("B_alg")
    assert lo < B_ALG < hi
    assert sp.expand(_poly(ALG["B_alg"]["poly_in_s"], s).subs(s, B_ALG)) == 0
    lo, hi = _interval("B_lim_Newton")
    assert lo < _b_lim() < hi


# X6: rational stages whose ell is recorded independently in followups.json.
X6_STAGES = [
    ("gao_2026_10_07", Fr(1001, 6000), "20999/24000"),
    ("liu_v1_2026_10_08", Fr(1, 6) + Fr(1, 10000), "34999/40000"),
    ("argonaut_2026_10_08", Fr(1, 6) + Fr(1, 10**6), "3499999/4000000"),
    ("levy_2026_10_10", Fr(167, 1000), "10499/12000"),
    ("xu_sang_2026_10_11", Fr(1253399, 7500000), "8748867/10000000"),      # B_1; ell from Newton's "from"
    ("newton_2026_10_16", Fr(6267002557, 37500000000), "43744332481/50000000000"),
]


@pytest.mark.parametrize("rid,ell,value", X6_STAGES)
def test_x6_rational_stages_on_the_majorant(rid, ell, value):
    assert rid in REC
    assert value in json.dumps(REC[rid])
    assert Fr(11, 12) - ell / 4 == Fr(value)


def test_x6_stages_without_a_recorded_ell_lie_on_the_admissible_range():
    # Guo 349999/400000 and 328/375 and Xu and Sang B_0 carry no ell in the JSON: only the
    # implied ell = 4(11/12 - B) is checked to lie in [1/6, 1/5].
    for value in ("349999/400000", "328/375", "69991/80000"):
        assert value in json.dumps(DATA)
        ell = 4 * (Fr(11, 12) - Fr(value))
        assert Fr(1, 6) <= ell <= Fr(1, 5), value


def test_x7_floor_condition_is_tomoto_barrier():
    ell, M, b = sp.symbols("ell M b")
    C0 = sp.Rational(1, 2) + ell / 2 - sp.Rational(3, 4) * M + b / 6
    lx = (M - b) / 2
    tomoto = 1 - sp.Rational(5, 2) * lx - sp.Rational(13, 12) * b
    assert sp.expand((C0 - tomoto).subs(M, 1 - ell)) == 0


def test_x8_floor_rows_alone_give_167_192():
    import assembly as A
    ell = Fr(3, 16)
    assert A.FROZEN.delta0 == Fr(1, 50)
    assert A.E_floor(ell, 1 - ell, Fr(0)) == 0
    assert A.target(ell, 1 - ell, Fr(0)) == Fr(167, 192)
    assert str(Fr(167, 192).numerator * 10**7 // Fr(167, 192).denominator) == "8697916"
    # and with no floor the same model's floor condition C0 = 0 lands on 13/15
    ell0 = Fr(1, 5)
    assert A.C0(ell0, 1 - ell0, Fr(0)) == 0
    assert A.target(ell0, 1 - ell0, Fr(0)) == Fr(13, 15)


def test_x9_b_alg_between_hunt_134_bounds():
    assert sp.Rational(44117, 50422) < B_ALG < sp.Rational(874958, 10**6)


def test_x10_collet_density_minus_no_slot_count():
    rho = 1 - 10 * d / (3 * (5 - 2 * d))
    diff = sp.simplify(rho - (1 - 2 * d / 3) - 4 * d**2 / (3 * (2 * d - 5)))
    assert diff == 0
    for t in (Fr(1, 100), Fr(1, 2), Fr(12, 5)):
        assert 4 * t**2 / (3 * (2 * t - 5)) < 0


def _round_sig(x, sig):
    """x rounded to sig significant figures, as the string FOLLOWUPS.md prints."""
    return format(float(sp.N(x, 40)), f".{sig - 1}e")


def test_x11_newton_above_b_flat():
    gap = NEWTON - B_FLAT
    assert gap > 0
    assert _round_sig(gap, 3) == "2.58e-09"


def test_x12_tracker_records_below_b_flat():
    rows = DATA["tracker_frontier_records"]
    assert len(rows) == 17
    assert all(sp.Rational(r["theta"]) < B_FLAT for r in rows)
    # recompute "lowered the catalogue minimum at merge" from merge times, starting from
    # Collet's PR 9 rational just above B_flat (the catalogue minimum before PR 26)
    best = sp.Rational(ALG["B_flat"]["nearby_rationals"][0]["value"])
    lowered = {}
    for r in sorted(rows, key=lambda r: datetime.fromisoformat(r["merged_at"].replace("Z", "+00:00"))):
        th = sp.Rational(r["theta"])
        lowered[r["pr"]] = th < best
        best = min(best, th)
    assert {pr for pr, low in lowered.items() if not low} == {48, 53}
    assert all(lowered[r["pr"]] == r["lowered_catalogue_minimum_at_merge"] for r in rows)


def test_x13_b_flat_minus_pr68():
    assert _round_sig(B_FLAT - PR68, 3) == "7.79e-05"


def test_x14_proofcouncil_above_b_new():
    pc = sp.Rational(REC["proofcouncil_2026_10_09"]["abscissa"]["exact"])
    assert _round_sig(pc - B_NEW, 2) == "9.0e-13"


def test_x15_pr69_gaps():
    assert PR68 - PR69 == sp.Rational(357103, 10**10)
    assert sp.Rational(7, 8) - PR69 == sp.Rational(2270103, 10**10)
    assert _round_sig(PR69 - sp.Rational(13, 15), 5) == "8.1063e-03"


def test_x16_b_new_minus_pr68():
    assert _round_sig(B_NEW - PR68, 3) == "1.48e-04"


def test_x17_liu_ell_new_and_b_new_digits():
    xi0 = _root_in(F.subs(u, xi), xi, sp.Rational(38858, 10**5), sp.Rational(38859, 10**5))
    ell_new = (5 - 6 * xi0) / (9 + 18 * xi0)
    b_new = 8 * (3 * xi0 - 1) * (12 * xi0**2 - 40 * xi0 + 15) / (9 * (2 * xi0 + 1) * (24 * xi0**2 - 20 * xi0 + 5))
    snippets = {ev["line"]: ev["snippet"] for r in DATA["records_improvements"] if r["id"] == "liu_v2_2026_10_12"
                for ev in r.get("evidence", [])}
    printed_b = snippets[329].split("=")[1].split("\\")[0]
    printed_l = snippets[332].split("=")[1].split("\\")[0]
    def trunc(x, n):
        return str(sp.floor(sp.N(x, 60) * 10**n) / sp.Integer(10) ** n)
    assert sp.Rational(trunc(b_new, 18)) == sp.Rational(printed_b)
    assert sp.Rational(trunc(ell_new, 18)) == sp.Rational(printed_l)
    assert sp.Rational(trunc(b_new, 10)) == sp.Rational("0.1234056854")
    assert sp.Rational(trunc(ell_new, 10)) == sp.Rational("0.1668385889")
    # and B_new = (18 xi + 7)/(18 xi + 9) is the same number
    lo, hi = _interval("B_new")
    assert lo < (18 * xi0 + 7) / (18 * xi0 + 9) < hi


def test_x18_target_on_balanced_lengths_is_the_direct_majorant():
    ell, b = sp.symbols("ell b")
    lx = (1 - b - ell) / 2
    h = 1 - lx + ell
    assert sp.expand(1 - h / 6 + b / 12 - (sp.Rational(11, 12) - ell / 4)) == 0


def test_every_scratch_identity_has_a_test_here():
    assert sorted(X, key=lambda k: int(k[1:])) == [f"X{i}" for i in range(1, 19)]
    src = Path(__file__).read_text()
    for k in X:
        assert f"def test_{k.lower()}_" in src, k


# ---------------------------------------------------------------- X19 to X22, tracker table
# (FOLLOWUPS.md section 14, read 2026-10-26 from the tracker's PR heads)

def test_x19_balanced_signal_shift_equals_the_h6_signal_on_m_plus_l_one():
    """-(5/6 - x/3 - ell/6) = -(4 + b)/6 = -(4 + y - x)/6 when x + y = 1 - ell."""
    x, y, ell = sp.symbols("x y ell")
    shift_balanced = -(sp.Rational(5, 6) - x / 3 - ell / 6)
    shift_b = -(4 + (y - x)) / 6
    assert sp.expand((shift_balanced - shift_b).subs(y, 1 - ell - x)) == 0
    # and signal(theta) at theta = 11/12 - ell/4 is the low exponent x/2 + b/12
    theta = sp.Rational(11, 12) - ell / 4
    sig = (theta + shift_b).subs(y, 1 - ell - x)
    assert sp.expand(sig - (x / 2 + ((1 - ell - x) - x) / 12)) == 0


def test_x20_pr72_constants_sit_on_the_floor_model_geometry():
    """PR 72's ReturnConstants.lean: theta = 1 - c, ell = 4c - 1/3, x = 1 + ell - h, y = h - 2 ell."""
    h = Fr(80008783, 10**8)
    theta = Fr(174954253, 200000000)
    c = 1 - theta
    ell = 4 * c - Fr(1, 3)
    x, y = 1 + ell - h, h - 2 * ell
    assert c == Fr(25045747, 200000000)
    assert ell == Fr(25137241, 150000000)
    assert x == Fr(110248133, 300000000) and y == Fr(27895477, 60000000)
    assert x + y == 1 - ell                       # M + l = 1
    assert theta == Fr(11, 12) - ell / 4          # the direct majorant
    assert theta + (-(4 + y - x) / 6) == x / 2 + (y - x) / 12   # signal_low


TRACKER_BOUNDS = {   # PR: (bound in Candidate/Main.lean, as read at the PR head)
    63: Fr(87483, 100000), 64: Fr(874835173, 10**9), 66: Fr(874828524351, 10**12),
    67: Fr(174963413, 200000000), 68: Fr(8748087, 10**7), 69: Fr(8747729897, 10**10),
    70: Fr(437386453, 500000000), 71: Fr(21869322649, 25000000000),
    72: Fr(174954253, 200000000), 73: Fr(8747289, 10**7), 74: Fr(1749387, 2000000),
    75: Fr(21867321, 25000000), 76: Fr(349843, 400000), 78: Fr(4373037, 5000000),
}


def test_x21_tracker_bounds_and_their_decimals():
    dec = {70: "0.874772906", 71: "0.87477290596", 72: "0.874771265", 73: "0.8747289",
           74: "0.8746935", 75: "0.87469284", 76: "0.8746075", 78: "0.8746074"}
    for pr, txt in dec.items():
        assert TRACKER_BOUNDS[pr] == Fr(txt), pr
    assert all(Fr(13, 15) < v < Fr(7, 8) for v in TRACKER_BOUNDS.values())


def test_x22_live_bar_gaps():
    pr76, pr78 = TRACKER_BOUNDS[76], TRACKER_BOUNDS[78]
    assert pr76 - pr78 == Fr(1, 10**7)                 # PR 78/79 claim one unit lower
    assert PR68 - pr76 == Fr(2012, 10**7)               # moved since the lane last looked
    assert TRACKER_BOUNDS[69] - pr76 == Fr(1654897, 10**10)
    assert pr76 - Fr(13, 15) == Fr(9529, 1200000)       # 0.0079408 of part (a)'s window left
    assert B_NEW - sp.Rational(pr76.numerator, pr76.denominator) > sp.Rational(3495, 10**7)
