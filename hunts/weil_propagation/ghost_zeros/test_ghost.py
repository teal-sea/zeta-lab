"""Pins for the ghost-zeros lane: PREREG.md, ghost.py, ghost_table.json, RESULTS.md.

Run from the repository root:

    .venv/bin/python -m pytest -q -n0 hunts/weil_propagation/ghost_zeros

Five groups:

1. the inputs PREREG.md takes as given agree with their sources;
2. the counter on planted elements of the band-N space with known zeros in the
   same rectangles (real zeros, a non-real pair at gamma_1 +- 0.3 i, a zero
   0.015 from some omega_k), by the Arb route and by the float route;
3. the algebra the lane leans on: the band-N representation of PREREG s3, the
   lesion matrix against wp_common.offline_quadruple, the residual bound;
4. one live DH unit (c = 29), recomputed and compared with the table and with
   ../numerics/grid_dh_N128.json (marked slow: about 30 s);
5. the table's decisions, the numbers RESULTS.md quotes, and the commit order
   (the prediction file was committed before any result).

Nothing here is evidence about RH (docs/08).
"""

from __future__ import annotations

import json
import math
import os
import subprocess
import sys
from fractions import Fraction

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ghost as G  # noqa: E402  (puts numerics/ and weil_trunc/ on sys.path)
import wp_common as W  # noqa: E402
from flint import acb, arb, arb_mat, ctx  # noqa: E402
from mpmath import mp  # noqa: E402

ROOT = G.ROOT
NUM = G.NUM


def _text(name: str) -> str:
    with open(os.path.join(HERE, name), encoding="utf-8") as f:
        return f.read()


def _table() -> dict:
    with open(G.TABLE) as f:
        return json.load(f)


# ---------------------------------------------------------------- 1. inputs


def test_prereg_inputs_agree_with_their_sources():
    pre = _text("PREREG.md")
    # the DH off-line zero: wp_common's 50-digit constants
    assert G.GAMMA_1 == W.GAMMA_OFF and G.DELTA_1 == W.DELTA_OFF
    # the 16-digit forms quoted are the 50-digit constants rounded
    with mp.workdps(60):
        assert "85.69934848537759" in pre and abs(mp.mpf(W.GAMMA_OFF) - mp.mpf("85.69934848537759")) < 5e-15
        assert "0.3085171824566374" in pre and abs(mp.mpf(W.DELTA_OFF) - mp.mpf("0.3085171824566374")) < 5e-17
    # the N = 128 crossing bracket
    cr = json.load(open(os.path.join(NUM, "crossing.json")))["by_N"]["128"]
    assert cr["c_pos"] == "15691/512" and cr["c_neg"] == "31383/1024"
    assert cr["hardened_negative"] and cr["hardened_positive"]
    assert "(15691/512, 31383/1024]" in pre and "(30.646484375, 30.6474609375]" in pre
    for c in G.C_BEFORE:
        assert Fraction(c) < Fraction(15691, 512)
    for c in G.C_LIST:
        if c not in G.C_BEFORE:
            assert Fraction(c) > Fraction(31383, 1024)
    # the DH on-line gap: consecutive entries of the cached zero list
    zs = G.dh_online()
    below = max(z for z in zs if z < float(G.GAMMA_1))
    above = min(z for z in zs if z > float(G.GAMMA_1))
    assert (below, above) == G.DH_GAP
    assert "83.10884108474983" in pre and "87.64747633255973" in pre
    # zeta's gap
    with mp.workdps(40):
        assert abs(mp.zetazero(23).imag - mp.mpf(G.ZETA_23)) < mp.mpf(10) ** -35
        assert abs(mp.zetazero(24).imag - mp.mpf(G.ZETA_24)) < mp.mpf(10) ** -35
    assert "84.73549298051705" in pre and "87.42527461312523" in pre
    # Epstein's off-line zero
    root = json.load(open(os.path.join(NUM, "epstein_offline.json")))["roots"][0]["root"]
    assert root[1] == G.GAMMA_E
    assert abs(float(root[0]) - 0.5 - float(G.DELTA_E)) < 1e-15
    assert "0.953260474794661 + 16.2902157203904 i" in pre
    # the continuum bound quoted
    assert "30.617188" in pre


def test_the_window_list_is_the_prereg_list():
    pre = _text("PREREG.md")
    assert "C = {29, 30, 61/2, 245/8, 31, 63/2, 47}" in pre
    assert G.C_LIST == ["29", "30", "61/2", "245/8", "31", "63/2", "47"]
    assert G.C_BEFORE == ["29", "30", "61/2", "245/8"]
    assert G.GHOST_RADIUS == Fraction(3, 10) and G.ACCOUNT_RADIUS == 0.15
    assert G.STEP_SC == Fraction(1, 512) and G.OMEGA_CLEAR == Fraction(1, 32)


# ---------------------------------------------------------------- 2. planted counter


def _planted():
    ctx.prec = 256
    L = arb(29).log()
    om46 = float(2 * arb.pi() * 46 / L)
    reals = [Fraction(842, 10), Fraction(om46 + 0.015)]
    cplx = [(Fraction(G.GAMMA_1[:10]) - Fraction(1, 2), Fraction(3, 10)), (Fraction(G.GAMMA_1[:10]), Fraction(3, 10))]
    x = G.planted_vector(L, 64, reals, cplx, 256)
    return L, x, reals, cplx, om46


def test_planted_counter_arb_route():
    """The adversary's planted function: 2 real zeros (one 0.015 from omega_46) and two
    non-real pairs, one exactly at gamma_1 + 0.3 i, all in DH's gap rectangle."""
    L, x, reals, cplx, om46 = _planted()
    T = G.Transform(x, L, 256, None)
    full = G.count_rect(T, 83.109, 87.647, Fraction(1, 2))
    assert full["closed"] and full["n_AP"] == 2 + 2 * 2
    sc = G.sign_scan(T, 83.109, 87.647, 60)
    assert sc["n_SC"] == 2 and not sc["undecided_points"]
    for z, r in zip(sc["zeros"], reals):
        assert Fraction(z["lo"]) <= r <= Fraction(z["hi"]) or abs(z["x"] - float(r)) < 1e-15
    # the ghost rectangle holds the pair at gamma_1 +- 0.3 i and the zero near omega_46
    gh = G.count_rect(T, float(G.GAMMA_1) - 0.3, float(G.GAMMA_1) + 0.3, Fraction(1, 2))
    assert gh["closed"] and gh["n_AP"] == 3
    # a thinner rectangle excludes every non-real zero (Im = 0.3)
    thin = G.count_rect(T, 83.109, 87.647, Fraction(1, 4))
    assert thin["closed"] and thin["n_AP"] == 2
    # a side asked to sit 0.01 left of omega_46 is moved right until clear of it by 1/32; that
    # excludes the zero at omega_46 + 0.015 and both pairs (left of omega_46 = 85.833), so 0 remain
    moved = G.count_rect(T, om46 - 0.01, 87.647, Fraction(1, 2))
    assert moved["side_moves"] >= 1 and moved["a_float"] - om46 > 1 / 32
    assert moved["closed"] and moved["n_AP"] == 0


def test_planted_counter_float_route():
    L, x, reals, cplx, om46 = _planted()
    xs = [x[i, 0] for i in range(x.nrows())]
    with mp.workdps(60):
        Lm = mp.log(29)
        xm = [mp.mpf(str(t.mid().str(60, radius=False))) for t in xs]
        oms = [2 * mp.pi * k / Lm for k in range(len(xm))]

        def F(z):
            tot = xm[0] * mp.sinc(z * Lm / 2)
            for k in range(1, len(xm)):
                term = mp.sqrt(2) * xm[k] * z * mp.sinc((z - oms[k]) * Lm / 2) / (z + oms[k])
                tot += term if k % 2 == 0 else -term
            return Lm * tot

        w = G._mp_winding(F, mp.mpf("83.109375"), mp.mpf("87.646484375"), mp.mpf(1) / 2, mp)
        zs = G._mp_real_zeros(F, 83.109, 87.647, mp)
    assert w["integral"] and w["n"] == 6
    assert len(zs) == 2
    assert abs(zs[0] - 84.2) < 1e-12 and abs(zs[1] - float(reals[1])) < 1e-12


# ---------------------------------------------------------------- 3. algebra


def test_band_n_representation_of_prereg_s3():
    """F_even_acb(v) = 2 sin(zL/2) p(z^2) / (z q(z^2)) with
    p(w) = v_0 prod(w - om_k^2) + sqrt2 sum_k v_k w prod_{j != k}(w - om_j^2)."""
    ctx.prec = 200
    N = 24
    L = arb(30).log()
    v = arb_mat(N + 1, 1, [arb(math.sin(1.3 * k + 0.2) / (1 + k)) for k in range(N + 1)])
    om2 = [(2 * arb.pi() * k / L) ** 2 for k in range(1, N + 1)]
    s2 = arb(2).sqrt()
    for z in (acb(arb("85.3"), arb("0.2")), acb(arb("12.7"), arb("-0.45")), acb(arb("40.1"))):
        w = z * z
        q = acb(1)
        for o in om2:
            q *= w - o
        p = v[0, 0] * q
        for k in range(N):
            t = s2 * v[k + 1, 0] * w
            for j in range(N):
                if j != k:
                    t *= w - om2[j]
            p += t
        rep = 2 * (z * L / 2).sin() * p / (z * q)
        assert (rep - W.F_even_acb(v, L, z)).real.contains(0) and (rep - W.F_even_acb(v, L, z)).imag.contains(0)


def test_lesion_matrix_is_the_offline_quadruple_form():
    ctx.prec = 300
    L = arb(Fraction(61, 2).numerator).log() - arb(2).log()
    n = 33
    x = arb_mat(n, 1, [arb(math.cos(0.7 * k) / (1 + k * k)) for k in range(n)])
    M = G.lesion_matrix("q1", L, n)
    lhs = W.quad(M, x)
    rhs = W.offline_quadruple(x, L, G.GAMMA_1, G.DELTA_1)
    assert (lhs - rhs).contains(0)
    S = G.lesion_matrix("sham", L, n)
    g = G.sham_ordinate()
    assert abs(g - 89.43924) < 1e-4
    F = W.F_even_acb(x, L, acb(arb(repr(g))))
    assert (W.quad(S, x) - 2 * F.real * F.real / L).contains(0)


def test_the_bound_behind_the_cauchy_remainder():
    """|sinc(w)| <= 1.1753 cosh(Im w) (|w| >= 1: |sin w| <= cosh Im w; |w| < 1: the series
    gives sinh|w|/|w| < sinh 1 = 1.17520), hence max_k |a_k(z)| <= Transform.B(|Im z|) on Re z >= 0."""
    import random

    rng = random.Random(20261021)
    ctx.prec = 128
    assert arb(1).sinh() < arb(G.SINC_ABS)
    for _ in range(400):
        w = acb(arb(rng.uniform(-6, 6)), arb(rng.uniform(-3, 3)))
        assert abs(w.sinc()) <= arb(G.SINC_ABS) * w.imag.cosh()
    L = arb(30).log()
    x = arb_mat(N := 33, 1, [arb(1)] + [arb(0)] * (N - 1))
    T = G.Transform(x, L, 128, None)
    for _ in range(200):
        z = acb(arb(rng.uniform(0, 120)), arb(rng.uniform(-1.2, 1.2)))
        bound = T.B(abs(z.imag).upper())
        assert all(abs(a) <= bound for a in G.basis_at(L, z, N) if a.is_finite())


def test_residual_bound_is_finite_at_rounding_level():
    """The defect that voided the first c = 31 unit: sqrt of a dot product whose ball
    reaches below 0 is NaN. residual_upper never takes sqrt of such a ball."""
    ctx.prec = 128
    A = arb_mat(2, 2, [1, 0, 0, 2])
    x = arb_mat(2, 1, [1, 0])
    rho = arb(1, 1e-30)
    bad = W.residual_norm(A, x, rho)
    good = G.residual_upper(A, x, rho)
    assert math.isfinite(float(good.mid())) and good >= 0 and good < arb("1e-29")
    assert not math.isfinite(float(bad.mid())) or bad.contains(0)


# ---------------------------------------------------------------- 4. one live unit


@pytest.mark.slow
def test_live_dh_unit_at_29_matches_the_table_and_the_grid():
    rec = G.unit("dh", "29")
    tab = _table()["units"]["primary_dh"]["29"]
    assert rec["H1_simple"] and rec["H2_even"] and rec["H3_isolated"]
    assert rec["ghost"] and tab["ghost"]
    a = Fraction(rec["ghosts"][0]["lo"]), Fraction(rec["ghosts"][0]["hi"])
    b = Fraction(tab["ghosts"][0]["lo"]), Fraction(tab["ghosts"][0]["hi"])
    assert a == b
    for name in ("gap", "ghost", "ctx"):
        assert rec["rects"][name]["AP"]["n_AP"] == tab["rects"][name]["AP"]["n_AP"]
    grid = json.load(open(os.path.join(NUM, "grid_dh_N128.json")))["cells"]["29"]
    assert arb(rec["rq"]).overlaps(arb(grid["lam1"]))
    assert arb(rec["Q1"]).overlaps(arb(grid["zero_side"]["Q1"]))
    for u, v in zip(rec["v_head"], grid["v_head"]):
        assert abs(u - v) < 1e-12


def test_table_reuses_the_grid_where_it_applies():
    """At the six windows that are also cells of ../numerics/grid_dh_N128.json the
    recomputed lambda_1, Q1 and v_head agree with the stored ones."""
    grid = json.load(open(os.path.join(NUM, "grid_dh_N128.json")))["cells"]
    units = _table()["units"]["primary_dh"]
    shared = [c for c in G.C_LIST if c in grid]
    assert shared == ["29", "30", "61/2", "245/8", "31", "63/2"]
    for c in shared:
        rec, g = units[c], grid[c]
        assert arb(rec["rq"]).overlaps(arb(g["lam1"])), c
        assert arb(rec["Q1"]).overlaps(arb(g["zero_side"]["Q1"])), c
        assert max(abs(u - v) for u, v in zip(rec["v_head"], g["v_head"])) < 1e-12, c


# ---------------------------------------------------------------- 5. decisions, RESULTS, commit order


def test_commit_of_the_prediction_precedes_the_results():
    def first_commit(path):
        out = subprocess.run(["git", "log", "--diff-filter=A", "--format=%H %ct", "--", path],
                             cwd=HERE, capture_output=True, text=True)
        lines = [ln for ln in out.stdout.splitlines() if ln.strip()]
        return lines[-1].split() if lines else None

    try:
        pre = first_commit("PREREG.md")
    except FileNotFoundError:  # pragma: no cover - no git
        pytest.skip("git not available")
    if pre is None:
        pytest.skip("PREREG.md not committed in this checkout")
    files = subprocess.run(["git", "show", "--name-only", "--format=", pre[0]], cwd=HERE,
                           capture_output=True, text=True).stdout.split()
    assert files == ["hunts/weil_propagation/ghost_zeros/PREREG.md"], files
    for later in ("ghost_table.json", "RESULTS.md", "ghost.py"):
        c = first_commit(later)
        if c is None:
            continue
        anc = subprocess.run(["git", "merge-base", "--is-ancestor", pre[0], c[0]], cwd=HERE)
        assert anc.returncode == 0 and c[0] != pre[0], later
        assert int(c[1]) >= int(pre[1]), later


def test_results_quotes_the_tables_verbatim():
    res = _text("RESULTS.md")
    for name, t in G.tables(_table()).items():
        assert t in res, f"table {name} in RESULTS.md differs from ghost.tables()"


def test_results_prose_numbers_come_from_the_table():
    res = _text("RESULTS.md")
    for key, val in G.results_numbers(_table()).items():
        assert val in res, (key, val)


#: Decimal numbers RESULTS.md may quote that are not computed results: PREREG
#: parameters and inputs (pinned above against their sources), the planted
#: zeros of test_planted_counter_*, and the DH on-line ordinates of
#: data/dh_zeros_online_T120.json (pinned by test_the_numbers_quoted_from_inputs).
ALLOWED_INPUTS = {
    "85.69934848", "85.6993484", "85.1993484", "0.3085", "0.3", "0.15", "0.01", "0.02", "0.015", "0.05",
    "83.109", "87.647", "80.5", "90.5", "84.2", "89.4392", "83.1088", "83.10884", "87.6475", "81.9254",
    "30.646484375", "30.6474609375", "30.647", "30.617188", "16.2902", "16.29", "14.6305", "18.8285",
    "15.9381", "18.9859", "0.453", "0.4533",
    "82.91038", "84.73549", "87.42527", "88.80911", "114.1633427308", "0.1508300806", "112.37639", "116.72151",
}


def _prose_numbers(text: str) -> list:
    import re

    body, out, fence = [], [], False
    for ln in text.splitlines():
        if ln.startswith("    ") or ln.startswith("|"):
            continue  # code block or table row (tables are pinned verbatim)
        if ln.strip().startswith("```"):
            fence = not fence
            continue
        if not fence:
            body.append(ln)
    for m in re.finditer(r"(?<![\w.])-?\d+\.\d+(?:e[-+]?\d+)?", "\n".join(body)):
        out.append(m.group(0).lstrip("-"))
    return out


def test_every_decimal_in_the_results_prose_is_pinned():
    tab = _table()
    res = _text("RESULTS.md")
    import re

    tables = "\n".join(G.tables(tab).values())
    vals = list(G.results_numbers(tab).values())
    nums = set(vals) | {m.lstrip("-") for v in vals for m in re.findall(r"-?\d+\.\d+(?:e[-+]?\d+)?", v)}
    bad = [x for x in _prose_numbers(res) if x not in ALLOWED_INPUTS and x not in nums and x not in tables]
    assert not bad, f"unpinned decimals in RESULTS.md prose: {sorted(set(bad))}"


def test_the_numbers_quoted_from_inputs():
    zs = G.dh_online()
    for s in ("89.4392", "83.1088", "87.6475", "81.9254", "112.37639", "116.72151"):
        assert any(abs(z - float(s)) < 5e-5 for z in zs), s
    assert abs(G.DH_GAP[0] - 83.10884) < 5e-6
    assert (G.DH_GAP2[0], G.DH_GAP2[1]) == (max(z for z in zs if z < 114.16), min(z for z in zs if z > 114.17))
    assert W.GAMMA_OFF2 == "114.1633427308" and W.DELTA_OFF2 == "0.1508300806"
    with mp.workdps(30):
        for n, s in ((22, "82.91038"), (23, "84.73549"), (24, "87.42527"), (25, "88.80911")):
            assert abs(mp.zetazero(n).imag - mp.mpf(s)) < 5e-6, s
    win = _table()["windows"]
    assert any(abs(z - 14.6305) < 5e-5 for z in win["epstein_online"])
    assert any(abs(z - 18.8285) < 5e-5 for z in win["epstein_online"])
    assert abs(win["epstein_gap"][0] - 14.6305) < 5e-5 and abs(win["epstein_gap"][1] - 18.8285) < 5e-5
    assert any(abs(z - 15.9381) < 5e-5 for z in win["dedekind_online"])
    assert any(abs(z - 18.9859) < 5e-5 for z in win["dedekind_online"])
    assert all(win["epstein_confirmed_by_Z_epstein_sign_change"])
    assert all(win["dedekind_confirmed_by_classgroup_sign_change"]) and win["dedekind_lists_agree_to_1e-8"]


def test_the_preregistered_decisions():
    dec = _table()["decisions"]
    assert dec["P"]["verdict"] == "confirmed"
    assert dec["P"]["c_with_ghost_at_or_before"] == G.C_BEFORE
    assert all(dec["P"]["ghost_after_crossing"].values())
    assert dec["S1"]["holds"] and dec["S1"]["rectangles_checked"] > 0
    assert dec["S2"]["holds"]
    assert dec["S2_exploratory_scan"]["violations"] == ["18"]
    assert dec["S3"]["holds"]
    assert dec["S6"]["holds"]
    assert dec["S7"]["holds"] and dec["S7"]["complete"]
    units = _table()["units"]
    for c in G.C_LIST:
        p = units["primary_dh"][c]
        assert p["H1_simple"] and p["H3_isolated"] and p["ghost"]
        assert p["rects"]["gap"]["AP"]["n_AP"] == 1 and p["rects"]["ghost"]["AP"]["n_AP"] == 1
        assert abs(p["ghosts"][0]["dist"]) < 0.04
        assert not units["q1_dh"][c]["zeros_within_radius"]
        assert units["sham_dh"][c]["ghost"]
        assert units["primary_zeta"][c]["rects"]["gap"]["AP"]["n_AP"] == 0
    assert [c for c in G.C_LIST if units["primary_dh"][c]["H2_even"] is False] == ["63/2", "47"]
    # S4: Epstein's ghost at its own off-line ordinate, the only zero in its on-line gap
    assert dec["S4"]["holds"]
    for c in G.C_LIST:
        e = units["primary_epstein"][c]
        assert e["ghost"] and e["rects"]["gap"]["AP"]["n_AP"] == 1 and e["rects"]["ghost"]["AP"]["n_AP"] == 1
    assert [c for c in G.C_LIST if units["primary_epstein"][c]["H2_even"] is False] == ["29", "47"]
    # S5 fails as preregistered: no ghost, but zeta_K's zeros are not followed at that height
    assert not dec["S5"]["holds"]
    assert not any(r["ghost"] for r in dec["S5"]["by_c"].values())
    assert all(r["unaccounted"] for r in dec["S5"]["by_c"].values())
    # exploratory: a real zero within 0.3 of gamma_2 at every window
    for c in G.C_LIST:
        g = units["gap2_dh"][c]
        assert g["H1_simple"] and g["rects"]["ghost2"]["AP"]["n_AP"] >= 1
        assert abs(g["nearest_to_gamma2"]["dist"]) < 0.05


def test_zeta_ordinates_lie_inside_their_brackets():
    """RESULTS s4: in R_ctx, zeta's F_v has one real zero bracket per zeta zero in
    [80.5, 90.5], and each zetazero ordinate (60 digits) lies inside its bracket."""
    units = _table()["units"]["primary_zeta"]
    with mp.workdps(60):
        gam = [mp.zetazero(n).imag for n in (22, 23, 24, 25)]
        for c in G.C_LIST:
            zs = units[c]["rects"]["ctx"]["SC"]["zeros"]
            assert len(zs) == 4, c
            for z, g in zip(zs, gam):
                lo, hi = Fraction(z["lo"]), Fraction(z["hi"])
                assert mp.mpf(lo.numerator) / lo.denominator <= g <= mp.mpf(hi.numerator) / hi.denominator, (c, z)
                assert z["width"] <= 2.4e-38, (c, z)


def test_nominal_rectangle_counts():
    """RESULTS s1: counts on the nominal rectangles, read from R_ctx, and the one side
    move the prose names (left side of DH's R_gap at c = 30, off omega_45)."""
    dec = _table()["decisions"]["nominal_counts"]
    assert dec["all_read"]
    nom = dec["by_unit"]
    for c in G.C_LIST:
        assert nom[f"primary_dh|{c}"]["gap"]["nominal"] == 1 and nom[f"primary_dh|{c}"]["ghost"]["nominal"] == 1
        assert nom[f"primary_zeta|{c}"]["gap"]["nominal"] == 0 and nom[f"primary_zeta|{c}"]["ghost"]["nominal"] == 0
        assert nom[f"primary_epstein|{c}"]["gap"]["nominal"] == 1 and nom[f"primary_epstein|{c}"]["ghost"]["nominal"] == 1
        assert nom[f"primary_dedekind|{c}"]["ghost"]["nominal"] == 0
        assert nom[f"q1_dh|{c}"]["ghost"]["nominal"] == 0 and nom[f"sham_dh|{c}"]["ghost"]["nominal"] == 1
    diff = sorted(k + "|" + rn for k, r in nom.items() for rn, v in r.items() if v["nominal"] != v["moved_sides_AP"])
    assert diff == ["q1_dh|30|gap", "q1_dh|63/2|gap"], diff
    rec = _table()["units"]["primary_dh"]["30"]["rects"]["gap"]["AP"]
    L = math.log(30)
    k = min(range(1, 129), key=lambda j: abs(2 * math.pi * j / L - 83.109375))
    om = 2 * math.pi * k / L
    assert k == 45 and abs(om - 83.109375) < 1 / 32
    assert Fraction(rec["a"]) - Fraction(om) > Fraction(1, 32) and Fraction(rec["a"]) - Fraction(83109, 1000) < 0.054


def test_float_route_zeros_lie_in_the_arb_brackets():
    """RESULTS s6: every real zero of the float route lies in its Arb bracket widened
    by two float64 ulps, and every float winding number is within 1e-50 of an integer."""
    units = _table()["units"]
    n = 0
    for kind in G.KINDS:
        for c in G.C_LIST:
            a, f = units[f"primary_{kind}"][c], units[f"float_{kind}"][c]
            for rn, rr in f["rects"].items():
                assert rr["winding"]["defect"] < 1e-50, (kind, c, rn)
                za = a["rects"][rn]["SC"]["zeros"]
                assert len(za) == len(rr["real_zeros"]), (kind, c, rn)
                for u, v in zip(za, rr["real_zeros"]):
                    ulp = Fraction(math.ulp(v))
                    assert Fraction(u["lo"]) - 2 * ulp <= Fraction(v) <= Fraction(u["hi"]) + 2 * ulp, (kind, c, rn)
                    n += 1
    assert n == 165


def test_summary_keeps_table_units_when_unit_files_are_missing(tmp_path, monkeypatch):
    """``ghost.py summary`` in a checkout without ``units/`` must not wipe the record."""
    import shutil

    tab_copy = tmp_path / "ghost_table.json"
    shutil.copy(G.TABLE, tab_copy)
    empty = tmp_path / "units"
    empty.mkdir()
    monkeypatch.setattr(G, "TABLE", str(tab_copy))
    monkeypatch.setattr(G, "UNITS", str(empty))
    before = _table()
    dec = G.summarize()
    after = json.load(open(tab_copy))
    assert sorted(after["units"]) == sorted(before["units"])
    assert dec["P"]["verdict"] == "confirmed" and dec["S7"]["complete"]
    assert dec["S1"]["rectangles_checked"] == before["decisions"]["S1"]["rectangles_checked"]


def test_the_case_log_line():
    with open(os.path.join(ROOT, "hunts", "README.md"), encoding="utf-8") as f:
        lines = [ln for ln in f.read().splitlines() if "weil_propagation/ghost_zeros/" in ln]
    assert len(lines) == 1, lines
    nums = G.results_numbers(_table())
    for key in ("DIST_MIN", "DIST_MAX", "SCAN_FIRST"):
        assert nums[key] in lines[0], key
    # the PREREG inputs it quotes (pinned against their sources in test_prereg_inputs_agree_with_their_sources)
    for s in ("(83.109, 87.647)", "85.699", "30.647", "N = 128", "c = 29 to 47"):
        assert s in lines[0], s
    # the scope: seven windows, the scan windows, the band-128 matrix, |Im z| <= 1/2
    for s in ("each of the seven preregistered windows", "every scan window", "band-128 matrix only", "|Im z| <= 1/2"):
        assert s in lines[0], s
    assert chr(0x2014) not in lines[0]  # no em dash


def test_lane_files_keep_the_lexical_rules():
    banned = "cert" + "if"  # the stem of the reserved word, spelled so this file does not carry it
    for name in sorted(os.listdir(HERE)):
        if name.endswith((".md", ".py", ".json")):
            text = open(os.path.join(HERE, name), encoding="utf-8").read()
            assert banned not in text.lower(), name
            if name.endswith(".md"):
                assert chr(0x2014) not in text, name  # no em dash
