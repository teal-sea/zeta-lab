"""Checks for hunt #161: every number RESULTS.md quotes, and faults planted to see red.

Three kinds of test live here.

* Recomputation: the instrument is run again at reduced size and compared with
  the committed JSON (decade extremes, enclosures, level ratios, rival slopes).
* Pins: a number quoted in RESULTS.md must be the number in the JSON, formatted
  the same way.  A changed run that is not carried into the prose fails here.
* Planted faults: each check that could pass vacuously is shown to fail on a
  deliberately wrong input (sign of the zero sum, a dropped term, a missing
  zero, the wrong parity formula, a perturbed constant, a planted off-line
  zero).  A cross-check that cannot fail is not a cross-check.
"""

from __future__ import annotations

import json
import math
import re
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
from flint import arb, ctx

from hunts.rh_claim_interface import instrument as I
from hunts.rh_claim_interface import run_characters as RC
from hunts.rh_claim_interface import run_lesion as RL
from hunts.rh_claim_interface import run_rivals as RR
from hunts.rh_claim_interface import run_scan as RS
from hunts.rh_claim_interface import zero_side as Z

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def _load(name):
    return json.loads((HERE / name).read_text())


def _text(name="RESULTS.md"):
    return (HERE / name).read_text(encoding="utf-8")


def _lab_zeros(n=1000):
    d = json.loads((REPO / "data" / "zeros_1000.json").read_text())
    return np.array([float(x) for x in d["zeros"][:n]])


def _char(q, conrey):
    (c,) = [c for c in I.primitive_characters(q) if c.conrey == conrey]
    return c


def _mid(s: str) -> float:
    """Midpoint of an arb printed as '[m +/- r]'."""
    return float(s.strip("[]").split(" +/- ")[0])


# ---------------------------------------------------------------- transcription


def test_transcription_is_pinned_and_quoted_in_the_mission():
    t = _load("transcription.json")
    sha = t["archive"]["joined_tarball_sha256"]
    assert sha == "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"
    mission = _text("MISSION.md")
    assert sha in mission and sha in _text()
    by_id = {q["id"]: q for q in t["quotes"]}
    assert "Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x" in by_id["Gz"]["text"]
    assert "(3 * (Λ.o : ℝ) + 1)⁻¹" in by_id["Level.wt_Gm"]["text"]
    assert "Formalism.Gz y + ∑ ψ ∈ Λ.Nt, Λ.wt ψ * (An.gChi ψ.χ y).re" in by_id["Level.wt_Gm"]["text"]
    assert "Gm F y ≤ C * y ^ θ" in by_id["zeroFree_of_rpow_window"]["text"]
    assert "Set.Icc Y (Y ^ (1 + δ))" in by_id["zeroFree_of_rpow_window"]["text"]
    assert "(la := 3 / 2)" in by_id["top_window_exponent"]["text"]
    assert "(δ := la - 1) (C := 1)" in by_id["formB_uses_window_lemma"]["text"]
    for q in t["quotes"]:
        assert q["path"] in t["files"], q["id"]
        assert len(t["files"][q["path"]]) == 64


# ------------------------------------------------------------------ instrument


def test_c0_and_the_value_at_one():
    c0 = I.c0_arb(128)
    assert abs(float(c0.mid()) - I.C0) < 2e-16  # the float constant carries its own rounding
    assert I.C0 == pytest.approx(0.0461914179322420676, abs=2e-16)
    assert I.c0_arb(128).str(22).startswith("[0.04619141793224206762")
    (g1,) = I.G_arb([1], 128)
    (f1,) = I.F_arb([1], 128)
    ctx.prec = 128
    try:
        assert g1.overlaps(1 + arb.const_euler())  # G(1) = 1 + gamma
        assert f1.overlaps(c0) and float(abs(f1 - c0).upper()) < 1e-30  # F(1) = c0
    finally:
        ctx.prec = 53
    assert I.G_float(1.0) == pytest.approx(1.5772156649015329, abs=1e-15)


def test_T_closed_forms_and_series_agree():
    ctx.prec = 128
    try:
        assert abs(float(I.T_arb(arb(1)).mid()) - (math.log(2) - 1)) < 1e-16
        assert abs(float(I.T_odd_arb(arb(1)).mid()) + math.log(2)) < 1e-16
        for y in (1.5, 3.0, 6.0, 10.0, 100.0):
            series = -sum(y ** (-2 * k) / (2 * k * (2 * k + 1)) for k in range(1, 400))
            odd = -sum(y ** (-(2 * k - 1)) / ((2 * k - 1) * 2 * k) for k in range(1, 400))
            assert float(I.T_arb(arb(y)).mid()) == pytest.approx(series, abs=1e-13)
            assert float(I.T_float(y)) == pytest.approx(series, abs=1e-13)
            assert float(I.T_odd_arb(arb(y)).mid()) == pytest.approx(odd, abs=1e-13)
            assert float(I.T_odd_float(y)) == pytest.approx(odd, abs=1e-13)
    finally:
        ctx.prec = 53


def test_float_route_matches_arb_route():
    ys = [1, 2.5, 10.5, 1000, 1000.5, 150000, 150000.5, Fraction(22, 7)]
    arb_vals = I.G_arb(ys, 128)
    for y, a in zip(ys, arb_vals):
        assert I.G_float(float(y)) == pytest.approx(float(a.mid()), abs=2e-10)
    want = {1000: float(arb_vals[3].mid()), 150000: float(arb_vals[5].mid())}
    seen = 0
    for n, e, r, _ in I.scan_integers(200000, seg=1 << 16):
        g = n * e - r
        for m, v in want.items():
            if n[0] <= m <= n[-1]:
                assert g[int(m - n[0])] == pytest.approx(v, abs=1e-9)
                seen += 1
    assert seen == 2


def test_sieve_against_a_direct_von_mangoldt():
    lam = I.lambda_segment(0, 2000, I.small_primes(50))

    def direct(n):
        if n < 2:
            return 0.0
        for p in range(2, n + 1):
            if n % p == 0:
                m = n
                while m % p == 0:
                    m //= p
                return math.log(p) if m == 1 else 0.0
        return 0.0

    assert max(abs(lam[n] - direct(n)) for n in range(2000)) < 1e-15


# ------------------------------------------------------------------- the scan


def _decades(scan):
    bpd = scan["bins_per_decade"]
    out = []
    for k in range(len(scan["bin_max_F"]) // bpd):
        sl = slice(k * bpd, (k + 1) * bpd)
        fm, fn = scan["bin_max_F"][sl], scan["bin_min_F"][sl]
        i, j = int(np.argmax(fm)), int(np.argmin(fn))
        out.append((fm[i], scan["bin_argmax_n"][sl][i], fn[j], scan["bin_argmin_n"][sl][j]))
    return out


def test_scan_recomputes_below_1e6_and_matches_the_committed_run():
    scan = _load("scan_1e9.json")
    assert scan["y_max"] == 10**9
    best_max = [(-np.inf, 0)] * 6
    best_min = [(np.inf, 0)] * 6
    for n, e, r, _ in I.scan_integers(10**6 - 1, seg=1 << 18):
        f = I.F_from_ER(n, e, r)
        dec = np.floor(np.log10(n) + 1e-12).astype(int)
        for k in range(6):
            m = dec == k
            if m.any():
                fs, ns = f[m], n[m]
                i, j = int(np.argmax(fs)), int(np.argmin(fs))
                if fs[i] > best_max[k][0]:
                    best_max[k] = (float(fs[i]), int(ns[i]))
                if fs[j] < best_min[k][0]:
                    best_min[k] = (float(fs[j]), int(ns[j]))
    for k, (fmx, nmx, fmn, nmn) in enumerate(_decades(scan)[:6]):
        assert best_max[k][1] == nmx and best_min[k][1] == nmn
        assert best_max[k][0] == pytest.approx(fmx, abs=1e-12)
        assert best_min[k][0] == pytest.approx(fmn, abs=1e-12)


def test_scan_stays_inside_the_envelope_and_the_extremes_are_where_results_says():
    scan = _load("scan_1e9.json")
    enc = _load("scan_1e9_enclosed.json")
    c0 = I.C0
    assert max(scan["bin_max_F"]) < c0 and min(scan["bin_min_F"]) > -c0
    decs = enc["decades"]
    top = max(decs, key=lambda d: d["F_crit_over_c0"])
    bot = min(decs, key=lambda d: d["F_min_over_c0"])
    assert (top["decade"], top["n_max"]) == (7, 34186454)
    assert (bot["decade"], bot["n_min"]) == (5, 319439)
    text = _text()
    assert f"{_mid(top['F_crit_arb']):.16f}" in text  # 0.0246942450780346
    assert f"{top['y_crit']:.6f}" in text
    assert f"{top['F_crit_over_c0']:.4f}" in text
    assert f"{_mid(bot['F_min_arb']):.16f}" in text
    assert f"{bot['F_min_over_c0']:.4f}" in text
    assert "319439" in text and "34186454" in text
    # float against Arb at every decade extreme
    worst = max(max(abs(d["F_min_float_minus_arb"]), abs(d["F_max_float_minus_arb"])) for d in decs)
    assert worst < 1e-11
    assert f"{worst:.1e}" in text
    # every decade row of the table
    for d in decs:
        assert f"| {d['decade']} | {d['n_min']} | {_mid(d['F_min_arb']):.10f} | {d['F_min_over_c0']:.4f} |" in text
        assert f"{d['y_crit']:.4f} | {_mid(d['F_crit_arb']):.10f} | {d['F_crit_over_c0']:.4f} |" in text
    # the precision response: 128 against 192 bits
    for d in decs:
        assert abs(_mid(d["F_min_arb"]) - _mid(d["F_min_arb_prec2"])) < 1e-15


def test_the_global_minimum_and_maximum_enclosures_recompute():
    enc = _load("scan_1e9_enclosed.json")
    d5 = enc["decades"][5]
    d7 = enc["decades"][7]
    (fmin,) = I.F_arb([d5["n_min"]], 128)
    assert abs(float(fmin.mid()) - _mid(d5["F_min_arb"])) < 1e-24
    assert 319439 in [pk for pk, _ in I.prime_powers_upto(319439)][-1:]  # the minimum sits at a prime
    y_c = float.fromhex(d7["y_crit_hex"])
    assert y_c == d7["y_crit"]
    (fmax,) = I.F_arb([y_c], 128)
    assert abs(float(fmax.mid()) - _mid(d7["F_crit_arb"])) < 1e-24
    fp = I.F_prime_arb(y_c, 128)
    assert abs(float(fp.mid())) < 1e-18  # a critical point to float resolution
    ctx.prec = 128
    try:
        c0 = I.c0_arb(128)
        assert bool(fmax < c0) and bool(fmin > -c0)  # decided by Arb at these two points
    finally:
        ctx.prec = 53
    # the interior critical point is found again from the Arb prefix sums
    n = d7["n_max"]
    sums = I.arb_prefix_sums([n], 128)
    ctx.prec = 128
    try:
        psi, a = sums[n]
        e_n = float((a - arb(n).log() + arb.const_euler()).mid())
        r_n = float((psi - n).mid())
    finally:
        ctx.prec = 53
    cp = I.interior_critical_point(n, e_n, r_n)
    assert cp is not None and cp[0] == pytest.approx(y_c, abs=1e-6)
    assert cp[1] == pytest.approx(_mid(d7["F_crit_arb"]), abs=1e-13)


# --------------------------------------------------------- explicit formula, zeta


GRID = [1.0, 1.5, 2.5, 7.25, 10.5, 100.5, 1000.5, 4096.125, 30011.5, 99991.75]


def _zeta_defect_ratio(gammas, budget_gammas=None, sign=1.0, drop_T=False, gamma_shift=0.0):
    ys = np.array(GRID)
    ps = np.array([float(x.mid()) for x in I.G_arb(GRID, 128)]) + gamma_shift * ys
    zs = sign * Z.zeta_zero_sum(ys, gammas) + I.LOG_2PI + (0.0 if drop_T else I.T_float(ys))
    tail = Z.zeta_tail_budget(gammas if budget_gammas is None else budget_gammas)
    return (ps - zs) / (np.sqrt(ys) * tail)


def test_explicit_formula_for_G_within_the_exact_tail_budget():
    g = _lab_zeros()
    ratio = _zeta_defect_ratio(g)
    assert ratio[0] == pytest.approx(1.0, abs=1e-9)  # at y = 1 every phase is aligned
    assert np.max(np.abs(ratio[1:])) < 0.2
    z = _load("zeros.json")
    rung = {r["n_zeros"]: r for r in z["ladder"]}
    assert Z.zeta_tail_budget(g) == pytest.approx(rung[1000]["tail_budget"], rel=1e-12)
    for r in z["ladder"]:  # the budget follows the density of zeros
        assert r["tail_budget"] > 0
        assert r["tail_budget"] == pytest.approx(r["density_prediction"], rel=2e-3)
    text = _text()
    assert f"{rung[20000]['tail_budget']:.6e}" in text
    assert f"{rung[20000]['density_prediction']:.6e}" in text
    x = _load("explicit_zeta.json")
    for m in ("100", "1000", "5000", "20000"):
        assert x["ladder"][m]["max_abs_ratio_y_gt_1"] < 0.2
        assert f"{x['ladder'][m]['max_abs_ratio_y_gt_1']:.3f}" in text
    assert x["n_points"] == 256 and f"{x['n_points']} points" in text
    spots = x["arb_spots"]
    assert spots[0]["y"] == 1.0 and spots[0]["abs_defect_ball_overlaps_budget_ball"]
    assert all(s["abs_defect_le_budget_decided_by_arb"] for s in spots[1:])


def test_planted_faults_in_the_explicit_formula_go_red():
    g = _lab_zeros()

    def passes(ratio):
        return bool(np.max(np.abs(ratio[1:])) <= 1.0) and abs(ratio[0] - 1.0) < 1e-6

    assert passes(_zeta_defect_ratio(g))
    # the sign of the zero sum as one fetched source prints it
    assert not passes(_zeta_defect_ratio(g, sign=-1.0))
    # the trivial-zero term dropped
    assert not passes(_zeta_defect_ratio(g, drop_T=True))
    # gamma off by one part in a thousand in the linear term
    assert not passes(_zeta_defect_ratio(g, gamma_shift=1e-3))
    # one zero missing from the list while the budget believes the list is complete
    lesioned = np.delete(g, 4)
    assert not passes(_zeta_defect_ratio(lesioned, budget_gammas=g))
    # the constant c0 perturbed: the budget at y = 1 no longer closes
    ratio = _zeta_defect_ratio(g)
    wrong_tail = (I.C0 + 1e-4) - Z.zeta_partial(g)
    assert abs(ratio[0] * Z.zeta_tail_budget(g) / wrong_tail - 1.0) > 0.05


# ------------------------------------------------------------------ characters


def test_characters_are_characters():
    for q in (5, 7, 8, 12, 15, 16, 19):
        chars = I.characters_mod(q)
        units = [a for a in range(1, q) if math.gcd(a, q) == 1]
        assert len(chars) == len(units)
        vals = np.array([c.values() for c in chars])
        for c, v in zip(chars, vals):  # multiplicative
            for a in units[:6]:
                for b in units[:6]:
                    assert abs(v[a * b % q] - v[a] * v[b]) < 1e-12
        gram = vals @ vals.conj().T  # orthogonal
        assert np.allclose(gram, len(units) * np.eye(len(units)), atol=1e-9)
    counts = {q: len(I.primitive_characters(q)) for q in range(3, 21)}
    assert sum(counts.values()) == 79 and counts[6] == 0 and counts[19] == 17 and counts[16] == 4


def test_cyc_level_weights_are_three_or_four_over_3o_plus_1():
    # 1 + (3o+1)^-1 sum_{k=1}^{o-1} chi^k(n) = o (3 + [chi(n) = 1]) / (3o + 1) on units
    for q, con in ((5, 2), (7, 3), (13, 2), (16, 3)):
        chi = _char(q, con)
        lev = I.cyc_level(chi)
        o = lev["o"]
        v = I.level_weights(lev)
        for a in range(1, q):
            if math.gcd(a, q) == 1:
                want = o * (3 + (1 if chi.exps[a] == 0 else 0)) / (3 * o + 1)
                assert 1 + v[a] == pytest.approx(want, abs=1e-12)
    # an imprimitive power is replaced by its primitive inducer: chi mod 16 of order 4, squared, has conductor 8
    lev = I.cyc_level(_char(16, 3))
    assert sorted(m.q for m in lev["members"]) == [8, 16, 16]


def test_logderiv_at_one_three_routes_and_the_committed_table():
    ls = _load("lseries.json")
    assert ls["n_characters"] == 79 and ls["all_A_B_overlap"] and ls["all_const0_overlap"]
    assert ls["worst_abs_A_minus_B_upper"] < 1e-30 and ls["worst_abs_A_minus_C"] < 1e-30
    rows = {(r["q"], r["conrey"]): r for r in ls["rows"]}
    from mpmath import mp

    for q, con in ((3, 2), (5, 2), (8, 5)):
        chi = _char(q, con)
        a = I.logderiv_at_one_arb(chi, 128)
        b = I.logderiv_at_one_stieltjes(chi, 128)
        cm = I.logderiv_at_one_mpmath(chi, 25)
        ctx.prec = 128
        try:
            assert a.overlaps(b)
        finally:
            ctx.prec = 53
        assert abs(complex(float(a.real.mid()), float(a.imag.mid())) - complex(cm)) < 1e-14
        assert float(a.real.mid()) == pytest.approx(_mid(rows[(q, con)]["l1_re"]), abs=1e-15)
        k = I.char_constants(chi, 128)
        ctx.prec = 128
        try:
            assert k["direct0"].overlaps(k["derived0"])  # the s = 0 constant, two routes
        finally:
            ctx.prec = 53
    assert mp.dps == 15  # no global mpmath state left modified
    text = _text()
    assert f"{_mid(rows[(3, 2)]['l1_re']):.15f}" in text  # 0.368281615970148
    assert f"{ls['worst_abs_A_minus_B_upper']:.1e}" in text
    assert f"{ls['worst_abs_A_minus_C']:.1e}" in text


def test_character_explicit_formula_and_the_wrong_parity_goes_red():
    x = _load("explicit_chi.json")
    assert len(x["rows"]) == 26 and x["all_tails_positive"]
    assert x["worst_ratio_y_gt_1"] < 0.2
    text = _text()
    assert f"{x['worst_ratio_y_gt_1']:.3f}" in text
    assert f"{100 * x['worst_tail_vs_density']:.1f} percent" in text
    # recompute for one odd and one even character with a short zero list
    ys = np.array([1.0, 2.5, 10.5, 100.5, 1000.5, 20000.5])
    pk, lp = RC._prime_power_arrays(20001)
    for q, con in ((5, 2), (5, 4)):
        chi = _char(q, con)
        k = I.char_constants(chi, 128)
        l1 = RC._c(k["l1"])
        const0 = RC._c(k["direct0"])
        c = float(k["c"].mid())
        zs = Z.l_zero_ordinates(chi, 30.0, step=0.05)
        tail = c - Z.l_partial(zs)
        assert tail > 0
        lhs = RC.gchi_grid(chi, ys, l1, pk, lp)
        ratio = np.abs(lhs - Z.l_zero_side(chi, ys, zs, const0)) / (np.sqrt(ys) * tail)
        assert ratio[0] == pytest.approx(1.0, abs=1e-9)
        assert np.max(ratio[1:]) < 0.5
        # planted fault: the formula of the other parity
        if chi.parity() == 1:
            wrong = Z.l_zero_sum(ys, zs) + np.log(ys) + 1.0 + const0 + I.T_float(ys)
        else:
            wrong = Z.l_zero_sum(ys, zs) + const0 + I.T_odd_float(ys)
        bad = np.abs(lhs - wrong) / (np.sqrt(ys) * tail)
        assert np.max(bad[1:]) > 1.0
        # planted fault: L'/L(1) off by 1e-3 puts a linear term in the defect
        lhs2 = RC.gchi_grid(chi, ys, l1 + 1e-3, pk, lp)
        bad2 = np.abs(lhs2 - Z.l_zero_side(chi, ys, zs, const0)) / (np.sqrt(ys) * tail)
        assert np.max(bad2[1:]) > 1.0


def test_level_scan_recomputes_and_matches_the_committed_run():
    big = _load("levels_q20_y7.json")
    assert big["n_levels"] == 35 and big["n_characters"] == 79
    assert big["identity_at_y_1_holds_for_every_level"]
    small = RC.stage_levels(8, 10**5 - 1, write=False)  # stops where the fifth decade of the big run stops
    assert small["identity_at_y_1_holds_for_every_level"]
    by_gen = {tuple(map(tuple, r["generators"])): r for r in big["levels"]}
    for r in small["levels"]:
        ref = by_gen[tuple(map(tuple, r["generators"]))]
        assert r["C"] == pytest.approx(ref["C"], rel=1e-13)
        for d in range(5):  # decades [2,10) ... [10^4, 10^5)
            assert r["decade_max_ratio"][d] == pytest.approx(ref["decade_max_ratio"][d], abs=1e-9)
            assert r["decade_min_ratio"][d] == pytest.approx(ref["decade_min_ratio"][d], abs=1e-9)
    for key in ("worst_level_ratio_n_ge_100", "worst_char_ratio_n_ge_100", "worst_char_ratio_n_ge_2"):
        assert big[key] < 1.0
    text = _text()
    assert f"{big['worst_level_ratio_n_ge_100']:.4f}" in text
    assert f"{big['worst_char_ratio_n_ge_2']:.4f}" in text
    assert f"{big['worst_char_ratio_n_ge_100']:.4f}" in text
    assert f"{big['max_level_C']:.4f}" in text
    assert f"{big['max_level_sup_Gm_over_sqrt_n_ge_100']:.4f}" in text
    chk = big["arb_checks"][0]
    assert (chk["q"], chk["order"], chk["n"]) == (19, 2, 1855747)
    assert chk["abs_ratio_below_one_decided_by_arb"] and chk["abs_float_minus_arb"] < 1e-10
    assert f"{_mid(chk['ratio_arb']):.12f}" in text
    wide = _load("levels_q30_y6.json")
    assert wide["n_levels"] == 56 and wide["n_characters"] == 167
    assert wide["identity_at_y_1_holds_for_every_level"]
    assert wide["worst_level_ratio_n_ge_100"] < 1.0 and wide["worst_char_ratio_n_ge_2"] < 1.0
    assert f"{wide['worst_level_ratio_n_ge_100']:.4f}" in text


def test_the_worst_character_is_explained_by_a_low_zero():
    """chi_19(3, .) sits at 0.94 of its envelope because one zero carries 92 percent of c_chi."""
    chi = _char(19, 3)
    zs = Z.l_zero_ordinates(chi, 2.0, step=0.01)
    assert len(zs) == 1 and zs[0] == pytest.approx(-0.0190, abs=2e-4)
    c = float(I.char_constants(chi, 128)["c"].mid())
    share = (1.0 / (0.25 + zs[0] ** 2)) / c
    assert c == pytest.approx(4.357759, abs=1e-6) and share == pytest.approx(0.9166, abs=1e-3)
    text = _text()
    assert f"{c:.4f}" in text and f"{share:.3f}" in text and f"{zs[0]:.4f}" in text


def test_level_arb_route_against_float_route_and_a_planted_weight_fault():
    chi = _char(7, 3)  # order 6: members of conductor 7 only
    lev = I.cyc_level(chi)
    mod = I.level_model(lev, 128)
    y = 5000.5
    gm = I.Gm_arb(lev, y, 128)
    # float route by definition
    tot = I.G_float(y)
    for m in lev["members"]:
        l1 = RC._c(I.logderiv_at_one_arb(m, 128))
        tot += float(lev["lam"]) * I.Gchi_float(m, y, l1).real
    assert tot == pytest.approx(float(gm.mid()), abs=1e-9)
    ctx.prec = 128
    try:
        ratio = (gm - I.M_arb(mod, y, 128)) / (mod["C"] * arb(y).sqrt())
        assert bool(abs(ratio) < 1)
        # the identity at y = 1 holds with the archive's weight 1/(3o+1) ...
        d1 = I.Gm_arb(lev, 1, 128) - I.M_arb(mod, 1, 128)
        assert d1.overlaps(mod["C"])
    finally:
        ctx.prec = 53
    # ... and fails when Gm is built with weight 1/(3o) but the envelope keeps 1/(3o+1)
    bad = dict(lev)
    bad["lam"] = Fraction(1, 3 * lev["o"])
    ctx.prec = 128
    try:
        d1_bad = I.Gm_arb(bad, 1, 128) - I.M_arb(mod, 1, 128)
        assert not d1_bad.overlaps(mod["C"])
    finally:
        ctx.prec = 53


# ------------------------------------------------------------- lesion and decoy


def _first_detection(beta, gamma0, y_max, theta):
    env = None
    hit = None
    for n, e, r, _ in I.scan_integers(y_max, seg=1 << 18):
        g = n * e - r
        u = np.log(n)
        d = RL.lesion_delta(u, beta, gamma0)
        if env is None:
            env = RL.first_true((np.abs(g - I.LOG_2PI - I.T_float(n) + d) > I.C0 * np.sqrt(n)) & (n >= 10), n)
        if hit is None:
            hit = RL.first_true((g + d > np.exp(theta * u)) & (n >= 10), n)
    return env, hit


def test_lesion_is_flagged_and_the_control_is_silent():
    les = _load("lesion.json")
    ctrl = les["control_no_lesion"]
    assert ctrl["prime_side_first_envelope_violation_n_ge_2"] is None
    assert not ctrl["model"]["any_envelope_violation"]
    assert ctrl["prime_side_last_n_with_G_above_n_pow_theta"]["0.5"] == 3
    rows = {(r["beta"], r["gamma0"]): r for r in les["rows"]}
    r = rows[(1.0, 30.0)]
    env, hit = _first_detection(1.0, 30.0, 300000, 0.5)
    assert env == r["envelope_first_y_prime_side"] == 388.0
    th = {t["theta"]: t for t in r["thetas"]}
    assert hit == th[0.5]["first_y_prime_side"] == 229536.0
    # the planted zero is told apart from the true zeros: with no lesion nothing fires
    for n, e, r_, _ in I.scan_integers(300000, seg=1 << 18):
        g = n * e - r_
        assert not np.any((np.abs(g - I.LOG_2PI - I.T_float(n)) > I.C0 * np.sqrt(n)))
        assert not np.any((g > np.sqrt(n)) & (n >= 10))
    text = _text()
    assert "388" in text and "229536" in text
    # prime side and zero-side model agree on the first detection wherever both see it
    n_both = 0
    for row in les["rows"]:
        for t in row["thetas"]:
            if t["first_y_prime_side"] is not None:
                assert t["first_y_model"] == pytest.approx(t["first_y_prime_side"], rel=2e-3)
                n_both += 1
    assert n_both == 6 and f"{n_both} cases" in text
    # every detected case: violations recur in every window from onset^(2/3) on, none before
    detected = [t for row in les["rows"] for t in row["thetas"] if t["first_y_model"] is not None]
    assert len(detected) == 25 and f"{len(detected)} of the 48" in text
    for t in detected:
        assert t["windows_from_onset_two_thirds"]["every_window_has_violation"]
        assert t["windows_from_10"]["log10_last_clean_window_start"] == pytest.approx(t["log10_onset_to_the_two_thirds"], abs=2e-4)
        assert 0.6 < t["first_y_model"] / t["predicted_onset"] < 1.7
    worst = max(t["first_y_model"] / t["predicted_onset"] for t in detected)
    best = min(t["first_y_model"] / t["predicted_onset"] for t in detected)
    assert f"{best:.2f} and {worst:.2f}" in text
    # closed-form reach at the verified height, quoted in RESULTS and in MISSION
    assert math.log10(RL.predicted_onset(1.0, 3e12, 0.5)) == pytest.approx(49.31, abs=0.01)
    assert math.log10(RL.predicted_envelope_onset(1.0, 3e12)) == pytest.approx(46.64, abs=0.01)
    assert "10^49.3" in text and "10^46.6" in text


def test_decoy_recomputes():
    dec = _load("decoy.json")
    n = np.arange(2, 10**6 + 1, dtype=np.float64)
    logn = np.log(n)
    rng = np.random.default_rng(1000)
    keep = rng.random(len(n)) < 1.0 / np.maximum(logn, 1.0)
    lam = np.where(keep, logn, 0.0)
    e = I.EULER_GAMMA + np.cumsum(lam / n + np.log1p(-1.0 / n))
    r = -1.0 + np.cumsum(lam - 1.0)
    f = (n * e - r - I.LOG_2PI - I.T_float(n)) / np.sqrt(n)
    row = dec["rows"][0]
    assert row["seed"] == 1000
    assert float(np.max(np.abs(f[n >= 100]))) == pytest.approx(row["sup_abs_F_raw_n_ge_100"], rel=1e-9)
    assert dec["decoy_min_sup_abs_F_after_refit"] > 100 * I.C0
    assert dec["true_primes_sup_abs_F_n_ge_100"] < I.C0
    text = _text()
    assert f"{dec['decoy_min_sup_abs_F_after_refit']:.1f}" in text
    assert f"{dec['decoy_min_sup_abs_F_raw']:.0f}" in text
    assert f"{dec['decoy_max_fraction_inside_after_refit']:.2f}" in text


# ---------------------------------------------------------------------- rivals


def test_rival_coefficients_are_not_supported_on_prime_powers():
    n_max = 20000
    ppm = RR.prime_power_mask(n_max)
    kap = RR.dh_kappa()
    lam_dh = RR.log_derivative_coefficients(RR.dh_coefficients(n_max, kap))
    assert lam_dh[6] == pytest.approx((1 + kap * kap) * math.log(6), abs=1e-13)
    a_e = RR.epstein_coefficients(n_max)
    assert (a_e[2], a_e[3], a_e[6]) == (0.0, 0.0, 2.0)
    lam_e = RR.log_derivative_coefficients(a_e)
    assert lam_e[6] == pytest.approx(2 * math.log(6), abs=1e-13)
    for lam in (lam_dh, lam_e):
        off = (np.abs(lam) > 1e-9) & ~ppm
        assert off[6] and off.sum() > 1000 and lam.min() < -1.0
    # the same recursion gives back the von Mangoldt function for zeta
    ones = np.ones(n_max + 1)
    ones[0] = 0.0
    lam_z = RR.log_derivative_coefficients(ones)
    ref = I.lambda_segment(0, n_max + 1, I.small_primes(200))
    assert np.max(np.abs(lam_z - ref)) < 1e-11
    assert not ((np.abs(lam_z) > 1e-9) & ~ppm).any()
    # planted fault: a multiplicativity defect in one coefficient shows up off the prime powers
    bad = ones.copy()
    bad[6] = 1.5
    lam_bad = RR.log_derivative_coefficients(bad)
    assert abs(lam_bad[6]) > 0.5 and ((np.abs(lam_bad) > 1e-9) & ~ppm).any()


def test_rival_growth_matches_the_recorded_off_line_zeros():
    r = _load("rivals.json")
    z, d, e = r["zeta_control"], r["davenport_heilbronn"], r["epstein_1_1_6"]
    assert r["n_max"] == 10**7
    assert z["coefficients"]["count_nonzero_off_prime_powers"] == 0 and z["coefficients"]["count_negative"] == 0
    assert all(abs(s - 0.5) < 0.02 for s in z["demod_slopes_at_gamma1"])
    assert all(abs(s - d["known_zero"]["beta"]) < 0.005 for s in d["demod_slopes_at_known_zero"])
    assert all(abs(s - e["known_zero"]["beta"]) < 0.015 for s in e["demod_slopes_at_known_zero"])
    assert d["amplitude_hat_top_decade"] == pytest.approx(d["amplitude_from_residue_1_over_abs_rho_1_minus_rho"], rel=1e-3)
    assert e["amplitude_hat_top_decade"] == pytest.approx(e["amplitude_from_residue_1_over_abs_rho_1_minus_rho"], rel=5e-3)
    # the demodulation is specific to the zero: 8 units away the amplitude is far smaller
    assert d["demod_at_known_zero"][-1] > 50 * max(d["demod_at_gamma_minus_8"][-1], d["demod_at_gamma_plus_8"][-1])
    assert e["demod_at_known_zero"][-1] > 30 * max(e["demod_at_gamma_minus_8"][-1], e["demod_at_gamma_plus_8"][-1])
    # the recorded zeros are the ones the lab has on file
    from zeta.epstein import OFFLINE_ZERO_IM, OFFLINE_ZERO_RE

    assert d["known_zero"]["beta"] == pytest.approx(float(OFFLINE_ZERO_RE), abs=1e-15)
    assert d["known_zero"]["gamma"] == pytest.approx(float(OFFLINE_ZERO_IM), abs=1e-12)
    eo = json.loads((REPO / "hunts" / "weil_propagation" / "numerics" / "epstein_offline.json").read_text())
    beta, gamma = (float(v) for v in eo["roots"][0]["root"])
    assert (e["known_zero"]["beta"], e["known_zero"]["gamma"]) == (beta, gamma)
    # interface inequality on the rivals
    ei = {x["theta"]: x for x in e["interface"]}
    assert ei[0.6]["first_violation"] == 1025840 and ei[0.6]["last_clean_window_start"] == 10171
    assert ei[0.6]["first_violation"] == pytest.approx(e["predicted_first_violation"]["0.6"], rel=2e-3)
    assert ei[0.6]["last_clean_window_start"] == pytest.approx(ei[0.6]["first_violation"] ** (2 / 3), abs=1.0)
    assert ei[0.75]["n_violations"] == 0
    assert all(x["n_violations"] == 0 for x in d["interface"])
    assert all(x["n_violations"] == 0 for x in z["interface"])
    text = _text()
    for s in d["demod_slopes_at_known_zero"] + e["demod_slopes_at_known_zero"] + z["demod_slopes_at_gamma1"]:
        assert f"{s:.3f}" in text
    for key in ("count_nonzero_off_prime_powers", "count_nonzero", "count_negative"):
        assert str(d["coefficients"][key]) in text and str(e["coefficients"][key]) in text
    assert f"{d['coefficients']['decade_slopes_of_sum_abs_lambda'][-1]:.4f}" in text
    assert f"{e['coefficients']['decade_slopes_of_sum_abs_lambda'][-1]:.4f}" in text
    assert "1025840" in text and "10171" in text and "22132" in text
    assert f"{d['predicted_first_violation_theta_0.6']:.1e}" in text
    assert f"{d['logderiv_at_1']['flint_re']:.12f}" in text
    assert f"{e['g0']['g0_kronecker']:.12f}" in text
    assert d["logderiv_at_1"]["abs_diff"] < 1e-14 and e["g0"]["abs_diff"] < 1e-20


def test_epstein_first_decades_recompute():
    r = _load("rivals.json")["epstein_1_1_6"]
    n_max = 10**5
    a_e = RR.epstein_coefficients(n_max)
    lam = RR.log_derivative_coefficients(a_e)
    g = RR.smoothed_sum(lam, r["g0"]["g0_kronecker"], with_pole=True)
    dem = RR.demodulate(g, r["known_zero"]["gamma"], 3, 5)
    assert dem[0] == pytest.approx(r["demod_at_known_zero"][0], rel=1e-9)
    assert dem[1] == pytest.approx(r["demod_at_known_zero"][1], rel=1e-9)
    w = RR.interface_windows(g, 0.55)
    assert w["first_violation"] == 22132
    # zeta through the same smoothing: G_f is the G of the instrument
    lam_z = I.lambda_segment(0, n_max + 1, I.small_primes(400))
    gz = RR.smoothed_sum(lam_z, I.EULER_GAMMA, with_pole=True)
    assert gz[1000] == pytest.approx(I.G_float(1000.0), abs=1e-9)
    assert gz[99991] == pytest.approx(I.G_float(99991.0), abs=1e-8)
    assert RR.interface_windows(gz, 0.5)["n_violations"] == 0


# ------------------------------------------------- the remaining quoted numbers


def test_remaining_numbers_quoted_in_results():
    text = _text()
    # zeros and the ladder table
    z = _load("zeros.json")
    assert z["n_zeros"] == 20000 and z["max_abs_diff_vs_data_zeros_1000"] == 0.0
    assert f"{z['height']:.3f}" in text and f"{z['max_ball_radius']:.1e}" in text
    x = _load("explicit_zeta.json")
    assert len(RS.explicit_grid()) == x["n_points"]
    for m in ("100", "1000", "5000", "20000"):
        lad = x["ladder"][m]
        row = f"| {m} | {lad['tail_budget']:.2e} | {lad['max_abs_ratio_y_gt_1']:.3f} | {lad['tail_budget'] * lad['max_abs_ratio_y_gt_1']:.2e} |"
        assert row in text, row
        assert abs(lad["ratio_at_y_1"] - 1.0) < 1e-11
    # scan side remarks
    scan = _load("scan_1e9.json")
    enc = _load("scan_1e9_enclosed.json")
    assert f"{scan['elapsed_s']:.1f} s" in text
    d2 = enc["decades"][2]
    assert d2["n_gmax"] == 118 and f"{_mid(d2['G_over_sqrt_max_arb']):.5f} at `n = 118`" in text.replace("\n", " ")
    assert all(_mid(d["G_over_sqrt_max_arb"]) < 1 for d in enc["decades"][1:])
    assert _mid(enc["decades"][0]["G_over_sqrt_max_arb"]) > 1 and enc["decades"][0]["n_gmax"] == 2
    for d in enc["decades"][1:]:  # the interior maximum exceeds the integer one by at most about 1/(8 n^1.5)
        assert 0 <= d["F_crit_minus_F_int"] <= 1.05 / (8 * (d["n_max"] - 1) ** 1.5)
    # characters
    c = _load("explicit_chi.json")
    assert sum(r["n_zeros"] for r in c["rows"]) == 2396 and "2396 zeros" in text
    assert c["n_points"] == 60 and "60 points" in text
    ls = _load("lseries.json")
    assert f"{ls['worst_abs_const0_direct_minus_derived_upper']:.1e}" in text
    big = _load("levels_q20_y7.json")
    assert big["max_level_last_n_with_Gm_above_sqrt"] == 6 and "beyond `n = 6`" in text
    assert len(big["arb_checks"]) == 3 and all(a["abs_ratio_below_one_decided_by_arb"] for a in big["arb_checks"])
    zs17 = Z.l_zero_ordinates(_char(17, 5), 2.0, step=0.01)
    assert len(zs17) == 1 and f"{zs17[0]:.3f}" in text  # -0.391
    # lesion remarks
    les = _load("lesion.json")
    both = [t for row in les["rows"] for t in row["thetas"] if t["first_y_prime_side"] is not None]
    assert max(abs(t["first_y_model"] / t["first_y_prime_side"] - 1) for t in both) < 2e-4  # "0.02 percent"
    gaps = [
        t["max_gap_between_violations_in_log_y"] / t["period_2pi_over_gamma0"]
        for row in les["rows"]
        for t in row["thetas"]
        if t.get("max_gap_between_violations_in_log_y")
    ]
    assert max(gaps) < 2.01
    assert RL.predicted_envelope_onset(1.0, 1170.0) == pytest.approx(1e9, rel=0.02)
    assert RL.predicted_envelope_onset(0.6, 18.5) == pytest.approx(1e9, rel=0.05)
    assert "about 1170" in text and "about 18.5" in text
    # rivals remarks
    r = _load("rivals.json")
    zc, d, e = r["zeta_control"], r["davenport_heilbronn"], r["epstein_1_1_6"]
    assert str(zc["coefficients"]["count_nonzero"]) in text  # 665134 prime powers below 10^7
    assert f"{zc['coefficients']['decade_slopes_of_sum_abs_lambda'][-1]:.4f}" in text
    assert zc["recursion_reproduces_von_mangoldt_max_abs_diff"] < 1.3e-14
    assert d["recursion_vs_lab_mpmath_max_abs_diff_n_le_240"] < 1.2e-15
    assert abs(d["amplitude_hat_top_decade"] / d["amplitude_from_residue_1_over_abs_rho_1_minus_rho"] - 1) < 1.5e-4
    assert abs(e["amplitude_hat_top_decade"] / e["amplitude_from_residue_1_over_abs_rho_1_minus_rho"] - 1) < 2.5e-3
    sel_d = d["demod_at_known_zero"][-1] / max(d["demod_at_gamma_minus_8"][-1], d["demod_at_gamma_plus_8"][-1])
    sel_e = e["demod_at_known_zero"][-1] / max(e["demod_at_gamma_minus_8"][-1], e["demod_at_gamma_plus_8"][-1])
    assert f"{sel_d:.0f} and {sel_e:.0f} times smaller" in text
    assert f"{e['predicted_first_violation']['0.6']:.0f}" in text  # 1026448
    assert 2.7e10 < e["predicted_first_violation"]["0.75"] < 2.9e10
    assert e["g0"]["residue"] == pytest.approx(2 * math.pi / math.sqrt(23), rel=1e-14)
    # decoy remarks
    dec = _load("decoy.json")
    assert len(dec["rows"]) == 8 and f"{dec['true_primes_sup_abs_F_n_ge_100']:.4f}" in text
    assert 850 < dec["decoy_min_sup_abs_F_after_refit"] / I.C0 < 950  # "a factor near 900"
    # the fetched lemma: its printed bounded term against the calibrated one at x = 1
    printed_b1 = 0.5 + I.LOG_2PI
    needed_b1 = I.LOG_2PI + math.log(2) - 1
    assert f"{printed_b1:.3f}" in text and f"{needed_b1:.3f}" in text
    assert needed_b1 == pytest.approx(math.log(4 * math.pi) - 1, abs=1e-14)
    # the doors
    share = 2 / (0.25 + 14.134725141734693**2) / I.C0
    assert f"{100 * share:.1f} percent" in text
    per_decade = ", ".join(f"{d['F_crit_over_c0']:.2f}" for d in enc["decades"])
    assert per_decade in text.replace("\n", " ").replace("   ", " ")


# ------------------------------------------------------------- hygiene of the hunt


def test_no_reserved_word_and_no_em_dash_in_this_hunt():
    stem = "cer" + "tif"  # spelled in two pieces so that this file passes its own check
    long_dash = chr(0x2014)
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".py", ".md", ".json"}:
            continue
        body = path.read_text(encoding="utf-8")
        assert stem not in body.lower(), path.name
        assert long_dash not in body, path.name


def test_results_has_the_required_sections():
    text = _text()
    for heading in ("## The doors", "## Standing checklist", "## Literature", "## Caveats"):
        assert heading in text
    for word in ("the archive states",):
        assert word in text
    assert "the archive proves" not in text.lower()
    runs = _text("RUNS.md")
    assert len(re.findall(r"```runmanifest\n", runs)) >= 8
