"""bound_quad/: pins for DERIVATION.md s2 and RESULTS.md (every stated number), and the inequalities.

Run from the worktree root:
    PYTHONPATH=$PWD <venv python> -m pytest -q -n 2 hunts/weil_propagation/c4_s2/bound_quad
"""

from __future__ import annotations

import json
import math
import os
import sys

import numpy as np
import pytest
from flint import acb, acb_mat, arb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
TWO_ADIC = os.path.join(C4S2, "two_adic")
for p in (HERE, TWO_ADIC):
    if p not in sys.path:
        sys.path.insert(0, p)

import eps_quad as E  # noqa: E402
import ta_mellin as TM  # noqa: E402  (two_adic/, read-only)

KEYS = {"c", "N", "nvec", "S", "Kmax", "eps_upper", "grade", "assumptions"}


@pytest.fixture(scope="module")
def js():
    with open(E.OUT) as fh:
        return json.load(fh)


@pytest.fixture(scope="module")
def gram():
    with open(os.path.join(HERE, "bound_quad_gram.json")) as fh:
        return {(r["nvec"], r["S"]): r for r in json.load(fh)["rows"]}


def _entry(js, c, N, nvec):
    (r,) = [r for r in js if r["c"] == c and r["N"] == N and r["nvec"] == nvec]
    return r


def _f(s):
    return float(s)


# ------------------------------------------------------------ the interface


def test_json_covers_every_stored_build_with_the_interface_keys(js):
    assert len(js) == 33
    got = {(r["c"], r["N"], r["nvec"], int(r["S"])) for r in js}
    want = {(c, N, nv, int(S)) for N, nv, S in E.BUILDS for c in E.CELLS}
    assert got == want
    for r in js:
        assert KEYS <= set(r)
        assert r["eps_upper"] is None, "no finite bound is claimed on any build (E2 open)"
        assert "E2" in r["why"] or "no bound" in r["why"]
        assert r["Kmax"] == E.kmax_for(r["nvec"])


def test_kmax_matches_two_adic_and_the_snapshot():
    import ta_prolate as TP

    with open(E.SNAPSHOT) as fh:
        units = json.load(fh)["units"]
    for N, nv, S in E.BUILDS:
        assert E.kmax_for(nv) == TP.kmax_for(nv)
        key = f"{nv}|{int(S)}|{16 if N == 8 else N}"
        assert units[key]["kmax"] == TP.kmax_for(nv)


def test_eps_quad_returns_plus_infinity_on_every_build():
    for N, nv, S in E.BUILDS:
        for c in E.CELLS:
            x = E.eps_quad(c, N, nv, S, E.kmax_for(nv))
            assert isinstance(x, arb)
            assert x > 10**300 and not x.is_finite()


def test_json_is_what_the_module_computes(js):
    assert E.build_json() == js


def test_s_nodes_match_two_adic_s_grid():
    for S in (1200.0, 2266.1020257693895, 3060.0807085398565):
        s, _ = TM.s_grid(S, width=1.0, per_panel=8)
        assert s.size == E.s_nodes(S)
        assert s.max() < E.s_covered(S) and s.min() > -S
    assert E.s_nodes(2266.1020257693895) == 36256  # two_adic/ s10.1 table
    assert E.s_nodes(3060.0807085398565) == 48960


# ------------------------------------------------------------ E1


@pytest.mark.parametrize("c,N,S0", [("2.2", 8, 1200.0), ("2.9", 32, 2265.1), ("2.5", 16, 1600.0)])
def test_kappa_dominates_the_sampled_window_energy(c, N, S0):
    """Prop 2's kappa against sum_n |V^_n(s)|^2 sampled on |s| in [S0, 6 S0] (float64, measured)."""
    L = math.log(float(c))
    s = np.concatenate([np.linspace(S0, 6 * S0, 20001), -np.linspace(S0, 6 * S0, 20001)])
    V = TM.window_hat(L, N, s)
    sup = float((np.abs(V) ** 2).sum(axis=0).max())
    k = E.kappa(c, N, S0)
    assert sup <= float(k.lower())
    assert sup >= 0.5 * float(k.upper())  # and it is not loose by more than a factor 2 there


def test_E1_values(js):
    pins = {("2.9", 8, 80): 3.703e-3, ("2.9", 16, 80): 7.496e-3, ("2.9", 32, 200): 9.216e-3,
            ("2.9", 32, 280): 1.455e-2, ("2.9", 32, 364): 1.013e-2, ("2.9", 32, 319): 1.213e-2,
            ("2.9", 32, 240): 1.106e-2}
    for (c, N, nv), v in pins.items():
        r = [r for r in js if r["c"] == c and r["N"] == N and r["nvec"] == nv]
        vals = {_f(x["parts_upper"]["E1"]) for x in r}
        assert any(abs(x - v) <= 1e-3 * v for x in vals), (c, N, nv, vals)
    e1_16 = [_f(r["parts_upper"]["E1"]) for r in js if r["c"] == "2.9" and r["N"] == 16]
    assert min(e1_16) >= 4.1e-3 and max(e1_16) <= 1.13e-2
    e1_32 = [_f(r["parts_upper"]["E1"]) for r in js if r["c"] == "2.9" and r["N"] == 32]
    assert min(e1_32) >= 9.2e-3 and max(e1_32) <= 1.46e-2


# ------------------------------------------------------------ the measured S responses


def _gram_probe():
    with open(os.path.join(TWO_ADIC, "ta_gram_probe.json")) as fh:
        return json.load(fh)


def test_S_responses_and_what_they_can_show():
    """two_adic/ s7b: 6.5e-4 (1200 -> 2400), 1.1e-4 (2400 -> 4800) at 80 modes, 1.8e-4 (4800 -> 9600)
    at 160, all c = 2.2, N = 8. A complete bound eps would have to satisfy eps(S1) + eps(S2) >= response
    (triangle inequality through Delta_T_exact at the same nvec). eps_upper is null (+inf), which
    satisfies it trivially. The partial bound E1 alone also exceeds every response, so the responses
    cannot show that E2 is needed (DERIVATION s2.9, correction to s1)."""
    js = _gram_probe()
    dT = {k: np.array(v["dT"]) for k, v in js["runs"].items()}
    pairs = [((80, 1200), (80, 2400), 6.5e-4), ((80, 2400), (80, 4800), 1.1e-4), ((160, 4800), (160, 9600), 1.8e-4)]
    for (n1, S1), (n2, S2), quoted in pairs:
        resp = float(np.linalg.norm(dT[f"{n1},{S1}"] - dT[f"{n2},{S2}"], 2))
        assert abs(resp - quoted) <= 0.06 * quoted, (resp, quoted)
        assert E.eps_quad("2.2", 8, n1, float(S1)) > resp  # +inf
        e1_sum = E.e1("2.2", 8, n1, float(S1)) + E.e1("2.2", 8, n2, float(S2))
        assert e1_sum > resp
        assert float(e1_sum.lower()) >= 2 * resp


# ------------------------------------------------------------ E2


def test_E2_obstruction_is_far_above_one_on_every_build(js):
    for r in js:
        ob = _f(r["e2_obstruction_lower"])
        assert ob > 3, (r["c"], r["N"], r["nvec"], ob)
    n32 = [_f(r["e2_obstruction_lower"]) for r in js if r["N"] == 32]
    assert min(n32) > 9.2e9 and max(n32) < 9.5e10
    ob = {(r["nvec"], int(r["S"])): _f(r["e2_obstruction_lower"]) for r in js if r["c"] == "2.9"}
    assert abs(ob[(120, 1600)] - 1.684e4) < 10 and abs(ob[(120, 1200)] - 3.914e6) < 1e3
    assert abs(ob[(160, 1600)] - 6.096e9) < 1e6 and abs(ob[(280, 2266)] - 4.642e10) < 1e7
    assert abs(ob[(200, 2400)] - 1.483e10) < 1e7


def test_measured_gram_at_the_two_best_builds(gram):
    g = gram[(80, 1200.0)]
    assert abs(g["Gz_eig_min"] - 0.0126) < 5e-4 and abs(g["Gz_eig_max"] - 3.44) < 1e-2
    assert abs(g["cond_Fz"] - 16.51) < 0.02  # the recorded diag, same build
    assert abs(g["leverage_sum_z"] - 78.99) < 0.01 and g["leverage_sum_z"] <= 82  # A5
    for c, v in (("2.2", 3.8e-3), ("2.5", 4.0e-3), ("2.9", 4.2e-3)):
        assert abs(g["probe_norm"][c]["8"] - v) < 0.05e-3
    g2 = gram[(80, 1600.0)]
    assert abs(g2["cond_Fz"] - 5.3835) < 0.01
    assert abs(g2["Gz_eig_min"] - 0.091) < 5e-4 and abs(g2["Gz_eig_max"] - 2.64) < 1e-2
    ob = float(E.e2_obstruction(80, 1200.0, 8).lower())
    assert 69 < ob < 72
    assert 8.8 < float(E.e2_obstruction(80, 1600.0, 16).lower()) < 9.0


def test_E2_measured_size_at_N32_two_adic_A4():
    """The S response at N = 32, 200 modes, S 1200 -> 2400 (two_adic/ s10.3 A4): 5.63e-3 / 6.2e-3 /
    8.0e-3 at c = 2.2 / 2.5 / 2.9; (200, 1200) is at S / nvec^2 = 0.030, the stored 280, 319, 364-mode
    builds at 0.029, 0.026, 0.023; checker/'s band at c = 2.9, N = 32 is 8.18e-3."""
    with open(os.path.join(TWO_ADIC, "ta_rho_check.json")) as fh:
        a4 = json.load(fh)["A4"]
    got = {c: a4["cells"][c]["new_S_response_norm2"] for c in E.CELLS}
    for c, v in (("2.2", 5.63e-3), ("2.5", 6.2e-3), ("2.9", 8.0e-3)):
        assert abs(got[c] - v) <= 0.01 * v, (c, got[c])
    assert (a4["nvec"], a4["S"], a4["N"]) == (200, 1200.0, 32)
    ratios = [round(S / nv**2, 3) for nv, S in ((200, 1200.0), (280, 2266.1), (319, 2633.2), (364, 3060.1))]
    assert ratios == [0.03, 0.029, 0.026, 0.023]
    with open(os.path.join(C4S2, "checker", "checker_inertia.json")) as fh:
        band = json.load(fh)["builds"]["280|2266|32"]["band"]
    assert abs(band - 8.18e-3) < 1e-5


def test_zeta_half_probe_is_the_N32_band():
    """s2.3: two_adic/'s probe (largest entry of M_inf(G_S) - M_inf(I)) at (200, 2400), N = 32 is
    8.16e-3 / 7.55e-3 / 8.18e-3; checker/'s N = 32 band at c = 2.9 is 8.18e-3."""
    with open(os.path.join(TWO_ADIC, "ta_ts_prolate.json")) as fh:
        rows = json.load(fh)["rows"]
    p = {r["c"]: r["gram_sensitivity"] for r in rows if (r["nvec"], r["S"], r["N"]) == (200, 2400.0, 32)}
    for c, v in (("2.2", 8.16e-3), ("2.5", 7.55e-3), ("2.9", 8.18e-3)):
        assert abs(p[c] - v) < 0.005e-3
    with open(os.path.join(C4S2, "checker", "checker_inertia.json")) as fh:
        band = json.load(fh)["builds"]["200|2400|32"]["band"]
    assert abs(band - p["2.9"]) < 1e-12


def test_E1_against_checker_bands(js):
    """E1 alone is 0.70 x band at N = 8 and 1.13 to 1.78 x band on the N = 32 builds (c = 2.9)."""
    with open(os.path.join(C4S2, "checker", "checker_inertia.json")) as fh:
        builds = json.load(fh)["builds"]
    ratio = {}
    for b in builds.values():
        r = [x for x in js if x["c"] == "2.9" and x["N"] == b["N"] and x["nvec"] == b["nvec"] and int(x["S"]) == int(b["S"])]
        ratio[(b["N"], b["nvec"])] = _f(r[0]["parts_upper"]["E1"]) / b["band"]
    assert abs(ratio[(8, 80)] - 0.70) < 0.01
    n32 = [v for (N, _), v in ratio.items() if N == 32]
    assert abs(min(n32) - 1.13) < 0.01 and abs(max(n32) - 1.78) < 0.01


def test_quoted_constants_and_the_sample_sensitivity(gram):
    """cond(G_b,exact) <= ((1 + 2^-1/2) / (1 - 2^-1/2))^2 = 33.97 (two_adic/ s10.1); the sample
    sensitivity delta sqrt(nvec) cond(F_z) with delta = 1e-13 is of order 30 on the 280, 319 and
    364-mode builds (s2.7); run_bound_quad.py took 903 s at a load average of 60 to 80."""
    r = 2**-0.5
    assert abs(((1 + r) / (1 - r)) ** 2 - 33.97) < 0.01
    with open(E.SNAPSHOT) as fh:
        units = json.load(fh)["units"]
    sens = [1e-13 * math.sqrt(nv) * units[f"{nv}|{S}|32"]["diag"]["cond_Fz"] for nv, S in ((280, 2266), (319, 2633), (364, 3060))]
    assert all(25 < x < 45 for x in sens)
    assert abs(sum(r["seconds"] for r in gram.values()) - 903) < 1


def test_unit_cost_record():
    with open(os.path.join(HERE, "bound_quad_unit.json")) as fh:
        u = json.load(fh)
    assert abs(u["seconds_per_phase"] - 2.2e-5) < 0.1e-5
    assert abs(u["seconds_per_pair_mode_product"] - 2.2e-7) < 0.1e-7
    g = {x["nvec"]: x for x in u["grids"]}
    assert g[280]["w_nodes"] == 238752 and g[280]["s_nodes"] == 36256  # two_adic/ s10.1 table
    assert g[364]["w_nodes"] == 454044 and g[364]["s_nodes"] == 48960
    assert abs(g[80]["core_seconds_estimate"] - 2.2e4) < 0.1e4
    assert abs(g[280]["core_seconds_estimate"] - 7.2e5) < 0.1e5
    assert abs(g[364]["core_seconds_estimate"] - 2.2e6) < 0.1e6
    usd = g[280]["core_seconds_estimate"] / 3600 * u["usd_per_core_hour"]
    assert abs(usd - 9.4) < 0.1
    assert abs(g[280]["core_seconds_estimate"] / 3600 - 200) < 2


# ------------------------------------------------------------ E6


def test_E6_values_and_where_it_closes(js):
    closes = {(r["N"], r["nvec"], int(r["S"])) for r in js if r["parts_upper"]["E6"] is not None}
    assert closes == {(8, 80, 1200), (16, 80, 1200), (16, 80, 1600), (16, 120, 1200), (16, 120, 1600), (16, 160, 1600)}
    e = {(r["c"], r["nvec"], int(r["S"])): _f(r["parts_upper"]["E6"]) for r in js if r["N"] == 16 and r["parts_upper"]["E6"]}
    assert abs(e[("2.9", 80, 1200)] - 2.766e-4) < 1e-6
    assert abs(e[("2.9", 80, 1600)] - 1.202e-4) < 1e-6
    assert abs(e[("2.9", 120, 1600)] - 3.139e-2) < 1e-4
    assert abs(e[("2.9", 120, 1200)] - 0.3184) < 1e-3
    assert abs(e[("2.9", 160, 1600)] - 40.57) < 0.05


def test_tail_rows_at_80_1200():
    """s2.2, s2.3: sum_n A_n^2 / (pi S) = 3.38 and sum_n (J_n^2 + A_n^2) / (pi S) = 3.38 at (80, 1200);
    A_n^2 / (4n + 1) spans 0.89 to 12."""
    import ta_prolate as TP

    pm = TP.ProlateModes(nvec=80, dps=20)
    A = pm.derivs[:, 0] * pm.norm
    jz, _ = TP.jumps(pm, 1.0)
    assert abs((A**2).sum() / (math.pi * 1200) - 3.38) < 0.005
    assert abs((A**2 + jz**2).sum() / (math.pi * 1200) - 3.38) < 0.01
    r = A**2 / (4 * np.arange(80) + 1)
    assert abs(r.min() - 0.89) < 0.01 and abs(r.max() - 12.0) < 0.05


def test_E6_against_the_256_bit_reference_of_two_adic_s10_3():
    """two_adic/ s10.3 A2: the QR route against Arb at 256 bits, 64 s-nodes, at (80, S) for S = 300,
    200, 150, 120 (cond(F_z) 5.1e7 to 7.3e14). The measured deviations are 6.8e-9, 1.4e-5, 6.5e-2, 0.21.
    Prop 5 must dominate them where it closes; it closes at none of them (the bound is +inf there),
    which is the direction the measurements require: at 150 and 120 the deviation is of order 1e-1."""
    with open(os.path.join(TWO_ADIC, "ta_rho_check.json")) as fh:
        a2 = json.load(fh)["A2"]
    for key, dev in (("300", 6.8e-9), ("200", 1.4e-5), ("150", 6.5e-2), ("120", 0.21)):
        case = a2[key]
        assert abs(case["new_max_rel_dev"] - dev) <= 0.05 * dev
        b = E.rho_rel_error(case["n_nodes"] + 2, a2["nvec"], case["cond_Fz"])
        assert b is None or float(b.lower()) >= case["new_max_rel_dev"]
        assert b is None
    assert abs(a2["300"]["sample_max_abs_dev"] - 3.0e-13) < 0.05e-13


def test_prop5_dominates_a_high_precision_reference():
    """Prop 5 on a synthetic F (m = 402, n = 20, cond(F) about 1e3): float64 QR route against an
    enclosure of the exact rho of the same float64 samples (arb, 256 bits)."""
    rng = np.random.default_rng(7)
    m, n = 402, 20
    Q1, _ = np.linalg.qr(rng.standard_normal((m, n)) + 1j * rng.standard_normal((m, n)))
    Q2, _ = np.linalg.qr(rng.standard_normal((n, n)))
    F = (Q1 * np.logspace(0, -3, n)) @ Q2
    H = rng.standard_normal((n, 6)) + 1j * rng.standard_normal((n, 6))
    rho_f = TM.rho(H, factor=F)
    sv = np.linalg.svd(F, compute_uv=False)
    bound = E.rho_rel_error(m, n, sv[0] / sv[-1])
    assert bound is not None
    old = ctx.prec
    ctx.prec = 256
    try:
        Fa = acb_mat([[acb(complex(x).real, complex(x).imag) for x in row] for row in F])
        G = Fa.transpose().conjugate() * Fa
        Ha = acb_mat([[acb(complex(x).real, complex(x).imag) for x in row] for row in H])
        X = G.solve(Ha)
        for j in range(H.shape[1]):
            ref = sum((Ha[i, j].conjugate() * X[i, j] for i in range(n)), acb(0)).real
            rel = abs(arb(float(rho_f[j])) / ref - 1)
            assert rel < bound
    finally:
        ctx.prec = old


# ------------------------------------------------------------ E7


def test_E7_values(js):
    e7 = {(r["c"], r["N"], r["nvec"]): _f(r["parts_upper"]["E7"]) for r in js}
    assert abs(e7[("2.9", 8, 80)] - 3.282e-8) < 1e-10
    assert abs(e7[("2.9", 32, 364)] - 1.160e-6) < 1e-8
    assert abs(max(e7.values()) - 3.405e-6) < 1e-9  # RESULTS: E7 <= 3.41e-6


def test_no_s_node_sits_on_a_window_frequency():
    for N, nv, S in E.BUILDS:
        for c in E.CELLS:
            assert E.min_k_distance(c, N, S) > 1e-6


# ------------------------------------------------------------ house rules


def test_folder_text_rules():
    banned = "certif" + "ied"
    for name in os.listdir(HERE):
        if name.endswith((".md", ".py", ".json")):
            with open(os.path.join(HERE, name), encoding="utf-8") as fh:
                text = fh.read()
            assert banned not in text.lower(), name
            if name != "BRIEF.md":
                assert chr(0x2014) not in text, name
