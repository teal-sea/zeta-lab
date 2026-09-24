"""Tests for bound_trunc/ (DERIVATION.md, RESULTS.md). Every number RESULTS.md states is pinned here.

    PYTHONPATH=<worktree root> <venv python> -m pytest -q -n 2 hunts/weil_propagation/c4_s2/bound_trunc
"""

from __future__ import annotations

import json
import math
import os
import sys

import numpy as np
import pytest
from flint import arb, fmpq, fmpq_poly

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
for p in (HERE, os.path.join(C4S2, "kernel"), os.path.join(C4S2, "two_adic"), os.path.join(C4S2, "checker")):
    if p not in sys.path:
        sys.path.insert(0, p)

import eps_trunc as E  # noqa: E402

JSON = os.path.join(HERE, "eps_trunc.json")
RESP = os.path.join(HERE, "responses.json")
L1JSON = os.path.join(HERE, "lemma1_companion.json")
QUAD_JSON = os.path.join(C4S2, "bound_quad", "eps_quad.json")


@pytest.fixture(scope="module")
def doc():
    """{"entries": eps_trunc.json (a list, the brief's interface), "responses": responses.json's}."""
    with open(JSON) as fh:
        entries = json.load(fh)
    with open(RESP) as fh:
        resp = json.load(fh)
    assert isinstance(entries, list)
    return {"entries": entries, "responses": resp["responses"], "meta": resp["meta"]}


@pytest.fixture(scope="module")
def snap():
    return E._snapshot()


# ------------------------------------------------------------------ the interface


def test_json_has_every_build_with_null_and_reason(doc):
    """33 entries (11 builds x 3 c), the brief's keys, eps_upper null, a reason."""
    want = {(c, N, nv, S) for c in E.CELLS for N, bl in E.BUILDS.items() for nv, S in bl}
    got = {(e["c"], e["N"], e["nvec"], e["S"]) for e in doc["entries"]}
    assert got == want and len(doc["entries"]) == 33
    for e in doc["entries"]:
        assert {"c", "N", "nvec", "S", "Kmax", "eps_upper", "grade", "assumptions"} <= set(e)
        assert e["eps_upper"] is None
        assert "unresolved" in e["grade"] and e["reason"] and e["blocking_step"]
        assert e["Kmax"] == E.kmax_for(e["nvec"])


def test_kmax_matches_two_adic_and_the_stored_units(snap):
    import ta_prolate

    for N, bl in E.BUILDS.items():
        for nv, S in bl:
            assert E.kmax_for(nv) == ta_prolate.kmax_for(nv)
            assert snap["units"][f"{nv}|{S}|{N}"]["kmax"] == E.kmax_for(nv)


def test_eps_trunc_returns_no_finite_upper_end():
    for c in E.CELLS:
        for N, bl in E.BUILDS.items():
            for nv, S in bl:
                eps = E.eps_trunc(c, N, nv, S, E.kmax_for(nv))
                assert isinstance(eps, arb) and not eps.is_finite()
    with pytest.raises(ValueError):
        E.eps_trunc("2.9", 32, 200, 2400, 12)  # wrong Kmax
    with pytest.raises(ValueError):
        E.eps_trunc("2.7", 8, 80, 1200, 10)  # not a cell


# ------------------------------------------------------------------ responses and the necessary inequality


def test_responses_recomputed_from_the_snapshot(doc, snap):
    for key, rows in doc["responses"].items():
        c, N = key.split("|")
        again = E.responses(c, int(N), snap)
        assert [(r["a"], r["b"]) for r in again] == [(r["a"], r["b"]) for r in rows]
        for r0, r1 in zip(rows, again):
            assert abs(r0["norm2"] - r1["norm2"]) <= 1e-15 * max(1.0, r1["norm2"])


def test_response_values_quoted_in_results(doc):
    """RESULTS.md quotes these (spectral norms of T_S differences at equal (c, N))."""
    def resp(c, N, a, b):
        for r in doc["responses"][f"{c}|{N}"]:
            if tuple(r["a"]) == a and tuple(r["b"]) == b:
                return r["norm2"]
        raise KeyError((c, N, a, b))

    assert max(r["norm2"] for r in doc["responses"]["2.9|32"]) == pytest.approx(4.950e-3, abs=5e-7)
    assert resp("2.9", 32, (200, 2400), (280, 2266)) == pytest.approx(4.950e-3, abs=5e-7)
    assert resp("2.9", 32, (319, 2633), (364, 3060)) == pytest.approx(4.177e-3, abs=5e-7)
    assert resp("2.2", 16, (80, 1200), (120, 1200)) == pytest.approx(7.853e-2, abs=5e-6)
    assert resp("2.9", 16, (120, 1600), (160, 1600)) == pytest.approx(3.688e-3, abs=5e-7)
    assert max(r["norm2"] for r in doc["responses"]["2.2|32"]) == pytest.approx(2.974e-2, abs=5e-6)


def test_every_bound_dominates_every_response(doc):
    """The necessary condition (BRIEF.md milestone 3), triangle inequality made explicit:

        ||dT(a) - dT(b)|| <= ||dT(a) - dT_exact|| + ||dT_exact - dT(b)||
                          <= [eps_trunc(a) + eps_quad(a)] + [eps_trunc(b) + eps_quad(b)].

    A null eps_upper is +infinity here, so with this folder's nulls the
    inequality holds vacuously on every pair; the test states it so that a
    future finite entry (here or in bound_quad/) is checked against every
    measured response. Necessary, not sufficient."""
    def up(x):
        return math.inf if x is None else float(x)

    quad = {}
    if os.path.exists(QUAD_JSON):
        with open(QUAD_JSON) as fh:
            q = json.load(fh)
        for e in (q if isinstance(q, list) else q.get("entries", [])):
            quad[(str(e["c"]), int(e["N"]), int(e["nvec"]), int(round(float(e["S"]))))] = e["eps_upper"]

    mine = {(e["c"], e["N"], e["nvec"], e["S"]): up(e["eps_upper"]) for e in doc["entries"]}
    checked = 0
    for key, rows in doc["responses"].items():
        c, N = key.split("|")
        for r in rows:
            ka, kb = (c, int(N), *r["a"]), (c, int(N), *r["b"])
            total = mine[ka] + mine[kb] + (up(quad[ka]) if ka in quad else 0.0) + (up(quad[kb]) if kb in quad else 0.0)
            assert total >= r["norm2"]
            checked += 1
    assert checked == 3 * (10 + 10)  # 10 pairs at N = 16 and 10 at N = 32, per c


# ------------------------------------------------------------------ Lemma 3's constants and a falsification check


def test_kappa_and_K_enclosures():
    a = 1 / arb(2).sqrt()
    k = E.kappa_ball()
    K = E.K_ball()
    assert k.overlaps(((1 - a) / (1 + a)) ** 2)
    assert k.overlaps((arb(2).sqrt() - 1) ** 4)
    assert K.overlaps(((1 + a) / (1 - a)) ** 2)
    assert K.overlaps((arb(2).sqrt() + 1) ** 4)
    assert (k * K).overlaps(arb(1))
    assert float(k.rad()) <= 3.6e-15 and float(K.rad()) <= 4.6e-14  # the radii RESULTS.md quotes (53 bits)
    lo, hi = E.kappa_bounds()
    assert lo < hi and hi - lo == fmpq(12, 2**80)
    from flint import ctx

    old, ctx.prec = ctx.prec, 256
    try:
        k256 = 17 - 12 * arb(2).sqrt()
        assert arb(lo) < k256 and k256 < arb(hi)
    finally:
        ctx.prec = old
    assert k.contains(arb("0.02943725152286")) or abs(float(k.mid()) - 0.02943725152286) < 1e-14
    assert abs(float(K.mid()) - 33.9705627484771) < 1e-12


@pytest.fixture(scope="module")
def t_inf32():
    import sonin

    return {c: np.array(sonin.T_inf_matrix(c, 32, 40).tolist(), dtype=float) for c in E.CELLS}


def test_lemma3_holds_on_every_stored_build(snap, t_inf32):
    """kappa T_inf <= T_S <= K T_inf, tested on the stored matrices: necessary,
    not sufficient (the stored T_S carries the band). Smallest margins, measured:
    1.09e-3 on the lower side (c = 2.9, N = 32, 240 modes) and 2.78e-3 on the
    upper side (c = 2.9, N = 32, 364 modes)."""
    import checker_q as CQ  # noqa: F401  (central blocks are plain slices here)

    k_hi = float(E.kappa_bounds()[1]) * (1 + 1e-12)
    K_lo = 1.0 / k_hi
    lows, highs = [], []
    for c in E.CELLS:
        T32 = t_inf32[c]
        for N, bl in E.BUILDS.items():
            o = 32 - N
            T = T32[o:o + 2 * N + 1, o:o + 2 * N + 1]
            for nv, S in bl:
                TS = E.stored_T_S(snap, c, N, nv, S)
                lows.append((np.linalg.eigvalsh(TS - k_hi * T)[0], c, N, nv))
                highs.append((np.linalg.eigvalsh(K_lo * T - TS)[0], c, N, nv))
    lo, hi = min(lows), min(highs)
    assert lo[0] > 0 and hi[0] > 0
    assert lo[1:] == ("2.9", 32, 240) and lo[0] == pytest.approx(1.086e-3, abs=5e-6)
    assert hi[1:] == ("2.9", 32, 364) and hi[0] == pytest.approx(2.783e-3, abs=5e-6)


# ------------------------------------------------------------------ Lemma 2


def _legendre_even(j: int) -> fmpq_poly:
    return fmpq_poly.legendre_p(2 * j)


def _int01(p: fmpq_poly) -> fmpq:
    q = p.integral()
    return q(fmpq(1)) - q(fmpq(0))


def test_lemma2_D_inverse_keeps_the_degree_tail():
    """<p, D^{-1} P_2j> = sqrt2 int_0^{1/2} p(v) P_2j(2v) dv = sqrt2 2^{-1} int_0^1 p(y/2) P_2j(y) dy,
    zero for every even p of degree < 2j (exact rationals, up to the factor sqrt2)."""
    y = fmpq_poly([0, 1])
    for j in range(1, 9):
        P = _legendre_even(j)
        for k in range(j):
            p_half = (y / 2) ** (2 * k)  # p(y/2) for p = v^{2k}
            assert _int01(p_half * P) == 0
        # and not beyond: v^{2j} does see P_2j
        assert _int01((y / 2) ** (2 * j) * P) != 0


# ------------------------------------------------------------------ Proposition 4


def test_window_tail_closed_form_against_quadrature():
    for c, N, sig in (("2.9", 8, 92.37604307034013), ("2.2", 16, 92.37604307034013), ("2.2", 32, 230.94)):
        M = E.window_tail_matrix(c, N, sig)
        L = math.log(float(c))
        kap = 2 * math.pi * np.arange(-N, N + 1) / L
        x, w = np.polynomial.legendre.leggauss(40)
        edges = np.linspace(-sig, sig, 4001)
        s = np.concatenate([(a + b) / 2 + (b - a) / 2 * x for a, b in zip(edges[:-1], edges[1:])])
        ws = np.concatenate([(b - a) / 2 * w for a, b in zip(edges[:-1], edges[1:])])
        V = 2 / np.sqrt(L) * np.sin(s * L / 2)[None, :] / (s[None, :] - kap[:, None])
        M2 = np.eye(2 * N + 1) - (V * ws) @ V.T / (2 * math.pi)
        assert np.abs(M - M2).max() < 1e-10


def test_proposition4_inequalities_and_pinned_values(doc):
    for e in doc["entries"]:
        z = e["size_if_closed"]
        assert z["W"] >= z["W_v1"] - 1e-13
        if z["sigma"] > z["window_band"]:
            assert z["W"] <= z["upper_b"]
            assert z["W_continuous"] <= z["upper_d"]
            assert z["overlap_top_v1"] >= 0.94
        else:
            assert z["upper_b"] is None and z["W"] > 0.87
    got = {(e["c"], e["N"], e["nvec"]): e["size_if_closed"] for e in doc["entries"]}
    Ws = [got[("2.9", 32, n)]["W"] for n in (200, 240, 280, 319, 364)]
    W0 = [got[("2.9", 32, n)]["W_continuous"] for n in (200, 240, 280, 319, 364)]
    assert Ws == pytest.approx([0.2125, 0.1603, 0.1313, 0.1131, 0.0975], abs=5e-5)
    band = 8.2e-3  # the c = 2.9, N = 32 band, as c4_s2/RESULTS.md line 1 quotes it
    assert round(Ws[-1] / band) == 12 and round(Ws[0] / band) == 26
    assert W0 == pytest.approx([0.0275, 0.0115, 0.0063, 0.0040, 0.0025], abs=5e-5)
    assert [a / b for a, b in zip(Ws, W0)] == pytest.approx([7.7, 13.9, 20.8, 28.3, 39.0], abs=0.6)
    assert got[("2.9", 8, 80)]["W"] == pytest.approx(0.1174, abs=5e-5)
    assert got[("2.9", 16, 80)]["W"] == pytest.approx(0.8764, abs=5e-5)
    assert got[("2.2", 32, 200)]["W"] == pytest.approx(1.0, abs=1e-5)
    ov = [z["overlap_top_v1"] for z in got.values() if z["sigma"] > z["window_band"]]
    assert min(ov) == pytest.approx(0.944, abs=1e-3) and max(ov) == pytest.approx(0.999, abs=1e-3)
    app = [z["W"] for z in got.values() if z["sigma"] > z["window_band"]]
    assert min(app) == pytest.approx(0.0975, abs=5e-5) and max(app) == pytest.approx(0.2973, abs=5e-5)
    a0 = [z["W_continuous"] for z in got.values() if z["sigma"] > z["window_band"]]
    assert min(a0) == pytest.approx(0.0025, abs=5e-5) and max(a0) == pytest.approx(0.0799, abs=5e-5)


def test_proposition4_recomputed_for_one_build(doc):
    z0 = [e["size_if_closed"] for e in doc["entries"] if (e["c"], e["N"], e["nvec"]) == ("2.9", 32, 364)][0]
    z1 = E.window_tail_report("2.9", 32, E.sigma_heuristic(364))
    for k in ("W", "W_v1", "overlap_top_v1", "W_continuous", "upper_b", "upper_d"):
        assert z1[k] == pytest.approx(z0[k], rel=1e-12)


# ------------------------------------------------------------------ Lemma 1's measured companion


@pytest.fixture(scope="module")
def l1():
    with open(L1JSON) as fh:
        return json.load(fh)


def test_lemma1_partial_sums_grow_like_log_n(l1):
    P = {int(k): v for k, v in l1["P"].items()}
    ns = sorted(P)
    assert all(P[a] < P[b] for a, b in zip(ns, ns[1:]))
    wf = l1["w_f"]
    assert wf == pytest.approx(0.9899, abs=5e-4)
    for key in ("40-80", "80-160", "120-240"):
        assert l1["slope_per_log_n"][key] == pytest.approx(wf, rel=2e-3)
    assert P[240] == pytest.approx(4.2507, abs=5e-4) and P[80] == pytest.approx(3.1620, abs=5e-4)
    sl = l1["slope_per_log_n"]
    assert [sl["40-80"], sl["80-160"], sl["120-240"]] == pytest.approx([0.9900, 0.9910, 0.9909], abs=5e-5)
    cj = np.array(l1["c_j"])
    h = np.array(l1["heuristic_c_j"]["values"])  # j = 1 .. nmax - 1
    j = np.arange(20, cj.size)
    rel = np.abs(cj[20:] - h[19:]) / h[19:]  # c_j (mode j, 0-based) against the Poisson form at l = 2j
    assert np.all(rel < 0.5 / j)  # measured: 0.47/j at j = 20 falling to 0.27/j at j = 239
    assert rel[-1] * j[-1] == pytest.approx(0.270, abs=2e-3)
    assert rel[0] * j[0] == pytest.approx(0.467, abs=2e-3)
    tail = cj[120:240].sum()
    assert tail == pytest.approx(wf * math.log(2), rel=0.05)


def test_lemma1_stored_delta_T_entry_stays_put(l1):
    """The U_0 entry of the stored Delta_T at c = 2.9, N = 32 moves little over
    200 to 364 modes, while each of its two pieces grows like w_f log n."""
    d = [r["delta_T_00"] for r in l1["stored_delta_T_00"]]
    assert len(d) == 5
    spread = max(d) - min(d)
    growth = l1["w_f"] * math.log(364 / 200)
    assert spread < 0.01 * growth
    assert min(d) == pytest.approx(5.06e-3, abs=5e-5) and max(d) == pytest.approx(6.73e-3, abs=5e-5)
    assert spread == pytest.approx(1.67e-3, abs=5e-5) and growth == pytest.approx(0.593, abs=5e-4)
    assert spread / growth == pytest.approx(0.0028, abs=5e-5)


def test_lemma1_mode_contributions_reproduce():
    """Recompute the first 40 per-mode contributions with the same quadrature."""
    import lemma1_companion as C1

    with open(L1JSON) as fh:
        l1 = json.load(fh)
    cj, wf, _, _ = C1.mode_contributions(nmax=40)
    assert wf == pytest.approx(l1["w_f"], rel=1e-13)
    assert np.allclose(cj, np.array(l1["c_j"][:40]), rtol=1e-10, atol=1e-15)
