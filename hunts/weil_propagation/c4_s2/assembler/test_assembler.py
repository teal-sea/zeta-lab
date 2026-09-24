"""assembler/ tests, phase 1: the harness, before any bound exists.

Four groups, all fixed in PREREG.md before either bound folder held more
than its BRIEF.md:
1. the exact helpers (decimal and mpf to rational, rational square root);
2. the harness reproduces checker/: the stored matrices bitwise, the class
   basis at 29/10, T_inf bitwise, and s7.9's counts at eps = band and
   2 band (PIN_EXACT, PIN_V4 of test_checker_inertia.py, imported);
3. the decision rule of PREREG (c) on planted bounds, every branch;
4. the bound interface on planted JSON files.
The pins of synthetic.json (the stored matrices at eps = 0, band, 2 band)
are at the end; they are facts about the stored matrices, not about eps.
"""

from __future__ import annotations

import functools
import hashlib
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np
import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import assemble as AS  # noqa: E402  (puts checker/ on sys.path)
from flint import arb, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import test_checker_inertia as TCI  # noqa: E402  (checker/, read-only: its pins)

# ------------------------------------------------ 1. the exact helpers


def test_backend_lists_python_flint():
    from zeta import rigor
    assert "python-flint" in rigor.available_backends()


@pytest.mark.parametrize("s,q", [
    ("8.2e-3", fmpq(82, 10000)), ("0.0053175684479389584", fmpq(53175684479389584, 10 ** 19)),
    ("1", fmpq(1)), ("0", fmpq(0)), ("1.5E-2", fmpq(3, 200)), (" 2.5e-10 ", fmpq(1, 4 * 10 ** 9)),
])
def test_decimal_is_read_exactly(s, q):
    assert AS.dec_to_q(s) == q


@pytest.mark.parametrize("bad,exc", [(0.1, TypeError), (True, TypeError), (None, TypeError),
                                     ("-1e-3", ValueError), ("abc", ValueError)])
def test_decimal_refuses(bad, exc):
    with pytest.raises(exc):
        AS.dec_to_q(bad)


def test_mpf_is_read_exactly():
    with mp.workdps(40):
        xs = [mp.mpf(1) / 3 - 5, -mp.pi / 7, mp.mpf(0), mp.mpf(2) ** 70, mp.mpf("1e-45")]
    for x in xs:
        s, man, exp, bc = x._mpf_
        f = Fraction(-man if s else man) * Fraction(2) ** exp
        q = AS.mpf_to_q(x)
        assert q == fmpq(f.numerator, f.denominator)
        assert float(q) == float(x)
    with pytest.raises(ValueError):
        AS.mpf_to_q(mp.inf)


def test_sqrt_up_is_an_upper_bound_and_tight():
    assert AS.sqrt_up(fmpq(4)) == 2 and AS.sqrt_up(fmpq(9, 4)) == fmpq(3, 2) and AS.sqrt_up(fmpq(0)) == 0
    for s in (fmpq(2), fmpq(1, 3), fmpq(10 ** 40 + 7, 3 ** 30)):
        r = AS.sqrt_up(s)
        assert r * r >= s and (r - fmpq(1, int(s.q))) ** 2 < s


def test_frobenius_bound():
    rows = [[fmpq(3), fmpq(0)], [fmpq(0), fmpq(-4)]]
    assert AS.frob_up(rows) == 5
    rng = np.random.default_rng(2)
    X = rng.standard_normal((9, 9))
    b = AS.frob_up([[AS.RI.to_q(x) for x in r] for r in X])
    assert float(b) >= np.linalg.norm(X, 2) and float(b) >= np.linalg.norm(X, "fro")


# ------------------------------------------- 2. the harness against checker/


@functools.lru_cache(maxsize=None)
def _inertia():
    with open(AS.RI.OUT) as fh:
        return json.load(fh)


def test_stored_R_is_checker_s79_matrix():
    """At c = 2.9 the parameterised stored_R is bitwise run_checker_inertia's."""
    d = _inertia()["builds"]
    snap = AS.load_snapshot()
    for nv, S, N in [(80, 1200, 8), (120, 1600, 16), (200, 2400, 32)]:
        R = AS.stored_R("2.9", nv, S, N)
        assert np.array_equal(R, AS.RI.stored_R(snap, AS.q_full("2.9"), nv, S, N))
        assert hashlib.sha256(np.ascontiguousarray(R).tobytes()).hexdigest() == d[f"{nv}|{S}|{N}"]["R_sha256"]


def test_every_build_is_in_the_snapshot_at_every_cell():
    snap = AS.load_snapshot()
    for c in AS.CELLS:
        for nv, S, N in AS.BUILDS:
            assert AS.RT.unit_key(c, N, 40, nv, S) in snap["T_S"]
    assert sorted(f"{nv}|{S}|{N}" for nv, S, N in AS.BUILDS) == sorted(snap["units"])


def test_kmax_is_the_snapshot_units_kmax():
    for key, u in AS.load_snapshot()["units"].items():
        assert AS.kmax(int(key.split("|")[0])) == u["kmax"]


@pytest.mark.parametrize("c", AS.CELLS)
def test_t_inf_is_what_the_stored_T_S_added(c):
    """T_inf in float64 is bitwise KernelProvider.T_inf_matrix (the stored route)."""
    if AS.TWO_ADIC not in sys.path:
        sys.path.insert(0, AS.TWO_ADIC)
    import ta_ts
    for N in AS.NS:
        assert np.array_equal(AS.t_inf_float(c, N), ta_ts.KernelProvider(80, 1200).T_inf_matrix(c, N, 40))


@pytest.mark.parametrize("N", [8, 32])
def test_class_basis_c_at_29_10_is_checkers(N):
    for prec in AS.BALL_PRECS:
        Z, free = AS.class_basis_c(fmpq(29, 10), N, prec)
        Zc, freec = AS.RI.class_basis(N, prec)
        assert free == freec
        for i in range(Z.nrows()):
            for j in range(Z.ncols()):
                a, b = Z[i, j], Zc[i, j]
                assert a.mid() == b.mid() and a.rad() == b.rad()


@functools.lru_cache(maxsize=None)
def _rows(c, N):
    return AS.CQ.transform_rows(c, N, 40)


@pytest.mark.parametrize("c", AS.CELLS)
@pytest.mark.parametrize("N", [8, 16])
def test_class_V4_at_every_cell_is_the_transform_rows_kernel(c, N):
    """checker/'s derivation check (test_class_V4_is_the_transform_rows_kernel)
    repeated at each cell: the three transform rows vanish together exactly on
    the orthogonal complement of h, n h, e_0 with L = log c; and the basis
    Z(c) satisfies the three constraints."""
    rows = _rows(c, N)
    h, nh, e0 = AS.class_constraints_c(AS.C_EXACT[c], N, 256)
    with mp.workdps(40):
        hm = [mp.mpf(x.mid().str(50, radius=False)) for x in h]
        nhm = [mp.mpf(x.mid().str(50, radius=False)) for x in nh]
        p, m, z = rows["plus"], rows["minus"], rows["zero"]
        a = mp.re(p[N]) / hm[N]
        b = mp.im(p[N + 1]) / nhm[N + 1]
        scale = max(abs(x) for x in p)
        assert max(abs(mp.re(p[i]) - a * hm[i]) for i in range(2 * N + 1)) < mp.mpf("1e-35") * scale
        assert max(abs(mp.im(p[i]) - b * nhm[i]) for i in range(2 * N + 1)) < mp.mpf("1e-35") * scale
        ratio = [m[i] / mp.conj(p[i]) for i in range(2 * N + 1)]
        assert max(abs(r - ratio[0]) for r in ratio) < mp.mpf("1e-35")
        assert abs(mp.im(ratio[0])) < mp.mpf("1e-35")
        assert all(z[i] == 0 for i in range(2 * N + 1) if i != N) and z[N] != 0
    Z, free = AS.class_basis_c(AS.C_EXACT[c], N, 256)
    assert Z.ncols() == 2 * N + 1 - AS.CODIM_V4 == len(free)
    with AS.RI.arb_prec(256):
        for j in range(Z.ncols()):
            for row in (h, nh, e0):
                s = sum((row[i] * Z[i, j] for i in range(2 * N + 1)), arb(0))
                assert s.contains(0) and s.rad() < 1e-60


def test_fixed_terms_live_on_a_small_build():
    """PREREG (a) on one build, recomputed here: every term an upper bound,
    the Q and T_inf roundings within one ulp per entry, the total below 1e-14."""
    fx = AS.fixed_terms("2.9", 80, 1200, 8)
    n = 17
    assert fx["e_Q"] == n * AS.E_Q_ENTRY and fx["e_Tinf"] == n * AS.E_TINF_ENTRY
    Qf = AS.RT.to_np(AS.q_mp("2.9", 8)).real
    ulp = np.sqrt((np.spacing(np.abs(Qf)) ** 2).sum())
    assert 0 < float(fx["r_Q"]) <= ulp * (1 + 1e-12)
    assert fx["r_mirror"] == 0 and 0 <= float(fx["r_sub"]) < 1e-15
    assert float(fx["total"]) < 1e-14
    assert fx["total"] == sum((fx[k] for k in fx if k != "total"), fmpq(0))


def test_count_build_live_matches_the_band_count():
    """s7.9's 80|1200|8 at eps = band, live: L = 4 (PIN_EXACT), V_4 L = 3 (PIN_V4)."""
    R = AS.stored_R("2.9", 80, 1200, 8)
    beta = AS.RI.to_q(AS.band(AS.load_cells(), "2.9", 8))
    r = AS.count_build(AS.RI.lower_mirrored(R), beta, "2.9", 8)
    assert r["L"] == TCI.PIN_EXACT["80|1200|8"][0] and r["V4"]["L"] == TCI.PIN_V4["80|1200|8"][0]
    assert r["L"] <= r["U"] and r["V4"]["L"] <= r["V4"]["U"] and r["robust_delta"]
    w = np.linalg.eigvalsh(R)
    assert r["U"] == int((w < float(beta)).sum())


def test_eps_grow_is_checkers_bracket():
    """eps_grow brackets lambda_{m+1} exactly as s7.9 bracketed it (m = 10 on
    the delivered N = 32 row: lambda_11, counted there)."""
    g = AS.eps_grow("2.9", 200, 2400, 32, 10)
    br = _inertia()["builds"]["200|2400|32"]["brackets"][10]
    assert br["k"] == g["k"] == 11 and g["lo"] == br["lo"] and g["hi"] == br["hi"]
    assert g["grows_for_eps_below"] == -br["hi_float"] and g["no_growth_for_eps_at_least"] == -br["lo_float"]


# ----------------------------------------- 3. the decision rule, planted


def _agg(L, U, space="full", missing=()):
    pb = {N: ([None] if N in missing else [(L[i], U[i])]) for i, N in enumerate(AS.NS)}
    return AS.aggregate(pb, space)


@pytest.mark.parametrize("L,U,missing,expected", [
    ((4, 10, 20), (6, 20, 40), (), 1),
    ((4, 4, 6), (9, 12, 30), (), 1),       # growth at the last step only: still 1
    ((4, 8, 8), (8, 8, 8), (), 2),         # U*_32 = L*_16: pinned, no growth
    ((4, 8, 8), (9, 9, 30), (), 3),        # flat below -eps, undecided above
    ((0, 0, 0), (17, 33, 65), (), 3),      # eps swamps everything
    ((4, 10, 20), (6, 20, 40), (32,), 4),  # no bound at N = 32
    ((4, 10, 20), (6, 20, 40), (16,), 4),  # no bound at N = 16
])
def test_decide_every_branch(L, U, missing, expected):
    d = AS.decide(_agg(L, U, missing=missing))
    assert d["outcome"] == expected


def test_decide_reports_the_first_step():
    assert AS.decide(_agg((4, 10, 20), (6, 20, 40)))["first_step_rises"] is True
    assert AS.decide(_agg((4, 4, 6), (9, 12, 30)))["first_step_rises"] is False
    assert AS.decide(_agg((4, 8, 8), (4, 8, 8)))["first_step"] == "rises"
    assert AS.decide(_agg((8, 8, 8), (8, 8, 8)))["first_step"] == "absent"


def test_inconsistent_bounds_stop_the_rule():
    assert AS.decide(_agg((4, 10, 21), (6, 20, 20)))["outcome"] == "inconsistent"
    # across N by interlacing: a lower bound at N = 16 above the upper bound at 32
    assert AS.decide(_agg((4, 12, 12), (6, 20, 11)))["outcome"] == "inconsistent"


def test_aggregate_takes_the_best_build_and_interlaces():
    pb = {8: [(5, 9), (3, 7)], 16: [(4, 30), None, (2, 12)], 32: [(11, 50), (13, 40)]}
    a = AS.aggregate(pb, "full")
    assert a["raw_L"] == {8: 5, 16: 4, 32: 13} and a["raw_U"] == {8: 7, 16: 12, 32: 40}
    assert a["L"] == {8: 5, 16: 5, 32: 13} and a["U"] == {8: 7, 16: 12, 32: 40}
    assert a["has_bound"] == {8: True, 16: True, 32: True} and a["consistent"]
    none32 = AS.aggregate({8: [(1, 3)], 16: [(2, 5)], 32: [None]}, "V4")
    assert none32["U"][32] == 65 - 3 and not none32["has_bound"][32]


# ---------------------------------------- 4. the bound interface, planted


def _entry(c, N, nv, S, eps, **kw):
    e = {"c": c, "N": N, "nvec": nv, "S": S, "Kmax": AS.kmax(nv), "eps_upper": eps,
         "grade": "planted", "assumptions": ["A1"]}
    e.update(kw)
    return e


def test_load_bound_normalises_and_reads_exactly(tmp_path):
    p = tmp_path / "b.json"
    p.write_text(json.dumps([_entry(2.9, 8, 80, 1200, "1.25e-3"), _entry("2.50", 32, 200, 2400.0, None, why="tail open"),
                             _entry("2.2", 16, 120, 1600, "0")]))
    t = AS.load_bound(str(p))
    b = AS.bound_for(t, "2.9", 80, 1200, 8)
    assert b["eps"] == fmpq(125, 100000) and b["grade"] == "planted" and b["assumptions"] == ["A1"]
    n = AS.bound_for(t, "2.5", 200, 2400, 32)
    assert n["eps"] is None and n["why_null"] == "tail open"
    assert AS.bound_for(t, "2.2", 120, 1600, 16)["eps"] == 0
    assert AS.bound_for(t, "2.2", 80, 1200, 8)["eps"] is None and "no entry" in AS.bound_for(t, "2.2", 80, 1200, 8)["missing"]
    assert AS.bound_for(None, "2.9", 80, 1200, 8)["missing"] == "no bound file"
    p.write_text(json.dumps({"entries": [_entry("2.9", 8, 80, 1200, "1e-3")]}))
    assert AS.bound_for(AS.load_bound(str(p)), "2.9", 80, 1200, 8)["eps"] == fmpq(1, 1000)


def test_load_bound_refuses(tmp_path):
    p = tmp_path / "b.json"
    p.write_text(json.dumps([_entry("2.9", 8, 80, 1200, 1e-3)]))
    with pytest.raises(TypeError):
        AS.load_bound(str(p))
    p.write_text(json.dumps([_entry("2.9", 8, 80, 1200, "1e-3"), _entry(2.9, 8, 80, 1200, "2e-3")]))
    with pytest.raises(ValueError):
        AS.load_bound(str(p))
    # a Kmax that is not kmax_for(nvec) does not match the build
    p.write_text(json.dumps([_entry("2.9", 8, 80, 1200, "1e-3", Kmax=11)]))
    assert AS.bound_for(AS.load_bound(str(p)), "2.9", 80, 1200, 8)["eps"] is None


def test_run_routed_end_to_end_on_planted_bounds(tmp_path):
    """The phase 2 path on one build: eps = the stored band (trunc) + 0 (quad)
    + the fixed terms; the count is s7.9's 4 (V_4: 3); with no bound at
    N = 16 and 32 the rule says outcome 4."""
    beta = repr(AS.band(AS.load_cells(), "2.9", 8))
    t, q = tmp_path / "t.json", tmp_path / "q.json"
    t.write_text(json.dumps([_entry("2.9", 8, 80, 1200, beta)]))
    q.write_text(json.dumps([_entry("2.9", 8, 80, 1200, "0"), _entry("2.9", 32, 200, 2400, None, why="planted")]))
    out = AS.run_routed(out_path=str(tmp_path / "o" / "r.json"), trunc_path=str(t), quad_path=str(q),
                        builds=[("2.9", 80, 1200, 8), ("2.2", 80, 1200, 8)])
    b = out["builds"]["2.9|80|1200|8"]
    fx = AS.fixed_terms("2.9", 80, 1200, 8)["total"]
    assert b["eps"]["q"] == AS.q_pair(AS.dec_to_q(beta) + fx)
    assert b["count"]["L"] == 4 and b["count"]["V4"]["L"] == 3 and b["count"]["robust_delta"]
    assert out["builds"]["2.2|80|1200|8"]["eps"] is None and "no entry" in out["builds"]["2.2|80|1200|8"]["trunc"]["missing"]
    d = out["decisions"]["2.9|full"]
    assert d["decision"]["outcome"] == 4 and d["agg"]["L"][8] == 4 and d["agg"]["has_bound"] == {8: True, 16: False, 32: False}
    assert out["decisions"]["2.2|V4"]["decision"]["outcome"] == 4
    assert out["eps_grow_2.9_full"] == {"m": 4, "builds": {}}


# --------------------------------------------- 5. synthetic.json, as read


def _synth():
    if not os.path.exists(AS.SYNTH_JSON):
        pytest.skip("synthetic.json absent (run assemble.py --synthetic)")
    with open(AS.SYNTH_JSON) as fh:
        return json.load(fh)


def test_synthetic_covers_every_build():
    s = _synth()
    assert sorted(s["builds"]) == sorted(AS.build_key(c, nv, S, N) for c in AS.CELLS for nv, S, N in AS.BUILDS)
    assert s["meta"]["ts_inputs_digest"] == AS.DIGEST


def test_harness_reproduces_s79_at_band_and_2band():
    """BRIEF acceptance: at eps = band (a pure shift) the harness gives s7.9's
    counts on all eight c = 2.9 builds, full space and V_4; also at 2 band."""
    s = _synth()["builds"]
    for key in TCI.EXPECTED_BUILDS:
        b = s["2.9|" + key]
        assert [b["band_x1"]["L"], b["band_x2"]["L"]] == TCI.PIN_EXACT[key][:2], key
        assert [b["band_x1"]["V4"]["L"], b["band_x2"]["V4"]["L"]] == TCI.PIN_V4[key][:2], key
        assert b["band_x1"]["V4"]["L_by"] == b["band_x2"]["V4"]["L_by"] == "balls"
        assert b["R_sha256"] == _inertia()["builds"][key]["R_sha256"]


def test_delivered_rows_match_checkers_float_counts():
    """At 2.2 and 2.5 (and 2.9) the exact count at eps = band on the delivered
    row equals checker_ts_cells.json's float count (measured there)."""
    s, C = _synth()["builds"], AS.load_cells()
    for c in AS.CELLS:
        for N, (nv, S) in AS.DELIVERED.items():
            assert s[AS.build_key(c, nv, S, N)]["band_x1"]["L"] == C[c][str(N)]["full"]["n_minus"], (c, N)


def test_synthetic_invariants():
    for key, b in _synth()["builds"].items():
        e0, x1, x2, xf = b["eps0"], b["band_x1"], b["band_x2"], b["band_x1_plus_fixed"]
        assert e0["L"] == e0["U"] and e0["inertia_plus_eps"][1] == 0  # no eigenvalue exactly 0
        assert x2["L"] <= x1["L"] <= e0["L"] <= x1["U"] <= x2["U"]
        assert x1["V4"]["L"] <= x1["V4"]["U"] and x1["L"] - 3 <= x1["V4"]["L"] <= x1["L"]
        assert x1["robust_delta"] and x2["robust_delta"]
        # the fixed terms (Q, T_inf, float64 rounding) do not move any count
        assert xf["L"] == x1["L"] and xf["U"] == x1["U"]
        assert b["fixed"]["total"]["float"] < 1e-14 and b["symmetric_defect"] == 0.0
