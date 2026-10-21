"""Tests for the Arb evaluator of Polymath 15's effective approximation.

Run:  .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/evaluator/test_effective.py
(``-m "not slow"`` skips the ones that sum over n <= 630783 or rebuild oracles.)

Every number EVALUATOR.md states is asserted here, from a recomputation or from
the committed data files the scripts in this directory wrote.
"""

from __future__ import annotations

import json
import math
import random
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for p in (str(ROOT), str(HERE)):
    if p not in sys.path:
        sys.path.insert(0, p)

from flint import acb, arb, ctx  # noqa: E402

import effective as ef  # noqa: E402

X_ROW2 = 5000000194858
N0_ROW2 = 630783


def _load_jsonl(name: str) -> list[dict]:
    path = HERE / name
    return [json.loads(ln) for ln in path.read_text().splitlines() if ln.strip()]


# --------------------------------------------------------------------------- #
#  Building blocks
# --------------------------------------------------------------------------- #

def test_precision_is_restored() -> None:
    old = ctx.prec
    ef.point("300", "0.5", "0.2")
    assert ctx.prec == old


def test_alpha_is_the_log_derivative_of_M0() -> None:
    with ef.workprec(160):
        h = arb("1e-12")
        for s in (acb("0.7", "-150"), acb("0.2", "1000"), acb("1", "-123456.5")):
            num = (ef.log_M0(s + h) - ef.log_M0(s - h)) / (2 * h)
            assert abs(num - ef.alpha(s)) < arb("1e-18")
            num2 = (ef.alpha(s + h) - ef.alpha(s - h)) / (2 * h)
            assert abs(num2 - ef.alpha_prime(s)) < arb("1e-18")


def test_M0_is_the_stirling_form_of_the_gamma_factor() -> None:
    """Lemma 5.1(v): log Gamma(z) - Stirling = O(1/(12(|z| - 0.33))), z = s/2."""
    with ef.workprec(128):
        pi = arb.pi()
        for s in (acb("0.4", "-100"), acb("0.9", "300"), acb("0.5", "-5000")):
            exact = (s * (s - 1) / 16) * (-(s / 2) * pi.log()).exp() * (s / 2).gamma()
            approx = ef.log_M0(s).exp()
            bound = (1 / (12 * (abs(s / 2) - arb("0.33")))).exp() - 1
            assert abs(exact / approx - 1) < bound


def test_C0_is_bounded_by_one_half_and_continuous_at_its_removable_points() -> None:
    with ef.workprec(128):
        for k in range(-100, 101):
            p = arb(k) / 100
            assert abs(ef.C0(p)) < arb("0.5") + arb("1e-30")   # (cop)
        for p0 in (arb(1) / 2, -arb(1) / 2):
            c = ef.C0(p0)
            assert abs(c - acb("0.25", "-0.25")) < arb("1e-30")
            for eps in ("1e-9", "-1e-9", "2e-6", "-2e-6"):
                assert abs(ef.C0(p0 + arb(eps)) - c) < 3 * abs(arb(eps))
        # the series branch (|eps| < 1e-6) and the direct formula agree across the switch
        p = arb(1) / 2 + arb("9.9e-7")
        q = arb(1) / 2 + arb("1.01e-6")
        assert abs(ef.C0(p) - ef.C0(q)) < arb("1e-7")


def test_N_and_the_row2_interval() -> None:
    with ef.workprec(128):
        X = arb(X_ROW2)
        t0 = arb("0.186")
        assert ef.N_of(X, t0) == N0_ROW2
        assert ef.N_of(X + 1, t0) == N0_ROW2
        assert ef.N_of(X, arb(0)) == N0_ROW2
        assert X >= ef.x_of_N(N0_ROW2, t0)
        assert X + 1 < ef.x_of_N(N0_ROW2 + 1, t0)


def test_region_is_enforced() -> None:
    with pytest.raises(ValueError):
        ef.point("150", "0.5", "0.2")
    with pytest.raises(ValueError):
        ef.point("300", "1.5", "0.2")
    with pytest.raises(ValueError):
        ef.point("300", "0.5", "0.6")


# --------------------------------------------------------------------------- #
#  Theorem 1.3's closed-form bounds dominate the exact quantities
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("x", ["200", "400", "10000", "1000000"])
@pytest.mark.parametrize("y", ["0", "0.5", "1"])
@pytest.mark.parametrize("t", ["0.05", "0.5"])
def test_closed_form_bounds_dominate(x: str, y: str, t: str) -> None:
    P = ef.point(x, y, t)
    b = ef.theorem_bounds(P)
    with ef.workprec(P.prec):
        assert P.e_A + P.e_B < b["eAB_upper"]
        assert P.e_C < b["eC_upper_prop"]
        assert P.e_C0 < b["eC0_upper_prop"]
        assert b["eC0_upper_prop"] < b["eC0_upper_thm"]
        assert P.s_star.real > b["res_bound_prop"]
        assert abs(P.C0p) < arb("0.5") + arb("1e-30")
        if y == "0":
            # |gamma| = 1 and kappa = 0 exactly at y = 0, where the bounds are equalities
            assert not (abs(P.gamma) > b["gamma_upper"])
            assert not (abs(P.kappa) > b["kappa_upper"])
        else:
            assert abs(P.gamma) < b["gamma_upper"]
            assert abs(P.kappa) < b["kappa_upper"]


# --------------------------------------------------------------------------- #
#  Milestone 1: containment of two independent routes to H_t
# --------------------------------------------------------------------------- #

def _containment_table() -> list[dict]:
    rows: dict[tuple[str, str, str], dict] = {}
    for route in ("phi", "hk"):
        for r in _load_jsonl(f"agreement_{route}.jsonl"):
            rows.setdefault((r["x"], r["y"], r["t"]), {})[route] = r
    out = []
    for (x, y, t), routes in sorted(rows.items(), key=lambda kv: tuple(float(v) for v in kv[0])):
        P = ef.point(x, y, t)
        with ef.workprec(P.prec):
            Bt = P.Bt()
            m = abs(Bt)
            approx = P.ABC_value()
            rad_full = (P.e_A + P.e_B + P.e_C) * m
            rad_noC = (P.e_A + P.e_B) * m
            rad_AB = (P.e_A + P.e_B + P.e_C0) * m
            for route, r in routes.items():
                H = acb(arb(r["re"]), arb(r["im"]))
                d = abs(H - approx)
                out.append({
                    "x": x, "y": y, "t": t, "route": route,
                    "contained": bool(d < rad_full),
                    "contained_without_eC": bool(d < rad_noC),
                    "contained_AB_eC0": bool(abs(H - Bt * P.f) < rad_AB),
                    "rel_err": float((d / m).upper()),
                    "rel_bound": float((rad_full / m).lower()),
                })
            if len(routes) == 2:
                a = acb(arb(routes["phi"]["re"]), arb(routes["phi"]["im"]))
                b = acb(arb(routes["hk"]["re"]), arb(routes["hk"]["im"]))
                out.append({"x": x, "y": y, "t": t, "route": "phi_vs_hk",
                            "rel_diff": float((abs(a - b) / abs(a)).upper())})
    return out


def test_milestone1_every_oracle_value_is_inside_the_ABC_enclosure() -> None:
    tab = [r for r in _containment_table() if r["route"] != "phi_vs_hk"]
    phi = [r for r in tab if r["route"] == "phi"]
    hk = [r for r in tab if r["route"] == "hk"]
    assert len(phi) == 60 and len(hk) == 64
    assert all(r["contained"] for r in tab)
    assert all(r["contained_AB_eC0"] for r in tab)
    assert max(float(r["x"]) for r in hk) == 2000.0
    # how loose the bound is: measured error over radius, worst case 0.031
    worst = max(r["rel_err"] / r["rel_bound"] for r in tab)
    assert 0.030 < worst < 0.031


def test_milestone1_the_two_oracles_agree() -> None:
    pairs = [r for r in _containment_table() if r["route"] == "phi_vs_hk"]
    assert len(pairs) == 60
    assert max(r["rel_diff"] for r in pairs) < 1e-8


def test_lesion_dropping_eC_breaks_containment() -> None:
    """The adversary's lesion: without e_C the enclosure must fail somewhere."""
    tab = [r for r in _containment_table() if r["route"] != "phi_vs_hk"]
    failing = {(r["x"], r["y"], r["t"]) for r in tab if not r["contained_without_eC"]}
    assert len(failing) == 7
    assert all(float(k[0]) <= 400 for k in failing)
    assert ("200", "1", "0") in failing
    # each failing point fails under both routes
    both = [k for k in failing if sum(1 for r in tab if (r["x"], r["y"], r["t"]) == k and not r["contained_without_eC"]) == 2]
    assert len(both) == 7


def test_lesion_live_at_one_point() -> None:
    """Same lesion on a value computed now, not read from a file."""
    import oracles

    H = oracles.Ht_heat_kernel("200", "1", "0")
    P = ef.point("200", "1", "0")
    with ef.workprec(P.prec):
        Hb = acb(arb(str(H.real)), arb(str(H.imag)))
        assert P.Ht_ABC().contains(Hb)
        assert not P.Ht_ABC(drop=("C",)).contains(Hb)


@pytest.mark.slow
def test_milestone1_live_heatflow_point() -> None:
    import oracles

    H = oracles.Ht_phi("200", "0.5", "0.2")
    P = ef.point("200", "0.5", "0.2")
    with ef.workprec(P.prec):
        assert P.Ht_ABC().contains(acb(arb(str(H.real)), arb(str(H.imag))))


# --------------------------------------------------------------------------- #
#  Taylor multi-evaluation
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("t", ["0", "0.2"])
def test_multieval_overlaps_direct_summation(t: str) -> None:
    X = 100000000
    with ef.workprec(128):
        N = ef.N_of(arb(X), arb(t))
    ev = ef.FixedTimeMultiEval(f"{X}.5", "0.6", t, N, K=16)
    for x, y in ((str(X), "0.2"), (str(X + 1), "1"), (f"{X}.73", "0.2"), (f"{X}.5", "0.6")):
        v = ev.evaluate(x, y)
        P = ef.point(x, y, t, error_mode="envelope")
        assert v.overlaps(P.f)
        assert v.real.rad() < arb("1e-25")


def test_multieval_charges_its_truncation() -> None:
    """At K = 8 the tail is ~1e-12; it must be inside the ball, not dropped."""
    X = 10000000000
    with ef.workprec(128):
        N = ef.N_of(arb(X), arb("0.1"))
    ev = ef.FixedTimeMultiEval(f"{X}.5", "0.6", "0.1", N, K=8)
    v = ev.evaluate(str(X), "0.2")
    P = ef.point(str(X), "0.2", "0.1", error_mode="envelope")
    assert v.overlaps(P.f)
    assert v.real.rad() > arb("1e-14")


def test_lesion_multieval_without_tail_is_caught(monkeypatch: pytest.MonkeyPatch) -> None:
    """Planted fault: zero the tail bound.  The overlap test must then fail."""
    X = 10000000000
    with ef.workprec(128):
        N = ef.N_of(arb(X), arb("0.1"))
    ev = ef.FixedTimeMultiEval(f"{X}.5", "0.6", "0.1", N, K=8)
    monkeypatch.setattr(ef, "_pow_ui_upper", lambda r, k: arb(0))
    v = ev.evaluate(str(X), "0.2")
    P = ef.point(str(X), "0.2", "0.1", error_mode="envelope")
    assert not v.overlaps(P.f)


def test_derivative_bound_dominates_difference_quotients() -> None:
    X = 100000000
    t = "0.1"
    ys = ["0.2", "0.4", "0.6", "0.8", "1"]
    db = ef.derivative_bounds(str(X), str(X + 1), ys, t)
    rng = random.Random(7)
    with ef.workprec(128):
        for _ in range(12):
            u = rng.random()
            v = rng.random()
            x1 = arb(X) + arb(u)
            x2 = x1 + arb("0.001")
            y1 = arb("0.2") + arb("0.8") * arb(v)
            P1 = ef.point(x1, y1, t, error_mode="envelope")
            P2 = ef.point(x2, y1, t, error_mode="envelope")
            q = abs(P2.f - P1.f) / arb("0.001")
            j = min(3, int(v * 4))
            assert q < db["strip_z"][j]
            Q1 = ef.point(x1, y1, "0.1001", error_mode="envelope")
            qt = abs(Q1.f - P1.f) / arb("0.0001")
            assert qt < db["strip_t"][j]


# --------------------------------------------------------------------------- #
#  Lemma trib2 and the Euler 2 bound
# --------------------------------------------------------------------------- #

def test_trib2_on_random_instances() -> None:
    """Instances that satisfy the lemma's hypothesis: a_n = b_n n^{-s}, lambda = b_2 2^{-s}."""
    rng = random.Random(11)
    with ef.workprec(128):
        for _ in range(25):
            N = rng.randint(2, 300)
            t = arb(rng.randint(1, 50)) / 100
            s = acb(arb(rng.randint(30, 250)) / 100, arb(rng.randint(-10**6, 10**6)) / 7)
            terms = []
            for n in range(1, N + 1):
                L = arb(n).log()
                terms.append(((t / 4) * L * L - s * L).exp())
            lam = ((t / 4) * arb(2).log() ** 2 - s * arb(2).log()).exp()
            lo, hi = ef.trib2_bounds([abs(a) for a in terms], abs(lam))
            S = acb(0)
            for a in terms:
                S += a
            val = abs(1 - lam) * abs(S)
            assert not (val < lo)
            assert not (val > hi)


def test_trib2_lesion_hypothesis_violated() -> None:
    """With lambda of the wrong phase the 'lower bound' is violated somewhere."""
    rng = random.Random(3)
    broke = False
    with ef.workprec(128):
        for _ in range(200):
            N = rng.randint(2, 40)
            s = acb(arb("0.8"), arb(rng.randint(1, 10**5)))
            terms = [(-s * arb(n).log()).exp() for n in range(1, N + 1)]
            lam = -(-s * arb(2).log()).exp()        # sign flipped: hypothesis fails
            lo, _ = ef.trib2_bounds([abs(a) for a in terms], abs(lam))
            S = acb(0)
            for a in terms:
                S += a
            if abs(1 - lam) * abs(S) < lo:
                broke = True
                break
    assert broke


ROWS = [  # X, t0, y0^2, N0, printed column value (debruijn.tex lines 1949-1953), numerator to 6 places
    (2000000129093, "0.198", "0.024", 398942, 0.0341, 0.034132),
    (5000000194858, "0.186", "0.028", 630783, 0.0376, 0.037627),
    (20000000131252, "0.180", "0.020", 1261566, 0.0349, 0.034941),
    (60000000123375, "0.168", "0.024", 2185096, 0.0377, 0.037704),
    (300000000188911, "0.161", "0.018", 4886025, 0.0369, 0.036946),
]


def _row_numerator(X: int, ts: str, y2: str) -> tuple[int, arb, arb]:
    with ef.workprec(128):
        Xa, t0, y0 = arb(X), arb(ts), arb(y2).sqrt()
        N0 = ef.N_of(Xa, t0)
        sp = acb(1 + y0, -Xa) / 2
        sm = acb(1 - y0, Xa) / 2
        sigma = (sp + (t0 / 2) * ef.alpha(sp)).real
        g = abs((ef.log_Mt(sm, t0) - ef.log_Mt(sp, t0)).exp())
        k = abs((t0 / 2) * (ef.alpha(sm) - ef.alpha(acb(1 + y0, Xa) / 2)))
    r = ef.euler2_lower_bound(N0, ts, y0, sigma, g, k)
    with ef.workprec(128):
        numer = r["LB_beta"] - g * r["UB_alpha"] - (1 + r["r"]) * r["Z"]
    return N0, numer, r["joint"]


@pytest.mark.slow
@pytest.mark.parametrize("X,ts,y2,N0,printed,six", ROWS)
def test_table1_column_is_the_trib2_numerator(X: int, ts: str, y2: str, N0: int, printed: float, six: float) -> None:
    """The printed column is reproduced by the bound on |E_2 f|, not by the bound on |f|."""
    n0, numer, joint = _row_numerator(X, ts, y2)
    assert n0 == N0
    assert round(float(numer.mid()), 6) == six
    assert round(float(numer.mid()), 4) == printed
    assert abs(float(numer.mid()) - printed) < 5e-5
    assert round(float(joint.mid()), 4) != printed
    assert float(joint.upper()) < printed - 0.004


def test_unmollified_triangle_bound_tail_is_a_majorant() -> None:
    """The erfi tail over-counts the exact sum, so the bound is below the exact one."""
    exact = ef.unmollified_triangle_bound(20000, "0.186", "0.16733", M=20000)["bound"]
    tail = ef.unmollified_triangle_bound(20000, "0.186", "0.16733", M=500)["bound"]
    with ef.workprec(128):
        assert tail < exact
        assert exact - tail < arb("0.01")


def test_row2_N1_estimate_for_the_projection() -> None:
    """Where the unmollified triangle bound reaches 0.045 (the paper's claim (c) margin)."""
    b5 = ef.unmollified_triangle_bound(5 * 10**6, "0.186", "0.16733")["bound"]
    b10 = ef.unmollified_triangle_bound(10**7, "0.186", "0.16733")["bound"]
    with ef.workprec(128):
        assert b5 < arb("0.045") < b10
    assert round(float(b5.mid()), 4) == 0.0376
    assert round(float(b10.mid()), 3) == 0.169


# --------------------------------------------------------------------------- #
#  Euler 5 (Section 8.5): consistency, and the recorded paper comparison
# --------------------------------------------------------------------------- #

def test_euler_F_truncations_are_ordered_small_case() -> None:
    worst = ef.euler_mollified_F(1000, 1100, "0.2", "0.2", truncation="worst")["F"]
    plus = ef.euler_mollified_F(1000, 1100, "0.2", "0.2", truncation="N_plus")["F"]
    minus = ef.euler_mollified_F(1000, 1100, "0.2", "0.2", truncation="N_minus")["F"]
    with ef.workprec(128):
        assert worst < plus and worst < minus


def test_euler5_paper_comparison_record() -> None:
    d = json.loads((HERE / "euler5_paper.json").read_text())
    vals = {(r["constants"], len(r["primes"]), r["truncation"]): float(arb(r["F"]["str"]).mid()) for r in d["runs"]}
    assert d["interval"] == [69098, 80000]
    assert abs(vals[("paper", 3, "worst")] - 0.0178) < 1e-4
    assert abs(vals[("paper", 3, "N_plus")] - 0.0202) < 1e-4
    assert abs(vals[("paper", 3, "N_minus")] - 0.0576) < 1e-4
    assert abs(vals[("paper", 3, "none")] - (-2.776)) < 1e-3
    assert abs(vals[("paper", 4, "N_plus")] - 0.0639) < 1e-4
    assert abs(vals[("paper", 4, "N_minus")] - 0.1018) < 1e-4
    assert abs(vals[("derived", 3, "worst")] - 0.0308) < 1e-4
    # none of the variants prints as the paper's 0.0263
    assert all(round(v, 4) != 0.0263 for v in vals.values())
    # every truncated variant clears the paper's threshold 2.15e-3 for this interval
    assert min(v for k, v in vals.items() if k[2] != "none") > 2.15e-3


def test_euler5_row2_unit_record() -> None:
    d = json.loads((HERE / "euler5_row2_unit.json").read_text())
    assert d["interval"] == [630783, 640783]
    assert d["terms"] == 30 * 640783 - 1
    assert round(float(arb(d["F"]["str"]).mid()), 4) == 0.4686


@pytest.mark.slow
def test_euler5_paper_comparison_recomputed() -> None:
    with ef.workprec(128):
        c = arb("1.03")
        sig = arb("0.599") + arb("0.1") * arb(69098).log()
    r = ef.euler_mollified_F(69098, 80000, "0.2", "0.2", c_gamma=c, sigma=sig, truncation="worst")
    assert abs(float(r["F"].mid()) - 0.0178) < 1e-4


# --------------------------------------------------------------------------- #
#  The barrier rectangle routine
# --------------------------------------------------------------------------- #

def test_barrier_rectangle_moderate_height() -> None:
    r = ef.barrier_rectangle("100000000", "100000001", "0.2", "1", "0.1", initial_per_edge=16)
    assert r["n_failed"] == 0
    assert r["winding"] == 0
    assert r["min_margin"] > 0


def test_lesion_barrier_refuses_a_zero_on_the_boundary() -> None:
    """Bottom edge y = 0 through the zero x = 2 t_z of H_0, t_z = 50000000.4837200978...
    (a sign change of mpmath's siegelz, located here so the test does not trust a
    recorded number): the mesh cannot establish |f| > E + D h/2 near it, so no
    winding number is reported.  The control is the same x-range moved up to
    y in [0.2, 0.7], which passes, so the refusal is caused by the zero."""
    from mpmath import mp

    with mp.workdps(30):
        tz = mp.findroot(mp.siegelz, (mp.mpf("50000000.47"), mp.mpf("50000000.49")), solver="anderson")
        xz = 2 * tz
    assert 100000000.7 < float(xz) < 100000001.2
    r = ef.barrier_rectangle("100000000.7", "100000001.2", "0", "0.5", "0", initial_per_edge=16, max_depth=12)
    assert r["n_failed"] > 0
    assert r["winding"] is None
    c = ef.barrier_rectangle("100000000.7", "100000001.2", "0.2", "0.7", "0", initial_per_edge=16, max_depth=12)
    assert c["n_failed"] == 0
    assert c["winding"] == 0


# --------------------------------------------------------------------------- #
#  Row 2: the committed record and its recomputation
# --------------------------------------------------------------------------- #

def _row2() -> dict:
    return json.loads((HERE / "row2_check.json").read_text())


def test_row2_record_states_what_evaluator_md_says() -> None:
    d = _row2()
    assert d["printed"]["lower_bound_column"] == "0.0376"
    e = {sec["y0_label"]: sec for sec in d["euler2"]}
    for lab in ("0.16733", "sqrt(0.028)"):
        sec = e[lab]
        assert sec["N0"] == N0_ROW2 and sec["X_in_N0_interval"]
        pt = sec["variants"]["point"]
        numer = float(arb(pt["trib2_numerator_bounds_abs_E2_f"]["str"]).mid())
        joint = float(arb(pt["bound_abs_f_joint"]["str"]).mid())
        assert round(numer, 4) == 0.0376
        assert round(joint, 4) == 0.0292
        assert round(numer, 6) == {"0.16733": 0.037617, "sqrt(0.028)": 0.037627}[lab]
        assert round(joint, 6) == {"0.16733": 0.029195, "sqrt(0.028)": 0.029202}[lab]
        uni = sec["variants"]["uniform"]
        assert round(float(arb(uni["trib2_numerator_bounds_abs_E2_f"]["str"]).mid()), 4) == 0.0366
        assert round(float(arb(uni["bound_abs_f_joint"]["str"]).mid()), 4) == 0.0284
    pm = e["0.16733"]["variants"]["polymath_moll2_analytic"]
    assert round(float(arb(pm["value_bounds_abs_E2_f_approximately"]["str"]).mid()), 6) == 0.037603
    p = d["point"]
    assert p["N"] == N0_ROW2
    assert float(arb(p["abs_E2_times_f"]["str"]).lower()) > 0.0376
    assert round(float(arb(p["f"]["abs"]["str"]).mid()), 3) == 1.684
    assert round(float(arb(p["abs_E2_times_f"]["str"]).mid()), 3) == 1.206
    assert f"{float(arb(p['e_A']['str']).mid()):.2e}" == "1.06e-13"
    assert f"{float(arb(p['e_B']['str']).mid()):.2e}" == "7.48e-13"
    assert f"{float(arb(p['e_C0']['str']).mid()):.2e}" == "1.03e-07"
    rt = d["rectangle_t0"]
    assert rt["winding"] == 0 and rt["n_failed"] == 0
    assert rt["n_evaluations"] == 68
    assert round(float(rt["min_abs_f_lower"]["lower"]), 4) == 1.4458
    assert round(float(rt["Dz_bottom"]["upper"]), 4) == 8.4893
    assert f"{float(rt['E_upper']['upper']):.3e}" == "1.031e-07"
    rz = d["rectangle_t_zero"]
    assert rz["winding"] == 0 and rz["n_failed"] == 0
    assert rz["n_evaluations"] == 580
    assert round(float(rz["min_abs_f_lower"]["lower"]), 5) == 4.68315
    assert round(float(rz["Dz_bottom"]["upper"]), 2) == 10085.47
    assert round(float(rz["Dt_bottom"]["upper"]), 2) == 54745.85
    assert f"{float(rz['E_upper']['upper']):.3e}" == "4.119e-04"


@pytest.mark.slow
def test_row2_point_variant_recomputed() -> None:
    n0, numer, joint = _row_numerator(X_ROW2, "0.186", "0.028")
    d = _row2()
    sec = {s["y0_label"]: s for s in d["euler2"]}["sqrt(0.028)"]
    stored = arb(sec["variants"]["point"]["trib2_numerator_bounds_abs_E2_f"]["str"])
    assert n0 == N0_ROW2
    assert numer.overlaps(stored)


@pytest.mark.slow
def test_precision_response_at_row2_height() -> None:
    """A real quantity does not move when precision is added; its ball shrinks."""
    a = ef.point(str(X_ROW2), "0.16733", "0.186", prec=128, error_mode="envelope")
    b = ef.point(str(X_ROW2), "0.16733", "0.186", prec=192, error_mode="envelope")
    assert a.f.overlaps(b.f)
    assert b.f.real.rad() < a.f.real.rad()


def test_polymath_row2_barrier_log_as_recorded() -> None:
    """The project's own row-2 barrier log (read as data): the hash and first and
    last lines recorded in row2_check.json; and, when the downloaded file is
    present, its rectangle count and total mesh points recounted from the bytes."""
    import hashlib

    ref = _row2()["polymath_row2_barrier_log"]
    assert ref["available"]
    assert ref["sha256"] == "3406175695291ea000e37c9e6466c4d34975a58a76472ba6bde204ddb34022c7"
    assert ref["n_rectangles"] == 435
    assert ref["first"].split(":")[1].split(",")[1:3] == [" 54747", " 10087"]
    path = Path(ref["path"])
    if not path.exists():
        pytest.skip("downloaded Polymath log not present on this machine")
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == ref["sha256"]
    rects = [ln for ln in raw.decode("utf-8", "replace").splitlines() if ln.startswith("Rectangle(")]
    assert len(rects) == 435
    assert sum(int(ln.split(",")[-1]) for ln in rects) == 7368456
    first = [v.strip() for v in rects[0].split(":", 1)[1].split(",")]
    last = [v.strip() for v in rects[-1].split(":", 1)[1].split(",")]
    assert first[0] == "0" and first[3] == "0.0000000000"
    assert first[4].startswith("4.6831460650") and first[5] == "40344"
    assert last[0].startswith("0.17557")
    assert all(ln.split(",")[3].strip() == "0.0000000000" for ln in rects)
    # our t = 0 rectangle against theirs: derivative bounds and the mesh minimum of |f|
    rz = _row2()["rectangle_t_zero"]
    assert float(rz["Dz_bottom"]["upper"]) < int(first[2])
    assert float(rz["Dt_bottom"]["upper"]) < int(first[1])
    assert abs(float(rz["min_abs_f_lower"]["lower"]) - float(first[4])) < 1e-5


def test_the_series_cap_that_caused_the_first_defect() -> None:
    """python-flint truncates series at ctx.cap (10 by default) without warning."""
    from flint import arb_series

    old = ctx.cap
    try:
        ctx.cap = 10
        assert len(arb_series([0, arb("0.1")], prec=16).exp().coeffs()) == 10
    finally:
        ctx.cap = old


def test_arxiv_source_hash_when_present() -> None:
    import hashlib

    src = Path("/home/thomas/.cache/zeta-lab/dbn/evaluator-arxiv-1904.12438v2/source.bin")
    if not src.exists():
        pytest.skip("downloaded arXiv source not present on this machine")
    assert hashlib.sha256(src.read_bytes()).hexdigest() == (
        "1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863"
    )
