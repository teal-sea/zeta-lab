"""Tests for the Arb evaluator of Polymath 15's effective approximation.

Run:  .venv/bin/python -m pytest -q -n0 hunts/dbn_pt_height/evaluator/test_effective.py
(``-m "not slow"`` skips the ones that sum over n <= 630783 or rebuild oracles.)

Every number EVALUATOR.md states is asserted here, from a recomputation or from
the committed data files the scripts in this directory wrote.

The barrier pipeline is checked by re-deriving its decisions independently
(``_audit_barrier``), not by reading its own output back, and every check that
guards soundness has a lesion test: a private copy of effective.py with one
planted source edit (``_faulty``) must turn that check red.
"""

from __future__ import annotations

import json
import math
import os
import random
import sys
import types
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
DBN_CACHE = Path(os.environ.get("DBN_CACHE_ROOT", os.path.expanduser("~/.cache/zeta-lab/dbn")))
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


_FAULT_COUNTER = [0]


def _faulty(old: str, new: str) -> types.ModuleType:
    """A private copy of effective.py with exactly one source edit (a planted fault)."""
    src = (HERE / "effective.py").read_text()
    assert src.count(old) == 1, f"the fault anchor must occur exactly once: {old!r}"
    _FAULT_COUNTER[0] += 1
    name = f"effective_planted_fault_{_FAULT_COUNTER[0]}"
    mod = types.ModuleType(name)
    mod.__file__ = str(HERE / f"{name}.py")
    sys.modules[name] = mod  # dataclasses look the module up while the class is built
    exec(compile(src.replace(old, new), mod.__file__, "exec"), mod.__dict__)
    return mod


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
    with pytest.raises(ValueError):
        ef.barrier_rectangle("150", "151", "0.2", "1", "0.1")
    with pytest.raises(ValueError):
        ef.barrier_rectangle("1000", "1001", "0.2", "1.2", "0.1")


@pytest.mark.parametrize(
    "x,y,t",
    [("300", "0.5", "0.2"), ("2000.3", "1", "0"), ("100000.37", "0.2", "0.4"),
     ("211.7", "0", "0.5"), ("100000000.73", "0.6", "0.05")],
)
def test_formulas_agree_with_an_mpmath_rederivation(x: str, y: str, t: str) -> None:
    """effective.point against oracles.formula_mpmath, written from the TeX in a
    different algebraic form (the (ft-def) second sum with conj(s_*) + kappa, and
    Corollary 6.4's E_A, E_B).  This sees slips too small for any containment
    test: C_0 conjugated or kappa dropped change f or C/B far below e_C."""
    import oracles
    from mpmath import mp

    R = oracles.formula_mpmath(x, y, t, dps=45)
    P = ef.point(x, y, t)
    assert R["N"] == P.N
    with mp.workdps(50):
        def c(z):
            return acb(arb(mp.nstr(z.real, 45)), arb(mp.nstr(z.imag, 45)))

        def r(v):
            return arb(mp.nstr(v, 45))

        with ef.workprec(160):
            for key, v in (("f", P.f), ("CB", P.CB)):
                assert abs(v - c(R[key])) < arb("1e-26") * abs(v), key
            for key, v in (("e_A", P.e_A), ("e_B", P.e_B), ("e_C", P.e_C), ("e_C0", P.e_C0)):
                assert abs(v - r(R[key])) < arb("1e-26") * v, key


@pytest.mark.parametrize(
    "old,new",
    [("C0p = C0(p)\n", "C0p = C0(p).conjugate()\n"),
     ("ex_A = qL - s_2star * L", "ex_A = qL - (s_star.conjugate() - y) * L")],
    ids=["C0_conjugated", "kappa_dropped"],
)
def test_lesion_rederivation_sees_subresolution_slips(old: str, new: str) -> None:
    import oracles
    from mpmath import mp

    bad = _faulty(old, new)
    x, y, t = "300", "0.5", "0.2"
    R = oracles.formula_mpmath(x, y, t, dps=45)
    P = bad.point(x, y, t)
    with mp.workdps(50), ef.workprec(160):
        ok = all(
            abs(v - acb(arb(mp.nstr(R[k].real, 45)), arb(mp.nstr(R[k].imag, 45)))) < arb("1e-26") * abs(v)
            for k, v in (("f", P.f), ("CB", P.CB))
        )
    assert not ok


# --------------------------------------------------------------------------- #
#  Theorem 1.3's closed-form bounds, and where Proposition 6.6(vi) fails
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("x", ["200", "400", "10000", "1000000"])
@pytest.mark.parametrize("y", ["0", "0.5", "1"])
@pytest.mark.parametrize("t", ["0.05", "0.5"])
def test_closed_form_bounds_dominate(x: str, y: str, t: str) -> None:
    """At these x the fractional part of a is away from 0 (at x = 200 it is 0.99),
    which is where Proposition 6.6(vi) holds; see the next test for where it fails."""
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


def _just_above_jump(N: int, t: str) -> str:
    with ef.workprec(160):
        xN = ef.x_of_N(N, arb(t)) + arb("1e-9")
        return xN.mid().str(40, radius=False)


@pytest.mark.parametrize(
    "N,t,y,lo,hi",
    [(4, "0.05", "0", 1.13, 1.15), (4, "0.5", "1", 1.13, 1.15), (5, "0.05", "0", 1.09, 1.11),
     (6, "0.5", "0", 1.06, 1.09), (10, "0.05", "1", 1.02, 1.04)],
)
def test_prop66_vi_fails_just_above_small_jumps(N: int, t: str, y: str, lo: float, hi: float) -> None:
    """A source erratum, measured: just above x_N with small N, the exact e_C of
    (ecc-def) exceeds Proposition 6.6(vi) as printed by the factor in [lo, hi].
    Theorem 1.3's (ec-bound) for e_{C,0} still holds at these points (measured, not
    proved).  Nothing in effective.py uses (vi)."""
    P = ef.point(_just_above_jump(N, t), y, t)
    assert P.N == N
    b = ef.theorem_bounds(P)
    with ef.workprec(P.prec):
        ratio = P.e_C / b["eC_upper_prop"]
        assert lo < float(ratio.mid()) < hi
        assert P.e_C0 < b["eC0_upper_thm"]


def test_prop66_vi_holds_again_just_above_larger_jumps() -> None:
    for N in (20, 50):
        for t, y in (("0.05", "0"), ("0.5", "1")):
            P = ef.point(_just_above_jump(N, t), y, t)
            b = ef.theorem_bounds(P)
            with ef.workprec(P.prec):
                assert P.e_C < b["eC_upper_prop"]


def test_line_1107_needs_a_large_a() -> None:
    """The step at line 1107: with the paper's own factor exp(3.49/(T-4)) <= 1.037
    (T >= 100), 0.397 9^sigma 1.037/(a - 0.865) <= 1.24 3^{+-y}/(a - 0.125) holds
    only for a >= 187 (sigma = (1 +- y)/2, so 9^sigma = 3 3^{+-y}); the crossing is
    at a = 186.14."""
    with ef.workprec(128):
        def lhs_over_rhs(a: arb) -> arb:
            return (arb("0.397") * 3 * arb("1.037") / (a - arb("0.865"))) / (arb("1.24") / (a - arb("0.125")))

        assert lhs_over_rhs(arb(4)) > 1
        assert lhs_over_rhs(arb(186)) > 1
        assert lhs_over_rhs(arb(187)) < 1


# --------------------------------------------------------------------------- #
#  Milestone 1: containment of two independent routes to H_t
# --------------------------------------------------------------------------- #

def _containment_table(mod: types.ModuleType = ef) -> list[dict]:
    rows: dict[tuple[str, str, str], dict] = {}
    for route in ("phi", "hk"):
        for r in _load_jsonl(f"agreement_{route}.jsonl"):
            rows.setdefault((r["x"], r["y"], r["t"]), {})[route] = r
    out = []
    for (x, y, t), routes in sorted(rows.items(), key=lambda kv: tuple(float(v) for v in kv[0])):
        P = mod.point(x, y, t)
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
    # how loose the bound is on this grid: measured error over radius, worst case 0.031
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
#  Milestone 1b: containment at large x, where e_C << |C_t/B_t|
# --------------------------------------------------------------------------- #

C_FAULTS = {
    "y_phase_conjugated": ("(-i * pi * y / 8).exp()", "(i * pi * y / 8).exp()"),
    "e^{i pi/8}_dropped": ("* C0p * (i * pi / 8).exp()", "* C0p"),
    "exp(t pi^2/64)_dropped": ("* (t * pi * pi / 64).exp() * Wtilde.real", "* Wtilde.real"),
    "C_sign_flipped": ("sign = 1 if N % 2 == 0 else -1", "sign = -1 if N % 2 == 0 else 1"),
}


def _large_x_table(mod: types.ModuleType = ef) -> list[dict]:
    out = []
    for r in _load_jsonl("large_x_oracles.jsonl"):
        P = mod.point(r["x"], r["y"], r["t"])
        with ef.workprec(P.prec):
            Bt = P.Bt()
            H_over_B = acb(arb(r["re"]), arb(r["im"])) / Bt
            d = abs(H_over_B - (P.f - P.CB))
            rad = P.e_A + P.e_B + P.e_C
            out.append({
                "x": r["x"], "y": r["y"], "t": r["t"],
                "ratio": float((d / rad).upper()),
                "contained": bool(d < rad),
                "C_over_eC": float((abs(P.CB) / P.e_C).lower()),
                "routes": float(r["rel_diff_routes"]),
            })
    return out


def test_milestone1b_large_x_values_are_inside_the_ABC_enclosure() -> None:
    tab = _large_x_table()
    assert len(tab) == 12
    assert sum(1 for r in tab if r["t"] == "0") == 8
    assert min(float(r["x"]) for r in tab) > 1e5 - 1 and max(float(r["x"]) for r in tab) > 1e8
    # the two routes agree at every point (xi by mpmath and PARI at t = 0; 80 and 120
    # Gauss-Hermite nodes at t > 0), far below the enclosure radii
    assert max(r["routes"] for r in tab) < 1e-17
    assert all(r["contained"] for r in tab)
    # here the correction is large against its error, so the test is sharp for C_t
    assert 17 < min(r["C_over_eC"] for r in tab) < 18
    worst = max(r["ratio"] for r in tab)
    assert 0.25 < worst < 0.30


@pytest.mark.parametrize("fault", sorted(C_FAULTS))
def test_lesion_C_faults_are_caught_at_large_x_but_not_at_small_x(fault: str) -> None:
    """Each planted C_t fault leaves the field outside the enclosure at some large-x
    point.  The first three pass the whole x <= 2000 grid unnoticed, which is why
    milestone 1b exists."""
    bad = _faulty(*C_FAULTS[fault])
    assert not all(r["contained"] for r in _large_x_table(bad))
    if fault != "C_sign_flipped":
        assert all(r["contained"] for r in _containment_table(bad) if r["route"] != "phi_vs_hk")


def test_milestone1b_live_point() -> None:
    """One t = 0 value recomputed now from mpmath's xi, not read from the file."""
    sys.path.insert(0, str(HERE))
    import large_x_oracles as lxo
    from mpmath import mp

    H = lxo.H0_mpmath("1000000.37", "1")
    P = ef.point("1000000.37", "1", "0")
    with mp.workdps(30), ef.workprec(P.prec):
        Hb = acb(arb(mp.nstr(H.real, 25)), arb(mp.nstr(H.imag, 25)))
        assert P.Ht_ABC().contains(Hb)


# --------------------------------------------------------------------------- #
#  Taylor multi-evaluation and its truncation tail
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
        sB, sA, g = ev.evaluate_parts(x, y)
        assert sB.overlaps(P.sum_B) and sA.overlaps(P.sum_A) and g.overlaps(P.gamma)


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
    sB, sA, _ = ev.evaluate_parts(str(X), "0.2")
    assert sB.overlaps(P.sum_B) and sA.overlaps(P.sum_A)


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


def test_taylor_tail_bound_is_a_sharp_majorant() -> None:
    """For one exponential (A = 1) the omitted part sum_{k>=K} rho^k/k! is known
    exactly; the bound must lie between it and it / (1 - rho/(K+1))."""
    with ef.workprec(256):
        for K in (2, 4, 8, 16):
            fact = arb(1)
            for k in range(1, K + 1):
                fact *= k
            for rho_s in ("0.05", "0.5", "2"):
                rho = arb(rho_s)
                head = arb(0)
                term = arb(1)
                for k in range(K):
                    head += term
                    term = term * rho / (k + 1)
                exact = rho.exp() - head
                bound = ef._taylor_tail_bound(arb(1), rho, K, fact)
                assert exact < bound
                assert bound < exact / (1 - rho / (K + 1)) * (1 + arb("1e-40"))


def _two_term_tail_violations(mod: types.ModuleType, K: int = 4) -> tuple[list[str], list[float]]:
    """A multi-evaluation whose truncation tail is nearly attained.

    N = 2 and one block {1, 2} with ell = -+log(2)/2 = +-ell_max; at
    x_c = 20 pi / log 2 the two terms are in phase ((x_c/2) log 2 = 10 pi), so for
    even K the omitted part is (c_1 + c_2) (delta log(2)/2)^K / K! (1 + O(rho)),
    within a few per cent of the charged bound.  An under-charged tail then
    leaves the direct sum outside the ball.  Returns the violations and the
    ratios (actual error) / (bound computed here from the formula)."""
    t = "0.1"
    with ef.workprec(128):
        x_c = 20 * arb.pi() / arb(2).log()
        assert ef.N_of(x_c, arb(t)) == 2
    ev = mod.FixedTimeMultiEval(x_c, "0.5", t, 2, n_head=1, log_width=2.0, K=K)
    assert [(b.n_lo, b.n_hi) for b in ev.blocks] == [(1, 3)]
    viol: list[str] = []
    ratios: list[float] = []
    with ef.workprec(128):
        tt = arb(t)
        fact = arb(math.factorial(K))
        L2 = arb(2).log()
        sp0 = acb(1 + arb("0.5"), -x_c) / 2
        sm0 = acb(1 - arb("0.5"), x_c) / 2
        sB0 = sp0 + (tt / 2) * ef.alpha(sp0)
        sA0 = sm0 + (tt / 2) * ef.alpha(sm0)
        for dx, dy in (("0.5", "0.3"), ("-0.5", "-0.3"), ("0.3", "-0.4")):
            x = x_c + arb(dx)
            y = arb("0.5") + arb(dy)
            sB, sA, _ = ev.evaluate_parts(x, y)
            sp = acb(1 + y, -x) / 2
            sm = acb(1 - y, x) / 2
            s_star = sp + (tt / 2) * ef.alpha(sp)
            s_2star = sm + (tt / 2) * ef.alpha(sm)
            for label, ball, s, s0 in (("B", sB, s_star, sB0), ("A", sA, s_2star, sA0)):
                direct = 1 + ((tt / 4) * L2 * L2 - s * L2).exp()
                if not ball.contains(direct):
                    viol.append(f"{label} sum at dx={dx}: ball misses the direct value")
                c2 = abs(((tt / 4) * L2 * L2 - s0 * L2).exp())
                rho = abs(s - s0) * L2 / 2
                pref = abs((-(s - s0) * L2 / 2).exp())
                bound = pref * (1 + c2) * rho ** K / (fact * (1 - rho / (K + 1)))
                ratios.append(float((abs(direct - ball.mid()) / bound).mid()))
    return viol, ratios


def test_multieval_tail_is_charged_where_it_sets_the_width() -> None:
    viol, ratios = _two_term_tail_violations(ef)
    assert viol == []
    # the regime is tight: the actual truncation error uses most of the charged tail
    assert min(ratios) > 0.85 and max(ratios) <= 1.0


@pytest.mark.parametrize(
    "old,new",
    [("return A * _pow_ui_upper(rho, K) / (fact_K * (1 - rho / (K + 1)))",
      "return A * _pow_ui_upper(rho, K) / (fact_K * (1 - rho / (K + 1))) / 2"),
     ("tailB = _taylor_tail_bound(b.absB, rhoB, K, self._fact_K)",
      "tailB = _taylor_tail_bound(b.absB, rhoB, K, self._fact_K) / 1000")],
    ids=["tail_halved", "B_tail_over_1000"],
)
def test_lesion_undercharged_tail_is_caught(old: str, new: str) -> None:
    viol, _ = _two_term_tail_violations(_faulty(old, new))
    assert viol


# --------------------------------------------------------------------------- #
#  Derivative bounds: each part of the Lemma's majorant against exact derivatives
# --------------------------------------------------------------------------- #

def _termwise_derivative_sums(x, y, t, N: int, n_lo: int = 1, n_hi: int | None = None) -> dict[str, arb]:
    """Sums over n_lo <= n <= n_hi of the exact |d/dz| and |d/dt| of each summand
    of f_t = sum b_n n^{-s_*} + gamma sum b_n n^{-s_**}, split into the first sum
    ("zb", "tb") and the second ("zg", "tg").  From the Lemma's proof (lines
    1464-1505): d s_*/dx = -i/2 - (it/4) alpha'(s_+), d s_**/dx = i/2 + (it/4) alpha'(s_-),
    d log gamma/dx = (it/4)(alpha alpha'(s_-) + alpha alpha'(s_+)) + (i/2)(alpha(s_-) + alpha(s_+)),
    d s_*/dt = alpha(s_+)/2, d s_**/dt = alpha(s_-)/2,
    d log gamma/dt = (alpha(s_-)^2 - alpha(s_+)^2)/4, d log b_n/dt = log^2(n)/4, and
    |df/dz| = |df/dx| for holomorphic f.  The Lemma's majorant dominates every
    summand's derivative, so each part must dominate these sums pointwise."""
    n_hi = N if n_hi is None else n_hi
    with ef.workprec(128):
        x, y, t = ef.to_arb(x), ef.to_arb(y), ef.to_arb(t)
        i = acb(0, 1)
        sp = acb(1 + y, -x) / 2
        sm = acb(1 - y, x) / 2
        ap, am = ef.alpha(sp), ef.alpha(sm)
        app, amp = ef.alpha_prime(sp), ef.alpha_prime(sm)
        rs_B = (sp + (t / 2) * ap).real
        rs_A = (sm + (t / 2) * am).real
        g = abs((ef.log_Mt(sm, t) - ef.log_Mt(sp, t)).exp())
        dsB = abs(-i / 2 - (i * t / 4) * app)
        dsA = i / 2 + (i * t / 4) * amp
        dlg_x = (i * t / 4) * (am * amp + ap * app) + (i / 2) * (am + ap)
        dlg_t = (am * am - ap * ap) / 4
        zb = arb(0)
        zg = arb(0)
        tb = arb(0)
        tg = arb(0)
        for n in range(n_lo, n_hi + 1):
            L = arb(n).log()
            q = (t / 4) * L * L
            mB = (q - rs_B * L).exp()
            mA = (q - rs_A * L).exp()
            zb += mB * L * dsB
            zg += g * mA * abs(dlg_x - L * dsA)
            tb += mB * abs(L * L / 4 - ap * L / 2)
            tg += g * mA * abs(L * L / 4 - am * L / 2 + dlg_t)
    return {"zb": zb, "zg": zg, "tb": tb, "tg": tg}


PARTS = (("zb", "line_z_beta"), ("zg", "line_z_gamma"), ("tb", "line_t_beta"), ("tg", "line_t_gamma"))
DER_CASES = [
    ("100000000", "100000001", ["0.2", "0.6", "1"], "0.1"),
    ("1000000", "1000001", ["0", "0.5", "1"], "0"),
    ("1000000", "1000001", ["0.3", "1"], "0.4"),
]


def _derivative_violations(mod: types.ModuleType, case, windows=None) -> tuple[list[str], dict[str, float]]:
    x_lo, x_hi, ys, t = case
    with ef.workprec(128):
        N = ef.N_of(arb(x_lo), arb(t))
        xs = [arb(x_lo), (arb(x_lo) + arb(x_hi)) / 2, arb(x_hi)]
    windows = windows or [(1, 25), (N - 24, N), (1, N)]
    viol: list[str] = []
    worst: dict[str, float] = {}
    for (n_lo, n_hi) in windows:
        db = mod.derivative_bounds(x_lo, x_hi, ys, t, n_range=(n_lo, n_hi))
        for j, y in enumerate(ys):
            for x in xs:
                ex = _termwise_derivative_sums(x, y, t, N, n_lo, n_hi)
                with ef.workprec(128):
                    for key, part in PARTS:
                        if ex[key] > db[part][j]:  # equality is attained at t = 0
                            viol.append(f"{part}[{j}] < exact at x={x}, n in [{n_lo}, {n_hi}]")
                        else:
                            r = float((db[part][j] / ex[key]).upper())
                            worst[f"{part} {n_lo}-{n_hi}"] = max(worst.get(f"{part} {n_lo}-{n_hi}", 0.0), r)
        # strips: interior points against the strip bound of the total
        for j in range(len(ys) - 1):
            with ef.workprec(128):
                ym = (arb(ys[j]) + arb(ys[j + 1])) / 2
            ex = _termwise_derivative_sums(xs[1], ym, t, N, n_lo, n_hi)
            with ef.workprec(128):
                if ex["zb"] + ex["zg"] > db["strip_z"][j] or ex["tb"] + ex["tg"] > db["strip_t"][j]:
                    viol.append(f"strip {j} < exact, n in [{n_lo}, {n_hi}]")
    return viol, worst


@pytest.mark.parametrize("case", DER_CASES, ids=["1e8_t0.1", "1e6_t0", "1e6_t0.4"])
def test_derivative_majorant_parts_dominate_exact_termwise_derivatives(case) -> None:
    viol, worst = _derivative_violations(ef, case)
    assert viol == []
    # how sharp each part is (largest majorant / exact ratio seen): the first-sum
    # z-part is sharp to O(t/x); no part is looser than a factor 3 in these windows
    if case[0] == "100000000":
        assert all(v < 1.0001 for k, v in worst.items() if k.startswith("line_z_beta"))
    assert max(worst.values()) < 3


DER_FAULTS = {
    "z_weight_first_sum_halved": ("wz_b = L / 2 + c1 * L", "wz_b = L / 4 + c1 * L"),
    "z_weight_second_sum_halved": ("cz_g = Cmax * (arb(1) / 2 + c1)", "cz_g = Cmax * (arb(1) / 4 + c1)"),
    "t_weight_first_sum_slip": ("wt_b = L * lx / 4 + pi * L / 8", "wt_b = L * lx / 8 + pi * L / 8"),
    # halving this term is invisible here: the gamma t-part has slack 1.56 to 1.60
    # over the exact sums in every window (measured 2026-10-26); a tenth is not
    "t_weight_gamma_term_over_10": ("ct_g = (pi / 2 + 8 / (x_lo - 6)) * (lX4hi + 8 / (x_lo - 6)) / 4",
                                    "ct_g = (pi / 2 + 8 / (x_lo - 6)) * (lX4hi + 8 / (x_lo - 6)) / 40"),
    "tau_from_the_upper_end": ("tau_lo = tau.lower()", "tau_lo = tau.upper() + arb('0.01')"),
}


@pytest.mark.parametrize("fault", sorted(DER_FAULTS))
def test_lesion_derivative_majorant_slips_are_caught(fault: str) -> None:
    viol, _ = _derivative_violations(_faulty(*DER_FAULTS[fault]), DER_CASES[0])
    assert viol


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
#  The barrier rectangle, audited from outside
# --------------------------------------------------------------------------- #

def _z_of(edge: int, fr: Fraction, xl: arb, xh: arb, yl: arb, yh: arb) -> tuple[arb, arb]:
    # corners exactly: yl + (yh - yl) * 1 is a ball straddling yh = 1, outside the region
    corners = [(xl, yl), (xh, yl), (xh, yh), (xl, yh)]
    if fr == 0:
        return corners[edge]
    if fr == 1:
        return corners[(edge + 1) % 4]
    f = arb(fr.numerator) / fr.denominator
    if edge == 0:
        return xl + (xh - xl) * f, yl
    if edge == 1:
        return xh, yl + (yh - yl) * f
    if edge == 2:
        return xh - (xh - xl) * f, yh
    return xl, yh - (yh - yl) * f


def _audit_barrier(r: dict, x_lo: str, x_hi: str, y_lo: str, y_hi: str, t: str, termwise_every: int = 6) -> list[str]:
    """Re-derive a barrier_rectangle decision without trusting its internals.

    Uses only the returned list of accepted segments (edge and dyadic end
    fractions) and E, D per segment, and checks: (1) the segments tile every edge;
    (2) |f| at both ends, from direct summation (``point``, not the
    multi-evaluator), exceeds E + D h / 2 with h recomputed here; (3) E dominates
    the exact e_A + e_B + e_{C,0} at every mesh point; (4) each D is at least the
    derivative majorant of every strip the segment touches and at least the exact
    termwise derivative sum at its ends (every ``termwise_every``-th segment);
    (5) the multi-evaluator's values overlap the direct ones; (6) the winding
    number recomputed from the direct values is the reported one.  Returns the
    violations; an empty list means the decision stands.
    """
    viol: list[str] = []
    segs = r["segments"]
    if r["n_failed"] or r["winding"] is None:
        return ["the barrier did not decide"]
    for edge in range(4):
        fr = sorted((Fraction(s["num0"], s["den"]), Fraction(s["num1"], s["den"])) for s in segs if s["edge"] == edge)
        if not fr or fr[0][0] != 0 or fr[-1][1] != 1 or any(a[1] != b[0] for a, b in zip(fr, fr[1:])):
            viol.append(f"edge {edge} is not tiled")
    n_strips = r["n_strips"]
    with ef.workprec(128):
        xl, xh, yl, yh, tt = (arb(v) for v in (x_lo, x_hi, y_lo, y_hi, t))
        ys = [yl + (yh - yl) * j / n_strips for j in range(n_strips + 1)]
    db = ef.derivative_bounds(xl, xh, ys, tt)
    E = r["E_upper"]
    pts: dict[tuple[int, Fraction], ef.Point] = {}
    for s in segs:
        for fr in (Fraction(s["num0"], s["den"]), Fraction(s["num1"], s["den"])):
            if (s["edge"], fr) not in pts:
                with ef.workprec(128):
                    x, y = _z_of(s["edge"], fr, xl, xh, yl, yh)
                pts[(s["edge"], fr)] = ef.point(x, y, tt, error_mode="exact")
    with ef.workprec(128):
        for key, P in pts.items():
            if P.N != r["N"]:
                viol.append(f"N differs at {key}")
            if not (P.e_A + P.e_B + P.e_C0 < E):
                viol.append(f"E does not dominate e_A + e_B + e_C0 at {key}")
        tot = arb(0)
        for k, s in enumerate(segs):
            f0, f1 = Fraction(s["num0"], s["den"]), Fraction(s["num1"], s["den"])
            P0, P1 = pts[(s["edge"], f0)], pts[(s["edge"], f1)]
            length = (xh - xl) if s["edge"] in (0, 2) else (yh - yl)
            h = length * arb((f1 - f0).numerator) / (f1 - f0).denominator
            D = s["D"].upper()
            need = E + D * h / 2
            if not (P0.f.abs_lower() > need and P1.f.abs_lower() > need):
                viol.append(f"segment {k}: |f| <= E + D h/2")
            if not (s["f0"].overlaps(P0.f) and s["f1"].overlaps(P1.f)):
                viol.append(f"segment {k}: multi-evaluator value misses the direct value")
            if s["edge"] == 0:
                strip_bound = db["line_z"][0].upper()
            elif s["edge"] == 2:
                strip_bound = db["line_z"][-1].upper()
            else:
                lo, hi = (f0, f1) if s["edge"] == 1 else (1 - f1, 1 - f0)
                touched = [j for j in range(n_strips) if Fraction(j, n_strips) < hi and Fraction(j + 1, n_strips) > lo]
                strip_bound = max((db["strip_z"][j].upper() for j in touched), key=float)
            if not (D >= strip_bound):
                viol.append(f"segment {k}: D below the strip majorant")
            if k % termwise_every == 0:
                for P in (P0, P1):
                    ex = _termwise_derivative_sums(P.x, P.y, tt, r["N"])
                    if not (ex["zb"] + ex["zg"] < D):
                        viol.append(f"segment {k}: D below the exact termwise derivative sum")
            tot += (P1.f / P0.f).arg()
        w = tot / (2 * arb.pi())
        if not (w.contains(arb(r["winding"])) and w.rad() < arb("0.25")):
            viol.append("the winding number from direct values differs")
    return viol


AUDIT_CASES = [
    # 4 points per edge to start, so the acceptance rule has to refine (40
    # evaluations); from 16 no refinement is needed and the rule's lesions
    # (no derivative margin, margin h/4) cannot show (measured 2026-10-26)
    ("1000000", "1000001", "0.2", "1", "0.1", 4),
    ("100000000.7", "100000001.2", "0.2", "0.7", "0", 16),
]


@pytest.mark.parametrize("case", AUDIT_CASES, ids=["1e6_t0.1", "1e8_t0"])
def test_barrier_rectangle_decision_survives_an_independent_audit(case) -> None:
    x_lo, x_hi, y_lo, y_hi, t, init = case
    r = ef.barrier_rectangle(x_lo, x_hi, y_lo, y_hi, t, initial_per_edge=init)
    assert r["n_failed"] == 0 and r["winding"] == 0
    assert _audit_barrier(r, x_lo, x_hi, y_lo, y_hi, t) == []
    # E is a sharp bound, not just a valid one: its largest exact value on the mesh
    # is within 5% of it (the excess is the sub-box dependency overestimate)
    with ef.workprec(128):
        P = ef.point(x_lo, y_lo, t, error_mode="exact")
        ratio = (P.e_A + P.e_B + P.e_C0) / r["E_upper"]
        assert 0.95 < float(ratio.mid()) < 1


BARRIER_FAULTS = {
    "rouche_margin_h_over_4": ("need = E + D * h / 2", "need = E + D * h / 4"),
    "no_derivative_margin": ("need = E + D * h / 2", "need = E"),
    "derivative_bound_over_10": ("D = D_of(e_, a, b, den)\n", "D = D_of(e_, a, b, den) / 10\n"),
    "eC0_dropped_from_E": ('"E": (eAB + eC0).upper()}', '"E": eAB.upper()}'),
}


@pytest.mark.parametrize("fault", sorted(BARRIER_FAULTS))
def test_lesion_barrier_faults_fail_the_audit(fault: str) -> None:
    bad = _faulty(*BARRIER_FAULTS[fault])
    x_lo, x_hi, y_lo, y_hi, t, init = AUDIT_CASES[0]
    r = bad.barrier_rectangle(x_lo, x_hi, y_lo, y_hi, t, initial_per_edge=init)
    assert _audit_barrier(r, x_lo, x_hi, y_lo, y_hi, t)


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


def test_rectangle_error_bound_where_prop66_vi_would_fail() -> None:
    """Just above x_4 (N = 4) Proposition 6.6(vi) is below the exact e_C; the
    rectangle bound uses the exact (ec-def) and stays above the exact
    e_A + e_B + e_{C,0} at every sampled point."""
    t = "0.05"
    x_lo = _just_above_jump(4, t)
    with ef.workprec(128):
        x_hi = (arb(x_lo) + arb("0.5")).mid().str(40, radius=False)
    ys = ["0", "0.25", "0.5", "0.75", "1"]
    db = ef.derivative_bounds(x_lo, x_hi, ys, t)
    with ef.workprec(128):
        eb = ef._rectangle_error_bound(arb(x_lo), arb(x_hi), arb("0"), arb("1"), arb(t), 4, db)
        for x in (x_lo, x_hi):
            for y in ("0", "0.37", "1"):
                P = ef.point(x, y, t)
                assert P.N == 4
                assert P.e_A + P.e_B + P.e_C0 < eb["E"]
                b = ef.theorem_bounds(P)
                if x == x_lo:
                    assert P.e_C > b["eC_upper_prop"]   # (vi) would not have been a bound here


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
#  Row 2: the committed record, its recomputation, and the project's own log
# --------------------------------------------------------------------------- #

def _row2() -> dict:
    return json.loads((HERE / "row2_check.json").read_text())


def test_row2_record_states_what_evaluator_md_says() -> None:
    d = _row2()
    assert d["printed"]["lower_bound_column"] == "0.0376"
    assert "Corollary 6.4" in d["grade"] and "5.3" not in d["grade"]
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
    assert f"{float(rt['E_upper']['upper']):.3e}" == "1.067e-07"
    rz = d["rectangle_t_zero"]
    assert rz["winding"] == 0 and rz["n_failed"] == 0
    assert rz["n_evaluations"] == 580
    assert round(float(rz["min_abs_f_lower"]["lower"]), 5) == 4.68315
    assert round(float(rz["Dz_bottom"]["upper"]), 2) == 10085.47
    assert round(float(rz["Dt_bottom"]["upper"]), 2) == 54745.85
    assert f"{float(rz['E_upper']['upper']):.3e}" == "4.264e-04"
    # E at the worst corner: the exact e_{C,0} recorded by the point evaluation (t = t0)
    # is below the rectangle's E, and within 4% of it
    eC0_corner = float(arb(p["e_C0"]["str"]).mid())
    assert 0.96 < eC0_corner / float(rt["E_upper"]["upper"]) < 1


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


def _project_first_line() -> list[str]:
    return [v.strip() for v in _row2()["polymath_row2_barrier_log"]["first"].split(":", 1)[1].split(",")]


def _check_against_project_ceilings(Dz: float, Dt: float, min_abs: float) -> None:
    """The project's C code (TloopthreadedV4.c, generate_ddzbound and
    generate_ddtbound, read as data) bounds the same Lemma sums by an integral
    plus the n = 1 term, which exceeds the exact sum by about half the first term
    (about 1 here), and the log prints the ceiling.  So our exact-sum majorant
    must lie a little below the printed ceiling: within 2.5 of it (2.5e-4
    relative), on both sides of nothing else.  An under- or over-estimate of
    more than that in either direction fails."""
    first = _project_first_line()
    ddt, ddz = int(first[1]), int(first[2])
    assert ddz - 2.5 < Dz < ddz
    assert ddt - 2.5 < Dt < ddt
    assert abs(min_abs - float(first[4])) < 1e-5


def test_polymath_row2_barrier_log_as_recorded() -> None:
    """The project's own row-2 barrier log (read as data): the hash and first and
    last lines recorded in row2_check.json; and, when the downloaded file is
    present, its rectangle count, total mesh points and wall time recounted from
    the bytes."""
    import hashlib

    ref = _row2()["polymath_row2_barrier_log"]
    assert ref["available"]
    assert ref["sha256"] == "3406175695291ea000e37c9e6466c4d34975a58a76472ba6bde204ddb34022c7"
    assert ref["n_rectangles"] == 435
    assert ref["first"].split(":")[1].split(",")[1:3] == [" 54747", " 10087"]
    # RUNS.md E3 quotes the log's wall time
    assert any(ln.split()[-1] == "133.169" for ln in ref["summary_lines"] if ln.startswith("cpu/wall"))
    # our t = 0 rectangle against theirs, two-sided: derivative bounds and the mesh minimum
    rz = _row2()["rectangle_t_zero"]
    _check_against_project_ceilings(float(rz["Dz_bottom"]["upper"]), float(rz["Dt_bottom"]["upper"]),
                                    float(rz["min_abs_f_lower"]["lower"]))
    assert ref["path"].startswith("<cache>/dbn/")  # recorded without the operator's home
    path = DBN_CACHE / ref["path"][len("<cache>/dbn/"):]
    if not path.exists():
        pytest.skip("source tie NOT checked: the downloaded Polymath log is absent on this machine (as in CI); "
                    "this comparison runs only where the cache exists (../RESULTS.md, section 6)")
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == ref["sha256"]
    text = raw.decode("utf-8", "replace")
    rects = [ln for ln in text.splitlines() if ln.startswith("Rectangle(")]
    assert len(rects) == 435
    assert sum(int(ln.split(",")[-1]) for ln in rects) == 7368456
    first = [v.strip() for v in rects[0].split(":", 1)[1].split(",")]
    last = [v.strip() for v in rects[-1].split(":", 1)[1].split(",")]
    assert first[0] == "0" and first[3] == "0.0000000000"
    assert first[4].startswith("4.6831460650") and first[5] == "40344"
    assert last[0].startswith("0.17557")
    assert all(ln.split(",")[3].strip() == "0.0000000000" for ln in rects)
    assert text.rstrip().splitlines()[-1].split()[-1] == "133.169"


@pytest.mark.slow
def test_row2_rectangle_t_zero_recomputed() -> None:
    """The t = 0 row-2 rectangle recomputed now (about two minutes), against the
    committed record, against the project's ceilings on both sides, and through
    the part of the audit that needs no O(N) direct evaluation per mesh point:
    tiling, the rule with h recomputed here, and D against the strip majorants."""
    r = ef.barrier_rectangle(str(X_ROW2), str(X_ROW2 + 1), "0.16733", "1", "0", initial_per_edge=64)
    rec = _row2()["rectangle_t_zero"]
    assert r["winding"] == 0 and r["n_failed"] == 0
    assert r["n_evaluations"] == rec["n_evaluations"]
    for key in ("Dz_bottom", "Dt_bottom", "E_upper", "min_abs_f_lower"):
        mid = (float(rec[key]["lower"]) + float(rec[key]["upper"])) / 2  # "str" keeps only ~9 digits
        assert abs(float(r[key].mid()) / mid - 1) < 1e-9, key
    _check_against_project_ceilings(float(r["Dz_bottom"].upper()), float(r["Dt_bottom"].upper()),
                                    float(r["min_abs_f_lower"].lower()))
    with ef.workprec(128):
        E = r["E_upper"]
        for edge in range(4):
            fr = sorted((Fraction(s["num0"], s["den"]), Fraction(s["num1"], s["den"])) for s in r["segments"] if s["edge"] == edge)
            assert fr[0][0] == 0 and fr[-1][1] == 1 and all(a[1] == b[0] for a, b in zip(fr, fr[1:]))
        for s in r["segments"]:
            length = arb(1) if s["edge"] in (0, 2) else arb(1) - arb("0.16733")
            h = length * s["num1"] / s["den"] - length * s["num0"] / s["den"]
            need = E + s["D"].upper() * h / 2
            assert s["f0"].abs_lower() > need and s["f1"].abs_lower() > need
            if s["edge"] in (0, 2):
                assert s["D"].upper() >= r["Dz_bottom" if s["edge"] == 0 else "Dz_top"].upper()


@pytest.mark.slow
@pytest.mark.parametrize("t,key", [("0", "rectangle_t_zero"), ("0.186", "rectangle_t0")])
def test_row2_E_and_D_dominate_exact_values_at_the_worst_corner(t: str, key: str) -> None:
    """At (X, y0), where e_{C,0} and the derivative sums are largest, the recorded
    rectangle E and D_z dominate the exact e_A + e_B + e_{C,0} (one O(N) point
    evaluation) and the exact termwise derivative sum (one O(N) sum)."""
    rec = _row2()[key]
    P = ef.point(str(X_ROW2), "0.16733", t, error_mode="exact")
    ex = _termwise_derivative_sums(str(X_ROW2), "0.16733", t, N0_ROW2)
    with ef.workprec(128):
        exact = P.e_A + P.e_B + P.e_C0
        assert exact < arb(rec["E_upper"]["upper"])
        assert 0.96 < float((exact / arb(rec["E_upper"]["upper"])).mid()) < 1
        assert ex["zb"] + ex["zg"] < arb(rec["Dz_bottom"]["upper"])


def test_runs_md_numbers() -> None:
    """Numbers RUNS.md states outside the data files: N0 at the largest X that
    Platt-Trudgian's verification height allows (X/2 <= 3e12)."""
    with ef.workprec(128):
        for t in ("0", "0.2"):
            assert ef.N_of(arb(6 * 10**12), arb(t)) == 690988


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

    src = DBN_CACHE / "evaluator-arxiv-1904.12438v2" / "source.bin"
    if not src.exists():
        pytest.skip("source tie NOT checked: the downloaded arXiv source is absent on this machine (as in CI); "
                    "its digest is checked only where the cache exists (../RESULTS.md, section 6)")
    assert hashlib.sha256(src.read_bytes()).hexdigest() == (
        "1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863"
    )
