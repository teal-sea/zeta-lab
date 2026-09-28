"""Tests of the exact (U-S) gate (mission kill-control 1)."""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import checker_gate as CG  # noqa: E402


@pytest.fixture(scope="module")
def gate():
    return CG.run_gate()


def test_dedekind_two_routes():
    """Ideals of norm n: divisor sum of chi_{-23} against the three reduced
    forms of discriminant -23 (h = 3, w = 2)."""
    assert CG.coeffs_dedekind_m23() == CG.coeffs_dedekind_m23_forms()


def test_rep_count_matches_lab_oracle():
    from zeta.epstein import epstein_representation_count as erc

    for n in range(1, CG.N_MAX + 1):
        assert CG.rep_count(n, (1, 1, 6)) == erc(n, (1, 1, 6))


@pytest.mark.parametrize("build", [CG.coeffs_zeta, CG.coeffs_dedekind_m23, CG.coeffs_epstein_116])
def test_lambda_two_exact_routes(build):
    """Recursion in the log-prime basis against the formal logarithm."""
    a = build()
    lam = CG.lambda_vectors(a)
    b = CG.formal_log(a)
    for n in range(2, CG.N_MAX + 1):
        expect = {p: b[n] * e for p, e in CG.factorize(n).items() if b[n] * e != 0}
        assert lam[n] == expect, n


def test_zeta_is_von_mangoldt():
    lam = CG.lambda_vectors(CG.coeffs_zeta())
    for n in range(2, CG.N_MAX + 1):
        pk = CG.prime_power(n)
        assert lam[n] == ({pk[0]: Fraction(1)} if pk else {}), n


def test_mission_expectations(gate):
    """Mission control 1: reject Epstein from n = 6 (composite atom) and
    n = 8 (s_3(2) = 6 > 2), W_a from n = 2 (s_1(2) = 2^{1/4} + 2^{-1/4}),
    accept zeta and Dedekind throughout n <= 200."""
    e = gate["epstein_(1,1,6)"]
    assert e["first_composite_atom"] == 6
    assert e["first_tower_violation"] == 8
    assert e["events"][0] == {"n": 6, "kind": "composite_atom", "coeffs": {"2": "2", "3": "2"}}
    assert e["events"][1] == {"n": 8, "kind": "tower", "p": 2, "k": 3, "s_k": "6"}
    assert e["n_composite_atoms"] == 31
    assert [x["n"] for x in e["events"] if x["kind"] == "tower"] == [8, 27]
    assert e["n_foreign_log"] == 0
    w = gate["W_a(a=1/4)"]
    assert w["first_rejection_n"] == 2 and w["events"][0]["p"] == 2 and w["events"][0]["k"] == 1
    assert abs(w["events"][0]["s_k_float"] - 2.0301035302564356) < 1e-15
    assert w["n_composite_atoms"] == 0
    # every prime power <= 200 violates for W_a: pi(200) = 46 primes, 60 prime powers
    assert w["n_tower_violations"] == sum(1 for n in range(2, 201) if CG.prime_power(n))
    for name in ("zeta", "dedekind_Q(sqrt-23)"):
        assert gate[name]["events"] == [], name


def test_dedekind_towers(gate):
    """Split 2, 3: s_k = 2; inert 5, 7: s_k = 0, 2, 0, ...; ramified 23: 1."""
    t = gate["dedekind_Q(sqrt-23)"]["towers"]
    assert set(t["2"]) == {"2"} and set(t["3"]) == {"2"}
    assert t["5"] == ["0", "2", "0"] and t["7"] == ["0", "2"] and t["23"] == ["1"]


def test_gate_as_function_of_c(gate):
    ev = {k: v["events"] for k, v in gate.items()}
    # window mode: atoms n < c only
    assert CG.accepts_window(ev["epstein_(1,1,6)"], 6.0)
    assert not CG.accepts_window(ev["epstein_(1,1,6)"], 6.5)
    assert not CG.accepts_window(ev["W_a(a=1/4)"], 2.5)
    assert CG.accepts_window(ev["W_a(a=1/4)"], 2.0)  # vacuous: no atom inside
    for c in (1.5, 2.5, 30.0, 200.5):
        assert CG.accepts_window(ev["zeta"], c)
        assert CG.accepts_window(ev["dedekind_Q(sqrt-23)"], c)
    # place mode, S = {inf, 2} on c in [2, 3): the whole 2-tower counts
    for c in (2.2, 2.5, 2.9):
        assert not CG.accepts_places(ev["epstein_(1,1,6)"], c)  # s_3(2) = 6 at n = 8
        assert not CG.accepts_places(ev["W_a(a=1/4)"], c)
        assert CG.accepts_places(ev["zeta"], c)
        assert CG.accepts_places(ev["dedekind_Q(sqrt-23)"], c)
        assert CG.accepts_window(ev["epstein_(1,1,6)"], c)  # the window alone cannot see it


def test_closed_form_decision_negative_control():
    """a = 0 is zeta^2 (unitary, s_k = 2): the exact decision must accept."""
    t0 = CG.ClosedFormTower(Fraction(0))
    t = CG.ClosedFormTower(Fraction(1, 4))
    for n in range(2, CG.N_MAX + 1):
        pk = CG.prime_power(n)
        if pk:
            assert not t0.exceeds(*pk, 2)
            assert t.exceeds(*pk, 2)


def test_gate_catches_planted_faults():
    a = CG.coeffs_zeta()
    a[6] = Fraction(2)  # composite atom at 6
    ev = CG.gate_events(CG.lambda_vectors(a), 1)
    assert ev[0]["n"] == 6 and ev[0]["kind"] == "composite_atom"
    a = CG.coeffs_zeta()
    a[4] = Fraction(3)  # Lambda(4) = 3 log 4 - log 2 = 5 log 2: s_2(2) = 5 > 1
    ev = CG.gate_events(CG.lambda_vectors(a), 1)
    assert ev[0] == {"n": 4, "kind": "tower", "p": 2, "k": 2, "s_k": "5"}


def test_json_gate_pinned(gate):
    with open(os.path.join(HERE, "checker_q_cells.json")) as fh:
        stored = json.load(fh)["gate"]
    assert stored == json.loads(json.dumps(gate))


def test_agrees_with_numerics_us_check(gate):
    """Compared only after the gate above passed (brief step 3): the numerics
    worker's independent exact check, read from its branch with git show."""
    import subprocess

    try:
        raw = subprocess.run(
            ["git", "show", "teal-sea/weil-propagation:hunts/weil_propagation/numerics/us_check.json"],
            cwd=HERE, capture_output=True, text=True, check=True, timeout=30,
        ).stdout
    except Exception as e:  # branch absent in a fresh clone
        pytest.skip(f"numerics branch not available: {e}")
    U = json.loads(raw)
    for mine, theirs in (("epstein_(1,1,6)", "epstein_1_1_6"), ("dedekind_Q(sqrt-23)", "dedekind_Q_sqrt_m23")):
        ev = gate[mine]["events"]
        assert [e["n"] for e in ev if e["kind"] == "composite_atom"] == U[theirs]["composite_atoms"]
        assert [[e["n"], e["p"], e["k"], e["s_k"]] for e in ev if e["kind"] == "tower"] == U[theirs][
            "tower_violations_abs_s_gt_d"
        ]
        lam = CG.lambda_vectors(CG.OBJECTS[mine][1]())
        for p, d in U[theirs]["towers_small_p"].items():
            for k, s in d.items():
                assert str(lam[int(p) ** int(k)].get(int(p), 0)) == s, (mine, p, k)
