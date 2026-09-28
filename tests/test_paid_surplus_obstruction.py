"""Independent finite rational checks for the N=144 paid construction."""

from collections import defaultdict
from fractions import Fraction as F
import importlib.util
import json
from math import factorial
from pathlib import Path

import pytest
from sympy import factorint

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "paid_surplus", ROOT / "hunts/paid_surplus_obstruction/construction.py")
H = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(H)


def independent_weights(c):
    # Count pairs (j,m) with j*m <= floor(N/d), without the producer's division.
    return {d: sum((a for j, a in enumerate(c, 1)
                    for m in range(1, 145) if d * j * m <= 144), F(0))
            for d in range(2, 145)}


def test_exact_class_and_all_prime_power_constraints():
    c = H.WITNESS
    assert c == tuple(F(n, 20) for n in [20, -20, -20, 0, -20, -13, 7, 6, 0, 0, 0, 13])
    assert sum((a / j for j, a in enumerate(c, 1)), F(0)) == 0
    assert sum(map(abs, c)) == F(119, 20) <= 23
    assert [sum((a * len(range(j, q + 1, j)) for j, a in enumerate(c, 1)), F(0))
            for q in range(1, 6)] == [1] * 5
    weights = independent_weights(c)
    pp = [(d, int(next(iter(factorint(d))))) for d in range(2, 145) if len(factorint(d)) == 1]
    assert tuple(pp) == H.prime_powers()
    assert len(pp) == 47
    assert all(weights[d] <= 1 for d, _ in pp)
    assert all(weights[d] == H.weight(c, 144 // d) for d in weights)
    assert sum(weights[d] < 1 for d, _ in pp) == 8


def test_independent_factorial_cost_and_complete_repair():
    weights = independent_weights(H.WITNESS)
    factorial_cost, repair, psi = defaultdict(F), defaultdict(F), defaultdict(F)
    for j, c in enumerate(H.WITNESS, 1):
        for p, exponent in factorint(factorial(144 // j)).items():
            factorial_cost[int(p)] += c * int(exponent)
    for d in range(2, 145):
        factors = factorint(d)
        if len(factors) == 1:
            p = int(next(iter(factors)))
            repair[p] += max(F(0), 1 - weights[d])
            psi[p] += 1
    clean = lambda v: {p: a for p, a in v.items() if a}
    costs = H.cost_vectors(H.WITNESS)
    assert clean(factorial_cost) == costs["B"]
    assert clean(repair) == costs["P_Lambda"] == {
        2: F(27, 10), 3: F(21, 20), 7: F(1), 19: F(3, 10), 23: F(33, 20)}
    assert clean(psi) == costs["psi"]
    assert all(factorial_cost[p] + repair[p] == psi[p] for p in psi)
    assert costs["C"] == costs["psi"] and costs["S"] == {}


@pytest.mark.parametrize("kind", ["balance", "coverage", "mass", "domain", "support"])
def test_class_rejects_each_missing_hypothesis(kind):
    c = list(H.WITNESS)
    if kind == "balance":
        c[11] += 1
    elif kind == "coverage":
        c[0] += 1
        c[11] -= 12
    elif kind == "mass":
        c[5] += 60
        c[11] -= 120
    elif kind == "domain":
        c[11] = float(c[11])
    else:
        c.pop()
    assert H.class_failures(c)


def test_controls_detect_surplus_without_confusing_it_with_cap_residual():
    old = tuple(map(F, ("1", "-1", "-1", "0", "-1", "1", "-1", "0", "0", "1", "-1", "2/385")))
    assert not H.class_failures(old)
    assert [d for d, _ in H.surplus_violations(old)] == [2, 3, 7, 8, 11]
    assert H.cost_vectors(old)["S"] == {
        2: F(2, 55), 3: F(8, 385), 7: F(387, 385), 11: F(387, 385)}
    lesion = list(H.WITNESS)
    lesion[5] += F(3, 5)
    lesion[11] -= F(6, 5)
    assert not H.class_failures(lesion)
    assert len(H.surplus_violations(lesion)) == 4
    with pytest.raises(AssertionError):
        H.exact_checks(lesion)
    zero = (F(0),) * 12
    assert len(H.class_failures(zero)) == 5
    assert H.surplus_violations(zero) == []


def test_prefix_class_containment_and_material_change():
    from sympy import mobius

    for h in range(6, 13):
        c = [F(int(mobius(j))) if j < h else F(0) for j in range(1, 13)]
        c[h - 1] = -h * sum((a / j for j, a in enumerate(c, 1)), F(0))
        assert not H.class_failures(c)
        assert c[6] <= 0
    assert H.WITNESS[6] == F(7, 20) > 0


def test_saved_witness_rows_vectors_and_enclosures():
    path = ROOT / "hunts/paid_surplus_obstruction/computations/check-001/results.json"
    saved = json.loads(path.read_text())
    assert tuple(map(F, saved["coefficients"])) == H.WITNESS
    assert saved["checks"] == H.exact_checks(H.WITNESS)
    assert len(saved["prime_power_rows"]) == 47
    for row in saved["prime_power_rows"]:
        assert F(row["W"]) == H.weight(H.WITNESS, row["q"])
        assert F(row["slack"]) == 1 - F(row["W"]) >= 0
    price = H.price(H.WITNESS)
    assert saved["cost"] == price
    expected_displays = {"B_minus_N": "-13.366803", "P_Lambda": "11.027848",
                         "C_minus_N": "-2.338955", "psi_minus_N": "-2.338955", "S": "0"}
    for rows in price["enclosures"].values():
        for name, pair in rows.items():
            lo, hi = map(F, pair)
            assert lo <= hi
            assert F(expected_displays[name]) - F(1, 1000000) < lo
            assert hi < F(expected_displays[name]) + F(1, 1000000)
    assert saved["controls"] == {"old_endpoint_surplus_violations": 5,
                                  "balanced_lesion_surplus_violations": 4,
                                  "zero_decoy_coverage_failures": 5,
                                  "zero_decoy_surplus_violations": 0}


def test_precision_contexts_restored():
    import flint
    import mpmath as mp

    old = flint.ctx.prec, mp.mp.prec, mp.iv.prec
    H.price(H.WITNESS)
    assert (flint.ctx.prec, mp.mp.prec, mp.iv.prec) == old
