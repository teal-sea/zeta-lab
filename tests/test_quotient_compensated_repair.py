"""Independent exact checks for the fixed bundle and the conditional repair bound."""
from fractions import Fraction as F
import json
from pathlib import Path

from mpmath import mp
from sympy import factorint

from hunts.quotient_certificate import compensated_repair as repair

HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"


def independent_products():
    result = {1000 // d: 1 for d in range(2, 1001)}
    for d in range(2, 1001):
        factors = factorint(d)
        if len(factors) == 1:
            result[1000 // d] *= int(next(iter(factors)))
    return result


def test_fold_rates_by_triangular_solution_and_merged_prefix_destination():
    for a in (76, 200, 333, 40):
        kappa = [0] * 31
        for j in range(31, 0, -1):
            parity = a // j - 2 * ((a // 2) // j)
            assert parity in (0, 1)
            kappa[j - 1] = parity - sum(kappa[i - 1] * (i // j) for i in range(j + 1, 32))
        expected = {a: -1, a // 2: 2}
        for i, value in enumerate(kappa, 1):
            expected[i] = expected.get(i, 0) + value
        expected = {q: value for q, value in expected.items() if value}
        assert repair.fold(a, 31) == expected
        assert repair.moment_defects(expected, 31) == [0] * 31
        assert kappa[-1] == (a // 31) % 2
    # This algebra control tests the endpoint and the destination overlapping
    # the prefix. It is not a new bundle or capacity experiment.
    assert repair.fold(40, 31)[31] == 1
    assert repair.fold(40, 31)[20] == 1  # destination +2, prefix rate -1


def test_fixed_bundle_all_cells_moments_capacities_and_unique_bottleneck():
    data = repair.analyze()
    products = independent_products()
    D = {int(q): value for q, value in data["bundle"].items()}
    assert len(products) == data["attainable_cells"] == 61
    assert set(D) <= set(products)
    assert sum(D.values()) == 10
    assert repair.moment_defects(D, 31) == [0] * 31
    binding = []
    for q, product in products.items():
        value = D.get(q, 0)
        if value < 0:
            assert product ** 3 >= 7 ** (-value)
            if product ** 3 == 7 ** (-value):
                binding.append(q)
        if product == 1:
            assert value >= 0
    assert binding == [20]
    assert products[20] == 7 and D[20] == -3
    assert [sum(repair.fold(a, 31).values()) for a in (76, 200, 333)] == [2, 4, 0]


def test_single_group_repairs_all_empty_cells_without_gain_loss():
    products = independent_products()
    F76, F200, R = (repair.fold(a, 31) for a in (76, 200, 333))
    U = {q: F76.get(q, 0) + 2 * F200.get(q, 0) for q in products}
    empty = sorted(q for q, product in products.items() if product == 1)
    assert len(empty) == 21
    assert [q for q in empty if U[q] < 0] == [19, 25]
    assert max(-U[q] for q in (19, 25)) == 1
    assert all(R[q] == 1 for q in (19, 25))
    assert all(R.get(q, 0) >= 0 for q in empty)
    assert all(U[q] + R.get(q, 0) >= 0 for q in empty)
    assert sum(U.values()) == 10 and sum(R.values()) == 0
    assert R[166] == 2 and products[166] == 1  # retain empty destinations


def test_gross_positive_mass_envelopes_already_give_the_exact_scale():
    products = independent_products()
    F76, F200, R = (repair.fold(a, 31) for a in (76, 200, 333))
    equality, checked = [], 0
    for q, product in products.items():
        if product == 1:
            continue
        Uq = F76.get(q, 0) + 2 * F200.get(q, 0)
        b0, b = max(-Uq, 0), max(-R.get(q, 0), 0)
        if b0 + b:
            checked += 1
            assert product ** 3 >= 7 ** (b0 + b)
            if product ** 3 == 7 ** (b0 + b):
                equality.append(q)
        assert max(-Uq - R.get(q, 0), 0) <= b0 + b
    assert checked == 18 and equality == [20]


def test_contractive_repair_with_secondary_deficits_and_negative_gain():
    # Abstract four-row, one-moment example, not a prime-mass computation.
    # It exercises the lemma's nonzero spill and gain-sacrifice terms that
    # vanish in the prescribed fold bundle.
    U = [F(13), F(-1), F(-1), F(-2)]
    R1 = [F(-7, 6), F(1), F(-1, 2), F(1, 6)]
    R2 = [F(-5, 2), F(-1, 4), F(1), F(0)]
    for vector in (U, R1, R2):
        assert sum(q * v for q, v in enumerate(vector, 1)) == 0
    P = [[F(0), F(1, 4)], [F(1, 2), F(0)]]
    d, p, rho = [F(1), F(1)], [F(1), F(1)], F(1, 2)
    t = [F(10, 7), F(12, 7)]
    assert all(sum(p[k] * P[k][i] for k in range(2)) <= rho * p[i] for i in range(2))
    assert all(t[k] == d[k] + sum(P[k][i] * t[i] for i in range(2)) for k in range(2))
    S = sum(p[k] * d[k] for k in range(2)) / (1 - rho)
    assert S == 4 and sum(p[k] * t[k] for k in range(2)) <= S
    D = [u + t[0] * r1 + t[1] * r2 for u, r1, r2 in zip(U, R1, R2)]
    assert D[1:3] == [0, 0]
    ell, K, G0 = F(7, 4), F(10), sum(U)
    assert sum(R1) == -F(1, 2) and sum(R2) == -F(7, 4)
    assert G0 - ell * S == 2 and sum(D) == F(37, 7)
    # m_1=m_4=1; b0=(0,2), b=(5/2,0) on those positive cells.
    for i, b0, b in ((0, F(0), F(5, 2)), (3, F(2), F(0))):
        assert max(-U[i], 0) <= b0
        assert all(max(-R[i], 0) <= b for R in (R1, R2))
        assert b0 + S * b <= K
        assert 1 + D[i] / K >= 0
    assert sum(D) / K >= (G0 - ell * S) / K == F(1, 5)


def test_saved_report_replays_and_gain_enclosure_contains_independent_value():
    before = mp.dps
    actual = repair.analyze()
    saved = json.loads((HUNT / "compensated_repair_results.json").read_text())
    normalized = json.loads(json.dumps(actual))
    assert all(saved[key] == value for key, value in normalized.items())
    assert saved["completed_bundles"] == saved["requested_bundles"] == 1
    assert saved["searches"] == saved["optimizations"] == 0
    with mp.workdps(110):
        lo, hi = map(mp.mpf, saved["gain_enclosure"])
        assert lo <= mp.log(7) * 10 / 3 <= hi
        assert mp.mpf("6.486367163517710") < lo < hi < mp.mpf("6.486367163517712")
    assert mp.dps == before
