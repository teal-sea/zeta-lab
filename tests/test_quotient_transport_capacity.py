"""Independent arithmetic checks for the bounded transport-capacity result."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from mpmath import mp
from sympy import factorint

from hunts.quotient_certificate import transport_capacity as transport

HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"


def independent_product(N, q):
    product = 1
    for d in range(N // (q + 1) + 1, N // q + 1):
        factors = factorint(d)
        if len(factors) == 1:
            product *= int(next(iter(factors)))
    return product


def test_signed_relation_and_three_cell_control_have_exact_log97_capacity():
    report = json.loads((HUNT / "transport_capacity_results.json").read_text())
    assert report["status"] == "complete"
    equal = []
    for row in report["negative_capacity_checks"]:
        M = independent_product(10000, row["q"])
        required = 97 ** row["withdrawal_coefficient"]
        assert M == int(row["mass_product"]) >= required == int(row["required_product"])
        if M == required:
            equal.append(row["q"])
    assert equal == [103]
    small = {1: 1, 102: 1, 103: -1}
    assert sum(small.values()) == 1
    assert transport.moment_defects(small, 100) == [0] * 100
    assert independent_product(10000, 102) == 1
    assert independent_product(10000, 103) == 97


def test_true_prefix_rates_by_independent_triangular_back_substitution():
    for q in (101, 102, 103, 5000):
        independent = [0] * 100
        for j in range(100, 0, -1):
            independent[j - 1] = q // j - sum(independent[s - 1] * (s // j)
                                              for s in range(j + 1, 101))
        rates = transport.prefix_rates(q, 100)
        assert rates == independent
        assert rates[-1] == q // 100
        for u in range(51, 101):
            assert sum(rates[u - 1:]) == q // u
    assert transport.prefix_rates(5000, 100)[50] == 2
    assert transport.prefix_rates(5000, 100)[99] == 50


def test_profitable_exchange_passes_top_checks_but_has_zero_full_capacity():
    delta = transport.exchange(103, 101, 100)
    assert delta == {103: -1, 101: 1, 1: 3, 3: -1, 5: -1, 6: 1,
                     16: 1, 17: -1, 33: -1, 34: 1, 50: -1, 51: 1}
    assert sum(delta.values()) == 2
    assert transport.moment_defects(delta, 100) == [0] * 100
    Q = {10000 // d for d in range(2, 10001)}
    assert set(delta) <= Q
    assert all(delta.get(s, 0) >= 0 for s in range(51, 101))
    assert independent_product(10000, 101) == 1
    assert independent_product(10000, 33) == 1
    assert (10000 // 34 + 1, 10000 // 33) == (295, 303)
    failing = [q for q, v in delta.items() if v < 0 and independent_product(10000, q) < 97 ** (-v)]
    assert failing == [33]
    # The normalized measure fails the zero-capacity condition for every C.
    assert Fraction(-delta[33], sum(delta.values())) == Fraction(1, 2)


def test_exact_capacity_after_accumulated_refill_and_no_refill():
    delta = transport.exchange(103, 101, 100)
    negative = sorted(q for q, v in delta.items() if v < 0)
    assert negative == [3, 5, 17, 33, 50, 103]
    assert all(delta[q] == -1 for q in negative)
    # This is the coordinatewise nonnegativity calculation for any current
    # nonnegative measure; the zero-moment direction preserves its moments.
    for refill in (Fraction(0), Fraction(1, 7), Fraction(3)):
        current = {q: Fraction(2) for q in delta}
        current[33] = refill
        capacity = min(current[q] for q in negative)
        assert all(current[q] + capacity * change >= 0 for q, change in delta.items())
        assert any(current[q] + (capacity + Fraction(1, 100)) * change < 0
                   for q, change in delta.items())


def test_accumulated_signed_rates_and_upper_prefix_mass_telescope():
    # Fixed unequal amounts exercise the signed withdrawal/refill formulas.
    steps = [(103, 101, Fraction(2), Fraction(1)),
             (103, 102, Fraction(1), Fraction(3))]
    eta = {}
    drain = [Fraction(0)] * 100
    for a, b, u, v in steps:
        eta[a] = eta.get(a, 0) - u
        eta[b] = eta.get(b, 0) + v
        ra, rb = transport.prefix_rates(a, 100), transport.prefix_rates(b, 100)
        for s in range(100):
            D = v * max(rb[s], 0) + u * max(-ra[s], 0)
            F = u * max(ra[s], 0) + v * max(-rb[s], 0)
            assert D - F == v * rb[s] - u * ra[s]
            drain[s] += D - F
    for u in range(51, 101):
        assert sum(drain[u - 1:]) == sum(v * (q // u) for q, v in eta.items())
    for u in (51, 75, 100):
        left = 1
        for s in range(u, 101):
            left *= independent_product(10000, s)
        right = 1
        for d in range(10000 // 101 + 1, 10000 // u + 1):
            factors = factorint(d)
            if len(factors) == 1:
                right *= int(next(iter(factors)))
        assert left == right


def test_variance_recipe_ceiling_is_enclosed_and_replay_is_stable():
    before = mp.dps
    actual = transport.analyze()
    saved = json.loads((HUNT / "transport_capacity_results.json").read_text())
    assert mp.dps == before
    assert actual["constant_variance_procedure_ceiling"] == saved["constant_variance_procedure_ceiling"]
    payload = (HUNT / "height_kernel_results.json").read_bytes()
    assert actual["height_input_sha256"] == hashlib.sha256(payload).hexdigest()
    with mp.workdps(110):
        archive = next(row for row in json.loads((HUNT / "results.json").read_text())["results"]
                       if row["N"] == 10000)
        c = [Fraction(a, archive["denominator"]) for a in archive["coefficient_numerators"]]
        mass = {}
        for d in range(2, 10001):
            f = factorint(d)
            if len(f) == 1:
                p, q = int(next(iter(f))), 10000 // d
                mass[q] = mass.get(q, mp.mpf(0)) + mp.log(p)
        psi = mp.fsum(mass.values())
        W = {q: sum(v * (q // j) for j, v in enumerate(c, 1)) for q in mass}
        heights = {q: mp.mpf(v.numerator) / v.denominator for q, v in W.items()}
        mean = mp.fsum(mass[q] * heights[q] for q in mass) / psi
        variance = mp.fsum(mass[q] * (heights[q] - mean) ** 2 for q in mass) / psi
        ceiling = psi * mp.sqrt(mp.log(2) * variance / (psi - mp.log(2)))
        lo, hi = map(mp.mpf, saved["constant_variance_procedure_ceiling"])
        assert lo <= ceiling <= hi < mp.mpf("17.507109839685325")
        assert psi * mean <= 20000  # the comparison vector is in the broad class
