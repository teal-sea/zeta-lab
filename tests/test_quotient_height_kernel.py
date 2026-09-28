"""Exact kernel exclusion and independent checks of the consumed finite data."""
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from mpmath import mp
from mpmath.ctx_iv import MPIntervalContext
import pytest
from sympy import factorint

from hunts.quotient_certificate import height_kernel as kernel

HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"


def test_integer_relation_excludes_constant_heights_on_positive_mass_cells():
    N, y = 10000, 100
    w = kernel.RELATION
    assert len(w) == 21 and sum(w.values()) == 1
    # Independent exact factorization checks every support cell's positive mass.
    for q in w:
        assert any(len(factorint(d)) == 1 for d in range(N // (q + 1) + 1, N // q + 1))
    assert [sum(a * (q // j) for q, a in w.items()) for j in range(1, y + 1)] == [0] * y
    # For a hypothetical constant height k, the annihilated linear combination
    # equals k. It vanishes only at k=0, which violates the attained q=1 row.
    for k in (Fraction(1), Fraction(3, 2), Fraction(2)):
        assert sum(a * k for a in w.values()) == k > 0


def test_consumed_basis_and_logarithmic_moments_replay_without_a_solve():
    payload = (HUNT / "height_kernel_input.json").read_bytes()
    source = json.loads(payload)
    saved = json.loads((HUNT / "height_kernel_results.json").read_text())
    assert saved["input_sha256"] == hashlib.sha256(payload).hexdigest()
    before = mp.dps
    actual = kernel.analyze(source, dps=70)
    assert mp.dps == before
    assert actual["basis_determinant"] == "-1328"
    assert actual["archived_primal_equals_exact_optimizer"] is True
    assert actual["log_moment_equalities_checked"] == 122900
    assert actual["primes_checked"] == 1229
    assert actual["strictly_positive_dual_masses"] == 100
    assert actual["all_primal_cells_checked"] == 198
    assert actual["positive_mass_cells"] == 99
    assert actual["enclosures"] == saved["enclosures"]
    assert actual["dual_mass_enclosures"] == saved["dual_mass_enclosures"]
    assert actual["retained_constraint_control"] == saved["retained_constraint_control"]
    assert all(Fraction(interval[0]) > 0 for interval in actual["dual_mass_enclosures"].values())
    assert Fraction(actual["enclosures"]["Delta_broad"][0]) > 9759


def test_broken_consumed_ingredients_are_rejected():
    source = json.loads((HUNT / "height_kernel_input.json").read_text())
    broken = deepcopy(source)
    broken["primal_c"]["1"] = "2"
    with pytest.raises(ArithmeticError, match="not tight"):
        kernel.check_consumed_basis(broken)
    broken = deepcopy(source)
    broken["basis_cells"][1] = broken["basis_cells"][0]
    with pytest.raises(ValueError, match="distinct attainable"):
        kernel.check_consumed_basis(broken)
    broken = deepcopy(source)
    broken["N"] = 100000
    with pytest.raises(ValueError, match="only N=10000"):
        kernel.check_consumed_basis(broken)


def test_decimal_export_is_outward_even_across_zero():
    iv = MPIntervalContext()
    iv.dps = 65
    for value in (iv.log(2), -iv.log(3), iv.mpf([-1, 2]), iv.mpf(0)):
        lower, upper = kernel.enclosure(value)
        assert Fraction(lower) <= kernel.endpoint(value, 0)
        assert Fraction(upper) >= kernel.endpoint(value, 1)
    assert kernel.outward_bounds(Fraction(-1, 3), Fraction(1, 3), 2) == ["-0.34", "0.34"]
    with pytest.raises(ValueError):
        kernel.outward_bounds(Fraction(2), Fraction(1))


def test_independent_factorial_and_prime_evaluations_land_inside_enclosures():
    saved = json.loads((HUNT / "height_kernel_results.json").read_text())
    source = json.loads((HUNT / "height_kernel_input.json").read_text())
    with mp.workdps(110):
        mass = {}
        for d in range(2, 10001):
            factors = factorint(d)
            if len(factors) == 1:
                p = int(next(iter(factors)))
                q = 10000 // d
                mass[q] = mass.get(q, mp.mpf(0)) + mp.log(p)
        psi = mp.fsum(mass.values())
        T = mp.fsum(mp.mpf(Fraction(c).numerator) / Fraction(c).denominator
                    * mp.loggamma(10000 // int(j) + 1) for j, c in source["primal_c"].items())
        H = mp.fsum(w * w / mass[q] for q, w in kernel.RELATION.items())
        D = psi * H - 1
        values = {"psi": psi, "T_star": T, "optimal_excess": T - psi,
                  "Delta_broad": 20000 - T, "H": H, "D": D,
                  "variance_floor_from_coverage": 1 / D,
                  "variance_floor_from_optimality": (T / psi) ** 2 / D,
                  "atom_excess_from_optimality": T * mp.sqrt(mp.log(2) / ((psi - mp.log(2)) * D))}
        for key, value in values.items():
            lo, hi = map(mp.mpf, saved["enclosures"][key])
            assert lo <= value <= hi, key
        assert min(mass.values()) == mp.log(2)
        assert values["atom_excess_from_optimality"] < 1 < T - psi


def test_parameterization_retains_nonbasis_coverage_and_exact_cost_identity():
    source = json.loads((HUNT / "height_kernel_input.json").read_text())
    data = kernel.check_consumed_basis(source)
    control = json.loads((HUNT / "height_kernel_results.json").read_text())["retained_constraint_control"]
    d = [kernel.rational(data["inverse"][j, 0]) for j in range(100)]
    candidate = [a + b for a, b in zip(data["c"], d)]
    S = data["S"]
    basis_slack = [sum(c * (q // j) for j, c in enumerate(candidate, 1)) - 1 for q in S]
    assert basis_slack == [1] + [0] * 99
    assert 20 not in S
    assert sum(c * (20 // j) for j, c in enumerate(candidate, 1)) == Fraction(-13, 83)
    assert Fraction(control["cost_enclosure"][1]) < 20000
    # The coefficient of each log p in L^T d is the first dual mass's
    # coefficient. This checks the slack cost identity before taking logs.
    for k, p in enumerate(data["primes"]):
        exponent_dot = Fraction()
        for j, value in enumerate(d, 1):
            n, exponent = 10000 // j, 0
            while n:
                n //= p
                exponent += n
            exponent_dot += value * exponent
        assert exponent_dot == kernel.rational(data["dual_coefficients"][0, k])


def test_centered_relation_variance_bound_with_exact_rational_measure():
    # The weighted Cauchy step is valid for arbitrary positive probabilities.
    # Check a nonuniform rational measure independently of interval logarithms.
    factors = kernel.mass_factors(10000)
    P = [q for q in sorted(factors) if factors[q]]
    weights = {q: Fraction(i + 1, len(P) * (len(P) + 1) // 2) for i, q in enumerate(P)}
    H = sum(Fraction(w * w) / weights[q] for q, w in kernel.RELATION.items())
    for c in ({1: Fraction(1)}, {1: Fraction(2), 2: Fraction(-1)}):
        heights = {q: sum(v * (q // j) for j, v in c.items()) for q in P}
        mean = sum(weights[q] * heights[q] for q in P)
        variance = sum(weights[q] * (heights[q] - mean) ** 2 for q in P)
        assert variance * (H - 1) >= mean * mean
        assert sum(kernel.RELATION.get(q, 0) * heights[q] for q in P) == 0
