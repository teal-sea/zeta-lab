"""Exact controls and independent checks for the finite weighted transfer."""
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

from mpmath import mp
import pytest
from sympy import Matrix, Rational, factorint

from hunts.quotient_certificate import finite_transfer as transfer
from hunts.quotient_certificate import finite_transfer_exact as exact

HUNT = Path(__file__).resolve().parents[1] / "hunts/quotient_certificate"


def test_exact_constructor_reproduces_every_saved_witness_field():
    data = json.loads((HUNT / "finite_transfer_counterexample.json").read_text())
    for key, value in exact.construct().items():
        assert data[key] == value


def test_sampling_counterexample_is_exact_feasible_and_not_only_a_rank_count():
    data = json.loads((HUNT / "finite_transfer_counterexample.json").read_text())
    assert data["status"] == "complete"
    N, y, D = data["N"], data["y"], data["denominator"]
    nums = data["coefficient_numerators"]
    assert N == 10000 and y == 100 and len(nums) == y
    assert nums[0] == D and sum(abs(a) for a in nums[1:]) == D
    # Prime support independently obtained by factoring every d, not the probe sieve.
    P = sorted({N // d for d in range(2, N + 1) if len(factorint(d)) == 1})
    Q = sorted({N // d for d in range(2, N + 1)})
    assert P == data["positive_mass_cells"] and len(P) == 99
    assert len(Q) == data["cells_checked"] == 198
    heights = {q: sum(a * (q // j) for j, a in enumerate(nums, 1)) for q in Q}
    assert min(heights.values()) == D
    assert all(heights[q] >= (q - q // 2) * D for q in Q)
    c = [Fraction(a, D) for a in nums]
    saw = [sum(v * (Fraction(q % j, j) - Fraction(j - 1, 2 * j))
               for j, v in enumerate(c, 1)) for q in P]
    assert len(set(saw)) == 1 and str(saw[0]) == data["finite_saw_value_exact"]
    assert sum(v / j for j, v in enumerate(c, 1)) == 1
    assert all(heights[q] == q * D for q in P)
    full = sum(a * b * Fraction(math.gcd(i, j) ** 2 - 1, 12 * i * j)
               for i, a in enumerate(c, 1) for j, b in enumerate(c, 1))
    assert full == Fraction(data["period_variance_exact"]) > 0
    with mp.workdps(40):
        assert mp.loggamma(N + 1) > 2 * N
    R = Matrix([[(q % j) - (P[0] % j) for j in range(2, y + 1)] for q in P[1:]])
    assert R.shape == (98, 99)
    # Rational rref takes the exact integer-domain route. Generic rank() can
    # spend minutes simplifying expressions for this same small matrix.
    assert len(R.rref()[1]) == data["difference_matrix_rank"] == 95


def test_zero_mass_coverage_blocks_this_null_direction_at_the_saved_certificate():
    data = json.loads((HUNT / "finite_transfer_counterexample.json").read_text())
    saved = next(row for row in json.loads((HUNT / "results.json").read_text())["results"]
                 if row["N"] == 10000)
    c = [Fraction(a, saved["denominator"]) for a in saved["coefficient_numerators"]]
    v = [Fraction(0)] + [Fraction(a, data["denominator"])
                          for a in data["coefficient_numerators"][1:]]
    interval = data["saved_vector_tangent_interval"]
    assert interval["lower"] == interval["upper"] == "0"
    assert interval["lower_cell"] == 333 and interval["upper_cell"] == 60
    for q, sign in ((333, 1), (60, -1)):
        assert transfer.mass_factors(10000)[q] == {}
        assert sum(a * (q // j) for j, a in enumerate(c, 1)) == 1
        slope = sum(a * (q // j) for j, a in enumerate(v, 1))
        assert sign * slope > 0
        key = "lower_slope" if sign == 1 else "upper_slope"
        assert slope == Fraction(interval[key])
    # These two inequalities force t >= 0 and t <= 0. t=0 is feasible.
    Q = {10000 // d for d in range(2, 10001)}
    assert all(sum(a * (q // j) for j, a in enumerate(c, 1)) >= 1 for q in Q)


def test_mass_support_and_zero_cells_by_independent_factorization():
    for N in (4, 9, 16, 27, 100):
        actual = transfer.mass_factors(N)
        expected = {N // d: {} for d in range(2, N + 1)}
        for d in range(2, N + 1):
            factors = factorint(d)
            if len(factors) == 1:
                p = int(next(iter(factors)))
                q = N // d
                expected[q][p] = expected[q].get(p, 0) + 1
        assert actual == expected
        assert actual[N // 2] == {2: 1}
        assert min(math.prod(p ** k for p, k in counts.items())
                   for counts in actual.values() if counts) == 2
    assert transfer.mass_factors(27)[4] == {}


def test_N9_drift_cancels_positive_sawtooth_variance_exactly():
    N, c = 9, [Fraction(1), Fraction(-1), Fraction(-1)]
    masses = transfer.mass_factors(N)
    assert list(masses) == [1, 2, 3, 4]
    assert [math.prod(p ** k for p, k in counts.items()) for counts in masses.values()] == [210, 2, 3, 2]
    F = Matrix(transfer.floor_rows(list(masses), len(c)))
    assert F * Matrix(c) == Matrix([1, 1, 1, 1])
    assert len(c) == math.isqrt(N)
    assert sum(v / j for j, v in enumerate(c, 1)) == Fraction(1, 6)
    samples = [sum(v * (Fraction(q % j, j) - Fraction(j - 1, 2 * j))
                   for j, v in enumerate(c, 1)) for q in range(1, 7)]
    assert samples[:4] == [Fraction(q, 6) - Fraction(5, 12) for q in range(1, 5)]
    assert sum(samples) == 0
    assert sum(s * s for s in samples) / 6 == transfer.period_variance(c) == Fraction(59, 432)
    assert math.factorial(9) // (math.factorial(4) * math.factorial(3)) == 2520
    assert math.prod(math.prod(p ** k for p, k in counts.items()) for counts in masses.values()) == 2520
    # The full-period norm lower bound also has strictly positive RHS.
    H = sum(Fraction(1, j) for j in range(1, 4))
    projected_norm = Fraction(5, 6) ** 2 + 2
    assert projected_norm / (24 * H * H) == Fraction(97, 2904) > 0


def test_centered_gram_and_rank_restrictions_exactly():
    for N, y in ((4, 2), (9, 3), (16, 4), (27, 9)):
        cells = [q for q, factors in transfer.mass_factors(N).items() if factors]
        s = len(cells)
        F = Matrix(transfer.floor_rows(cells, y))
        f = Matrix([[Rational(q % j, j) - Rational(j - 1, 2 * j)
                     for j in range(1, y + 1)] for q in cells])
        q = Matrix(cells)
        a = Matrix([Rational(1, j) for j in range(1, y + 1)])
        b = Matrix([Rational(j - 1, 2 * j) for j in range(1, y + 1)])
        one = Matrix.ones(s, 1)
        assert F == q * a.T - f - one * b.T
        # Arbitrary unequal rational masses check the algebra independently
        # of logarithm evaluation; the identities hold for every positive p.
        p = Matrix([Rational(i, s * (s + 1) // 2) for i in range(1, s + 1)])
        C = Matrix.diag(*p) - p * p.T
        Cf, h, vq = f.T * C * f, f.T * C * q, (q.T * C * q)[0]
        G = F.T * C * F
        assert G == Cf - a * h.T - h * a.T + vq * a * a.T
        assert F.T * p == a * (q.T * p)[0] - f.T * p - b
        D = Matrix([list(F.row(i) - F.row(0)) for i in range(1, s)])
        residual = Cf - h * h.T / vq
        assert G.rank() == D.rank() <= min(y, s - 1)
        assert Cf.rank() <= min(y - 1, s - 1)
        assert residual.rank() <= min(y - 1, s - 2)
        assert all(G * k == Matrix.zeros(y, 1) for k in D.nullspace())
        if N == 9:
            assert G.rank() == 2 and residual.rank() == 1
            assert D.nullspace() == [Matrix([-1, 1, 1])]


def test_period_form_against_pairwise_gcd_formula():
    for c in ([Fraction(1), Fraction(-1), Fraction(-1)],
              [Fraction((-1) ** j * (j + 1), j + 2) for j in range(12)]):
        direct = sum(a * b * Fraction(math.gcd(i, j) ** 2 - 1, 12 * i * j)
                     for i, a in enumerate(c, 1) for j, b in enumerate(c, 1))
        assert transfer.period_variance(c) == direct


def test_atom_inequality_is_sharp_inside_the_feasible_class():
    F = Matrix(transfer.floor_rows([1, 2], 2))
    for t in (Rational(0), Rational(1, 2), Rational(1), Rational(2)):
        assert F * Matrix([1, t - 1]) - Matrix.ones(2, 1) == Matrix([0, t])
    # Symbolic probabilities, not rounded logarithms, suffice for sharpness.
    for alpha in (Fraction(1, 9), Fraction(1, 4), Fraction(1, 2)):
        for t in (Fraction(0), Fraction(1, 2), Fraction(3)):
            mu, v = alpha * t, alpha * (1 - alpha) * t * t
            assert mu * mu == alpha * v / (1 - alpha)
    assert transfer.mass_factors(4) == {1: {2: 1, 3: 1}, 2: {2: 1}}


def test_mean_bounds_and_integer_frame_constant_on_exact_controls():
    cells, y = [1, 2, 3, 4], 3
    F = Matrix(transfer.floor_rows(cells, y))
    D = Matrix([list(F.row(i) - F.row(0)) for i in range(1, 4)])
    r, L = D.rank(), sum(v * v for v in D)
    kernel = D.nullspace()[0]
    p = [Rational(1, 2), Rational(1, 6), Rational(1, 6), Rational(1, 6)]
    alpha = min(p)
    # Flat witness, constant floor perturbations, and large feasible heights.
    for c in (Matrix([1, -1, -1]), Matrix([2, -1, -1]), Matrix([1, 0, 0])):
        slack = F * c - Matrix.ones(4, 1)
        assert min(slack) >= 0
        mu = sum(w * x for w, x in zip(p, slack))
        v = sum(w * (x - mu) ** 2 for w, x in zip(p, slack))
        assert mu * mu >= alpha * v / (1 - alpha)
        assert v + mu * mu <= max(slack) * mu
        perpendicular = c - kernel * (kernel.dot(c) / kernel.dot(kernel))
        rhs = p[0] * alpha * perpendicular.dot(perpendicular) / L ** (r - 1)
        assert v >= rhs
        # No eigenvalue plot: a PSD test with exact rational principal minors.
        projection = Matrix.eye(y) - kernel * kernel.T / kernel.dot(kernel)
        assert (D.T * D - projection / L ** (r - 1)).is_positive_semidefinite


def test_saved_replay_matches_archive_and_keeps_evidence_grades_separate():
    source = (HUNT / "results.json").read_bytes()
    original = json.loads(source)
    report = json.loads((HUNT / "finite_transfer_results.json").read_text())
    assert report["status"] == "complete"
    assert report["requested"] == report["completed"] == len(report["results"]) == 9
    assert report["source_sha256"] == hashlib.sha256(source).hexdigest()
    rows = {row["name"]: row for row in report["results"]}
    with mp.workdps(80):
        for old in original["results"]:
            new = rows[f"saved_N{old['N']}"]["evaluations"][-1]
            assert new["cells_checked"] == old["cells_checked"]
            assert Fraction(new["minimum_height_exact"]) >= 1
            assert abs(mp.mpf(new["excess"]) - mp.mpf(old["evaluations"][-1]["excess"])) < mp.mpf("1e-65")
        for row in rows.values():
            low, high = row["evaluations"]
            for key in ("variance_W", "variance_S", "residual_variance", "excess"):
                assert abs(mp.mpf(low[key]) - mp.mpf(high[key])) < mp.mpf("1e-36")
            assert mp.mpf(high["atom_excess_lower_bound"]) <= mp.mpf(high["excess"]) + mp.mpf("1e-68")
        assert mp.mpf(rows["flat_N9"]["evaluations"][-1]["variance_W"]) == 0
        # A zero denominator is undefined, not a displayed ratio of zero.
        assert rows["e1_N9"]["evaluations"][-1]["height_to_period_variance_ratio"] is None


def test_live_replay_and_rejected_infeasible_control():
    before = mp.dps
    result = transfer.finite_moments(9, [Fraction(1), Fraction(-1), Fraction(-1)], 50)
    assert mp.dps == before
    assert result["variance_W"] == result["excess"] == "0.0"
    with pytest.raises(ValueError, match="coverage"):
        transfer.finite_moments(9, [Fraction(0)], 50)
    with pytest.raises(ValueError, match="Fraction"):
        transfer.finite_moments(9, [1.0], 50)
    # One-atom measures have no variance, so the alpha/(1-alpha) bound is omitted.
    result = transfer.finite_moments(2, [Fraction(2)], 50)
    assert result["variance_W"] == result["atom_excess_lower_bound"] == "0.0"
    assert mp.dps == before
