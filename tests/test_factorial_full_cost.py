"""The full-cost experiment's recorded seeds re-verify and its recorded bounds recompute.

``hunts/prime_pair_error/frontier/2026-09-06/factorial_full_cost/`` compares two LP
objectives on the factorial-certificate seed family of the preserved pilot: the pilot's
leading constant C, and the entire proved bound U_N of PILOT.md section 3, at the same
L, M and N. ``COST_COMPARISON.md`` states numbers; this file pins them to the record.

What is pinned, all cheap:

1. Every distinct full-cost seed in the record satisfies the pilot's exact constraints
   (indices divide L, balance, one full period, the [1, M) floor), with independent
   integer arithmetic. The LP proposed them; this is the check that admits them.
2. Every row's recorded U_baseline and U_full_cost recompute from the recorded rational
   coefficients at 30 digits, and the recorded difference is their difference. The
   baseline seed of every row is the pilot's recorded seed for that (L, M).
3. The headline counts: 348 rows, 0 rejected proposals, full cost never strictly worse,
   strictly better in exactly the rows whose seed differs from the baseline, and every
   full-cost seed at N = 10^8 and 10^12 equal to the baseline.
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

import mpmath as mp
import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FRONTIER = os.path.join(REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06")
RECORD = os.path.join(FRONTIER, "factorial_full_cost", "full_cost_results.json")
PILOT_RECORD = os.path.join(FRONTIER, "factorial_certificate_pilot", "results.json")


def _seed(d: dict) -> dict[int, Fraction]:
    return {int(j): Fraction(a) for j, a in d.items()}


def _verify(L: int, M: int, seed: dict[int, Fraction]) -> None:
    assert 2 <= M <= L
    assert seed and all(L % j == 0 for j in seed)
    assert sum((a / j for j, a in seed.items()), Fraction(0)) == 0
    scale = math.lcm(*(a.denominator for a in seed.values()))
    nums = {j: int(a * scale) for j, a in seed.items()}
    for r in range(L):
        assert sum(a * (r // j) for j, a in nums.items()) >= (scale if 1 <= r < M else 0), (L, M, r)


def _K(N: int, M: int) -> int:
    K, p = 0, M
    while p <= N:
        K += 1
        p *= M
    return K


def _U(seed: dict[int, Fraction], M: int, N: int) -> mp.mpf:
    K = _K(N, M)
    A = sum((abs(a) for a in seed.values()), Fraction(0))
    kappa = -sum((mp.mpf(a.numerator) / a.denominator) * mp.log(j) / j for j, a in seed.items())
    c1 = N * (1 - mp.mpf(M) ** (-K - 1)) / (1 - mp.mpf(1) / M)
    c2 = (K + 1) * (1 + mp.log(N)) - mp.log(M) * K * (K + 1) / 2
    return c1 * kappa + c2 * (mp.mpf(A.numerator) / A.denominator)


@pytest.fixture(scope="module")
def record():
    return json.load(open(RECORD, encoding="utf-8"))


@pytest.fixture(scope="module")
def pilot_seeds():
    data = json.load(open(PILOT_RECORD, encoding="utf-8"))
    return {(c["period"], c["radix"]): _seed(c["coefficients"]) for c in data["cases"]}


def test_headline_counts(record):
    assert record["rows_total"] == 348 == 87 * 4
    assert record["rows_with_accepted_full_cost_seed"] == 348
    assert record["full_cost_proposals_rejected_by_exact_check"] == 0
    assert record["rejections"] == []
    assert record["leading_constant_resolve_mismatches"] == 0
    assert record["rows_full_cost_strictly_worse"] == 0
    assert record["rows_full_cost_strictly_better"] == record["rows_different_seed_from_baseline"]
    assert record["rows_tied"] == record["rows_same_seed_as_baseline"]
    assert record["cutoffs"] == [10**4, 10**6, 10**8, 10**12]


def test_every_distinct_full_cost_seed_satisfies_the_pilot_constraints(record):
    seen = set()
    for row in record["rows"]:
        key = (row["L"], row["M"], json.dumps(row["full_cost_seed"], sort_keys=True))
        if key in seen:
            continue
        seen.add(key)
        _verify(row["L"], row["M"], _seed(row["full_cost_seed"]))
    assert len(seen) >= 87


def test_baselines_are_the_pilot_seeds_and_bounds_recompute(record, pilot_seeds):
    with mp.workdps(40):
        for row in record["rows"]:
            L, M, N = row["L"], row["M"], row["N"]
            base = _seed(row["baseline_seed"])
            assert base == pilot_seeds[(L, M)], (L, M)
            full = _seed(row["full_cost_seed"])
            assert _K(N, M) == row["K"]
            u_base, u_full = _U(base, M, N), _U(full, M, N)
            assert abs(u_base - mp.mpf(row["U_baseline"])) <= mp.mpf(10) ** -25 * u_base, (L, M, N)
            assert abs(u_full - mp.mpf(row["U_full_cost"])) <= mp.mpf(10) ** -25 * u_full, (L, M, N)
            diff = mp.mpf(row["U_baseline_minus_U_full_cost"])
            assert abs((u_base - u_full) - diff) <= mp.mpf(10) ** -15 * u_base, (L, M, N)
            assert diff >= 0, (L, M, N, "full cost must never be worse than its own baseline")
            assert (diff > 0) == (not row["same_seed_as_baseline"]), (L, M, N)


def test_large_cutoffs_return_the_leading_constant_seed(record):
    for row in record["rows"]:
        if row["N"] >= 10**8:
            assert row["same_seed_as_baseline"], (row["L"], row["M"], row["N"])


def test_the_one_headline_row(record):
    """(L, M, N) = (2310, 15, 10^4): the winner among all M at L = 2310 and N = 10^4."""
    [row] = [r for r in record["rows"] if (r["L"], r["M"], r["N"]) == (2310, 15, 10**4)]
    assert row["baseline_A"] == "15" and row["full_cost_A"] == "10"
    assert abs(float(row["U_baseline_minus_U_full_cost"]) - 91.2807433) < 1e-6
    assert abs(float(row["relative_improvement"]) - 0.00824784) < 1e-7
