"""The direct-B_N comparison's recorded seeds re-verify and its recorded values recompute.

``hunts/prime_pair_error/frontier/2026-09-06/factorial_direct_bn/`` minimizes the factorial
certificate value B_N itself (linear in the seed for fixed L, M, N) over the pilot's seed
family and compares, on B_N, against the pilot's leading-constant seed and the full-cost
seed of ``../factorial_full_cost/``. ``DIRECT_BN.md`` states numbers; this file pins them.

Pinned, all cheap:

1. Every distinct direct seed in the record satisfies the pilot's exact constraints, with
   independent integer arithmetic.
2. Every row's three recorded B_N values recompute from the recorded rationals at 40
   digits, and the recorded differences are their differences. The lead seed of every row
   is the pilot's recorded seed; the full-cost seed is the one ``full_cost_results.json``
   records for the same row.
3. The fallback rule held: the chosen seed's B_N is never above the lead seed's, a row is
   ``improves_lead`` exactly when the direct seed differs from lead and is strictly better,
   and no row fell back to a worse or rejected proposal.
4. The headline counts.
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
RECORD = os.path.join(FRONTIER, "factorial_direct_bn", "direct_bn_results.json")
FULL_COST_RECORD = os.path.join(FRONTIER, "factorial_full_cost", "full_cost_results.json")
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


def _B(seed: dict[int, Fraction], M: int, N: int) -> mp.mpf:
    total, power = mp.mpf(0), 1
    for _ in range(_K(N, M) + 1):
        for j, a in seed.items():
            total += (mp.mpf(a.numerator) / a.denominator) * mp.loggamma(N // (j * power) + 1)
        power *= M
    return total


@pytest.fixture(scope="module")
def record():
    return json.load(open(RECORD, encoding="utf-8"))


@pytest.fixture(scope="module")
def pilot_seeds():
    data = json.load(open(PILOT_RECORD, encoding="utf-8"))
    return {(c["period"], c["radix"]): _seed(c["coefficients"]) for c in data["cases"]}


@pytest.fixture(scope="module")
def full_cost_seeds():
    data = json.load(open(FULL_COST_RECORD, encoding="utf-8"))
    return {(r["L"], r["M"], r["N"]): _seed(r["full_cost_seed"]) for r in data["rows"]}


def test_headline_counts(record):
    assert record["rows_total"] == 348
    assert record["direct_proposals_rejected_by_exact_check"] == 0
    assert record["rejections"] == []
    assert record["rows_by_status"] == {"same_as_lead": 334, "improves_lead": 14}
    assert record["rows_direct_improves_lead"] == 14
    assert record["rows_direct_worse_than_full_cost_on_B_N"] == 0
    assert record["rows_direct_beats_full_cost_on_B_N"] == 31
    assert record["cutoffs"] == [10**4, 10**6, 10**8, 10**12]


def test_every_distinct_direct_seed_satisfies_the_pilot_constraints(record):
    seen = set()
    for row in record["rows"]:
        key = (row["L"], row["M"], json.dumps(row["direct_seed"], sort_keys=True))
        if key in seen:
            continue
        seen.add(key)
        _verify(row["L"], row["M"], _seed(row["direct_seed"]))
    assert len(seen) >= 87


def test_values_recompute_and_the_fallback_rule_held(record, pilot_seeds, full_cost_seeds):
    with mp.workdps(40):
        for row in record["rows"]:
            L, M, N = row["L"], row["M"], row["N"]
            lead, full, direct, chosen = (_seed(row[k]) for k in
                                          ("lead_seed", "full_cost_seed", "direct_seed", "chosen_seed"))
            assert lead == pilot_seeds[(L, M)], (L, M)
            assert full == full_cost_seeds[(L, M, N)], (L, M, N)
            assert _K(N, M) == row["K"]
            b_lead, b_full, b_direct = _B(lead, M, N), _B(full, M, N), _B(direct, M, N)
            tol = mp.mpf(10) ** -25
            assert abs(b_lead - mp.mpf(row["B_N_lead"])) <= tol * b_lead, (L, M, N)
            assert abs(b_full - mp.mpf(row["B_N_full_cost"])) <= tol * b_full, (L, M, N)
            assert abs(b_direct - mp.mpf(row["B_N_direct"])) <= tol * b_direct, (L, M, N)
            assert abs((b_lead - b_direct) - mp.mpf(row["B_lead_minus_B_direct"])) <= mp.mpf(10) ** -15 * b_lead
            assert abs((b_full - b_direct) - mp.mpf(row["B_full_minus_B_direct"])) <= mp.mpf(10) ** -15 * b_lead
            # the fallback rule
            b_chosen = _B(chosen, M, N)
            assert b_chosen <= b_lead, (L, M, N, "a worse certificate was accepted")
            if row["status"] == "improves_lead":
                assert chosen == direct and direct != lead and b_direct < b_lead, (L, M, N)
            else:
                assert row["status"] == "same_as_lead" and chosen == lead == direct, (L, M, N)
            assert row["direct_same_as_full_cost"] == (direct == full)


def test_the_headline_rows(record):
    """The pilot's selected seed at (2310, 15, 10^4) is not improved; the largest gain is at M = 17."""
    [row] = [r for r in record["rows"] if (r["L"], r["M"], r["N"]) == (2310, 15, 10**4)]
    assert row["status"] == "same_as_lead"
    assert row["B_N_lead"].startswith("10681.264020")
    assert row["B_N_full_cost"].startswith("10711.147559")
    [row] = [r for r in record["rows"] if (r["L"], r["M"], r["N"]) == (2310, 17, 10**4)]
    assert row["status"] == "improves_lead"
    assert row["B_N_lead"].startswith("10871.52777")
    assert row["B_N_direct"].startswith("10868.76996")
    assert abs(float(row["B_lead_minus_B_direct"]) - 2.7578127) < 1e-6
    improving = [(r["L"], r["M"], r["N"]) for r in record["rows"] if r["status"] == "improves_lead"]
    assert all(L == 2310 for L, _, _ in improving)
    assert sorted(N for _, _, N in improving) == [10**4] * 13 + [10**6]
    assert all(r["status"] == "same_as_lead" for r in record["rows"] if r["N"] >= 10**8)
