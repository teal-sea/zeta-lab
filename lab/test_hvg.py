"""Tests for lab/hvg.py: the fast algorithm against the definition, and the exact facts.

Run: lab/.venv/bin/python -m pytest -q -p no:cacheprovider -o addopts="" lab/test_hvg.py
"""
import itertools
import math
import sys
from pathlib import Path

import numpy as np
from hypothesis import given, settings
from hypothesis import strategies as st

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hvg  # noqa: E402

floats = st.floats(min_value=-1e6, max_value=1e6, allow_nan=False, allow_infinity=False)


def as_set(e):
    return {tuple(r) for r in e.tolist()}


@settings(max_examples=3000, deadline=None)
@given(st.lists(floats, min_size=0, max_size=40))
def test_stack_equals_definition_with_ties(xs):
    assert as_set(hvg.hvg_edges(xs)) == as_set(hvg.hvg_edges_brute(xs))


@settings(max_examples=3000, deadline=None)
@given(st.lists(st.integers(0, 4), min_size=0, max_size=30))
def test_stack_equals_definition_heavy_ties(xs):
    assert as_set(hvg.hvg_edges(xs)) == as_set(hvg.hvg_edges_brute(xs))


@settings(max_examples=3000, deadline=None)
@given(st.lists(floats, min_size=1, max_size=60, unique=True))
def test_edge_count_is_2n_minus_records(xs):
    left, right = hvg.records(xs)
    assert len(hvg.hvg_edges(xs)) == 2 * len(xs) - left - right


def closed(xs):
    """Sentinels taller than every value, so that every view is eventually blocked."""
    big = 1e300
    return [big] + list(xs) + [big]


@settings(max_examples=2000, deadline=None)
@given(st.lists(floats, min_size=1, max_size=60, unique=True))
def test_degree_two_iff_local_minimum_with_sentinels(xs):
    ys = closed(xs)
    deg, _, _ = hvg.degrees(ys)
    for i in range(1, len(ys) - 1):
        assert (deg[i] == 2) == (ys[i - 1] > ys[i] < ys[i + 1])


def test_bare_degree_two_claim_is_false():
    """The claim as first written, refuted: (2, 1, 0) gives the 1 degree 2, no minimum."""
    deg, _, _ = hvg.degrees([2, 1, 0])
    assert deg[1] == 2 and not (2 > 1 < 0)


def test_exhaustive_permutations_up_to_8():
    """Both identities on all n! orderings for n <= 8 (46,233 sequences in total)."""
    checked = 0
    for n in range(1, 9):
        for perm in itertools.permutations(range(n)):
            e = hvg.hvg_edges(perm)
            left, right = hvg.records(perm)
            assert len(e) == 2 * n - left - right
            ys = closed(perm)
            deg, _, _ = hvg.degrees(ys)
            for i in range(1, n + 1):
                assert (deg[i] == 2) == (ys[i - 1] > ys[i] < ys[i + 1])
            checked += 1
    assert checked == sum(math.factorial(n) for n in range(1, 9))


def test_exact_iid_facts_by_enumeration():
    """Exact rational checks over all 9! orders of a 9-window.

    * P(middle node has degree 2) = 1/3: degree 2 is a local minimum, decided by 3 values.
    * P(middle node has out-degree 1) = 1/2: decided by its right neighbour alone.
    * E|E| = 2n - 2 H_n, because E[L] = E[R] = H_n for a uniformly random order.

    Degree 3 is NOT decided by any finite window (a long decreasing run can postpone the
    deciding value), so it is checked statistically below, not here.
    """
    from fractions import Fraction

    n, mid = 9, 4
    c2 = c_out1 = 0
    edge_total = 0
    total = 0
    for perm in itertools.permutations(range(n)):
        deg, out, _ = hvg.degrees(closed(perm))
        c2 += int(deg[mid + 1] == 2)
        c_out1 += int(out[mid + 1] == 1)
        edge_total += len(hvg.hvg_edges(perm))
        total += 1
    assert 3 * c2 == total
    assert 2 * c_out1 == total
    harmonic = sum(Fraction(1, k) for k in range(1, n + 1))
    assert Fraction(edge_total, total) == 2 * n - 2 * harmonic


def test_iid_law_statistically():
    rng = np.random.default_rng(20261102)
    x = rng.random(400_000)
    deg, out, _ = hvg.degrees(x)
    deg = hvg.interior(deg, 200)
    out = hvg.interior(out, 200)
    for k in range(2, 9):
        p_hat = np.mean(deg == k)
        p = float(hvg.iid_degree_law(k))
        assert abs(p_hat - p) < 5 * math.sqrt(p * (1 - p) / deg.size)
    for k in range(1, 8):
        p_hat = np.mean(out == k)
        p = float(hvg.iid_out_degree_law(k))
        assert abs(p_hat - p) < 5 * math.sqrt(p * (1 - p) / out.size)


def test_records_small():
    assert hvg.records([2, 1, 3]) == (2, 1)
    assert hvg.records([1, 3, 2]) == (2, 2)
    assert hvg.records([3, 1, 2]) == (1, 2)


def test_kl_flags_support_mismatch():
    p = np.array([5, 0, 3])
    q = np.array([4, 2, 0])
    assert hvg.kl_support_mismatch(p, q) == 2
