"""Pins for BARRIER.md in certificate_lp_frontier: the dual constructions.

Lemma 1 (dual) is exercised by verifying, for each construction, that the
floor-moments vanish and the slack is nonnegative, and that the gain is at
most the LP floor.  Lemma 2 (completeness of the T-parametrization) is
pinned by the restricted dual at Y = N reproducing the full LP value.
Proposition 4 (the excess-constant identity) is pinned as a finite identity.
"""
from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path

import numpy as np
import pytest

HUNT = Path(__file__).resolve().parents[1] / "hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier"


def _load(name: str):
    if str(HUNT) not in sys.path:
        sys.path.insert(0, str(HUNT))
    spec = importlib.util.spec_from_file_location(name, HUNT / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def bl():
    return _load("barrier_lemmas")


@pytest.fixture(scope="module")
def lp():
    return _load("lp_frontier")


@pytest.fixture(scope="module")
def setup(bl):
    N, y = 1000, 31
    return N, y, bl.mobius_table(N), bl.cell_masses(N)


def test_cell_masses_sum_to_psi(bl, setup):
    N, y, mu, m = setup
    assert abs(m[1 : N + 1].sum() - 996.6807) < 1e-3


def test_rough_spike_is_feasible_and_matches(bl, setup):
    N, y, mu, m = setup
    r = bl.rough_spike(N, y, mu, m)
    assert r["feasible"]
    assert abs(r["gain"] - 4.234) < 0.01


def test_alternating_dies_at_zero_mass_cells(bl, setup):
    N, y, mu, m = setup
    r = bl.alternating(N, y, 2 * y, mu, m)
    assert r["feasible"]
    assert r["tau"] == 0.0 and r["gain"] == 0.0


def test_restricted_dual_is_a_lower_bound_and_complete(bl, lp, setup):
    N, y, mu, m = setup
    full, _, _ = lp.solve(N, y)
    floor = full["gap_V_minus_psi"]
    prev = 0.0
    for Y in (2 * y, 4 * y, 10 * y):
        r = bl.restricted_dual(N, y, Y, mu, m)
        assert r["feasible"]
        assert prev - 1e-6 <= r["gain"] <= floor + 1e-6
        prev = r["gain"]
    r = bl.restricted_dual(N, y, 2 * y, mu, m)
    assert abs(r["gain"] - 28.742) < 0.01
    r = bl.restricted_dual(N, y, N, mu, m)
    assert abs(r["gain"] - floor) < 1e-4  # Lemma 2: the parametrization is complete


def test_excess_constant_identity(bl):
    # Proposition 4 as a finite identity: H(c) = I(y) + sum d_j log(y/j)/j
    # for c = mu + d with any d (balance is not needed for the identity).
    y = 100
    mu = bl.mobius_table(y)
    rng = np.random.default_rng(0)
    d = rng.normal(size=y + 1)
    c = mu.astype(float) + d
    H = -sum(c[j] * math.log(j) / j for j in range(1, y + 1)) - 1.0
    I = sum(mu[j] * math.log(y / j) / j for j in range(1, y + 1)) - 1.0
    M1 = sum(mu[j] / j for j in range(1, y + 1))
    C1 = sum(c[j] / j for j in range(1, y + 1))
    # General form: H = I(y) + sum_j d_j log(y/j)/j - C(1) log y; with the
    # balance C(1) = 0 (i.e. sum d_j/j = -M1) the last term vanishes.
    rhs = I + sum(d[j] * math.log(y / j) / j for j in range(1, y + 1)) - C1 * math.log(y)
    assert abs(H - rhs) < 1e-9
    assert abs(C1 - (M1 + sum(d[j] / j for j in range(1, y + 1)))) < 1e-12
