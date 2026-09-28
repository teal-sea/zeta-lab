"""Pins for hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier.

The LP floor of the factorial-certificate family at small sizes, the
prime-aware collapse to zero once the support exceeds the prime-looking
cells, the rigorous rough-spike lower bound, and the Selberg test-function
identity.  Each number is quoted in RESULTS.md; this is what keeps them true.
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
    spec = importlib.util.spec_from_file_location(name, HUNT / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def mods():
    if str(HUNT) not in sys.path:
        sys.path.insert(0, str(HUNT))
    return {n: _load(n) for n in ("lp_frontier", "lp_allcells_cg", "lp_prime_cells", "lp_dictionaries")}


def test_prime_blind_floor_at_1000_31(mods):
    out, c, u = mods["lp_frontier"].solve(1000, 31)
    assert out["W_min_on_cells"] >= 1 - 1e-9
    assert abs(out["psi_N"] - 996.6807) < 1e-3  # psi(1000)
    assert abs(out["gap_V_minus_psi"] - 62.923) < 0.01
    # The optimum is mu on an initial segment: (1,-1,-1,0,-1,1,-1,0,0,1).
    assert np.allclose(c[:10], [1, -1, -1, 0, -1, 1, -1, 0, 0, 1], atol=1e-7)
    # The primes are dual-feasible: sum_m psi(N/(jm)) = log floor(N/j)! for all j.
    assert out["prime_dual_residual"] < 1e-7


def test_prime_blind_floor_is_exact_mobius_at_full_support(mods):
    out, c, u = mods["lp_frontier"].solve(1000, 200)
    assert abs(out["gap_V_minus_psi"]) < 1e-6


def test_constraint_generation_matches_dense(mods):
    dense, _, _ = mods["lp_frontier"].solve(1000, 31)
    cg = mods["lp_allcells_cg"].solve(1000, 31)
    assert abs(cg["excess"] - dense["gap_V_minus_psi"]) < 1e-6
    assert cg["W_min_all_cells"] >= 1 - 1e-7


def test_prime_aware_floor_values_at_10000(mods):
    # Measured LP values only.  The zero at y = 158 is a fact about this
    # instance, not a consequence of y exceeding the cell count: Codex's
    # N = 27, y = 9 example (PR #203) has eight cells and minimum excess
    # log 2, so no counting argument is asserted here.
    pc = mods["lp_prime_cells"]
    a = pc.solve(10_000, 100)
    b = pc.solve(10_000, 158)
    assert a["n_cells"] == 135
    assert abs(a["excess"] - 106.895) < 0.01
    assert abs(a["excess"] - a["excess_direct"]) < 1e-6
    assert abs(b["excess"]) < 1e-6
    assert b["W_min_at_prime_cells"] >= 1 - 1e-7


def test_attainable_quotient_floor_matches_the_audit(mods):
    # Codex's T* (PR #203): constraints on Q_N only, no prime information.
    # 41.28216944 at (1000, 31) is their rational-certificate value; the
    # floating LP optimum agrees to 1e-3 and sits between P* and V*.
    import math

    from scipy.optimize import linprog

    pc = mods["lp_prime_cells"]
    N, y = 1000, 31
    lam = pc.mangoldt(N)
    r = int(math.isqrt(N))
    cells = np.unique(np.concatenate([np.arange(1, r + 1), N // np.arange(2, r + 1)]))
    cells = cells[cells < N]
    j = np.arange(1, y + 1)
    L = pc.log_factorial(N // j)
    A = (cells[:, None] // j[None, :]).astype(float)
    res = linprog(L, A_ub=-A, b_ub=-np.ones(cells.size), bounds=(-1e6, 1e6), method="highs-ds")
    T = float(res.fun) - float(lam.sum())
    assert abs(T - 41.282) < 1e-2
    full, _, _ = mods["lp_frontier"].solve(N, y)
    assert T <= full["gap_V_minus_psi"] + 1e-6


def test_rough_spike_lower_bound_is_below_the_lp(mods):
    cg = mods["lp_allcells_cg"]
    N, y = 1000, 31
    lam = cg.mangoldt(N)
    psi = np.cumsum(lam)
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    m = np.arange(y + 1, N + 1)
    rough = m[spf[m] > y]
    bound = float(np.sum(psi[N // rough] - psi[N // (rough + 1)]))
    assert abs(bound - 4.234) < 0.01
    dense, _, _ = mods["lp_frontier"].solve(N, y)
    assert bound <= dense["gap_V_minus_psi"]


def test_selberg_identity_holds(mods):
    assert abs(mods["lp_dictionaries"].check_selberg_identity(3000)) < 1e-6


def test_selberg_dictionary_does_not_lose(mods):
    d = mods["lp_dictionaries"]
    plain = d.solve(1000, 31, None, False)
    with_s = d.solve(1000, 31, None, True)
    assert abs(plain["excess"] - 62.923) < 0.01
    assert with_s["excess"] <= plain["excess"] + 1e-6
    assert with_s["W_min_all_cells"] >= 1 - 1e-6
