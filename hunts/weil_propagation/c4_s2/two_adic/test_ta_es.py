"""E_S / theta_S matrix entries on the shared CCM basis, pinned.

Tolerances are measured deviations at dps 40 (see RESULTS.md s3), rounded
up by one to two orders of magnitude:
  closed form C vs quadrature (quad at dps 50)  measured <= 2.1e-42, tol 1e-39
  Wp from C vs galerkin.py                      measured <= 4.5e-40, tol 5e-39
  identity -Wp = log2 (Gram(Theta) - 3/2 I)     measured <= 1.2e-41, tol 1e-39
  E_S Gram closed form vs operator series       measured <= 4.6e-41, tol 5e-39
"""

from __future__ import annotations

import json
import os
import sys

import pytest
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_es as E  # noqa: E402
import ta_run_es as R  # noqa: E402

DPS = 40
CS = ("2.2", "2.5", "2.9")


def _maxdiff(A, B):
    return max(abs(A[i, j] - B[i, j]) for i in range(A.rows) for j in range(A.cols))


@pytest.mark.parametrize("c", CS)
def test_shift_correlation_closed_form_matches_quadrature(c):
    N = 8
    with mp.workdps(DPS):
        C = E.shift_corr(mp.mpf(c), N, DPS)
        dev = max(
            abs(C[m + N, n + N] - E.shift_corr_quad(mp.mpf(c), m, n, DPS + 10))
            for m in (-8, -3, 0, 2, 8)
            for n in (-8, -1, 0, 5, 8)
        )
    assert dev < mp.mpf("1e-39")


def test_shift_correlation_vanishes_without_overlap():
    with mp.workdps(DPS):
        C = E.shift_corr(mp.mpf("1.9"), 4, DPS)
        assert max(abs(C[i, j]) for i in range(9) for j in range(9)) == 0
        C2 = E.shift_corr(mp.mpf("2.9"), 4, DPS, k=2)  # 2 log 2 > log 2.9
        assert max(abs(C2[i, j]) for i in range(9) for j in range(9)) == 0


@pytest.mark.parametrize("c", CS)
def test_prime_block_is_the_shift_correlation(c):
    """Wp = (log 2 / sqrt 2)(C + C^*) against the independent galerkin.py block."""
    N = 8
    with mp.workdps(DPS):
        dev = _maxdiff(E.prime_block_from_C(mp.mpf(c), N, (1,), DPS), E.galerkin_prime_block(mp.mpf(c), N, DPS))
    assert dev < mp.mpf("5e-39")


@pytest.mark.parametrize("c", CS)
@pytest.mark.parametrize("alphas", [(1,), (1, 1), (-1,), (1j,)])
def test_prime_atom_equals_theta_gram_defect(c, alphas):
    """-Wp_alpha = log 2 (Gram(Theta_alpha) - sum_j (1 + |alpha_j|^2/2) I), 2 < c < 4."""
    with mp.workdps(DPS):
        assert E.identity_defect(mp.mpf(c), 8, alphas, DPS) < mp.mpf("1e-39")


@pytest.mark.parametrize("c", ("2.2", "2.9"))
@pytest.mark.parametrize("alpha", [1, -1, 1j])
def test_es_gram_closed_form_matches_series(c, alpha):
    with mp.workdps(DPS):
        dev = _maxdiff(E.es_gram_series(mp.mpf(c), 6, alpha, DPS, kmax=140), E.es_gram(mp.mpf(c), 6, (alpha,), DPS))
    assert dev < mp.mpf("5e-39")


def test_three_term_forms_refuse_windows_outside_2_4():
    with pytest.raises(ValueError):
        E.theta_gram(mp.mpf("4.5"), 4, (1,), DPS)
    with pytest.raises(ValueError):
        E.es_gram(mp.mpf("1.5"), 4, (1,), DPS)


@pytest.fixture(scope="module")
def cells():
    with open(os.path.join(HERE, "ta_es_cells.json")) as fh:
        return json.load(fh)


def test_cell_json_covers_the_mission_cells(cells):
    got = {(r["c"], r["N"]) for r in cells["cells"]}
    assert got == {(c, N) for c in CS for N in (8, 16, 32)}
    assert all(r["dps"] == 40 for r in cells["cells"])


@pytest.mark.parametrize("c,N", [("2.2", 8), ("2.5", 16), ("2.9", 32)])
def test_cell_json_reproduces(cells, c, N):
    fresh = R.cell(c, N)
    stored = next(r for r in cells["cells"] if r["c"] == c and r["N"] == N)
    for key in ("theta_gram_eig_min", "theta_gram_eig_max", "prime_block_eig_min", "prime_block_eig_max"):
        assert abs(mp.mpf(fresh[key]) - mp.mpf(stored[key])) < mp.mpf("1e-18")


@mp.workdps(40)
def test_theta_spectrum_inside_the_cauchy_schwarz_band_and_reaches_it(cells):
    """JSON strings carry 20 significant digits, hence the 1e-19 slack."""
    lo = mp.mpf(3) / 2 - 1 / mp.sqrt(2)
    hi = mp.mpf(3) / 2 + 1 / mp.sqrt(2)
    for r in cells["cells"]:
        assert mp.mpf(r["theta_gram_eig_min"]) >= lo - mp.mpf("1e-19")
        assert mp.mpf(r["theta_gram_eig_max"]) <= hi + mp.mpf("1e-19")
        # prime block = -log 2 (theta - 3/2): its ends are +-log2/sqrt2 at most
        assert abs(mp.mpf(r["prime_block_eig_min"])) <= mp.log(2) / mp.sqrt(2) + mp.mpf("1e-19")
    # at N = 32 the ends sit on the band to the stated digits (measured)
    reach = {"2.2": mp.mpf("1e-9"), "2.5": mp.mpf("1e-18"), "2.9": mp.mpf("1e-18")}
    for r in cells["cells"]:
        if r["N"] == 32:
            assert abs(mp.mpf(r["theta_gram_eig_min"]) - lo) < reach[r["c"]]
            assert abs(mp.mpf(r["theta_gram_eig_max"]) - hi) < reach[r["c"]]
