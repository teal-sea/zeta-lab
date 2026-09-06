"""The residue-class decomposition of the prime-pair error (hunts/prime_pair_error/residue.py).

What is pinned here, and why each pin is the shape it is:

1. **The exact identities are exact.** psi_2 = A_q + L_q + X_q + D_q is checked with
   psi_2 from a pure-Python pair count (no numpy, no FFT) and D_q from an independent
   direct convolution, so a defect in any one piece shows as a residual, not as a
   cancellation.  The four other exact facts (I2, I3, I4, the q = 1 specialisation)
   are each checked against a route that shares no code with the one under test.
2. **The modulo-3 formula is the q = 3 member of the family.**  The closed form in
   the character mod 3, which never forms residue-class sums of the centered
   function, must coincide with the general code to rounding.
3. **The coefficients are frozen.**  The prediction reads one-point data only: it is
   a function of Lambda, N, q and the singular series, and a test scrambles the pair
   structure of Lambda without touching its residue-class partial sums and checks that
   the prediction does not move.  The FROZEN table must hold the derived values.
4. **The recorded results reproduce.**  results_residue.json is recomputed at its
   smallest cutoff and the squared-error reductions must match to 1e-9 relative.

The hunt's vocabulary rules are enforced by tests/test_hunt_probe_discipline.py.
Nothing here bears on RH (docs/08).
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
HUNT = _REPO_ROOT / "hunts" / "prime_pair_error"
if str(HUNT) not in sys.path:
    sys.path.insert(0, str(HUNT))

import probe  # noqa: E402
import residue  # noqa: E402

N_SMALL = 3000


@pytest.fixture(scope="module")
def data():
    lam, lam_p = probe.von_mangoldt(N_SMALL)
    S = probe.singular_series(N_SMALL)
    psi2_py = np.array(probe.psi2_python(N_SMALL))[1:]           # pure Python, no numpy
    return lam, lam_p, S, psi2_py


def _direct_autocorr(f: np.ndarray, N: int) -> np.ndarray:
    """sum_{n <= N-k} f(n) f(n+k), k = 1..N, by explicit dot products (no FFT)."""
    return np.array([float(np.dot(f[: N + 1 - k], f[k : N + 1])) for k in range(1, N + 1)])


# ---------------------------------------------------------------------------
# 1. the exact identities
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("q", [1, 3, 30])
def test_I1_four_pieces_sum_to_the_pair_count(data, q):
    lam, _, _, psi2_py = data
    N = N_SMALL
    A, _ = residue.periodic_baseline(N, q)
    _, _, dprime = residue.model_and_centered(lam, N, q)
    L = residue.endpoint_terms(dprime, N, q)
    X = residue.exceptional_pairs(lam, N, q) if q > 1 else np.zeros(N)
    D = _direct_autocorr(dprime, N)
    assert np.max(np.abs(A + L + X + D - psi2_py)) < 1e-6


@pytest.mark.parametrize("q", [2, 3, 6, 30])
def test_I2_baseline_is_S_q_times_length_plus_bounded_periodic(q):
    N = 2001          # odd, so that rho_2 is not identically zero on even k
    k = np.arange(1, N + 1)
    A, rho = residue.periodic_baseline(N, q)
    # S_q by counting residue pairs directly, against the product of local factors
    red = residue.reduced_residues(q)
    phi = len(red)
    nu = residue.nu_table(q)
    S_count = q * nu[k % q] / phi ** 2
    assert np.max(np.abs(S_count - residue.S_q(k, q))) < 1e-12
    # A by brute force at a handful of k
    for kk in (1, 2, 6, 30, 31, 997, N - 1):
        n = np.arange(1, N - kk + 1)
        brute = (q / phi) ** 2 * np.sum((np.gcd(n, q) == 1) & (np.gcd(n + kk, q) == 1))
        assert abs(A[kk - 1] - brute) < 1e-9
    bound = (q / phi) ** 2 * nu[k % q]
    assert np.all(np.abs(rho) <= bound + 1e-9)
    assert np.max(np.abs(rho)) > 0.1                      # the bounded term is not trivially zero


def test_I3_singular_series_factors_over_the_modulus():
    N = 5000
    k = np.arange(1, N + 1)
    S = probe.singular_series(N)[1:]
    for q in (1, 2, 3, 5, 30, 210):
        Scop = residue.singular_series_coprime(N, q)[1:]
        assert np.max(np.abs(residue.S_q(k, q) * Scop - S)) < 1e-12, q
    # and the trial-division route agrees with the coprime sieve at q = 30 via the factorisation
    for kk in (2, 6, 14, 30, 210, 2310, 4998):
        s = probe.singular_series_python(kk)
        s30 = float(residue.S_q(np.array([kk]), 30)[0])
        assert abs(s30 * residue.singular_series_coprime(N, 30)[kk] - s) < 1e-12


def test_the_q1_member_is_the_first_pass_formula(data):
    lam, _, S, _ = data
    N = N_SMALL
    c1 = residue.correction(lam, N, 1, S)["c"]
    k = np.arange(1, N + 1)
    R = np.cumsum(lam[: N + 1]) - np.arange(N + 1)
    R[0] = 0.0
    formula = S[1 : N + 1] * (R[N] + R[N - k] - R[k])
    assert np.max(np.abs(c1 - formula)) < 1e-8
    assert np.max(np.abs(residue.original_correction(lam, N, S) - formula)) < 1e-8


def test_exceptional_pairs_by_brute_force(data):
    lam, _, _, _ = data
    N = 1200
    for q in (2, 3, 30):
        X = residue.exceptional_pairs(lam, N, q)
        brute = np.zeros(N)
        support = [n for n in range(1, N + 1) if lam[n] > 0]
        for n in support:
            for m in support:
                if m > n and (math.gcd(n, q) > 1 or math.gcd(m, q) > 1):
                    brute[m - n - 1] += lam[n] * lam[m]
        assert np.max(np.abs(X - brute)) < 1e-9, q
    assert np.max(residue.exceptional_pairs(lam, N, 30)) > 0


# ---------------------------------------------------------------------------
# 2. the modulo-3 formula is the q = 3 member
# ---------------------------------------------------------------------------

def test_chi3_closed_form_matches_the_general_code(data):
    lam, _, S, _ = data
    N = N_SMALL
    c3 = residue.correction(lam, N, 3, S)["c"]
    closed = residue.chi3_closed_form(lam, N, S)
    assert np.max(np.abs(closed - c3)) < 1e-7
    # the sign rule: on 3 | k the character term vanishes, and the two classes k = 1, 2
    # mod 3 carry opposite signs of the same profile
    k = np.arange(1, N + 1)
    chi = np.where(k % 3 == 1, 1.0, np.where(k % 3 == 2, -1.0, 0.0))
    diff = c3 - residue.correction(lam, N, 1, S)["c"]
    # the difference c3 - c1 on 3 | k has no character part: it is only R -> R' and the
    # bounded pieces, so its size is bounded by a few times log N times S(k) plus X_3
    on3 = (k % 3 == 0) & (k % 2 == 0)
    assert np.max(np.abs(diff[on3])) < 200 * S[1 : N + 1][on3].max()
    # on 3 not | k the character part is present: its correlation with chi(k) * profile is strong
    psi_chi = np.cumsum(lam[: N + 1] * np.where(np.arange(N + 1) % 3 == 1, 1.0, np.where(np.arange(N + 1) % 3 == 2, -1.0, 0.0)))
    prof = S[1 : N + 1] * chi * (psi_chi[N - k] - psi_chi[N] + psi_chi[k])
    off3 = (k % 3 != 0) & (k % 2 == 0) & (k < N)
    assert np.corrcoef(diff[off3], prof[off3])[0, 1] > 0.9


# ---------------------------------------------------------------------------
# 3. the coefficients are frozen and the prediction reads no pair data
# ---------------------------------------------------------------------------

def test_frozen_table_holds_the_derived_values():
    assert residue.FROZEN == {
        "q1_alpha_over_R_N": 1.0, "q1_beta_B": 0.0, "q1_gamma_R": 1.0,
        "coef_baseline_rho": 1.0, "coef_endpoint_L": 1.0, "coef_exceptional_X": 1.0,
    }
    assert residue.MODULI == (1, 3, 30)
    assert not set(residue.FRESH_CUTOFFS) & set(residue.FIRST_PASS_CUTOFFS)


def test_prediction_does_not_read_the_pair_structure(data):
    """Permute Lambda within each residue class mod 30 in a way that keeps every
    residue-class partial sum at the checked endpoints, and the prediction must not
    move, while the pair count itself does."""
    lam, _, S, _ = data
    N = 600
    rng = np.random.default_rng(7)
    lam2 = lam[: N + 1].copy()
    # swap the values at two primes in the same class mod 30 that sit inside (N/2, N):
    # the partial sums at x in {N} are unchanged, at x = k or N - k they change only for
    # k in a small window, so compare predictions on k outside that window
    idx = [n for n in range(N // 2 + 1, N) if lam2[n] > 0 and n % 30 == 1]
    a, b = idx[0], idx[1]
    lam2[a], lam2[b] = lam2[b], lam2[a]
    # the values are different primes' logs, so the swap changes the pair counts
    assert lam2[a] != lam[a]
    c_before = residue.correction(lam[: N + 1], N, 30, S)["c"]
    c_after = residue.correction(lam2, N, 30, S)["c"]
    k = np.arange(1, N + 1)
    window = ((k >= min(a, b)) & (k <= max(a, b))) | ((N - k >= min(a, b)) & (N - k <= max(a, b)))
    # the exceptional-pair term pairs a power of 2, 3 or 5 with a or b at O(log N) values of k
    exc = {int(n) for n in np.nonzero(lam[: N + 1] > 0)[0] if math.gcd(int(n), 30) > 1}
    touched = {abs(x - m) for x in (a, b) for m in exc} | {x + m for x in (a, b) for m in exc}
    window |= np.isin(k, sorted(touched))
    assert np.max(np.abs((c_after - c_before)[~window])) < 1e-9
    assert np.max(np.abs(residue.original_correction(lam2, N, S) - residue.original_correction(lam[: N + 1], N, S))[~window]) < 1e-9
    psi2_before = probe.psi2_fft(lam[: N + 1], N)
    psi2_after = probe.psi2_fft(lam2, N)
    assert np.max(np.abs(psi2_after - psi2_before)) > 1e-3


# ---------------------------------------------------------------------------
# 4. the recorded results reproduce
# ---------------------------------------------------------------------------

def test_results_file_reproduces_at_its_smallest_cutoff():
    path = HUNT / "results_residue.json"
    rec = json.loads(path.read_text())
    assert rec["frozen"] == residue.FROZEN
    assert rec["first_pass_overlap"] == []
    run = min(rec["runs"], key=lambda r: r["N"])
    N = run["N"]
    assert N == 200_000
    lam, lam_p = probe.von_mangoldt(N)
    S = probe.singular_series(N)
    fresh = residue.analyse(N, lam, lam_p, S, with_next=False)
    for q in ("1", "3", "30"):
        for key in ("reduction_all_k", "reduction_even_k", "posthoc_slope_e_on_c_even"):
            assert fresh["comparison"][q][key] == pytest.approx(run["comparison"][q][key], rel=1e-9), (q, key)
    assert fresh["E_over_N2log2N"] == pytest.approx(run["E_over_N2log2N"], rel=1e-12)
    assert fresh["T_chi3"]["T_measured"] == pytest.approx(run["T_chi3"]["T_measured"], rel=1e-9)
    # the checks recorded in the file must have passed at every cutoff
    for r in rec["runs"]:
        assert r["check_q1_equals_original_formula_maxabs"] < 1e-5
        assert max(r["check_identity_I1_maxabs"].values()) < 1e-5
        assert r["check_I3_S_eq_Sq_times_Scop_maxabs"] < 1e-12
        assert r["check_chi3_closed_form_vs_general_maxabs"] < 1e-5


def test_the_reductions_are_ordered_and_the_slopes_are_near_one():
    """The measured shape RESULTS.md reports: each refinement removes more of the
    squared error than the last, and the post-hoc slope of e on each correction is
    within ten percent of the derived value 1 at every fresh cutoff."""
    rec = json.loads((HUNT / "results_residue.json").read_text())
    for r in rec["runs"]:
        c = r["comparison"]
        assert c["1"]["reduction_all_k"] < c["3"]["reduction_all_k"] < c["30"]["reduction_all_k"], r["N"]
        for q in ("3", "30"):
            assert abs(c[q]["posthoc_slope_e_on_c_even"] - 1.0) < 0.1, (r["N"], q)
