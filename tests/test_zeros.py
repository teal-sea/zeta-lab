"""Tests for :mod:`zeta.zeros` — zero location and zero counting.

Ground truth used here:
  * the first ten ordinates γ_n to 20 significant digits,
  * N(100) = 29, N(1000) = 649,
  * Gram's law first fails at n = 126,
and, as an *independent oracle*, mpmath's own ``siegeltheta``, ``siegelz``,
``grampoint``, ``zetazero`` and ``backlunds`` (the last returns S(T)).
"""

from __future__ import annotations

import json
import math
import os

import pytest
from mpmath import mp

import zeta.zeros
from zeta.zeros import (
    DATA_DIR,
    THETA_ARGMIN,
    N_of_T,
    S_of_T,
    Z,
    first_n_zeros,
    gram_law_violations,
    gram_point,
    gram_points,
    riemann_von_mangoldt,
    rs_theta,
    verify_rh_up_to,
    zeros_by_sign_change,
    zeros_from_scratch,
)

# First ten zero ordinates, 20 significant digits.
FIRST_TEN = [
    "14.134725141734693790",
    "21.022039638771554993",
    "25.010857580145688763",
    "30.424876125859513210",
    "32.935061587739189691",
    "37.586178158825671257",
    "40.918719012147495187",
    "43.327073280914999519",
    "48.005150881167159727",
    "49.773832477672302182",
]


@pytest.fixture(autouse=True)
def _precision():
    """Run every test at 30 digits."""
    with mp.workdps(30):
        yield


# ---------------------------------------------------------------------------
# θ and Z against mpmath
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("t", [1, 7, 20, 50, 100, 1000])
def test_rs_theta_matches_siegeltheta(t):
    assert abs(rs_theta(t) - mp.siegeltheta(t)) < mp.mpf("1e-28")


def test_rs_theta_is_odd_and_zero_at_origin():
    assert rs_theta(0) == 0
    assert abs(rs_theta(-37) + rs_theta(37)) < mp.mpf("1e-28")


@pytest.mark.parametrize("t", [0, 10, 14.5, 100, 300])
def test_Z_matches_siegelz(t):
    assert abs(Z(t) - mp.siegelz(t)) < mp.mpf("1e-28")


def test_Z_at_zero_is_zeta_half():
    # Z(0) = e^{i·0} ζ(1/2) = ζ(1/2) = −1.4603545088095868…
    assert abs(Z(0) - mp.zeta(mp.mpf(1) / 2)) < mp.mpf("1e-28")


def test_Z_modulus_equals_zeta_modulus():
    # |Z(t)| = |ζ(1/2 + it)| is the whole reason Z is useful.
    for t in [3, 17, 55.5, 123]:
        assert abs(abs(Z(t)) - abs(mp.zeta(mp.mpc(0.5, t)))) < mp.mpf("1e-25")


# ---------------------------------------------------------------------------
# Gram points
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("n", [-1, 0, 1, 2, 10, 126, 134, 1000])
def test_gram_point_matches_mpmath(n):
    assert abs(gram_point(n) - mp.grampoint(n)) < mp.mpf("1e-25")


@pytest.mark.parametrize("n", [-1, 0, 5, 126])
def test_gram_point_solves_theta_eq_n_pi(n):
    """The defining property: θ(g_n) = n·π, and g_n > 7."""
    g = gram_point(n)
    assert g > 7
    assert abs(rs_theta(g) - n * mp.pi) < mp.mpf("1e-26")


def test_gram_point_rejects_n_below_minus_one():
    # min θ = −3.53097… = −1.12394π, so θ(t) = −2π has no solution with t > 7.
    with pytest.raises(ValueError):
        gram_point(-2)


def test_gram_points_range_is_inclusive():
    gs = gram_points(0, 3)
    assert len(gs) == 4
    assert gs == [gram_point(n) for n in (0, 1, 2, 3)]
    assert all(gs[i] < gs[i + 1] for i in range(3))  # θ increasing ⇒ g_n increasing


# ---------------------------------------------------------------------------
# zeros by sign change
# ---------------------------------------------------------------------------


def test_zeros_by_sign_change_finds_all_29_below_100():
    zs = zeros_by_sign_change(0, 100)
    assert len(zs) == 29
    assert all(zs[i] < zs[i + 1] for i in range(len(zs) - 1))


def test_first_ten_zeros_by_sign_change_match_ground_truth():
    """Measured max deviation is 9.425e-19 — which is exactly the truncation of
    the 20-digit strings above, not an error in the roots (see
    :func:`test_sign_change_zeros_beat_the_ground_truth_strings`)."""
    zs = zeros_by_sign_change(0, 100)
    for got, want in zip(zs[:10], FIRST_TEN):
        assert abs(got - mp.mpf(want)) < mp.mpf("2e-18")


def test_sign_change_zeros_beat_the_ground_truth_strings():
    """The 20-digit strings, not the module, are the accuracy bottleneck."""
    zs = zeros_by_sign_change(0, 60)
    with mp.workdps(60):
        ref = [mp.mpf(mp.im(mp.zetazero(k))) for k in range(1, 11)]
        assert max(abs(a - b) for a, b in zip(zs[:10], ref)) < mp.mpf("1e-23")
        # ... while the strings themselves are only good to ~1e-18:
        assert max(abs(mp.mpf(s) - b) for s, b in zip(FIRST_TEN, ref)) > mp.mpf("1e-19")


def test_sign_change_roots_actually_annihilate_Z():
    for r in zeros_by_sign_change(0, 100):
        assert abs(Z(r)) < mp.mpf("1e-20")


def test_zeros_by_sign_change_empty_below_first_zero():
    # γ_1 = 14.1347…, so there is nothing at all below 14.
    assert zeros_by_sign_change(0, 14) == []


# ---------------------------------------------------------------------------
# first_n_zeros, caching, and the from-scratch cross-check
# ---------------------------------------------------------------------------


def test_first_n_zeros_match_ground_truth():
    zs = first_n_zeros(10)
    assert len(zs) == 10
    for got, want in zip(zs, FIRST_TEN):  # measured max deviation 9.425e-19
        assert abs(got - mp.mpf(want)) < mp.mpf("2e-18")


def test_first_n_zeros_empty_for_non_positive_n():
    assert first_n_zeros(0) == []
    assert first_n_zeros(-3) == []


def test_first_n_zeros_cache_round_trips_bit_exactly(tmp_path, monkeypatch):
    """A cache miss writes zeros_<n>.json; reloading it is bit-identical."""
    monkeypatch.setattr(zeta.zeros, "DATA_DIR", str(tmp_path))

    fresh = first_n_zeros(12, cache=False)
    assert not os.path.exists(tmp_path / "zeros_12.json")  # cache=False writes nothing

    cached_write = first_n_zeros(12, cache=True)
    path = tmp_path / "zeros_12.json"
    assert path.exists()
    with open(path) as fh:
        blob = json.load(fh)
    assert blob["n"] == 12 and len(blob["zeros"]) == 12

    cached_read = first_n_zeros(12, cache=True)
    assert cached_read == cached_write  # bit-identical, not merely close
    assert all(abs(a - b) < mp.mpf("1e-28") for a, b in zip(fresh, cached_read))


def test_bigger_cache_serves_a_smaller_request(tmp_path, monkeypatch):
    """zeros_20.json answers a request for 8 zeros — no new file, exact prefix."""
    monkeypatch.setattr(zeta.zeros, "DATA_DIR", str(tmp_path))

    twenty = first_n_zeros(20, cache=True)
    eight = first_n_zeros(8, cache=True)
    assert eight == twenty[:8]
    assert not os.path.exists(tmp_path / "zeros_8.json")


def test_data_dir_points_into_the_repo():
    assert os.path.basename(DATA_DIR) == "data"


def test_zeros_from_scratch_cross_checks_zetazero_on_first_50():
    """The from-scratch Gram walk must reproduce mpmath.zetazero exactly."""
    scratch = zeros_from_scratch(50)
    engine = first_n_zeros(50)
    assert len(scratch) == 50
    assert max(abs(a - b) for a, b in zip(scratch, engine)) < mp.mpf("1e-20")


def test_zeros_from_scratch_matches_ground_truth():
    for got, want in zip(zeros_from_scratch(10), FIRST_TEN):  # measured 9.425e-19
        assert abs(got - mp.mpf(want)) < mp.mpf("2e-18")


# ---------------------------------------------------------------------------
# counting: N(T), S(T), Riemann–von Mangoldt
# ---------------------------------------------------------------------------


def test_N_of_100_is_29():
    assert N_of_T(100) == 29


@pytest.mark.parametrize(
    "T,expected",
    [(10, 0), (14, 0), (15, 1), (20, 1), (25, 2), (30, 3), (50, 10), (100, 29), (200, 79)],
)
def test_N_of_T_known_values(T, expected):
    assert N_of_T(T) == expected


def test_N_of_T_agrees_with_counting_the_zeros():
    """The argument principle and the sign-change scan must agree."""
    zs = zeros_by_sign_change(0, 100)
    assert N_of_T(100) == len([z for z in zs if z < 100]) == 29


def test_N_of_T_steps_by_one_across_a_zero():
    # γ_10 = 49.7738…
    assert N_of_T(49.7) == 9
    assert N_of_T(49.9) == 10


@pytest.mark.parametrize("T", [20, 50, 100, 300, 1000])
def test_S_of_T_matches_backlunds(T):
    """mpmath.backlunds(T) returns S(T) — an independent oracle."""
    assert abs(S_of_T(T) - mp.backlunds(T)) < mp.mpf("1e-20")


@pytest.mark.parametrize("T", [50, 100, 1000])
def test_S_of_T_is_the_defect_in_the_counting_formula(T):
    """S(T) = N(T) − 1 − θ(T)/π, exactly as advertised."""
    assert abs(S_of_T(T) - (N_of_T(T) - 1 - rs_theta(T) / mp.pi)) < mp.mpf("1e-20")


def test_riemann_von_mangoldt_within_one_of_true_count_at_1000():
    main = riemann_von_mangoldt(1000)
    assert N_of_T(1000) == 649
    assert abs(main - 649) < 1.0  # actual error 0.3838


@pytest.mark.parametrize("T", [100, 200, 500, 1000])
def test_riemann_von_mangoldt_tracks_N_of_T(T):
    assert abs(riemann_von_mangoldt(T) - N_of_T(T)) < 1.0


def test_riemann_von_mangoldt_non_positive_T():
    assert riemann_von_mangoldt(0) == 0.0
    assert riemann_von_mangoldt(-5) == 0.0


# ---------------------------------------------------------------------------
# Gram's law
# ---------------------------------------------------------------------------


def test_gram_law_first_fails_at_126():
    assert gram_law_violations(-1, 125) == []
    violations = gram_law_violations(-1, 140)
    assert violations[0] == 126
    assert 126 in violations


def test_gram_law_known_violation_list():
    # The classical first exceptions to Gram's law.
    assert gram_law_violations(-1, 250) == [126, 134, 195, 211, 232]


def test_gram_law_violation_means_wrong_sign_of_Z():
    g = gram_point(126)
    assert (-1) ** 126 * Z(g) < 0  # the law demands > 0
    g_ok = gram_point(125)
    assert (-1) ** 125 * Z(g_ok) > 0


# ---------------------------------------------------------------------------
# the Turing-style verification
# ---------------------------------------------------------------------------


def test_verify_rh_up_to_100_reports_all_on_line():
    r = verify_rh_up_to(100)
    assert r["all_on_line"] is True
    assert r["N_T"] == 29
    assert r["n_sign_changes"] == 29
    assert r["T"] == 100.0
    assert r["gram_violations"] == []
    for key in ("T", "n_sign_changes", "N_T", "all_on_line", "gram_violations"):
        assert key in r


def test_verify_rh_up_to_zeros_match_ground_truth():
    r = verify_rh_up_to(100)
    for got, want in zip(r["zeros"][:10], FIRST_TEN):
        assert abs(got - mp.mpf(want)) < mp.mpf("1e-15")


def test_verify_rh_up_to_50():
    r = verify_rh_up_to(50)
    assert r["all_on_line"] is True
    assert r["N_T"] == r["n_sign_changes"] == 10


@pytest.mark.slow
def test_verify_rh_up_to_300_crosses_first_gram_failures():
    r = verify_rh_up_to(300)
    assert r["all_on_line"] is True
    assert r["N_T"] == r["n_sign_changes"] == 138
    assert r["gram_violations"] == [126, 134]


# ---------------------------------------------------------------------------
# the precision contract
#
# Regression tests for a real defect: :mod:`zeta.core` exposes
# ``rs_theta(t, dps=30)`` / ``Z(t, dps=30)`` whose precision is pinned by a
# *default argument*.  Bound bare, they capped every result in this module at
# 30 digits regardless of the requested ``dps`` — silently for rs_theta/Z, and
# with a hard ``ValueError`` out of gram_point for dps >= 50.
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("d", [20, 30, 50, 80])
def test_rs_theta_delivers_the_requested_dps(d):
    got = rs_theta(100, dps=d)
    with mp.workdps(d + 25):
        assert abs(got - mp.siegeltheta(100)) < mp.mpf(10) ** (-(d - 2)) * 100


@pytest.mark.parametrize("d", [20, 30, 50, 80])
def test_Z_delivers_the_requested_dps(d):
    got = Z(20, dps=d)
    with mp.workdps(d + 25):
        assert abs(got - mp.siegelz(20)) < mp.mpf(10) ** (-(d - 2))


@pytest.mark.parametrize("d", [30, 50, 80])
def test_gram_point_delivers_the_requested_dps(d):
    g = gram_point(10, dps=d)  # this raised ValueError for d >= 50 before the fix
    with mp.workdps(d + 25):
        assert abs(g - mp.grampoint(10)) < mp.mpf(10) ** (-(d - 2)) * 100
        assert abs(mp.siegeltheta(g) - 10 * mp.pi) < mp.mpf(10) ** (-(d - 2)) * 100


@pytest.mark.parametrize("d", [50, 80])
def test_zero_finding_delivers_the_requested_dps(d):
    """γ₁ from a raw sign-change bracket, at 50 and 80 digits."""
    root = zeros_by_sign_change(14, 15, dps=d)[0]
    with mp.workdps(d + 25):
        assert abs(root - mp.im(mp.zetazero(1))) < mp.mpf(10) ** (-(d - 2)) * 100


@pytest.mark.parametrize(
    "fn,dps",
    [
        (lambda d: gram_points(0, 2, dps=d), 60),
        (lambda d: gram_law_violations(-1, 3, dps=d), 60),
        (lambda d: zeros_from_scratch(3, dps=d), 60),
        (lambda d: verify_rh_up_to(30, dps=d), 60),
        (lambda d: N_of_T(100, dps=d), 60),
        (lambda d: S_of_T(100, dps=d), 60),
    ],
)
def test_every_entry_point_survives_high_precision(fn, dps):
    assert fn(dps) is not None


def test_resolve_core_rejects_a_precision_capping_backend():
    """The guard that would have caught the defect in the first place."""
    local = zeta.zeros._rs_theta_local

    def capped(t, dps=30):  # honest to 30 digits, silently wrong beyond
        with mp.workdps(30):
            return +local(t)

    assert zeta.zeros._honours_precision(zeta.zeros._ambient(capped), local, (7, 100)) is False
    assert zeta.zeros._honours_precision(local, local, (7, 100)) is True


def test_resolve_core_rejects_a_sign_flipped_backend():
    local = zeta.zeros._rs_theta_local
    flipped = zeta.zeros._ambient(lambda t, dps=30: -local(t))
    assert zeta.zeros._honours_precision(flipped, local, (7, 100)) is False


def test_the_bound_theta_and_Z_agree_with_the_local_fallbacks():
    """Whichever backend won, it must equal the local reference implementation."""
    with mp.workdps(40):
        for t in (0, 7, 20, 100, 300.5):
            assert abs(zeta.zeros._THETA(t) - zeta.zeros._rs_theta_local(t)) < mp.mpf("1e-35")
            assert abs(zeta.zeros._Z(t) - zeta.zeros._Z_local(t)) < mp.mpf("1e-35")


# ---------------------------------------------------------------------------
# θ′, THETA_ARGMIN  (exported but previously never exercised)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("t", [8, 10, 50, 300.5, 1000])
def test_theta_prime_closed_form(t):
    """θ′(t) = ½[Re ψ(¼ + it/2) − log π] — the derivative gram_point's Newton uses."""
    analytic = (mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, mp.mpf(t) / 2))) - mp.log(mp.pi)) / 2
    numeric = mp.diff(mp.siegeltheta, mp.mpf(t))
    assert abs(analytic - numeric) < mp.mpf("1e-22")
    assert analytic > 0  # θ strictly increasing past the minimum


def test_theta_argmin_really_is_the_minimum_of_theta():
    tm = mp.mpf(THETA_ARGMIN)
    dtheta = (mp.re(mp.digamma(mp.mpc(mp.mpf(1) / 4, tm / 2))) - mp.log(mp.pi)) / 2
    assert abs(dtheta) < mp.mpf("1e-15")  # θ′ vanishes there
    for h in (mp.mpf("1e-3"), mp.mpf("1e-2"), mp.mpf(1)):
        assert rs_theta(tm) < rs_theta(tm + h)
        assert rs_theta(tm) < rs_theta(tm - h)
    assert abs(rs_theta(tm) - mp.mpf("-3.530972829016607437704")) < mp.mpf("1e-15")
    assert rs_theta(tm) / mp.pi < -1  # hence n = −1 is the smallest usable index


# ---------------------------------------------------------------------------
# N(T) against a second, independent argument-variation implementation
# ---------------------------------------------------------------------------


def _N_dense(T, m=200):
    """N(T) by *dense uniform* unwrapping along 2 → 2+iT → ½+iT.

    Deliberately different from :func:`zeta.zeros.S_of_T`, which uses adaptive
    bisection with a π/3 acceptance test — this one just takes many small steps
    and unwraps each, so the two share no logic beyond the contour itself.
    """
    T = mp.mpf(T)
    total = mp.mpf(0)
    prev = mp.arg(mp.zeta(mp.mpc(2, 0)))
    pts = [mp.mpc(2, T * k / 40) for k in range(1, 41)]
    pts += [mp.mpc(2 - mp.mpf(3) / 2 * k / m, T) for k in range(1, m + 1)]
    for p in pts:
        cur = mp.arg(mp.zeta(p))
        d = cur - prev
        while d > mp.pi:
            d -= 2 * mp.pi
        while d < -mp.pi:
            d += 2 * mp.pi
        total += d
        prev = cur
    return 1 + mp.siegeltheta(T) / mp.pi + total / mp.pi


@pytest.mark.parametrize("T", [37.3, 101.7, 250.5, 499.5, 1000.5, 1999.5])
def test_N_of_T_matches_a_dense_unwrapping(T):
    assert abs(_N_dense(T) - N_of_T(T)) < mp.mpf("0.02")


def test_N_of_T_straddles_every_one_of_the_first_ten_zeros():
    """N must be exactly k just below γ_k and k+1 just above — no off-by-one."""
    eps = mp.mpf("1e-6")
    for k, g in enumerate(first_n_zeros(10), start=1):
        assert N_of_T(g - eps) == k - 1
        assert N_of_T(g + eps) == k


def test_S_of_T_vertical_leg_needs_no_unwrapping():
    """|ζ(2+iy) − 1| ≤ ζ(2) − 1 = 0.6449… < 1, so arg ζ(2+iy) never wraps."""
    bound = mp.zeta(2) - 1
    for y in [0, 0.3, 1, 2, 5, 13, 50, 137, 1000]:
        assert abs(mp.zeta(mp.mpc(2, y)) - 1) <= bound
        assert abs(mp.arg(mp.zeta(mp.mpc(2, y)))) < mp.pi / 2


@pytest.mark.parametrize("T", [100.5, 300.5, 1000.5, 2000.5])
def test_riemann_von_mangoldt_error_is_exactly_minus_S(T):
    """N(T) = 1 + θ(T)/π + S(T) and RvM drops S plus a 1/(48πT) tail."""
    err = riemann_von_mangoldt(T) - N_of_T(T)
    assert abs(err + S_of_T(T)) < 3.0 / (48 * math.pi * T)


# ---------------------------------------------------------------------------
# the sign-change scan can only miss zeros, never invent them
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("n_samples", [20, 30, 40, 60])
def test_coarse_grids_only_miss_zeros_never_invent_them(n_samples):
    fine = zeros_by_sign_change(0, 100)
    coarse = zeros_by_sign_change(0, 100, n_samples=n_samples)
    assert len(coarse) < len(fine)  # a coarse grid really does miss some
    for c in coarse:  # but every root it does report is a genuine one
        assert min(abs(c - f) for f in fine) < mp.mpf("1e-18")


# ---------------------------------------------------------------------------
# Gram walk across the first failure of Gram's law
# ---------------------------------------------------------------------------


@pytest.mark.slow
def test_zeros_from_scratch_survives_the_gram_law_failure_at_126():
    """The branch the 50-zero cross-check never reaches: an empty Gram interval
    followed by one holding two zeros."""
    scratch = zeros_from_scratch(140)
    engine = first_n_zeros(140)
    assert len(scratch) == 140
    assert max(abs(a - b) for a, b in zip(scratch, engine)) < mp.mpf("1e-20")

    g125, g126, g127 = gram_point(125), gram_point(126), gram_point(127)
    assert len([z for z in scratch if g125 <= z < g126]) == 0
    assert len([z for z in scratch if g126 <= z < g127]) == 2


# ---------------------------------------------------------------------------
# verify_rh_up_to: reporting, the Gram range, and the failure branch
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("T", [3, 5, 9, 9.7, 10, 17.8, 17.9, 50])
def test_verify_rh_gram_range_stays_on_the_increasing_branch_and_below_T(T):
    """θ is *decreasing* below 6.28983…, so θ(T)/π is not an inverse there:
    θ(3)/π = −0.953 would otherwise "admit" g_{−1} = 9.6669 > 3."""
    n = verify_rh_up_to(T)["n_gram_max"]
    if n < -1:
        assert gram_point(-1) > T
    else:
        assert gram_point(n) <= T
        assert gram_point(n + 1) > T


def test_verify_rh_verbose_prints_a_report(capsys):
    verify_rh_up_to(50, verbose=True)
    out = capsys.readouterr().out
    assert "N(T)" in out
    assert "sign changes" in out
    assert "critical line" in out


def test_verify_rh_reports_disagreement_honestly(monkeypatch):
    """If the scan cannot reach N(T), nothing is claimed to be proved."""
    monkeypatch.setattr(zeta.zeros, "N_of_T", lambda T, dps=25: 999)
    r = verify_rh_up_to(20, max_samples=32)
    assert r["N_T"] == 999
    assert r["all_on_line"] is False
    assert r["n_sign_changes"] < 999


def test_zeros_from_scratch_verify_flag_is_a_real_check(monkeypatch):
    """verify=True must actually raise when the count comes out wrong."""
    monkeypatch.setattr(zeta.zeros, "N_of_T", lambda T, dps=25: 10_000)
    with pytest.raises(ArithmeticError):
        zeros_from_scratch(3, verify=True)
    assert len(zeros_from_scratch(3, verify=False)) == 3
