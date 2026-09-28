"""Tests for zeta.heatflow, heat flow on Ξ and the de Bruijn–Newman constant.

Every tolerance here is one that was measured on this machine, not guessed.
Where a check is only good to k digits, the test says so.
"""

from __future__ import annotations

import math

import numpy as np
import pytest
from mpmath import mp

from zeta.heatflow import (
    H0_RELATION,
    H0_vs_Xi,
    H_t,
    PHI_STRIP,
    Phi,
    Phi_is_even_defect,
    Xi_reference,
    heat_equation_residual,
    lambda_facts,
    polynomial_heat_flow,
    recommended_dps,
    track_zeros,
    zero_gap_statistics,
    zeros_of_H_t,
)


def _xi_oracle(T, guard=60):
    """ξ(1/2 + iT) computed from scratch with mpmath, independent of zeta.heatflow."""
    with mp.workdps(mp.dps + guard):
        s = mp.mpf(1) / 2 + 1j * mp.mpmathify(T)
        return mp.mpmathify(
            mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
        )

# First 10 zeta zero ordinates (ground truth, independent of anything computed here).
GAMMA = [
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


# --------------------------------------------------------------------------- #
#  Phi
# --------------------------------------------------------------------------- #

def test_phi_is_even_relative_where_meaningful():
    """Φ(u) = Φ(−u) for the *unfolded* series, judged RELATIVELY.

    The absolute defect sits at the rounding floor (~2e-41 at dps = 40) for every
    u, including u = 2 where Φ(2) ≈ 9e-4059, so an absolute-tolerance assertion
    out there cannot fail and proves nothing.  The relative defect is the quantity
    that can fail; measured at dps = 40 it is 7.5e-41 (u=0.1), 5.0e-38 (u=0.37),
    1.0e-34 (u=0.5), and it blows past 1 by u ≈ 0.9.
    """
    for u, tol in [(0.1, -38), (0.37, -35), (0.5, -32)]:
        assert Phi_is_even_defect(u, dps=40, relative=True) < mp.mpf(10) ** tol


def test_phi_raw_series_cancellation_is_real_and_documented():
    """The reason Phi() folds: the raw series at u < 0 is noise of the wrong sign.

    Pins the caveat in ``Phi_is_even_defect``'s docstring so it cannot silently
    become false, and guards against anyone "simplifying" the folding away.
    """
    from zeta.heatflow import _phi_series

    raw = _phi_series(mp.mpf(-1), None, 40)
    assert raw < 0                      # wrong sign
    assert abs(raw) > mp.mpf(10) ** -45  # and ~1e29 times too large
    assert Phi_is_even_defect(1.0, dps=40, relative=True) > mp.mpf(10) ** 20


def test_phi_is_positive_and_exactly_even_after_folding():
    """REGRESSION: Phi() used to return negative garbage for u <~ −0.85.

    ``Phi(-1.0)`` returned −2.73e-41 where the true value is +5.10e-70, and
    ``Phi(-3.0)`` returned −1.36e-39 where the truth is +1.7e-222046, despite the
    docstring promising strict positivity.  Folding through the exact identity
    Φ(u) = Φ(−u) fixes it and makes evenness bit-exact.
    """
    for u in [0.0, 0.1, 0.5, 0.9, 1.0, 1.5, 3.0, 6.0]:
        assert Phi(u, dps=40) > 0
        assert Phi(-u, dps=40) > 0
        assert Phi(-u, dps=40) == Phi(u, dps=40)  # bit-identical, not merely close


def test_phi_matches_nsum_on_the_left_half_line():
    """Folded Phi agrees with a *properly provisioned* mpmath.nsum oracle, u < 0.

    REGRESSION, of the test itself.  The oracle used to run at a flat dps = 120,
    but the unfolded series at u < 0 cancels ~π e^{4|u|}/ln 10 digits: 369 of them
    at u = −1.4, where the dps-120 nsum returned −3.2e-220 against a true value of
    +6.4e-363, the old oracle was pure noise there and the assertion compared the
    module against garbage.  The oracle needs dps = 40 + (digits cancelled), per u.

    Tolerance is modelled, not guessed: at dps = 40 the exponent argument
    π n² e^{4|u|} carries an absolute error ≈ π e^{4|u|}·10^{−40}, which becomes
    the relative error of the result, so the per-u bound is
    (1 + π e^{4|u|})·10^{−38} (two digits of slack).  Measured: 5.1e-41 (u=−0.3),
    1.1e-40 (−0.7), 2.1e-39 (−1.0), 1.2e-38 (−1.4), that last one exceeds the old
    blanket 1e-38, so the flat tolerance was also wrong.
    """
    for u in [-0.3, -0.7, -1.0, -1.4]:
        got = Phi(u, dps=40)
        cancel = int(mp.pi * mp.exp(4 * abs(mp.mpf(u))) / mp.log(10)) + 1
        with mp.workdps(40 + cancel):
            uu = mp.mpf(u)
            want = mp.nsum(
                lambda n: (2 * mp.pi**2 * n**4 * mp.exp(9 * uu)
                           - 3 * mp.pi * n**2 * mp.exp(5 * uu))
                * mp.exp(-mp.pi * n**2 * mp.exp(4 * uu)),
                [1, mp.inf],
            )
            tol = (1 + mp.pi * mp.exp(4 * abs(uu))) * mp.mpf(10) ** -38
            rel = abs(got - want) / abs(want)
        assert rel < tol, (u, rel, tol)


def test_phi_complex_strip():
    """Φ's series converges only on |Im u| < π/8; outside it must raise, not guess.

    REGRESSION 1: ``Phi(0.5j)`` used to return −1.29e41 − 1.21e41j where the series
    diverges outright (relative error ~1e157), because the term count was derived
    from e^{4·Re u} instead of Re(e^{4u}) = e^{4Re u}·cos(4 Im u).

    REGRESSION 2: ``Phi(mp.mpc(0, str(math.pi/8)))`` used to HANG (~7.5e8 terms,
    hours of CPU) instead of raising: float(π/8) rounds 1.5e-17 *below* the true
    boundary, so the argument is inside the open strip and sails past the strip
    check, but the term count diverges like (π/8 − |Im u|)^{−1/2} there.  The
    ``_MAX_TERMS`` cap must reject it in finite time.
    """
    assert PHI_STRIP == pytest.approx(math.pi / 8)
    # inside the strip: agrees with nsum
    for u in [mp.mpc("0.2", "0.1"), mp.mpc(0, "0.3"), mp.mpc("0.1", "0.35")]:
        got = Phi(u, dps=30)
        with mp.workdps(90):
            want = mp.nsum(
                lambda n: (2 * mp.pi**2 * n**4 * mp.exp(9 * u)
                           - 3 * mp.pi * n**2 * mp.exp(5 * u))
                * mp.exp(-mp.pi * n**2 * mp.exp(4 * u)),
                [1, mp.inf],
            )
        assert abs(got - want) / abs(want) < mp.mpf(10) ** -28
    # on/beyond the boundary: ValueError from the strip check
    # (0.3927 > pi/8 = 0.39269908...; the old third case str(math.pi/8) is NOT
    # outside the open strip and is exercised separately below)
    for u in [mp.mpc(0, "0.5"), mp.mpc("0.2", "1.0"), mp.mpc(0, "0.3927")]:
        with pytest.raises(ValueError, match="pi/8"):
            Phi(u, dps=30)
    # inside the strip but too close to the boundary: term cap, not a hang
    with pytest.raises(ValueError, match="refusing rather than hanging"):
        Phi(mp.mpc(0, str(math.pi / 8)), dps=30)


def test_phi_positive_and_decaying():
    """Φ > 0 everywhere, and super-exponentially small by u = 1."""
    vals = [Phi(u, dps=30) for u in [0.0, 0.1, 0.3, 0.5, 0.8]]
    assert all(v > 0 for v in vals)
    # strictly decreasing on u > 0 in this range
    assert all(vals[i] > vals[i + 1] for i in range(len(vals) - 1))
    assert Phi(1.0, dps=30) < mp.mpf(10) ** -20
    assert Phi(1.5, dps=40) < mp.mpf(10) ** -250


def test_phi_value_at_zero():
    """Φ(0) against direct term-by-term summation."""
    got = Phi(0, dps=30)
    with mp.workdps(30):
        want = mp.nsum(
            lambda n: (2 * mp.pi**2 * n**4 - 3 * mp.pi * n**2) * mp.exp(-mp.pi * n**2),
            [1, mp.inf],
        )
    assert abs(got - want) < mp.mpf(10) ** -25


def test_phi_terms_argument_converged():
    """Explicit `terms` beyond the automatic cutoff changes nothing."""
    assert abs(Phi(0.2, terms=8, dps=30) - Phi(0.2, terms=40, dps=30)) < mp.mpf(10) ** -28


# --------------------------------------------------------------------------- #
#  The H_0 <-> Xi relation
# --------------------------------------------------------------------------- #

def test_H0_vs_Xi_relation_is_one_eighth_and_one_half():
    """H₀(z) = (1/8)·Ξ(z/2), with c and a *fitted*, not assumed.

    Measured at dps = 40 over real z ∈ [0,100] plus two complex probes:
        c_measured - 1/8            =  1.7e-41
        a_from_curvature  - 1/2     = -2.9e-41
        a_from_first_zero - 1/2     = -2.8e-32   (limited by zeta.zeros)
        max_residual (vs local xi)  =  7.9e-42   (this module's quadrature)
        max_residual (vs zeta.core) =  2.9e-33   (limited by zeta.core.Xi)
    """
    res = H0_vs_Xi(dps=40)
    assert res["c_rational"] == (1, 8)
    assert res["a_rational"] == (1, 2)
    # the raw fitted values land on the rationals to ~full precision
    assert abs(res["c_measured"] - mp.mpf(1) / 8) < mp.mpf(10) ** -35
    assert abs(res["a_measured"] - mp.mpf(1) / 2) < mp.mpf(10) ** -35
    assert res["max_residual"] < mp.mpf(10) ** -38
    assert "1/8" in res["relation"] and "1/2" in res["relation"]
    # the two independent determinations of `a` agree
    assert res["a_from_first_zero"] is not None
    assert abs(res["a_from_curvature"] - res["a_from_first_zero"]) < mp.mpf(10) ** -20
    # cross-check against the sibling zeta.core, whose own accuracy (~1e-32)
    # is the binding constraint here -- not ours
    assert res["max_residual_vs_sibling"] < mp.mpf(10) ** -30


ZS = [0, 1, 3.5, 14, 30, 60, 100, mp.mpc(5, 1), mp.mpc(28, 0.5), mp.mpc(2, -3)]


def test_H0_equals_Xi_over_8_pointwise_local():
    """Direct pointwise check of H₀(z) = Ξ(z/2)/8, including complex z.

    Against this module's own high-precision ξ, so the residual measures the
    quadrature and nothing else: measured max 7.9e-42 at dps = 40.
    """
    with mp.workdps(40):
        for z in ZS:
            lhs = H_t(z, 0, dps=40)
            rhs = Xi_reference(mp.mpc(z) / 2, backend="local") / 8
            assert abs(lhs - rhs) < mp.mpf(10) ** -38


def test_H0_equals_Xi_over_8_pointwise_sibling():
    """Same identity, cross-checked against the sibling zeta.core.

    Looser on purpose: zeta.core.Xi carries a fixed ~1e-32 absolute error, so the
    residual here (measured 1.3e-33) is bounded by *its* accuracy, not ours.
    """
    with mp.workdps(40):
        for z in ZS:
            lhs = H_t(z, 0, dps=40)
            rhs = Xi_reference(mp.mpc(z) / 2) / 8
            assert abs(lhs - rhs) < mp.mpf(10) ** -30


def test_H0_is_real_and_even_on_real_axis():
    with mp.workdps(30):
        for z in [0.7, 5, 28.5, 61]:
            h_pos = H_t(z, 0, dps=30)
            h_neg = H_t(-z, 0, dps=30)
            assert abs(mp.im(h_pos)) < mp.mpf(10) ** -28
            assert abs(h_pos - h_neg) < mp.mpf(10) ** -28


def test_cached_and_adaptive_quadrature_agree():
    """The fast memoised rule matches mpmath.quadgl (measured worst 1.1e-31 at dps = 30).

    The worst case is z = 2−3i (1.1e-31), not any of the real ones; the previous
    tolerance of 1e-30 held only because that point was not sampled here.
    """
    with mp.workdps(30):
        for z, t in [
            (0, 0), (28.27, 0), (60, 0), (100, 0), (150, 0.3),
            (60, -0.4), (mp.mpc(30, 2), 0.1), (mp.mpc(2, -3), 0),
        ]:
            a = H_t(z, t, dps=30, quad="cached")
            b = H_t(z, t, dps=30, quad="adaptive")
            assert abs(a - b) < mp.mpf(10) ** -29


def test_H_t_converges_with_dps():
    """REGRESSION: raising dps must actually buy digits.

    The panel count used to depend only on |z|, so the composite Gauss rule had a
    fixed discretisation floor: H₀(30) stalled at an absolute error of 5.2e-58 at
    dps = 60 and then got *worse* (1.6e-56 at dps = 80, 1.1e-55 at dps = 100),
    because more digits widen the integration limit without adding panels.
    Measured after the fix: 1.6e-33 / 8.4e-43 / 2.0e-63 / 5.6e-83.

    Asserted against 10^{−(dps−2)}, the figure the module docstring promises,
    with the oracle ξ(1/2+iz/2)/8 built from scratch at dps + 80.
    """
    for z in (0, 30, 100):
        errs = []
        for dps in (30, 40, 60, 80):
            with mp.workdps(dps + 80):
                ref = _xi_oracle(mp.mpf(z) / 2, guard=0) / 8
                err = abs(mp.mpmathify(H_t(z, 0, dps=dps)) - ref)
            assert err < mp.mpf(10) ** (-(dps - 2)), f"z={z} dps={dps} err={err}"
            errs.append(err)
        # and it must actually improve, not merely stay under a loose bound
        for a, b in zip(errs, errs[1:]):
            assert b < a


def test_H_t_rejects_unknown_quad():
    with pytest.raises(ValueError):
        H_t(1, 0, quad="simpson")


# --------------------------------------------------------------------------- #
#  Heat equation
# --------------------------------------------------------------------------- #

def test_heat_equation_residual_is_small():
    """∂H/∂t + ∂²H/∂z² = 0 (backward heat equation).

    Measured residuals at dps = 30, h = 1e-6: 1.6e-18, 1.0e-18, 3.4e-19.
    Asserted at 1e-14, the finite-difference floor, not the quadrature floor.
    """
    for z, t in [(3, 0), (10, 0.2), (28, -0.1), (5, 0.5)]:
        assert heat_equation_residual(z, t, dps=30) < mp.mpf(10) ** -14


def test_heat_equation_sign_is_backward_not_forward():
    """∂H/∂t and ∂²H/∂z² are exact negatives, and both are genuinely non-zero.

    This is what pins the sign: if the convention were the forward heat equation
    the *difference*, not the sum, would vanish.
    """
    with mp.workdps(30):
        h = mp.mpf(10) ** -6
        z, t = mp.mpf(10), mp.mpf("0.2")
        dH_dt = (H_t(z, t + h, dps=30) - H_t(z, t - h, dps=30)) / (2 * h)
        d2H_dz2 = (
            H_t(z + h, t, dps=30) - 2 * H_t(z, t, dps=30) + H_t(z - h, t, dps=30)
        ) / h**2
        assert abs(dH_dt) > mp.mpf(10) ** -6          # not a trivially-zero check
        assert abs(dH_dt + d2H_dz2) < mp.mpf(10) ** -14   # backward: sum vanishes
        assert abs(dH_dt - d2H_dz2) > mp.mpf(10) ** -6    # forward would be wrong


# --------------------------------------------------------------------------- #
#  Zeros of H_0 are the rescaled zeta ordinates
# --------------------------------------------------------------------------- #

def test_zeros_of_H0_match_zeta_ordinates():
    """Real zeros of H₀ on [20,105] are exactly z = 2γ_n.

    Measured max error 1.3e-19 vs mpmath.zetazero at dps = 30, and 1.8e-18 vs the
    20-digit literals below (that 1.8e-18 is the *literals'* resolution, not ours:
    2*gamma_1 = 28.269450283469387580 has only 19 significant digits).
    Required by the brief: 1e-8.
    """
    zs = zeros_of_H_t(0, 20, 105, dps=30)
    assert len(zs) == 10
    with mp.workdps(30):
        for z, g in zip(zs, GAMMA):
            assert abs(z - 2 * mp.mpf(g)) < mp.mpf(10) ** -8


def test_zeros_of_H0_cross_check_against_zeta_zeros_module():
    """Same check, but against zeta.zeros.first_n_zeros / mpmath.zetazero."""
    from zeta.heatflow import _reference_ordinates

    zs = zeros_of_H_t(0, 20, 105, dps=30)
    gammas = _reference_ordinates(len(zs))
    with mp.workdps(30):
        for z, g in zip(zs, gammas):
            assert abs(z - 2 * g) < mp.mpf(10) ** -8


@pytest.mark.slow
def test_zero_count_matches_riemann_von_mangoldt():
    """29 zeta zeros have 0 < γ < 100, so H₀ has 29 zeros on 0 < z < 200."""
    zs = zeros_of_H_t(0, 0.001, 200, dps=recommended_dps(200, 12))
    assert len(zs) == 29


# --------------------------------------------------------------------------- #
#  Forward flow repels: the minimum gap strictly increases
# --------------------------------------------------------------------------- #

@pytest.mark.slow
def test_forward_flow_strictly_increases_min_gap():
    """min gap of consecutive real zeros of H_t is strictly increasing in t.

    Measured on [20,105] (first 10 zeros):
        t = -0.3 -> 3.28939,  t = -0.1 -> 3.45836,  t = 0 -> 3.53736,
        t = +0.1 -> 3.61308,  t = +0.3 -> 3.75556,  t = +0.6 -> 3.94962.
    """
    ts = [-0.3, -0.1, 0.0, 0.1, 0.3, 0.6]
    mins = [zero_gap_statistics(t, 20, 105, dps=30)["min_gap"] for t in ts]
    for a, b in zip(mins, mins[1:]):
        assert b > a
    assert all(m > 0 for m in mins)
    assert abs(mins[2] - mp.mpf("3.53736319301")) < mp.mpf("1e-9")


def test_zero_gap_statistics_shape():
    st = zero_gap_statistics(0.0, 20, 105, dps=30)
    assert st["n_zeros"] == 10
    assert len(st["gaps"]) == 9
    assert st["min_gap"] <= st["mean_gap"] <= st["max_gap"]
    assert st["window"] == (mp.mpf(20), mp.mpf(105))


# --------------------------------------------------------------------------- #
#  Zero tracking
# --------------------------------------------------------------------------- #

@pytest.mark.slow
def test_track_zeros_trajectories(tmp_path, monkeypatch):
    """Zeros stay real over t ∈ [−0.4, 0.6] and the spread widens with t."""
    import zeta.heatflow as hf

    monkeypatch.setattr(hf, "_DATA_DIR", tmp_path)
    ts = [-0.4, -0.2, 0.0, 0.2, 0.4, 0.6]
    res = track_zeros(ts, z_max=105.0, n_zeros=10, dps=30, use_cache=False)

    assert res["zeros"].shape == (6, 10)
    assert np.all(res["n_real"] == 10)
    assert not np.any(np.isnan(res["zeros"]))
    # min gap and overall spread both increase monotonically with t
    assert np.all(np.diff(res["min_gap"]) > 0)
    assert np.all(np.diff(res["spread"]) > 0)
    # the t = 0 row reproduces 2*gamma_n
    i0 = list(res["t_values"]).index(0.0)
    for z, g in zip(res["zeros"][i0], GAMMA):
        assert abs(z - 2 * float(g)) < 1e-8


def test_track_zeros_cache_roundtrip(tmp_path, monkeypatch):
    import zeta.heatflow as hf

    monkeypatch.setattr(hf, "_DATA_DIR", tmp_path)
    ts = [0.0, 0.2]
    a = track_zeros(ts, z_max=60.0, n_zeros=3, dps=30)
    assert a["source"] == "computed"
    b = track_zeros(ts, z_max=60.0, n_zeros=3, dps=30)
    assert b["source"] == "cache"
    assert np.allclose(a["zeros"], b["zeros"], equal_nan=True)


def test_track_zeros_raises_when_window_too_small():
    with pytest.raises(ValueError, match="raise z_max"):
        track_zeros([0.0], z_max=40.0, n_zeros=10, dps=30, use_cache=False)


# --------------------------------------------------------------------------- #
#  Polynomial illustration
# --------------------------------------------------------------------------- #

def test_polynomial_root_ode_matches_exact_heat_evolution():
    """RK4 on dr_i/dt = +2Σ1/(r_i−r_j) reproduces exp(−tD²)p exactly.

    Measured max |ODE − exact| = 9.3e-15 for 5 roots over t ∈ [0, 0.35].
    """
    res = polynomial_heat_flow([-3.0, -1.0, 0.5, 2.0, 4.5], [0.0, 0.1, 0.2, 0.35])
    assert res["max_ode_error"] < 1e-11
    assert res["ode"] == "dr_i/dt = +2 * sum_{j != i} 1/(r_i - r_j)"


def test_polynomial_forward_flow_repels_backward_collides():
    """t > 0 spreads the roots; t < 0 collapses them and drives them off the axis."""
    res = polynomial_heat_flow([-3.0, -1.0, 0.5, 2.0, 4.5], [-0.6, -0.3, 0.0, 0.3, 0.6])
    ts = list(res["t_values"])
    i0 = ts.index(0.0)
    # spread is strictly increasing in t
    assert np.all(np.diff(res["spread"]) > 0)
    assert res["spread"][i0] == pytest.approx(7.5, abs=1e-12)
    # forward: still all real, gaps widened
    assert res["all_real"][-1]
    assert res["min_gap"][-1] > res["min_gap"][i0]
    # backward far enough: roots have left the real axis
    assert not res["all_real"][0]
    assert res["max_abs_imag"][0] > 1e-6
    assert res["collision_t"] is not None and res["collision_t"] < 0


def test_polynomial_quadratic_closed_form():
    """p = x²−1 under exp(−tD²) is x²−1−2t, roots ±√(1+2t), a closed-form check."""
    ts = [0.0, 0.25, 1.0, 4.0]
    res = polynomial_heat_flow([-1.0, 1.0], ts)
    for t, row in zip(ts, res["roots_exact"]):
        want = math.sqrt(1 + 2 * t)
        assert row[1].real == pytest.approx(want, abs=1e-12)
        assert row[0].real == pytest.approx(-want, abs=1e-12)


def test_polynomial_wrong_sign_would_fail():
    """Sanity: the opposite constant genuinely does *not* reproduce exp(−tD²)."""
    from zeta.heatflow import _heat_evolve_coeffs, _rk4, _sort_complex

    r0 = np.array([-3.0, -1.0, 0.5, 2.0, 4.5])
    exact = _sort_complex(np.roots(_heat_evolve_coeffs(np.poly(r0), 0.35, -1)))
    good = _sort_complex(_rk4(r0, 0.0, 0.35, +2.0, 4000))
    bad = _sort_complex(_rk4(r0, 0.0, 0.35, -2.0, 4000))
    assert np.max(np.abs(exact - good)) < 1e-11
    assert np.max(np.abs(exact - bad)) > 0.1


def test_polynomial_rejects_repeated_roots():
    with pytest.raises(ValueError, match="distinct"):
        polynomial_heat_flow([1.0, 1.0], [0.0])


@pytest.mark.parametrize("offset", [-10000.0, 10000.0, 1000000.0])
def test_polynomial_translation_preserves_collisions_and_gaps(offset):
    """A change of origin must not invent a collision, even at time zero."""
    roots = np.arange(-2.0, 3.0)
    times = [-0.6, 0.0, 0.1]
    base = polynomial_heat_flow(roots, times, ode_steps_per_unit_t=200)
    moved = polynomial_heat_flow(roots + offset, times, ode_steps_per_unit_t=200)
    assert base["all_real"].tolist() == [False, True, True]
    np.testing.assert_array_equal(moved["all_real"], base["all_real"])
    assert moved["collision_t"] == base["collision_t"] == -0.6
    for field in ["min_gap", "spread", "max_abs_imag"]:
        np.testing.assert_allclose(moved[field], base[field], rtol=0, atol=1e-12)
    np.testing.assert_array_equal(moved["roots_exact"][1], roots + offset)
    assert moved["max_ode_error"] < 1e-10


def test_polynomial_shifted_quintic_against_exact_algebra():
    """An independent rational polynomial gives five explicit real roots."""
    import sympy as sp

    x = sp.Symbol("x")
    p = x * (x**2 - 1) * (x**2 - 4)
    t = sp.Rational(1, 10)
    evolved = sp.expand(p - t * sp.diff(p, x, 2) + t**2 / 2 * sp.diff(p, x, 4))
    assert evolved == x**5 - 7*x**3 + sp.Rational(38, 5)*x
    assert sp.Poly(evolved, x).count_roots(-sp.oo, sp.oo) == 5
    exact = sorted(float(r.evalf(50)) for r in sp.solve(evolved, x))
    offset = 10000.0
    result = polynomial_heat_flow(
        np.arange(-2.0, 3.0) + offset, [0.1], ode_steps_per_unit_t=200
    )
    assert result["all_real"].tolist() == [True]
    assert result["collision_t"] is None
    np.testing.assert_allclose(
        result["roots_exact"][0], np.array(exact) + offset, rtol=0, atol=1e-10
    )


# --------------------------------------------------------------------------- #
#  Lambda facts
# --------------------------------------------------------------------------- #

def test_lambda_facts():
    f = lambda_facts()
    assert f["lower_bound"] == 0.0
    assert f["upper_bound"] == 0.2
    assert f["lower_bound"] <= f["upper_bound"]
    # Platt-Trudgian prove Lambda <= 0.2, not Lambda < 0.2; the only strict upper
    # bound in the literature is Ki-Kim-Lee's Lambda < 1/2.
    assert f["upper_bound_is_strict"] is False
    assert f["current_interval"] == "0 <= Lambda <= 0.2"
    joined = " ".join(h["who"] + h["where"] for h in f["history"])
    for name in ["de Bruijn", "Newman", "Rodgers", "Tao", "Platt", "Trudgian",
                 "Polymath", "Odlyzko", "Saouter", "Ki"]:
        assert name in joined
    assert all({"bound", "who", "where"} <= set(h) for h in f["history"])


def test_lambda_facts_bounds_are_attributed_to_the_right_papers():
    """REGRESSION: two lower bounds were pinned to the wrong papers.

    The module used to credit Csordas-Odlyzko-Smith-Varga (ETNA 1, 1993) with
    Λ ≥ −1.1e-11 and Csordas-Smith-Varga (Constr. Approx. 10, 1994) with
    Λ > −1.15e-11.  Those papers prove −5.895e-9 and −4.379e-6 respectively; the
    −1.1e-11 figure is Saouter-Gourdon-Demichel (Math. Comp. 80, 2011), which was
    missing entirely.  The old list was also internally incoherent, it made 1993
    stronger than Odlyzko's 2000 bound of −2.7e-9.
    """
    hist = lambda_facts()["history"]

    def bound_of(author_substr, where_substr=""):
        hits = [h for h in hist
                if author_substr in h["who"] and where_substr in h["where"]]
        assert len(hits) == 1, (author_substr, where_substr, [h["who"] for h in hits])
        return hits[0]["bound"]

    assert bound_of("de Bruijn") == "Lambda <= 1/2"
    assert bound_of("Odlyzko", "Numer. Algorithms") == "Lambda > -2.7e-9"
    assert bound_of("Saouter") == "Lambda > -1.14541e-11"
    assert bound_of("Ki") == "Lambda < 1/2  (strict)"
    assert bound_of("Csordas", "Electron. Trans. Numer. Anal.") == "Lambda > -5.895e-9"
    assert bound_of("Csordas", "Constr. Approx.") == "Lambda > -4.379e-6"
    assert bound_of("Platt") == "Lambda <= 0.2"
    assert bound_of("Polymath") == "Lambda <= 0.22"
    assert bound_of("Rodgers").startswith("Lambda >= 0")

    # the -1.1e-11 class of bound belongs to Saouter et al. and nobody else
    owners = {h["who"] for h in hist if "1.1" in h["bound"] and "e-11" in h["bound"]}
    assert owners == {"Y. Saouter, X. Gourdon, P. Demichel"}, owners


def test_H0_RELATION_matches_the_fitted_result():
    """The exported constant must agree with what H0_vs_Xi actually measures.

    ``H0_RELATION`` was in ``__all__`` but referenced by nothing, it could have
    drifted out of sync with the fit without any test noticing.
    """
    res = H0_vs_Xi(dps=40)
    assert H0_RELATION["c"] == res["c_rational"] == (1, 8)
    assert H0_RELATION["a"] == res["a_rational"] == (1, 2)
    assert H0_RELATION["relation"] == "H_0(z) = (1/8) * Xi(z/2)"
    with mp.workdps(40):
        c = mp.mpf(H0_RELATION["c"][0]) / H0_RELATION["c"][1]
        a = mp.mpf(H0_RELATION["a"][0]) / H0_RELATION["a"][1]
        for z in [0, 7, 28.27, 61]:
            lhs = H_t(z, 0, dps=40)
            rhs = c * Xi_reference(a * mp.mpf(z), backend="local")
            assert abs(lhs - rhs) < mp.mpf(10) ** -38


def test_Xi_reference_rejects_unknown_backend():
    """A typo must not silently fall through to the sibling and look like a pass."""
    with pytest.raises(ValueError, match="backend must be"):
        Xi_reference(1, backend="loc")


def test_default_dps_paths():
    """The dps=None branches of zeros_of_H_t / zero_gap_statistics were never run."""
    zs = zeros_of_H_t(0, 20, 105)  # dps=None -> recommended_dps(105, 15) = 38
    assert len(zs) == 10
    with mp.workdps(50):
        for k, z in enumerate(zs, 1):
            assert abs(z - 2 * mp.zetazero(k).imag) < mp.mpf(10) ** -24
    empty = zero_gap_statistics(0.0, 30.0, 35.0, dps=30)  # window with no zeros
    assert empty["n_zeros"] == 0
    assert empty["gaps"] == [] and empty["min_gap"] is None and empty["mean_gap"] is None


def test_recommended_dps_monotone_and_sufficient():
    assert recommended_dps(0) < recommended_dps(100) < recommended_dps(200)
    # at the recommended precision, H_0 near z = 100 still resolves ~15 digits
    d = recommended_dps(100, 15)
    with mp.workdps(d):
        z = mp.mpf(100)
        rel = abs(H_t(z, 0, dps=d) - Xi_reference(z / 2) / 8) / abs(H_t(z, 0, dps=d))
        assert rel < mp.mpf(10) ** -15


def test_ordinate_extraction_handles_both_conventions():
    """Regression: mpf(14.13).imag is 0, so `.imag` alone silently yields garbage.

    `zeta.zeros.first_n_zeros` returns bare ordinates on this build; the helper
    must also cope with the rho = 1/2 + i*gamma convention.
    """
    from zeta.heatflow import _ordinate_of, _reference_ordinates

    assert _ordinate_of(mp.mpf("14.134725141734693790")) == mp.mpf("14.134725141734693790")
    assert abs(_ordinate_of(mp.mpc("0.5", "14.134725141734693790"))
               - mp.mpf("14.134725141734693790")) < mp.mpf(10) ** -20
    ords = _reference_ordinates(10)
    assert len(ords) == 10
    with mp.workdps(20):
        for got, want in zip(ords, GAMMA):
            assert abs(got - mp.mpf(want)) < mp.mpf(10) ** -12


def test_xi_backend_cross_check():
    """zeta.core.Xi and the local xi agree to the sibling's own accuracy.

    Measured max |zeta.core - local| = 1.4e-32 at dps = 40 (zeta.core.Xi carries a
    fixed ~1e-32 absolute error regardless of requested dps, and is real-only, so
    complex arguments fall back to the local xi).
    """
    from zeta.heatflow import xi_backend_report

    rep = xi_backend_report(dps=40)
    assert rep["max_abs_difference"] < mp.mpf(10) ** -30
