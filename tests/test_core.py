"""Tests for zeta.core, every ground-truth fact, checked against mpmath as an
independent oracle and against closed forms where they exist.

Numbers quoted as literals in this file were verified independently in this
environment before being asserted.
"""

from __future__ import annotations

import json
import os

import mpmath
import pytest
from mpmath import mp

from zeta.core import (
    DPS_DEFAULT,
    HEAT_DIFFUSIVITY,
    Xi,
    Z,
    completed_zeta,
    eta,
    euler_maclaurin_suggest_N,
    functional_equation_defect,
    hardy_Z_sign_changes,
    mellin_gamma_zeta,
    mellin_gamma_zeta_defect,
    omega,
    rs_theta,
    theta,
    theta_heat,
    theta_heat_gaussian,
    theta_heat_poisson_defect,
    theta_heat_residual,
    theta_mellin_xi,
    theta_mellin_xi_defect,
    theta_modular_defect,
    xi,
    zeta,
    zeta_euler_maclaurin,
    zeta_via_eta,
)

# First ten zero ordinates gamma_n (verified ground truth).
GAMMAS = [
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


def _abs(x):
    return abs(mpmath.mpmathify(x))


# ---------------------------------------------------------------------------
# zeta: values and landmarks
# ---------------------------------------------------------------------------

def test_dps_default():
    assert DPS_DEFAULT == 30


def test_zeta_two_is_pi_squared_over_six():
    with mp.workdps(40):
        v = zeta(2, dps=35)
        assert _abs(v - mp.pi ** 2 / 6) < mp.mpf("1e-33")
    # the literal ground-truth digits (nstr, because str() honours the *global* dps)
    assert mp.nstr(zeta(2, dps=30), 30) == "1.64493406684822643647241516665"


def test_zeta_special_values():
    with mp.workdps(40):
        assert _abs(zeta(-1, dps=35) + mp.mpf(1) / 12) < mp.mpf("1e-33")
        assert _abs(zeta(0, dps=35) + mp.mpf(1) / 2) < mp.mpf("1e-33")
        assert _abs(zeta(4, dps=35) - mp.pi ** 4 / 90) < mp.mpf("1e-33")
        assert _abs(zeta(-3, dps=35) - mp.mpf(1) / 120) < mp.mpf("1e-33")


def test_zeta_matches_mpmath_oracle():
    with mp.workdps(45):
        for s in [mp.mpf(2), mp.mpf("0.5"), mp.mpc("0.5", "14.1347"), mp.mpf(-5),
                  mp.mpc(3, 4), mp.mpf("1.5")]:
            assert _abs(zeta(s, dps=35) - mp.zeta(s)) < mp.mpf("1e-33")


def test_zeta_vanishes_at_the_first_ten_zeros():
    """The ordinates are given to 20 significant digits, so |zeta| there is
    limited by |zeta'| * 1e-18 ~ 1e-18, not by our accuracy."""
    with mp.workdps(45):
        for g in GAMMAS:
            v = zeta(mp.mpc("0.5", g), dps=35)
            assert _abs(v) < mp.mpf("1e-17"), f"zeta(1/2+{g}i) = {v}"


def test_zeta_zeros_match_mpmath_zetazero_oracle():
    with mp.workdps(40):
        for n, g in enumerate(GAMMAS, start=1):
            assert _abs(mp.im(mp.zetazero(n)) - mp.mpf(g)) < mp.mpf("1e-18"), n


# ---------------------------------------------------------------------------
# eta and zeta_via_eta
# ---------------------------------------------------------------------------

def test_eta_matches_alternating_series_definition():
    """Cross-check Borwein's algorithm against the raw alternating sum where
    the raw sum actually converges fast enough to be usable (Re s large)."""
    with mp.workdps(40):
        s = mp.mpf(4)
        naive = mp.nsum(lambda n: (-1) ** (n - 1) * mp.power(n, -s), [1, mp.inf])
        assert _abs(eta(s, dps=30) - naive) < mp.mpf("1e-28")


def test_eta_equals_one_minus_two_pow_relation():
    with mp.workdps(45):
        for s in [mp.mpf(2), mp.mpf("0.5"), mp.mpf(3), mp.mpc("0.5", "14.1347"),
                  mp.mpc("0.25", "5")]:
            lhs = eta(s, dps=30)
            rhs = (1 - mp.power(2, 1 - s)) * mp.zeta(s)
            assert _abs(lhs - rhs) < mp.mpf("1e-28"), s


def test_eta_at_one_is_log_two():
    """eta(1) = sum (-1)^{n-1}/n = log 2, even though zeta(1) is a pole."""
    with mp.workdps(40):
        assert _abs(eta(1, dps=30) - mp.log(2)) < mp.mpf("1e-28")


def test_zeta_via_eta_in_the_critical_strip():
    with mp.workdps(45):
        for s in [mp.mpf("0.5"), mp.mpf(2), mp.mpc("0.5", "14.1347251417346937904"),
                  mp.mpc("0.3", "10"), mp.mpf("0.75")]:
            assert _abs(zeta_via_eta(s, dps=30) - mp.zeta(s)) < mp.mpf("1e-27"), s


def test_zeta_via_eta_kills_a_zero():
    with mp.workdps(45):
        v = zeta_via_eta(mp.mpc("0.5", GAMMAS[0]), dps=30)
        assert _abs(v) < mp.mpf("1e-18")


def test_zeta_via_eta_raises_at_the_pole():
    with pytest.raises(ZeroDivisionError):
        zeta_via_eta(1)


# ---------------------------------------------------------------------------
# Euler-Maclaurin: the hand-rolled continuation
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "s_str",
    ["2", "3", "0.5", "-1", "0", "-5", "1.5", "0.5+14.134725141734693790j"],
)
def test_euler_maclaurin_agrees_with_mpmath(s_str):
    """Required: >= 15 digits at s = 2, 1/2 + 14.13i, -1, 0 (plus more).

    Tolerance is set just above the *measured* worst case (4.6e-31, at
    s = 1/2 + 14.1347i), not at the 1e-25 the requirement would allow: a loose
    tolerance cannot catch a regression."""
    with mp.workdps(45):
        s = mp.mpmathify(s_str)
        got = zeta_euler_maclaurin(s, N=20, M=20, dps=30)
        ref = mp.zeta(s)
        scale = max(_abs(ref), mp.mpf(1))
        assert _abs(got - ref) / scale < mp.mpf("1e-29"), (s, got, ref)


def test_euler_maclaurin_gives_minus_one_twelfth_exactly():
    """At s = -1 every Pochhammer factor with k >= 2 vanishes, so the formula
    is algebraically exact: the answer is -1/12 to the last bit."""
    with mp.workdps(50):
        for N in (2, 5, 20, 50):
            v = zeta_euler_maclaurin(-1, N=N, M=20, dps=40)
            assert _abs(v + mp.mpf(1) / 12) < mp.mpf("1e-38"), N


def test_euler_maclaurin_gives_minus_one_half_exactly():
    with mp.workdps(50):
        for N in (2, 5, 20, 50):
            v = zeta_euler_maclaurin(0, N=N, M=20, dps=40)
            assert _abs(v + mp.mpf(1) / 2) < mp.mpf("1e-38"), N


def test_euler_maclaurin_is_independent_of_N():
    """The continuation must not depend on where we cut the Dirichlet sum."""
    with mp.workdps(45):
        vals = [zeta_euler_maclaurin("0.5+14.1347251417346937904j", N=N, M=20, dps=30)
                for N in (20, 30, 45)]
        for v in vals[1:]:
            assert _abs(v - vals[0]) < mp.mpf("1e-25")


def test_euler_maclaurin_high_t_needs_larger_N():
    """N = 20 is not enough at t = 100; the suggested N fixes it."""
    with mp.workdps(45):
        s = mp.mpc("0.5", "100")
        ref = mp.zeta(s)
        bad = zeta_euler_maclaurin(s, N=20, M=20, dps=30)
        assert _abs(bad - ref) > mp.mpf("1e-8")          # genuinely inaccurate
        N = euler_maclaurin_suggest_N(s, dps=30, M=20)
        good = zeta_euler_maclaurin(s, N=N, M=20, dps=30)
        assert _abs(good - ref) < mp.mpf("1e-25")


def test_euler_maclaurin_rejects_the_pole():
    with pytest.raises(ValueError):
        zeta_euler_maclaurin(1)


# ---------------------------------------------------------------------------
# theta and the modular relation
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("x", ["0.05", "0.25", "0.5", "0.9", "1", "1.7", "3", "10"])
def test_theta_modular_defect_is_zero(x):
    """theta(1/x) - sqrt(x) theta(x) == 0, required < 1e-25.

    Measured worst case at dps=40 is 3.1e-61 (it is exactly 0.0 at most of
    these x), so the tolerance is pinned near reality rather than at 1e-25."""
    d = theta_modular_defect(x, dps=40)
    assert _abs(d) < mp.mpf("1e-50"), (x, d)


def test_theta_fixed_point_at_one():
    """x = 1 is the fixed point of x -> 1/x, so the relation is trivial there,
    but theta(1) has the closed form pi^{1/4}/Gamma(3/4)."""
    with mp.workdps(45):
        v = theta(1, dps=35)
        closed = mp.power(mp.pi, mp.mpf(1) / 4) / mp.gamma(mp.mpf(3) / 4)
        assert _abs(v - closed) < mp.mpf("1e-33")


def test_theta_matches_mpmath_jtheta_oracle():
    """theta(x) = jtheta(3, 0, q) with nome q = exp(-pi x)."""
    with mp.workdps(40):
        for x in ["0.3", "1", "2.5"]:
            xv = mp.mpf(x)
            assert _abs(theta(xv, dps=30) - mp.jtheta(3, 0, mp.exp(-mp.pi * xv))) < mp.mpf("1e-28")


def test_omega_is_half_theta_minus_one():
    with mp.workdps(40):
        for x in ["0.4", "1", "3"]:
            assert _abs(omega(x, dps=30) - (theta(x, dps=30) - 1) / 2) < mp.mpf("1e-28")


def test_theta_requires_positive_real_x():
    with pytest.raises(ValueError):
        theta(-1)
    with pytest.raises(ValueError):
        theta(mp.mpc(1, 1))


# ---------------------------------------------------------------------------
# heat kernel on the circle
# ---------------------------------------------------------------------------

def test_heat_diffusivity_constant_is_one():
    assert HEAT_DIFFUSIVITY == 1


@pytest.mark.parametrize("x,t", [("0.0", "0.05"), ("0.3", "0.05"),
                                 ("0.5", "0.2"), ("0.17", "0.01")])
def test_theta_heat_poisson_summation(x, t):
    """Spectral form == periodised-Gaussian form (Poisson summation).

    Measured: exactly 0.0 at every one of these points at dps=35."""
    d = theta_heat_poisson_defect(x, t, dps=35)
    assert _abs(d) < mp.mpf("1e-40"), (x, t, d)


def test_theta_heat_is_periodic_and_even():
    with mp.workdps(40):
        a = theta_heat("0.3", "0.05", dps=30)
        assert _abs(a - theta_heat("1.3", "0.05", dps=30)) < mp.mpf("1e-28")
        assert _abs(a - theta_heat("-0.3", "0.05", dps=30)) < mp.mpf("1e-28")


def test_theta_heat_at_zero_is_jacobi_theta():
    """Theta(0, t) = theta(4 pi t), since 4 pi^2 n^2 t = pi n^2 (4 pi t)."""
    with mp.workdps(45):
        for t in ["0.02", "0.1"]:
            tv = mp.mpf(t)
            assert _abs(theta_heat(0, tv, dps=30) - theta(4 * mp.pi * tv, dps=30)) < mp.mpf("1e-27")


def test_theta_heat_integrates_to_one():
    """The heat kernel is a probability density on the circle: only the n = 0
    Fourier mode survives integration over one period."""
    with mp.workdps(35):
        val = mp.quad(lambda x: theta_heat(x, mp.mpf("0.03"), dps=25), [0, 1])
        assert _abs(val - 1) < mp.mpf("1e-22")


@pytest.mark.parametrize("x,t", [("0.3", "0.05"), ("0.0", "0.02"), ("0.5", "0.1"),
                                 ("0.77", "0.013"), ("0.0", "0.005")])
def test_theta_heat_satisfies_the_heat_equation_with_D_equal_one(x, t):
    """dTheta/dt - 1 * d^2Theta/dx^2 = 0, to far better than the 8 digits asked.

    The second derivative is O(1)-O(400) at these points and the residual is
    below 1e-27, so D = 1 is confirmed to >= 25 significant digits.
    """
    r = theta_heat_residual(x, t, dps=30)
    assert _abs(r) < mp.mpf("1e-27"), (x, t, r)


def test_theta_heat_residual_is_fourth_order_in_h():
    """Sanity check on the stencils: shrinking h by 100 must shrink the
    residual by ~1e8.  If it does not, we are measuring round-off, not the
    heat equation."""
    x, t = "0.3", "0.05"
    r6 = _abs(theta_heat_residual(x, t, h="1e-6", dps=30))
    r8 = _abs(theta_heat_residual(x, t, h="1e-8", dps=30))
    with mp.workdps(40):
        ratio = r6 / r8
        assert mp.mpf("1e7") < ratio < mp.mpf("1e9"), ratio


def test_theta_heat_residual_rejects_the_wrong_diffusivity():
    """Guard against a vacuous test: D = 1/(4 pi^2) must NOT work."""
    with mp.workdps(40):
        wrong = theta_heat_residual("0.3", "0.05", dps=30,
                                    diffusivity=1 / (4 * mp.pi ** 2))
        assert _abs(wrong) > mp.mpf("1e-3")


def test_theta_heat_residual_scale_is_meaningful():
    """Guard against a vacuously-small residual: the derivatives being
    cancelled must themselves be O(1) or larger."""
    with mp.workdps(50):
        x, t, h = mp.mpf("0.3"), mp.mpf("0.05"), mp.mpf("1e-6")
        f = lambda tt: theta_heat(x, tt, dps=40)
        u_t = (-f(t + 2 * h) + 8 * f(t + h) - 8 * f(t - h) + f(t - 2 * h)) / (12 * h)
        assert _abs(u_t) > mp.mpf(1)                       # derivative is O(1)+
        assert _abs(theta_heat_residual(x, t, dps=30)) / _abs(u_t) < mp.mpf("1e-27")


# ---------------------------------------------------------------------------
# xi, Xi, functional equation
# ---------------------------------------------------------------------------

def test_xi_landmarks():
    """xi(0) = xi(1) = 1/2 -- both are removable singularities of the naive
    formula (Gamma(s/2) blows up at 0, zeta blows up at 1)."""
    with mp.workdps(45):
        assert _abs(xi(0, dps=35) - mp.mpf(1) / 2) < mp.mpf("1e-33")
        assert _abs(xi(1, dps=35) - mp.mpf(1) / 2) < mp.mpf("1e-33")
        # and the limits approached from nearby points agree
        assert _abs(xi(mp.mpf("1e-20"), dps=30) - mp.mpf(1) / 2) < mp.mpf("1e-19")
        assert _abs(xi(1 + mp.mpf("1e-20"), dps=30) - mp.mpf(1) / 2) < mp.mpf("1e-19")


def test_xi_matches_the_literal_defining_formula():
    """Our stable form (s-1) pi^{-s/2} Gamma(s/2+1) zeta(s) must equal the
    literal (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s) away from s = 0, 1."""
    with mp.workdps(45):
        for s_str in ["2", "0.5", "-3.5", "3+4j", "0.25+9j"]:
            s = mp.mpmathify(s_str)
            literal = (mp.mpf(1) / 2 * s * (s - 1) * mp.power(mp.pi, -s / 2)
                       * mp.gamma(s / 2) * mp.zeta(s))
            assert _abs(xi(s, dps=35) - literal) / max(_abs(literal), mp.mpf(1)) < mp.mpf("1e-32"), s_str


def test_Xi_zero_value():
    """Xi(0) = xi(1/2) ~ 0.4971207781..."""
    v = Xi(0, dps=30)
    assert isinstance(v, mpmath.mpf)
    with mp.workdps(40):
        assert _abs(v - mp.mpf("0.4971207781")) < mp.mpf("1e-10")
        assert _abs(v - xi(mp.mpf("0.5"), dps=30)) < mp.mpf("1e-28")


def test_Xi_is_real_and_even():
    for t in ["0", "1", "5.5", "14.134725141734693790", "30"]:
        v = Xi(t, dps=30)
        assert isinstance(v, mpmath.mpf), t
        with mp.workdps(40):
            assert _abs(v - Xi(mp.mpf(t) * -1, dps=30)) < mp.mpf("1e-28"), t


def test_Xi_vanishes_at_the_zeros():
    with mp.workdps(45):
        for g in GAMMAS[:5]:
            assert _abs(Xi(g, dps=35)) < mp.mpf("1e-18"), g


def test_Xi_rejects_complex_input():
    with pytest.raises(ValueError):
        Xi(mp.mpc(1, 1))


@pytest.mark.parametrize(
    "s_str", ["2", "0.5", "-3.5", "0.3+7j", "2+3j", "0.5+14.134725141734693790j", "-1"]
)
def test_functional_equation_defect_is_zero(s_str):
    """xi(s) - xi(1-s) == 0, required < 1e-32."""
    d = functional_equation_defect(s_str, dps=40)
    assert _abs(d) < mp.mpf("1e-35"), (s_str, d)


def test_completed_zeta_symmetry():
    with mp.workdps(45):
        for s in [mp.mpf(2), mp.mpc(3, 4)]:
            a = completed_zeta(s, dps=35)
            b = completed_zeta(1 - s, dps=35)
            assert _abs(a - b) / _abs(a) < mp.mpf("1e-32")


def test_xi_relates_to_Xi():
    with mp.workdps(45):
        t = mp.mpf("7.25")
        assert _abs(xi(mp.mpc("0.5", t), dps=35) - Xi(t, dps=35)) < mp.mpf("1e-32")


# ---------------------------------------------------------------------------
# Riemann-Siegel theta, Hardy Z
# ---------------------------------------------------------------------------

def test_rs_theta_matches_mpmath_siegeltheta():
    with mp.workdps(45):
        for t in ["0", "1", "10", "14.134725141734693790", "100", "1000"]:
            got = rs_theta(t, dps=30)
            assert _abs(got - mp.siegeltheta(mp.mpf(t))) < mp.mpf("1e-27"), t


def test_rs_theta_is_odd_and_zero_at_origin():
    with mp.workdps(40):
        assert _abs(rs_theta(0, dps=30)) < mp.mpf("1e-28")
        for t in ["3", "17.5"]:
            assert _abs(rs_theta(t, dps=30) + rs_theta("-" + t, dps=30)) < mp.mpf("1e-27")


def test_rs_theta_asymptotic():
    """theta(t) ~ (t/2)log(t/2pi) - t/2 - pi/8 + 1/(48t) + 7/(5760 t^3).

    Both truncations are checked, at tolerances just above the measured error
    (1.22e-12 and 3.84e-19 at t = 1000).  Checking only the first, at 1e-10,
    would pass even if rs_theta were wrong in the 11th decimal."""
    with mp.workdps(40):
        t = mp.mpf(1000)
        got = rs_theta(t, dps=30)
        a3 = t / 2 * mp.log(t / (2 * mp.pi)) - t / 2 - mp.pi / 8 + 1 / (48 * t)
        a4 = a3 + 7 / (5760 * t ** 3)
        assert mp.mpf("1e-13") < _abs(got - a3) < mp.mpf("3e-12")
        assert _abs(got - a4) < mp.mpf("1e-17")


def test_Z_is_real_and_matches_siegelz():
    with mp.workdps(45):
        for t in ["0.5", "1", "10", "20", "50", "100"]:
            v = Z(t, dps=30)
            assert isinstance(v, mpmath.mpf), t
            assert _abs(v - mp.siegelz(mp.mpf(t))) < mp.mpf("1e-25"), t


def test_Z_modulus_equals_zeta_modulus():
    with mp.workdps(45):
        for t in ["3", "14.5", "40"]:
            tv = mp.mpf(t)
            assert _abs(_abs(Z(tv, dps=30)) - _abs(mp.zeta(mp.mpc("0.5", tv)))) < mp.mpf("1e-27")


def test_Z_vanishes_at_the_first_five_zeros():
    with mp.workdps(45):
        for g in GAMMAS[:5]:
            v = Z(g, dps=35)
            assert _abs(v) < mp.mpf("1e-17"), (g, v)


def test_Z_is_even():
    with mp.workdps(40):
        for t in ["4", "22.5"]:
            assert _abs(Z(t, dps=30) - Z("-" + t, dps=30)) < mp.mpf("1e-27")


def test_Z_rejects_complex_input():
    with pytest.raises(ValueError):
        Z(mp.mpc(1, 1))


def test_hardy_Z_sign_changes_finds_the_first_ten_zeros():
    brackets = hardy_Z_sign_changes(0.5, 50.5, 3000, dps=15, cache=False)
    assert len(brackets) == 10, brackets
    with mp.workdps(40):
        for (a, b), g in zip(brackets, GAMMAS):
            gv = mp.mpf(g)
            assert a < gv < b, (a, b, g)
            # each bracket really does contain a sign change
            assert Z(a, dps=15) * Z(b, dps=15) < 0


def test_hardy_Z_sign_changes_count_below_100_is_29():
    """Ground truth: 29 zeros with 0 < gamma < 100.  A fine enough scan of Z
    finds all 29 as sign changes -- all of them are on the critical line."""
    brackets = hardy_Z_sign_changes(0.5, 100.0, 6000, dps=15, cache=False)
    assert len(brackets) == 29, len(brackets)
    # Independent cross-check via Riemann-von Mangoldt:
    #     N(T) = theta(T)/pi + 1 + S(T),   S(T) = arg zeta(1/2+iT)/pi
    # mpmath's backlunds(T) IS S(T) (not an error bound).
    with mp.workdps(30):
        T = mp.mpf(100)
        N = rs_theta(T, dps=25) / mp.pi + 1 + mp.backlunds(T)
        assert _abs(N - 29) < mp.mpf("1e-20"), N


def test_hardy_Z_sign_changes_brackets_refine_to_the_true_zeros():
    brackets = hardy_Z_sign_changes(0.5, 33.0, 2000, dps=15, cache=False)
    assert len(brackets) == 5
    with mp.workdps(30):
        for (a, b), g in zip(brackets, GAMMAS[:5]):
            root = mp.findroot(lambda t: Z(t, dps=25), (mp.mpf(a), mp.mpf(b)),
                               solver="bisect", tol=mp.mpf("1e-40"))
            assert _abs(root - mp.mpf(g)) < mp.mpf("1e-12"), (g, root)


def test_hardy_Z_sign_changes_cache_roundtrip():
    a = hardy_Z_sign_changes(0.5, 30.0, 400, dps=15, cache=True)
    b = hardy_Z_sign_changes(0.5, 30.0, 400, dps=15, cache=True)  # served from disk
    assert a == b
    assert len(a) == 3           # gamma_1..3 < 30 < gamma_4 = 30.4248...


def test_hardy_Z_sign_changes_validates_arguments():
    with pytest.raises(ValueError):
        hardy_Z_sign_changes(1.0, 2.0, 1)
    with pytest.raises(ValueError):
        hardy_Z_sign_changes(2.0, 1.0, 10)


# ---------------------------------------------------------------------------
# Mellin transforms
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("s_str", ["2", "3", "1.5", "10", "2+1j", "4"])
def test_mellin_gamma_zeta_raw_integral(s_str):
    """The literal integral int_0^inf x^{s-1}/(e^x-1) dx = Gamma(s) zeta(s)."""
    with mp.workdps(45):
        s = mp.mpmathify(s_str)
        got = mellin_gamma_zeta(s, dps=30, regularized=False)
        ref = mp.gamma(s) * mp.zeta(s)
        # measured: 1.2e-25 at s=1.5 (the endpoint singularity bites), <1e-31 elsewhere
        assert _abs(got - ref) / _abs(ref) < mp.mpf("1e-23"), (s_str, got, ref)


@pytest.mark.parametrize(
    "s_str", ["2", "3", "1.2", "1.05", "10", "0.5", "-0.5", "2+1j", "0.5+3j"]
)
def test_mellin_gamma_zeta_regularized(s_str):
    """The regularized form is accurate AND continues to Re(s) > -1."""
    with mp.workdps(45):
        s = mp.mpmathify(s_str)
        got = mellin_gamma_zeta(s, dps=30)
        ref = mp.gamma(s) * mp.zeta(s)
        assert _abs(got - ref) / _abs(ref) < mp.mpf("1e-28"), (s_str, got, ref)


def test_mellin_gamma_zeta_defect_small():
    for s in ["2", "3", "1.5", "0.75"]:
        assert _abs(mellin_gamma_zeta_defect(s, dps=30)) < mp.mpf("1e-25"), s


def test_mellin_gives_zeta_four_and_stefan_boltzmann():
    """Gamma(4) zeta(4) = 6 * pi^4/90 = pi^4/15 -- the Stefan-Boltzmann integral."""
    with mp.workdps(45):
        v = mellin_gamma_zeta(4, dps=35, regularized=False)
        assert _abs(v - mp.pi ** 4 / 15) < mp.mpf("1e-30")


def test_mellin_raw_form_rejects_re_s_le_one():
    with pytest.raises(ValueError):
        mellin_gamma_zeta("0.5", regularized=False)


@pytest.mark.parametrize("s_str", ["1", "0", "-1", "-3", "-5"])
def test_mellin_regularized_rejects_the_real_poles(s_str):
    """Gamma(s)zeta(s) has poles at s = 1 (from zeta) and s = 0, -1, -3, -5, ...
    (from Gamma).  The Gamma poles at the EVEN negative integers are cancelled
    by the trivial zeros of zeta, so -2, -4, ... must NOT be rejected."""
    with pytest.raises(ValueError):
        mellin_gamma_zeta(s_str)


@pytest.mark.parametrize("m", [1, 2, 3])
def test_mellin_is_finite_at_the_trivial_zeros(m):
    """At s = -2m the Gamma pole meets a zeta zero.  mpmath cannot form the
    product there at all, so we check against the limit

        lim_{s -> -2m} Gamma(s) zeta(s) = Res_{s=-2m} Gamma(s) * zeta'(-2m)
                                        = zeta'(-2m) / (2m)!

    with zeta' supplied by mpmath as an independent oracle."""
    s0 = -2 * m
    got = mellin_gamma_zeta(s0, dps=35)
    with mp.workdps(45):
        limit = mp.zeta(s0, derivative=1) / mp.factorial(2 * m)
        assert _abs(got - limit) / _abs(limit) < mp.mpf("1e-30"), (s0, got, limit)


@pytest.mark.parametrize("s_str", ["-0.5", "-0.9", "-0.99", "-1.5", "-2.5",
                                   "-4.5", "-10.5", "-19.5", "-8+2j"])
def test_mellin_regularized_continues_left_of_minus_one(s_str):
    """Regression guard.  Subtracting only 1/x - 1/2 (the naive regularisation)
    makes the quadrature silently return rubbish as Re(s) falls to -1: measured
    relative error 8.4e-07 at s = -0.9 and 0.25 at s = -0.99.  Subtracting J
    Bernoulli terms in closed form fixes it and reaches Re(s) > -(2J+1)."""
    with mp.workdps(50):
        s = mp.mpmathify(s_str)
        got = mellin_gamma_zeta(s, dps=35)
        ref = mp.gamma(s) * mp.zeta(s)
        assert _abs(got - ref) / _abs(ref) < mp.mpf("1e-30"), (s_str, got, ref)


@pytest.mark.parametrize(
    "s_str,J_marginal,floor",
    [("-0.5", 0, "1e-32"), ("-0.9", 0, "1e-9"), ("-0.99", 0, "1e-3"),
     ("-2.5", 1, "1e-32"), ("-4.5", 2, "1e-32")],
)
def test_mellin_too_few_subtractions_really_does_fail(s_str, J_marginal, floor):
    """Guard against a vacuous fix.

    n_subtract=0 IS the old implementation -- only 1/x and -1/2 removed -- and
    it must visibly fail near Re(s) = -1, or the accuracy test above proves
    nothing.  Measured at dps=35: 9.9e-30 at s=-0.5, 2.7e-06 at s=-0.9, and
    0.278 at s=-0.99.  More generally the *smallest* J that makes the integral
    converge still loses ~8 digits (1.5e-29 at s=-2.5 with J=1), which is why
    _mellin_subtractions carries one extra term of margin.
    """
    with mp.workdps(55):
        s = mp.mpf(s_str)
        ref = mp.gamma(s) * mp.zeta(s)
        marginal = mellin_gamma_zeta(s, dps=35, n_subtract=J_marginal)
        assert _abs(marginal - ref) / _abs(ref) > mp.mpf(floor), (s_str, marginal)
        auto = mellin_gamma_zeta(s, dps=35)
        assert _abs(auto - ref) / _abs(ref) < mp.mpf("1e-34"), (s_str, auto)


def test_mellin_rejects_out_of_range_and_bad_n_subtract():
    with pytest.raises(ValueError):
        mellin_gamma_zeta(-25)                       # past the documented cap
    with pytest.raises(ValueError):
        mellin_gamma_zeta("-3.5", n_subtract=1)      # J=1 only reaches Re(s) > -3
    with pytest.raises(ValueError):
        mellin_gamma_zeta("-1.5", n_subtract=0)      # J=0 only reaches Re(s) > -1
    with pytest.raises(ValueError):
        mellin_gamma_zeta(2, n_subtract=-1)


# ---------------------------------------------------------------------------
# Riemann's theta-Mellin representation == the functional equation
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "s_str",
    ["2", "0.5", "-1", "3", "0.3", "3+4j", "0.5+14.134725141734693790j", "-2.5"],
)
def test_theta_mellin_xi_matches_completed_zeta(s_str):
    """RHS of Riemann's formula == pi^{-s/2} Gamma(s/2) zeta(s)."""
    with mp.workdps(45):
        s = mp.mpmathify(s_str)
        got = theta_mellin_xi(s, dps=35)
        ref = mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)
        scale = max(_abs(ref), mp.mpf(1))
        assert _abs(got - ref) / scale < mp.mpf("1e-30"), (s_str, got, ref)


def test_theta_mellin_xi_defect_small():
    for s in ["2", "0.5", "-1", "3+4j"]:
        assert _abs(theta_mellin_xi_defect(s, dps=35)) < mp.mpf("1e-30"), s


@pytest.mark.parametrize("s_str", ["2", "3", "0.3", "3+4j", "-1.5"])
def test_theta_mellin_representation_is_manifestly_symmetric(s_str):
    """THE PROOF: the RHS of Riemann's formula is invariant under s -> 1-s,
    because 1/(s(s-1)) is symmetric and x^{s/2-1}, x^{(1-s)/2-1} swap.
    This is the functional equation, obtained from the theta modular relation.
    """
    with mp.workdps(45):
        s = mp.mpmathify(s_str)
        a = theta_mellin_xi(s, dps=35)
        b = theta_mellin_xi(1 - s, dps=35)
        assert _abs(a - b) / max(_abs(a), mp.mpf(1)) < mp.mpf("1e-30"), (s_str, a, b)


def test_theta_mellin_gives_xi_and_hence_the_functional_equation():
    """xi(s) = (1/2) s (s-1) * [theta-Mellin RHS] reproduces xi, including
    xi(0) = xi(1) = 1/2 as a limit of the manifestly symmetric formula."""
    with mp.workdps(45):
        for s_str in ["2", "0.5", "3+4j"]:
            s = mp.mpmathify(s_str)
            built = mp.mpf(1) / 2 * s * (s - 1) * theta_mellin_xi(s, dps=35)
            assert _abs(built - xi(s, dps=35)) < mp.mpf("1e-30"), s_str


def test_theta_mellin_xi_rejects_poles():
    with pytest.raises(ValueError):
        theta_mellin_xi(0)
    with pytest.raises(ValueError):
        theta_mellin_xi(1)


# ---------------------------------------------------------------------------
# the chain: theta identity -> functional equation, end to end
# ---------------------------------------------------------------------------

def test_end_to_end_theta_identity_implies_functional_equation():
    """One test that walks the whole argument numerically:

    (1) theta(1/x) = sqrt(x) theta(x)                     [modular relation]
    (2) => omega(1/x) = -1/2 + sqrt(x)/2 + sqrt(x) omega(x)
    (3) => Lambda(s) = 1/(s(s-1)) + int_1^inf (x^{s/2-1}+x^{(1-s)/2-1}) omega(x) dx
    (4) => Lambda(s) = Lambda(1-s), i.e. xi(s) = xi(1-s).
    """
    with mp.workdps(45):
        x = mp.mpf("0.37")
        # (1)
        assert _abs(theta_modular_defect(x, dps=35)) < mp.mpf("1e-30")
        # (2)
        lhs = omega(1 / x, dps=35)
        rhs = -mp.mpf(1) / 2 + mp.sqrt(x) / 2 + mp.sqrt(x) * omega(x, dps=35)
        assert _abs(lhs - rhs) < mp.mpf("1e-30")
        # (3)
        s = mp.mpc("0.3", "6")
        assert _abs(theta_mellin_xi(s, dps=35) - completed_zeta(s, dps=35)) < mp.mpf("1e-30")
        # (4)
        assert _abs(theta_mellin_xi(s, dps=35) - theta_mellin_xi(1 - s, dps=35)) < mp.mpf("1e-30")
        assert _abs(functional_equation_defect(s, dps=35)) < mp.mpf("1e-30")


# ---------------------------------------------------------------------------
# Regression tests added by adversarial verification.
#
# Each of these covers a real defect that the original suite did not exercise.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("m", [1, 2, 3, 4, 5, 8])
def test_xi_is_entire_at_the_trivial_zeros(m):
    """REGRESSION.  xi is documented as entire, but

        xi(s) = (s-1) pi^{-s/2} Gamma(s/2+1) zeta(s)

    hits a Gamma pole at s = -2, -4, -6, ... (so does the literal
    (1/2)s(s-1)pi^{-s/2}Gamma(s/2)zeta(s) -- moving Gamma(s/2) to Gamma(s/2+1)
    repairs s = 0 and nothing else).  mpmath raised "gamma function pole" and
    xi(-2), xi(-4), ... were simply uncomputable, which also took out
    functional_equation_defect at s = 3, 5, 7, ...

    The removable singularity is now evaluated as a circle average of the SAME
    generic branch (Cauchy's integral formula), which uses no functional
    equation -- so comparing xi(-2m) against xi(2m+1), computed by the ordinary
    product formula, is a genuine test of xi(s) = xi(1-s).
    """
    s0 = -2 * m
    got = xi(s0, dps=35)
    assert isinstance(got, mpmath.mpf)
    other = xi(2 * m + 1, dps=35)          # = xi(1 - s0), generic branch
    with mp.workdps(45):
        assert _abs(got - other) / _abs(other) < mp.mpf("1e-32"), (s0, got, other)


def test_xi_at_minus_two_has_the_closed_form():
    """xi(-2) = xi(3) = (1/2)*3*2*pi^{-3/2}*Gamma(3/2)*zeta(3) = 3 zeta(3)/(2 pi)."""
    with mp.workdps(45):
        closed = mp.mpf(3) * mp.zeta(3) / (2 * mp.pi)
        assert _abs(xi(-2, dps=35) - closed) < mp.mpf("1e-33")


@pytest.mark.parametrize("s_str", ["3", "5", "7", "-2", "-4", "-6", "-10"])
def test_functional_equation_holds_at_the_trivial_zeros(s_str):
    """REGRESSION: these all raised ValueError before the fix."""
    d = functional_equation_defect(s_str, dps=35)
    assert _abs(d) < mp.mpf("1e-30"), (s_str, d)


@pytest.mark.parametrize("m", [1, 2, 3])
def test_completed_zeta_is_finite_at_the_trivial_zeros(m):
    a = completed_zeta(-2 * m, dps=35)
    b = completed_zeta(2 * m + 1, dps=35)
    with mp.workdps(45):
        assert _abs(a - b) / _abs(b) < mp.mpf("1e-32"), (m, a, b)


def test_completed_zeta_still_raises_at_its_two_real_poles():
    """Lambda(s) = pi^{-s/2}Gamma(s/2)zeta(s) genuinely blows up at s = 0 and 1."""
    for s in (0, 1):
        with pytest.raises(ValueError):
            completed_zeta(s)


def test_theta_mellin_xi_defect_at_a_trivial_zero():
    """REGRESSION: completed_zeta(-2) used to raise, taking this with it."""
    for s in ("-2", "-4"):
        assert _abs(theta_mellin_xi_defect(s, dps=30)) < mp.mpf("1e-25"), s


# --- eta outside the strip --------------------------------------------------

@pytest.mark.parametrize(
    "s_str", ["0", "-0.5", "-1", "-2", "-3", "-5", "-6", "-8", "-10", "-12",
              "-15", "-20", "-20.5"]
)
def test_eta_is_accurate_for_negative_re_s(s_str):
    """REGRESSION.  Borwein's error bound is proven only for Re(s) >= 1/2, and
    _eta_workload used to (a) swallow the Gamma-pole exception and pretend the
    blow-up factor was 1, and (b) assume the 0.766 digits/term rate everywhere.
    Result: eta(-10) = -1.2e-15 instead of 0 and eta(-20) = -6.7e+08 instead
    of 0.  The estimator now bounds 1/|Gamma(s)| through the reflection formula
    and uses the measured left-half-plane rate."""
    with mp.workdps(50):
        s = mp.mpf(s_str)
        got = eta(s, dps=30)
        ref = (1 - mp.power(2, 1 - s)) * mp.zeta(s)
        assert _abs(got - ref) / max(_abs(ref), mp.mpf(1)) < mp.mpf("1e-28"), (s_str, got, ref)


def test_eta_at_minus_twenty_is_zero():
    """eta(-20) = (1 - 2^21) zeta(-20) = 0 exactly (zeta(-20) is a trivial zero)."""
    assert _abs(eta(-20, dps=30)) < mp.mpf("1e-28")


@pytest.mark.parametrize("t_str", ["30", "70", "150"])
def test_eta_still_works_at_moderate_height(t_str):
    """The guard digits grow like e^{pi|Im s|}; the estimator must keep up."""
    with mp.workdps(60):
        s = mp.mpc("0.5", t_str)
        got = eta(s, dps=30)
        ref = (1 - mp.power(2, 1 - s)) * mp.zeta(s)
        assert _abs(got - ref) < mp.mpf("1e-28"), (t_str, got, ref)


# --- reality checks must survive python -O ----------------------------------

def test_Z_reality_check_raises_valueerror_not_assertionerror():
    """The imaginary-residue guard used to be a bare `assert`, which vanishes
    under `python -O`.  Force it to trip by demanding an impossible tolerance."""
    with pytest.raises(ValueError):
        Z(10, dps=30, tol_digits=-100)


def test_Xi_reality_check_raises_valueerror_not_assertionerror():
    with pytest.raises(ValueError):
        Xi(10, dps=30, tol_digits=-100)


# --- cache correctness ------------------------------------------------------

def test_scan_cache_key_separates_nearby_endpoints():
    """REGRESSION: a '%.6f' cache key merged t1 = 100.0 with t1 = 100.0000001
    and served one scan's brackets for the other."""
    from zeta.core import _scan_cache_path
    assert _scan_cache_path(0.5, 100.0, 1000, 15) != _scan_cache_path(
        0.5, 100.0000001, 1000, 15
    )


def test_scan_cache_ignores_a_payload_that_does_not_match_the_request(tmp_path):
    """REGRESSION: the cached payload's own t0/t1/n/dps were never checked, so a
    stale or colliding file was trusted blindly."""
    from zeta.core import _scan_cache_path

    path = _scan_cache_path(0.5, 31.0, 401, 15)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump({"t0": 999.0, "t1": 1000.0, "n_samples": 7, "dps": 99,
                   "brackets": [[1.0, 2.0]]}, fh)
    try:
        got = hardy_Z_sign_changes(0.5, 31.0, 401, dps=15, cache=True)
        assert got != [(1.0, 2.0)]
        assert len(got) == 4          # gamma_1..4 all lie below 31
    finally:
        if os.path.exists(path):
            os.remove(path)


def test_data_dir_points_at_the_repo_data_folder():
    from zeta.core import DATA_DIR
    assert os.path.basename(DATA_DIR) == "data"
    assert os.path.isdir(os.path.dirname(DATA_DIR))


# --- previously unexercised public surface ----------------------------------

@pytest.mark.parametrize("x,t", [("0.3", "0.05"), ("0.0", "0.4"), ("0.42", "1.0")])
def test_theta_heat_gaussian_matches_mpmath_jtheta(x, t):
    """The periodised-Gaussian form was exported and imported but never called
    directly by a test.  Oracle: Theta(x,t) = jtheta(3, pi x, exp(-4 pi^2 t))."""
    with mp.workdps(50):
        xv, tv = mp.mpf(x), mp.mpf(t)
        oracle = mp.jtheta(3, mp.pi * xv, mp.exp(-4 * mp.pi ** 2 * tv))
        assert _abs(theta_heat_gaussian(xv, tv, dps=35) - oracle) < mp.mpf("1e-33")
        assert _abs(theta_heat(xv, tv, dps=35) - oracle) < mp.mpf("1e-33")


def test_theta_explicit_term_count():
    """The `terms` argument is part of the API; truncating must lose exactly the
    dropped tail, 2*sum_{n>K} exp(-pi n^2 x)."""
    with mp.workdps(45):
        x = mp.mpf("0.6")
        full = theta(x, dps=35)
        cut = theta(x, dps=35, terms=3)
        tail = 2 * mp.fsum([mp.exp(-mp.pi * n * n * x) for n in range(4, 60)])
        assert _abs((full - cut) - tail) < mp.mpf("1e-33")


def test_zeta_raises_at_the_pole():
    with pytest.raises(ValueError):
        zeta(1)


# --- independent oracles for the headline claims ----------------------------

def test_zero_count_below_100_against_mpmath_nzeros():
    """Third independent route to 'exactly 29 zeros with 0 < gamma < 100':
    the Z-scan, Riemann-von Mangoldt with Backlund's S(T), and mp.nzeros."""
    with mp.workdps(30):
        assert mp.nzeros(100) == 29
        assert mp.nzeros(50) == 10
        assert mp.nzeros(30) == 3
    for T, n_expected in [(30.0, 3), (50.0, 10), (100.0, 29)]:
        brackets = hardy_Z_sign_changes(0.5, T, int(60 * T), dps=15, cache=False)
        assert len(brackets) == n_expected, (T, len(brackets))


@pytest.mark.parametrize("n", [-1, 0, 1, 2, 5, 20, 100])
def test_rs_theta_hits_the_gram_points(n):
    """Gram points are DEFINED by theta(g_n) = n*pi; mp.grampoint is an oracle
    that never touches our loggamma branch choice."""
    with mp.workdps(45):
        g = mp.grampoint(n)
        assert _abs(rs_theta(g, dps=35) - n * mp.pi) < mp.mpf("1e-33"), n


def test_Xi_zero_value_via_the_theta_mellin_route():
    """Xi(0) = xi(1/2) computed a second, wholly different way: from Riemann's
    theta-Mellin representation (tanh-sinh quadrature of a theta series), with
    xi(1/2) = (1/2)(1/2)(1/2 - 1) * Lambda(1/2) = -Lambda(1/2)/8."""
    with mp.workdps(50):
        indep = -theta_mellin_xi(mp.mpf(1) / 2, dps=40) / 8
        assert _abs(Xi(0, dps=35) - indep) < mp.mpf("1e-33")
        # true digits: 0.49712077818831410991277374...  (the previous literal
        # ...10986 was off in its own last two digits, hidden by the tolerance)
        assert _abs(indep - mp.mpf("0.49712077818831410991277374")) < mp.mpf("1e-25")


@pytest.mark.parametrize("t,rel_tol", [("0.02", "1e-33"), ("0.05", "1e-35"),
                                       ("0.1", "1e-35"), ("0.3", "1e-35")])
def test_heat_residual_relative_accuracy_where_it_is_good(t, rel_tol):
    """Relative, not absolute: |residual| / |d^2 Theta/dx^2|, with the second
    derivative computed independently by differentiating the series term by
    term.  This is the figure that actually certifies D = 1."""
    with mp.workdps(60):
        x, tv = mp.mpf("0.42"), mp.mpf(t)
        dxx = mp.fsum([-2 * (2 * mp.pi * n) ** 2
                       * mp.exp(-(2 * mp.pi * n) ** 2 * tv)
                       * mp.cos(2 * mp.pi * n * x) for n in range(1, 200)])
        r = theta_heat_residual(x, tv, dps=30)
        assert _abs(r) / _abs(dxx) < mp.mpf(rel_tol), (t, r, dxx)


def test_heat_residual_relative_accuracy_degrades_at_large_t():
    """Honesty test.  At t = 1 the second derivative has decayed to 5.0e-16, so
    the finite-difference RELATIVE residual is limited by round-off (measured
    8.9e-27 at dps=30) even though the ABSOLUTE residual is 4.4e-42.  Raising
    the working precision recovers it (8.1e-36 at dps=45).  The docstring says
    exactly this; the test makes sure it stays true."""
    with mp.workdps(70):
        x, tv = mp.mpf("0.42"), mp.mpf(1)
        dxx = mp.fsum([-2 * (2 * mp.pi * n) ** 2
                       * mp.exp(-(2 * mp.pi * n) ** 2 * tv)
                       * mp.cos(2 * mp.pi * n * x) for n in range(1, 200)])
        assert _abs(dxx) < mp.mpf("1e-15")            # exponentially small
        lo = theta_heat_residual(x, tv, dps=30)
        hi = theta_heat_residual(x, tv, dps=45)
        assert _abs(lo) < mp.mpf("1e-40")             # absolute: still excellent
        assert _abs(lo) / _abs(dxx) > mp.mpf("1e-30")  # relative: genuinely worse
        assert _abs(hi) / _abs(dxx) < mp.mpf("1e-34")  # ... and dps fixes it


# ---------------------------------------------------------------------------
# Regression tests from the second adversarial verification pass.
# ---------------------------------------------------------------------------

def test_euler_maclaurin_negative_sigma_cancellation_guard():
    """REGRESSION.  For Re(s) = sigma < 1 the truncated sum and the integral
    term N^{1-s}/(s-1) both grow like N^{1-sigma} and cancel; the fixed 15
    guard digits could not absorb it.  Measured before the fix at dps=30:
    rel err 1.7e-26 at s=-15.5 (N=20) and 1.2e-17 at s=-19.5 (N=40) -- and
    euler_maclaurin_suggest_N made it WORSE (larger N = more cancellation).
    The working precision now carries ceil((1-sigma) log10 N) extra digits.

    Post-fix measurements: <= 4.6e-32 relative with the suggested N.  The
    guard fixes round-off only: at s=-19.5 with N=20 < |s| the remaining
    3.6e-27 is the honest asymptotic-series remainder (hence the looser bound
    on that line -- pre-fix the same point was 1e-22-ish and N=40 was 1.2e-17)."""
    with mp.workdps(60):
        for s_str in ["-10.5", "-15.5", "-19.5"]:
            s = mp.mpf(s_str)
            ref = mp.zeta(s)
            for N in (euler_maclaurin_suggest_N(s, dps=30), 40):
                got = zeta_euler_maclaurin(s, N=N, M=20, dps=30)
                rel = _abs(got - ref) / _abs(ref)
                assert rel < mp.mpf("1e-28"), (s_str, N, rel)
        s = mp.mpf("-19.5")
        got = zeta_euler_maclaurin(s, N=20, M=20, dps=30)
        assert _abs(got - mp.zeta(s)) / _abs(mp.zeta(s)) < mp.mpf("1e-24")
        # complex, negative real part
        s = mp.mpc(-12, 5)
        got = zeta_euler_maclaurin(s, N=40, M=20, dps=30)
        assert _abs(got - mp.zeta(s)) / _abs(mp.zeta(s)) < mp.mpf("1e-28")


def test_zeta_via_eta_near_a_nonpole_zero_of_the_denominator():
    """REGRESSION.  At s = 1 + 2 pi i k / log 2 (k != 0), zeta is finite and
    eta has a matching zero, but eta is computed to fixed ABSOLUTE accuracy
    while the denominator is ~1e-41 for the rounded input: the quotient came
    out as -3.2e-6 - 2.6e-7j instead of zeta(s) = 1.3466 + 0.1099j, silently.
    Guard digits now track -log10|1 - 2^{1-s}|.

    The oracle needs care here: mp.zeta itself goes through the SAME
    1/(1 - 2^{1-s}) factor for complex s in the strip, so mp.zeta(sk) at
    45 dps is itself 3.2e-6 wrong at this point.  The reference must be
    computed with enough working precision (120 dps: denominator error 1e-120
    against |denom| ~ 1e-46 leaves 74 good digits)."""
    with mp.workdps(45):
        sk = 1 + 2 * mp.pi * mp.mpc(0, 1) / mp.log(2)   # k = 1, to 45 digits
    with mp.workdps(120):
        ref = mp.zeta(sk)
    got = zeta_via_eta(sk, dps=30)
    with mp.workdps(45):
        assert _abs(got - ref) / _abs(ref) < mp.mpf("1e-27"), (got, ref)
        # and mpmath's own zeta really is off here at matched precision,
        # i.e. the fixed quotient beats the naive oracle:
        naive = mp.zeta(sk)
        assert _abs(naive - ref) / _abs(ref) > mp.mpf("1e-7")


def test_real_argument_functions_accept_mpc_with_zero_imag():
    """REGRESSION.  Xi(mpc(5,0)) etc. raised TypeError ('cannot create mpf
    from mpc') from mp.mpf(mpc): the imag-part check passed but the coercion
    could not handle an mpc.  All real-argument entry points now share one
    coercion helper."""
    with mp.workdps(40):
        assert _abs(Xi(mp.mpc(5, 0), dps=30) - Xi(5, dps=30)) < mp.mpf("1e-28")
        assert _abs(Z(mp.mpc(5, 0), dps=30) - Z(5, dps=30)) < mp.mpf("1e-28")
        assert _abs(rs_theta(mp.mpc(5, 0), dps=30) - rs_theta(5, dps=30)) < mp.mpf("1e-28")
        assert _abs(theta(mp.mpc(2, 0), dps=30) - theta(2, dps=30)) < mp.mpf("1e-28")
        assert _abs(omega(mp.mpc(2, 0), dps=30) - omega(2, dps=30)) < mp.mpf("1e-28")
        assert _abs(theta_modular_defect(mp.mpc(2, 0), dps=30)) < mp.mpf("1e-28")
        a = theta_heat(mp.mpc("0.3", 0), mp.mpc("0.05", 0), dps=30)
        assert _abs(a - theta_heat("0.3", "0.05", dps=30)) < mp.mpf("1e-28")


def test_real_argument_functions_reject_complex_with_valueerror():
    """REGRESSION.  omega/theta_heat/theta_heat_gaussian/theta_heat_residual
    raised TypeError (or nothing) on genuinely complex input; the documented
    contract is ValueError, which theta/Z/Xi already honoured."""
    with pytest.raises(ValueError):
        omega(mp.mpc(1, 1))
    with pytest.raises(ValueError):
        theta_modular_defect(mp.mpc(1, 1))
    with pytest.raises(ValueError):
        theta_heat(mp.mpc("0.3", "0.1"), "0.05")
    with pytest.raises(ValueError):
        theta_heat_gaussian("0.3", mp.mpc("0.05", "0.1"))
    with pytest.raises(ValueError):
        theta_heat_residual(mp.mpc("0.3", "0.1"), "0.05")
    with pytest.raises(ValueError):
        rs_theta(mp.mpc(1, 1))


def test_domain_validated_even_with_explicit_terms():
    """REGRESSION.  With `terms` given, the adaptive term-count helper (which
    held the only x > 0 / t > 0 check) is skipped: theta(-1, terms=5) happily
    summed exp(+pi n^2) and returned garbage.  Ditto omega and theta_heat.
    A negative h in theta_heat_residual slipped past the t > 2h check."""
    with pytest.raises(ValueError):
        theta(-1, terms=5)
    with pytest.raises(ValueError):
        omega(-1, terms=5)
    with pytest.raises(ValueError):
        theta_heat("0.3", "-0.05", terms=5)
    with pytest.raises(ValueError):
        theta_heat_residual("0.3", "0.05", h="-1e-8")
