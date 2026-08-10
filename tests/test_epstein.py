"""Tests for zeta.epstein — the Davenport-Heilbronn counterexample battery.

Every literal quoted here was computed and cross-checked in this environment
before being asserted (kappa derivation at dps = 50 from four independent
base points; the off-line zero polished at dps = 70 with |f(rho)| = 4.1e-71
and confirmed against Spira, Math. Comp. 63 (1994), 747-748:
0.808517 + 85.699348i).

The headline assertions, in the order the module's story runs:

1. kappa is *derived* from the functional-equation condition and satisfies it
   (defect < 1e-25 as required, measured far smaller), is real, is base-point
   independent, and — observation, never input — matches the closed form
   (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1).
2. f has real, periodic, NON-multiplicative Dirichlet coefficients, is
   entire (no pole at s = 1: mean-value certificate), and obeys F(s) = F(1-s).
3. f has a verified zero OFF the critical line at the pinned location —
   |f(rho)| tiny, |Re rho - 1/2| = 0.3085... > 0.05, winding certificate 1 —
   while the box-count vs line-count discrepancy that led to it is
   reproduced.  The functional equation alone cannot imply RH.
"""

from __future__ import annotations

import mpmath
import pytest
from mpmath import mp

from zeta.epstein import (
    KAPPA_REF,
    OFFLINE_ZERO_IM,
    OFFLINE_ZERO_RE,
    L_chi,
    Z_dh,
    battery,
    chi5,
    claim_functional_equation,
    claim_multiplicativity,
    completed_dh,
    count_zeros_box,
    dh_coefficient,
    dh_f,
    dh_functional_equation_defect,
    dh_mean_value_defect,
    dh_theta,
    find_offline_zero,
    kappa,
    zeros_on_line,
    zeta_interface,
)


def _pinned_zero(dps: int):
    """The pinned off-line zero parsed at ``dps`` digits (parse *inside* a
    workdps context — parsing at ambient precision would silently truncate)."""
    with mp.workdps(dps):
        return mp.mpc(mp.mpf(OFFLINE_ZERO_RE), mp.mpf(OFFLINE_ZERO_IM))


# ---------------------------------------------------------------------------
# the character and the L-functions
# ---------------------------------------------------------------------------

def test_chi5_is_the_odd_character_with_chi2_eq_i():
    assert chi5(2) == mp.mpc(0, 1)
    assert chi5(1) == 1 and chi5(4) == -1 and chi5(3) == mp.mpc(0, -1)
    assert chi5(5) == 0 and chi5(0) == 0
    assert chi5(7) == chi5(2)  # period 5
    # completely multiplicative on the residues: chi(2)^2 = chi(4), etc.
    assert chi5(2) ** 2 == chi5(4)
    assert chi5(2) ** 3 == chi5(3)
    # odd: chi(-1) = chi(4) = -1
    assert chi5(-1) == -1


def test_L_chi_against_mpmath_dirichlet_oracle():
    """L via our Hurwitz assembly == mpmath.dirichlet (independent assembly)."""
    with mp.workdps(35):
        for s in [mp.mpc(mp.mpf(3) / 5, mp.mpf(71) / 5), mp.mpc(2, -3), mp.mpf(3)]:
            ours = L_chi(s, dps=30)
            oracle = mpmath.dirichlet(s, [0, 1, mp.mpc(0, 1), mp.mpc(0, -1), -1])
            assert abs(ours - oracle) < mp.mpf("1e-28")
            ours_bar = L_chi(s, conjugate=True, dps=30)
            oracle_bar = mpmath.dirichlet(s, [0, 1, mp.mpc(0, -1), mp.mpc(0, 1), -1])
            assert abs(ours_bar - oracle_bar) < mp.mpf("1e-28")


# ---------------------------------------------------------------------------
# kappa: derived, real, base-point independent, satisfies its condition
# ---------------------------------------------------------------------------

def test_kappa_matches_pinned_reference():
    with mp.workdps(50):
        assert abs(kappa(40) - mp.mpf(KAPPA_REF)) < mp.mpf("1e-38")


def test_kappa_satisfies_defining_condition_via_manual_completion():
    """Rebuild F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s) by hand from
    L_chi and the *returned* kappa(40), and check F(s) = F(1-s).  This does
    not reuse the derivation path, so it is a genuine closure test.  kappa is
    delivered at 40 digits, so the defect floor is ~|dF/dkappa|*1e-40."""
    with mp.workdps(55):
        k = kappa(40)
        c = (1 - mp.mpc(0, 1) * k) / 2

        def F(s):
            f = c * L_chi(s, dps=50) + mp.conj(c) * L_chi(s, conjugate=True, dps=50)
            return mp.power(mp.pi / 5, -(s + 1) / 2) * mp.gamma((s + 1) / 2) * f

        for s in [mp.mpc(mp.mpf(3) / 5, 7), mp.mpc(-1, mp.mpf(21) / 2), mp.mpc(2, -4)]:
            assert abs(F(s) - F(1 - s)) < mp.mpf("1e-36")


def test_kappa_independent_of_derivation_point():
    """Deriving kappa by the same linear solve at an unrelated base point
    gives the same real constant — the numerical content of the Gauss-sum
    identity that makes the Davenport-Heilbronn combination work."""
    with mp.workdps(50):
        def Lam(s, conj):
            return (
                mp.power(mp.pi / 5, -(s + 1) / 2)
                * mp.gamma((s + 1) / 2)
                * L_chi(s, conjugate=conj, dps=mp.dps)
            )

        s0 = mp.mpc(mp.mpf(7) / 5, mp.mpf(-7) / 10)  # != the module's 0.75+1.5i
        A = Lam(s0, False) + Lam(s0, True) - Lam(1 - s0, False) - Lam(1 - s0, True)
        B = Lam(s0, False) - Lam(s0, True) - Lam(1 - s0, False) + Lam(1 - s0, True)
        k = A / (mp.mpc(0, 1) * B)
        assert abs(mp.im(k)) < mp.mpf("1e-40")          # real
        assert abs(mp.re(k) - kappa(45)) < mp.mpf("1e-40")  # same constant


def test_kappa_matches_closed_form_observation():
    """Observation (never used by the code): kappa equals
    (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1).  Verified to 1e-50 at dps 50."""
    with mp.workdps(50):
        closed = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
        assert abs(kappa(45) - closed) < mp.mpf("1e-43")


# ---------------------------------------------------------------------------
# the functional equation: defect < 1e-25 (measured far smaller)
# ---------------------------------------------------------------------------

def test_functional_equation_defect_below_1e25():
    with mp.workdps(50):
        pts = [
            mp.mpc(2, 3),
            mp.mpc(mp.mpf(-7) / 10, mp.mpf(113) / 10),
            mp.mpc(mp.mpf(1) / 5, -6),
            mp.mpc(mp.mpf(29) / 10, mp.mpf(171) / 10),
        ]
        for s in pts:
            d = dh_functional_equation_defect(s, dps=40)
            assert abs(d) < mp.mpf("1e-25")


def test_completed_symmetric_across_trivial_zeros():
    """F(-1) = F(2) and F(-3) = F(4): the removable-singularity branch of
    completed_dh (circle average at the Gamma poles) agrees with the generic
    branch across the functional equation — a non-circular check, exactly as
    for zeta.core.xi at the trivial zeros."""
    with mp.workdps(40):
        assert abs(completed_dh(-1, dps=30) - completed_dh(2, dps=30)) < mp.mpf("1e-28")
        assert abs(completed_dh(-3, dps=30) - completed_dh(4, dps=30)) < mp.mpf("1e-28")
        # and the completion is finite, real, nonzero there
        assert completed_dh(-1, dps=30) > 1


def test_completed_dh_keeps_precision_near_removable_point():
    """Regression (adversarial-verifier find): the generic branch of
    completed_dh must inherit dh_f's Hurwitz-cancellation guard near the
    removable s = 1.  Without it, completed_dh(1 + 1e-20, dps=30) was off by
    ~4e-23 (the pole cancellation silently ate ~20 of the requested digits);
    with the guard the dps-30 and dps-60 evaluations agree to ~1e-31."""
    with mp.workdps(70):
        for eps in [mp.mpf("1e-8"), mp.mpf("1e-20")]:
            s = 1 + eps
            lo = completed_dh(s, dps=30)
            hi = completed_dh(s, dps=60)
            assert abs(lo - hi) < mp.mpf("1e-27")


# ---------------------------------------------------------------------------
# f itself: entire, real coefficients, trivial zeros, no Euler product
# ---------------------------------------------------------------------------

def test_dh_f_is_entire_no_pole_at_1():
    """The four Hurwitz poles at s = 1 cancel.  Certified two ways: the Gauss
    mean value over a circle whose disc CONTAINS s = 1 equals the centre
    value (a simple pole inside would leave residue/(pole - centre)), and f
    is continuous through s = 1 (removable point evaluated by circle mean)."""
    with mp.workdps(40):
        mv = dh_mean_value_defect(mp.mpf("1.001"), radius=mp.mpf(1) / 4, dps=30)
        assert abs(mv) < mp.mpf("1e-25")
        f1 = dh_f(1, dps=30)
        assert mp.isfinite(f1)
        # value computed independently at dps 70: f(1) = 0.9228018738028908721...
        assert abs(f1 - mp.mpf("0.9228018738028908721")) < mp.mpf("1e-15")
        assert abs(dh_f(mp.mpf(1) + mp.mpf("1e-12"), dps=30) - f1) < mp.mpf("1e-9")


def test_dh_coefficients_real_periodic_and_correct():
    with mp.workdps(40):
        k = kappa(30)
        want = [mp.mpf(1), k, -k, mp.mpf(-1), mp.mpf(0)]
        for n in range(1, 21):
            a = dh_coefficient(n, dps=30)
            assert isinstance(a, mp.mpf)  # real by construction, checked
            assert abs(a - want[(n - 1) % 5]) < mp.mpf("1e-28")
        # first ~20 coefficients real: the n-th coefficient of the combination
        # c*L(s,chi) + conj(c)*L(s,chibar) is c*chi(n) + conj(c)*conj(chi(n)),
        # assembled here in complex arithmetic — its Im must vanish
        c = (1 - mp.mpc(0, 1) * k) / 2
        for n in range(1, 21):
            v = c * chi5(n) + mp.conj(c) * mp.conj(chi5(n))
            assert abs(mp.im(v)) < mp.mpf("1e-28")
            assert abs(mp.re(v) - want[(n - 1) % 5]) < mp.mpf("1e-28")


def test_dh_coefficients_reproduce_f_dirichlet_series():
    """Independent oracle for f: the raw truncated Dirichlet series
    sum_{n<=N} a_n n^{-s} at s = 3 + 0.7i (no Hurwitz continuation involved).
    Bounded coefficient partial sums give |tail| ~ N^{-3}: N = 2000 -> ~1e-10."""
    with mp.workdps(30):
        s = mp.mpc(3, mp.mpf(7) / 10)
        acc = mp.mpc(0)
        coeffs = [dh_coefficient(n, dps=25) for n in range(1, 6)]
        for n in range(1, 2001):
            acc += coeffs[(n - 1) % 5] * mp.power(n, -s)
        assert abs(acc - dh_f(s, dps=25)) < mp.mpf("1e-8")


def test_dh_trivial_zeros_at_odd_negative_integers():
    """chi is odd, so f's trivial zeros sit at s = -1, -3, -5 (zeta's sit at
    -2, -4, ...): f vanishes at the former and not at the latter."""
    with mp.workdps(45):
        assert abs(dh_f(-1, dps=40)) < mp.mpf("1e-30")
        assert abs(dh_f(-3, dps=40)) < mp.mpf("1e-30")
        assert abs(dh_f(-2, dps=40)) > mp.mpf("0.5")   # = -0.9136...


def test_no_euler_product_coefficients_not_multiplicative():
    """a_6 = a_1 = 1 but a_2 a_3 = -kappa^2 = -0.0807...;
    a_14 = a_4 = -1 but a_2 a_7 = +kappa^2.  This is the single structural
    property that separates f from zeta (docs/08 section 4.1)."""
    with mp.workdps(40):
        a = lambda n: dh_coefficient(n, dps=30)
        assert abs(a(6) - a(2) * a(3)) > mp.mpf("0.9")
        assert abs(a(14) - a(2) * a(7)) > mp.mpf("0.9")
        # the accidental survivor: (3,4) passes by the period-5 pattern
        assert abs(a(12) - a(3) * a(4)) < mp.mpf("1e-28")
        # zeta's coefficients (all 1) are trivially multiplicative
        za = zeta_interface(30)["coefficient"]
        assert za(6) == za(2) * za(3) == 1


def test_zero_free_for_sigma_ge_2():
    """sum_{n>=2} |a_n| n^{-2} < 1 pins |f(s) - 1| < 1 for Re s >= 2, so all
    complex zeros have Re s < 2 (and, by the functional equation, Re s > -1):
    the [-1, 2] strip used by the box counts really contains them all."""
    with mp.workdps(30):
        k = kappa(25)
        total = mp.power(5, -2) * (
            mp.zeta(2, mp.mpf(1) / 5) + k * mp.zeta(2, mp.mpf(2) / 5)
            + k * mp.zeta(2, mp.mpf(3) / 5) + mp.zeta(2, mp.mpf(4) / 5)
        ) - 1
        assert total < mp.mpf("0.27")  # = 0.26666..., comfortably < 1


# ---------------------------------------------------------------------------
# the Hardy-Z analogue
# ---------------------------------------------------------------------------

def test_Z_dh_is_real_and_matches_pinned_value():
    with mp.workdps(30):
        v = Z_dh(mp.mpf("85.7"), dps=25)
        assert isinstance(v, mp.mpf)
        # value verified at dps 25 and 40 in this environment
        assert abs(v - mp.mpf("-0.356831920821522")) < mp.mpf("1e-10")


def test_Z_dh_equals_completed_over_positive_factor():
    """Z_f(t) and F(1/2 + it) must have the same sign pattern: Z_f is F
    divided by |(pi/5)^{-(s+1)/2} Gamma((s+1)/2)| > 0."""
    with mp.workdps(30):
        for t in [mp.mpf(5), mp.mpf(20), mp.mpf("85.7")]:
            s = mp.mpc(mp.mpf(1) / 2, t)
            P = mp.power(mp.pi / 5, -(s + 1) / 2) * mp.gamma((s + 1) / 2)
            F = completed_dh(s, dps=25)
            z = Z_dh(t, dps=25)
            assert abs(z - mp.re(F) / abs(P)) < mp.mpf("1e-20") * (1 + abs(z))


def test_dh_theta_continuous_branch():
    """theta_f grows ~ (t/2) log(5t/(2 pi e)); spot-check monotonicity and a
    finite value (loggamma branch, no +-pi wrapping)."""
    with mp.workdps(30):
        v50, v51 = dh_theta(50, dps=25), dh_theta(51, dps=25)
        assert v51 > v50 > 0
        # rate ~ 0.5*log(5t/(2 pi)) ~ 1.84 at t = 50
        assert mp.mpf("1.5") < v51 - v50 < mp.mpf("2.2")


# ---------------------------------------------------------------------------
# THE PAYOFF: the off-critical-line zero
# ---------------------------------------------------------------------------

def test_offline_zero_is_a_zero_and_is_off_the_line():
    """The pinned zero satisfies |f(rho)| < 1e-25 (measured ~5e-49 for the
    50-digit rounding) and |Re rho - 1/2| = 0.30851... > 0.05.  The
    functional equation alone permitted this; the Euler product would not
    have.  RH is FALSE for the Davenport-Heilbronn function."""
    rho = _pinned_zero(60)
    with mp.workdps(60):
        assert abs(dh_f(rho, dps=55)) < mp.mpf("1e-25")
        assert abs(mp.re(rho) - mp.mpf(1) / 2) > mp.mpf("0.05")
        assert abs(mp.re(rho) - mp.mpf("0.80851718245663738555")) < mp.mpf("1e-18")
        assert abs(mp.im(rho) - mp.mpf("85.699348485377592171929")) < mp.mpf("1e-18")


def test_offline_zero_mirror_partner():
    """Real coefficients + F(s) = F(1-s) force the mirror zero 1 - conj(rho);
    both it and conj(rho) (Schwarz) vanish to the same accuracy."""
    rho = _pinned_zero(60)
    with mp.workdps(60):
        assert abs(dh_f(1 - mp.conj(rho), dps=55)) < mp.mpf("1e-25")
        assert abs(dh_f(mp.conj(rho), dps=55)) < mp.mpf("1e-25")


def test_offline_zero_survives_independent_polish():
    """mp.findroot restarted from the pinned value at dps 50 does not move:
    the constant is a genuine root to its stated precision."""
    rho = _pinned_zero(55)
    with mp.workdps(55):
        root = mp.findroot(lambda z: dh_f(z, dps=50), rho)
        assert abs(root - rho) < mp.mpf("1e-40")


def test_offline_zero_winding_certificate():
    """Argument-principle certificate: winding number 1 around a side-0.2 box
    centred on rho, a box that sits entirely RIGHT of the critical line
    (Re in [0.7085, 0.9085]), so the zero inside cannot be a line zero."""
    rho = _pinned_zero(30)
    with mp.workdps(30):
        h = mp.mpc(mp.mpf(1) / 10, mp.mpf(1) / 10)
        assert mp.re(rho) - mp.mpf(1) / 10 > mp.mpf(1) / 2  # box clear of line
        assert count_zeros_box(rho - h, rho + h, dps=20) == 1


def test_box_count_exceeds_line_count_in_offline_window():
    """The smoking gun, scripts/02 in reverse: the strip box around
    t in [85.2, 86.2] holds 2 zeros while Z_f has 0 sign changes there —
    for zeta that equality never breaks (verify_rh_up_to); for f it does.
    The right half-box isolates 1 of the pair (its mirror holds the other)."""
    with mp.workdps(25):
        t0, t1 = mp.mpf("85.2"), mp.mpf("86.2")
        n_box = count_zeros_box(mp.mpc(-1, t0), mp.mpc(2, t1), dps=20)
        n_line = zeros_on_line(t0, t1, dps=15)
        assert n_box == 2
        assert n_line == 0
        assert n_box > n_line
        n_right = count_zeros_box(mp.mpc(mp.mpf("0.55"), t0), mp.mpc(2, t1), dps=20)
        assert n_right == 1


@pytest.mark.slow
def test_no_offline_zero_below_the_pinned_one():
    """The pinned zero at t ~ 85.7 is the *lowest* off-line zero, so the Lean
    arm's certification target is forced rather than chosen.

    A box with Re in [0.55, 2] contains only off-line zeros by construction
    (line zeros have Re = 1/2 exactly, and `test_zero_free_for_sigma_ge_2`
    pins f away from 0 for Re >= 2).  Scanning 0 < t < 80 in ten-wide
    windows finds none; the window holding the pinned zero finds one.
    Coefficients are real, so the t < 0 half mirrors this one.

    Why it is worth a standing test: the cost of certifying the zero inside
    Lean scales like ||s||^2.2 (`lean/ZetaLean/DHDemo.lean`, HANDOFF), so a
    lower-height off-line zero would have been worth orders of magnitude.
    There is none, and this test is what says so.
    """
    with mp.workdps(20):
        for a in range(0, 80, 10):
            t0, t1 = mp.mpf(a) + mp.mpf("0.3"), mp.mpf(a + 10) + mp.mpf("0.3")
            n = count_zeros_box(mp.mpc(mp.mpf("0.55"), t0), mp.mpc(2, t1), dps=20)
            assert n == 0, (float(t0), float(t1), n)
        t0, t1 = mp.mpf("80.3"), mp.mpf("90.3")
        assert count_zeros_box(mp.mpc(mp.mpf("0.55"), t0), mp.mpc(2, t1), dps=20) == 1


def test_line_zeros_do_exist_too():
    """f is not zero-free on the line — infinitely many line zeros (a positive
    proportion, Bombieri-Ghosh); one sits in [86, 88]."""
    assert zeros_on_line(86, 88, dps=15) == 1


def test_zeta_interface_box_equals_line_where_dh_disagrees():
    """The contrast that IS gate #3: for zeta, box count == line count
    (here around gamma_1 = 14.13...); f fails exactly this equality."""
    zi = zeta_interface(25)
    with mp.workdps(25):
        assert zi["count_zeros_box"](mp.mpc(-1, 13), mp.mpc(2, 15)) == 1
        assert zi["zeros_on_line"](13, 15) == 1


@pytest.mark.slow
def test_full_offline_window_84_92():
    """The original discovery window: box [ -1, 2] x [84, 92] holds 5 zeros,
    the line only 3 — an excess of exactly one mirror pair."""
    with mp.workdps(25):
        n_box = count_zeros_box(mp.mpc(-1, 84), mp.mpc(2, 92), dps=20)
        n_line = zeros_on_line(84, 92, dps=15)
        assert n_box == 5
        assert n_line == 3


@pytest.mark.slow
def test_find_offline_zero_end_to_end():
    """The full hunt (window scan -> bisect -> polish -> verify) reproduces
    the pinned zero from scratch in the [84, 88] window."""
    rho = find_offline_zero(t_lo=84, t_hi=88, window=4, dps=30)
    ref = _pinned_zero(40)
    with mp.workdps(40):
        assert abs(mp.mpmathify(rho) - ref) < mp.mpf("1e-25")
        assert abs(mp.re(rho) - mp.mpf(1) / 2) > mp.mpf("0.05")


# ---------------------------------------------------------------------------
# the falsification harness
# ---------------------------------------------------------------------------

def test_battery_functional_equation_does_not_distinguish():
    res = battery(claim_functional_equation)
    assert res["riemann_zeta"] is True
    assert res["davenport_heilbronn"] is True
    assert res["distinguishes"] is False


def test_battery_multiplicativity_distinguishes():
    res = battery(claim_multiplicativity)
    assert res["riemann_zeta"] is True
    assert res["davenport_heilbronn"] is False
    assert res["distinguishes"] is True


def test_battery_reports_claim_name():
    res = battery(claim_multiplicativity)
    assert res["claim"] == "claim_multiplicativity"


def test_battery_accepts_custom_claims():
    """A user-supplied claim runs against both interfaces: 'the completed
    function is real on the critical line' — true for both (and therefore,
    per gate #3, useless on its own as an RH mechanism)."""
    def claim_real_on_line(iface):
        with mp.workdps(30):
            v = iface["Z"](mp.mpf("17.3"))
            return isinstance(v, mp.mpf)

    res = battery(claim_real_on_line)
    assert res["riemann_zeta"] is True
    assert res["davenport_heilbronn"] is True
    assert res["distinguishes"] is False


# ---------------------------------------------------------------------------
# Epstein zeta functions -- gate #3's second counterexample family
# ---------------------------------------------------------------------------

def test_reduced_forms_have_the_right_class_numbers():
    from zeta.epstein import epstein_reduced_forms

    assert epstein_reduced_forms(-4) == ((1, 0, 1),)                  # h = 1
    assert epstein_reduced_forms(-15) == ((1, 1, 4), (2, 1, 2))       # h = 2
    assert epstein_reduced_forms(-23) == ((1, 1, 6), (2, -1, 3), (2, 1, 3))
    for form in epstein_reduced_forms(-23):
        a, b, c = form
        assert b * b - 4 * a * c == -23
    with pytest.raises(ValueError):
        epstein_reduced_forms(23)


def test_representation_counts_and_their_multiplicativity_failure():
    from zeta.epstein import epstein_representation_count as r

    principal = (1, 1, 6)
    assert [r(n, principal) for n in range(1, 13)] == [2, 0, 0, 2, 0, 4, 0, 4, 2, 0, 0, 4]
    assert [r(n, (2, 1, 3)) for n in range(1, 13)] == [0, 2, 2, 2, 0, 2, 0, 2, 2, 0, 0, 4]
    # No Euler product: r(6) != r(2) r(3) for either form.
    assert r(6, principal) == 4 and r(2, principal) == 0 and r(3, principal) == 0
    assert r(6, (2, 1, 3)) == 2 and r(2, (2, 1, 3)) * r(3, (2, 1, 3)) == 4
    with pytest.raises(ValueError):
        r(0, principal)


def test_epstein_zeta_matches_its_defining_sum_where_that_converges():
    from zeta.epstein import epstein_zeta

    for form in ((1, 1, 6), (2, 1, 3)):
        a, b, c = form
        with mp.workdps(25):
            direct = mp.fsum(
                mp.power(a * m * m + b * m * n + c * n * n, -mp.mpf(4))
                for m in range(-70, 71)
                for n in range(-70, 71)
                if (m, n) != (0, 0)
            )
        assert epstein_zeta(4, form, dps=20) == pytest.approx(float(direct), rel=1e-10)


def test_class_group_identity_is_the_independent_check():
    """sum_Q zeta_Q(s) = w zeta(s) L(s, chi_D), computed with disjoint code.

    This is the validation that can actually fail: the right-hand side uses
    mpmath's zeta and a Hurwitz-zeta character sum, sharing nothing with the
    lattice sums on the left.
    """
    from zeta.epstein import epstein_class_group_defect

    for D in (-4, -15, -23):
        for s in (mp.mpf(2), mp.mpc(mp.mpf(1) / 2, 4)):
            assert abs(epstein_class_group_defect(s, D, dps=20)) < mp.mpf("1e-18")


def test_epstein_functional_equation_is_structural_not_measured():
    """Documented as built into the representation -- pinned so it stays honest.

    A future rewrite that makes this defect merely small rather than exactly
    zero would mean the symmetry is no longer manifest, and the docstring's
    warning would need revisiting.
    """
    from zeta.epstein import epstein_functional_equation_defect

    for form in ((1, 1, 6), (2, 1, 3)):
        defect = epstein_functional_equation_defect(mp.mpc(mp.mpf(3) / 4, 5), form, dps=20)
        assert defect == 0


def test_Z_epstein_is_real_on_the_critical_line():
    from zeta.epstein import Z_epstein

    for form in ((1, 1, 6), (2, 1, 3)):
        for t in (3, 5, 11):
            value = Z_epstein(t, form, dps=20)
            assert mp.im(mp.mpmathify(value)) == 0


def test_battery_runs_epstein_as_a_second_counterexample():
    """Gate #3 names Davenport-Heilbronn *and* generic Epstein zeta functions.

    Both discriminant -23 forms run by default: the non-principal (2,1,3) and
    the principal (1,1,6) — each a linear combination of the three Hecke
    L-functions of the class group, instantiating the linear-combination
    sharpening of the gate (docs/09 SS5.1)."""
    res = battery(claim_functional_equation, dps=20)
    assert res["riemann_zeta"] and res["davenport_heilbronn"]
    assert res["epstein_2_1_3"] and res["epstein_1_1_6"]
    assert res["distinguishes"] is False
    assert "epstein_2_1_3" in res["shared_with"]
    assert "epstein_1_1_6" in res["shared_with"]

    res = battery(claim_multiplicativity, dps=20)
    assert res["riemann_zeta"]
    assert not res["davenport_heilbronn"]
    assert not res["epstein_2_1_3"] and not res["epstein_1_1_6"]
    assert res["distinguishes"] is True
    assert res["shared_with"] == ()


def test_battery_requires_every_counterexample_to_fail():
    """A claim shared with any rival must not be reported as distinguishing."""
    shared_with_epstein_only = lambda iface: iface["name"] != "davenport_heilbronn"
    res = battery(shared_with_epstein_only, dps=20)
    assert res["riemann_zeta"] and res["epstein_2_1_3"] and res["epstein_1_1_6"]
    assert res["distinguishes"] is False
    assert res["shared_with"] == ("epstein_1_1_6", "epstein_2_1_3")


# ---------------------------------------------------------------------------
# The steeper tail bounds (lean/ZetaLean/DHTailBound2.lean)
#
# These pin, numerically, exactly the three inequalities the Lean arm proves
# about the Dirichlet-series tail of f:
#
#   order 0 (DH_tail_bound):        |f(s) - S_K|
#       <= (3+k)|s| 5^(-sig-1) (K-1)^(-sig) / sig
#   order 1 (DH_tail_bound_order1): |f(s) - (S_K - F(K))|
#       <= (3+k)|s||s+1| (5K+1)^(-sig-1) / (sig+1)
#   order 2 (DH_tail_bound_order2): |f(s) - (S_K + B(K)/2 - F(K))|
#       <= (5/8)(3+k)|s||s+1||s+2| (5K+1)^(-sig-2) / (sig+2)
#
# with S_K the 5K-term partial sum, B(x) the paired block
# (5x+1)^{-s} - (5x+4)^{-s} + k[(5x+2)^{-s} - (5x+3)^{-s}], and
# F(x) = [(5x+1)^{1-s} - (5x+4)^{1-s} + k((5x+2)^{1-s} - (5x+3)^{1-s})]
# / (5(1-s)) the closed-form block antiderivative (finite precisely because
# the coefficients sum to zero).  The reference value is dh_f — the Hurwitz
# route, which never touches the Dirichlet series.  Each extra order is one
# power of K: it is what turns rung 3's certification from months into hours
# (K for a 1e-3 tail at the oracle zero: 195301 -> 1741 -> 243).
# ---------------------------------------------------------------------------


def _dh_pair(w, x, k):
    """(5x+1)^w - (5x+4)^w + k[(5x+2)^w - (5x+3)^w] — dhPair in the Lean arm."""
    return (
        mp.power(5 * x + 1, w)
        - mp.power(5 * x + 4, w)
        + k * (mp.power(5 * x + 2, w) - mp.power(5 * x + 3, w))
    )


def _dh_partial(s, K, k):
    """The 5K-term partial sum of the DH Dirichlet series."""
    total = mp.mpc(0)
    for j in range(K):
        total += _dh_pair(-s, mp.mpf(j), k)
    return total


def _dh_tail_bounds(s, K, k):
    """The three kernel-checked tail radii at (s, K)."""
    sig, ns = mp.re(s), abs(s)
    b0 = (3 + k) * ns * mp.power(5, -sig - 1) * mp.power(K - 1, -sig) / sig
    b1 = (3 + k) * ns * abs(s + 1) * mp.power(5 * K + 1, -sig - 1) / (sig + 1)
    b2 = (
        mp.mpf(5) / 8 * (3 + k) * ns * abs(s + 1) * abs(s + 2)
        * mp.power(5 * K + 1, -sig - 2) / (sig + 2)
    )
    return b0, b1, b2


def test_dh_tail_bounds_hold_at_all_three_orders():
    """The corrected partial sums land within the certified radii.

    Mirrors DH_tail_bound / DH_tail_bound_order1 / DH_tail_bound_order2
    (lean/ZetaLean/DHTailBound.lean, DHTailBound2.lean) at the oracle zero,
    the DHDemo point, and a thin-strip stress point, against dh_f as the
    series-free reference.
    """
    with mp.workdps(35):
        k = kappa(35)
        points = [
            mp.mpc(mp.mpf(OFFLINE_ZERO_RE), mp.mpf(OFFLINE_ZERO_IM)),
            mp.mpc("1.5", "3"),
            mp.mpc("0.05", "20"),
        ]
        for s in points:
            ref = dh_f(s, dps=30)
            for K in (8, 64, 512):
                S = _dh_partial(s, K, k)
                F = _dh_pair(1 - s, mp.mpf(K), k) / (5 * (1 - s))
                B = _dh_pair(-s, mp.mpf(K), k)
                b0, b1, b2 = _dh_tail_bounds(s, K, k)
                assert abs(ref - S) <= b0
                assert abs(ref - (S - F)) <= b1
                assert abs(ref - (S + B / 2 - F)) <= b2
            # at scale, each order is strictly sharper than the last
            assert b2 < b1 < b0


def test_dh_tail_bound_order2_decay_exponent_is_sigma_plus_2():
    """The measured order-2 error decays like K^-(sigma+2) at the oracle zero.

    The bound's exponent is a theorem; this checks the *actual* error tracks
    it (between K = 256 and K = 1024), so the correction terms are really
    cancelling the lower orders rather than being absorbed by slack.
    """
    with mp.workdps(35):
        k = kappa(35)
        s = mp.mpc(mp.mpf(OFFLINE_ZERO_RE), mp.mpf(OFFLINE_ZERO_IM))
        ref = dh_f(s, dps=30)
        errs = []
        for K in (256, 1024):
            S = _dh_partial(s, K, k)
            F = _dh_pair(1 - s, mp.mpf(K), k) / (5 * (1 - s))
            B = _dh_pair(-s, mp.mpf(K), k)
            errs.append(abs(ref - (S + B / 2 - F)))
        slope = mp.log(errs[0] / errs[1]) / mp.log(4)
        assert abs(slope - (mp.re(s) + 2)) < mp.mpf("0.1")


def test_dh_tail_bound_required_K_pins_the_cost_model():
    """The minimal K with tail radius <= 1e-3 at the oracle zero, per order.

    These three integers are the cost model of rung 3's remaining compute
    (HANDOFF.md): the certified-term count falls 195301 -> 1741 -> 243
    blocks, a 804x reduction, which is what moves the offline kernel run
    from months to hours.  Computed by bisection on the closed-form radii.
    """
    with mp.workdps(40):
        k = kappa(40)
        s = mp.mpc(mp.mpf(OFFLINE_ZERO_RE), mp.mpf(OFFLINE_ZERO_IM))

        def min_K(order):
            lo, hi = 2, 10**7
            while lo < hi:
                mid = (lo + hi) // 2
                if _dh_tail_bounds(s, mid, k)[order] <= mp.mpf("1e-3"):
                    hi = mid
                else:
                    lo = mid + 1
            return lo

        assert min_K(0) == 195301
        assert min_K(1) == 1741
        assert min_K(2) == 243
