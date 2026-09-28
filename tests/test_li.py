"""
Tests for zeta.li: Li's criterion and Jensen polynomials.

The load-bearing test is :func:`test_two_methods_agree`: λ_n computed from the
Cauchy/Taylor side (ξ only, no zeros) against λ_n computed from the zero side
(zeros only, no ξ).  Everything else in the Li half of the module hangs off
that agreement.

Measured on this machine (tolerances below are set to roughly 2–20x the
measured error, so a real regression fails):

  λ₁ vs closed form 1+γ/2−log(4π)/2, dps 30:  difference exactly 0.0
                                              (equal to all 30 returned digits;
                                              also exact to all 50 at dps = 50)
  λ_n vs the Stieltjes-constant route, n ≤ 8: 8.5e-27 relative
  Cauchy vs zero-sum, n ≤ 8, 1000 zeros:      max |Δ| 1.55e-8, max rel 1.06e-8
  Cauchy vs zero-sum, n ≤ 8, 100 zeros:       max |Δ| 1.91e-6, max rel 1.31e-6
  Cauchy vs zero-sum at n = 50:               rel 1.39e-8 (no degradation)
  generating function vs literal d^n/ds^n:    7.3e-63 … 7.4e-61 for n ≤ 4 (dps 30)
  Cauchy radius independence, r ∈ {.3,…,.92}: identical to all 25 digits
  γ(n) integral vs Cauchy, n ≤ 20:            bit-identical at dps 30 and 50
  γ(n) vs Riemann's ω′ integral, n ≤ 8:       9.2e-32 relative
  γ(n) vs a dps-80 reference, n ≤ 12:         9.2e-32 (dps 30), 1.3e-51 (dps 50)
  γ(n) Cauchy radius ∈ {4, 30, 300}:          bit-identical to the integral path
  λ_n > 0 for every n ≤ 60 (and ≤ 300 in the slow tier): no violation found
  λ_n vs (n/2)(log n − log 2π + γ − 1) + 1:   rel ≤ 2.95e-2 for 50 ≤ n ≤ 300
  J^{d,n} hyperbolic for 1 ≤ d ≤ 8, 0 ≤ n ≤ 12: max rel |Im root| 1.7e-105
  X² + 1 control:                             hyperbolic False, max|Im| = 1.0
  Jensen roots vs Hermite (standardised), d=6: 0.0681 (n=10) → 0.0434 (n=110)

Independent oracles.  Three of them run *inside* this file rather than being
quoted from a notebook:

* λ_n from **Stieltjes constants and polygamma**
  (``test_lambda_from_stieltjes_constants_a_third_independent_route``), a
  closed-form expansion of log ξ(1+x) plus a binomial transform, sharing no
  code with either module method.
* γ(n) from **Riemann's ω′ form of the Ξ integral**
  (``test_gamma_against_riemanns_other_integral_an_independent_oracle``), a
  different integral representation, with ω′ and ω″ summed directly.
* the Jensen roots against **numpy.roots** (LAPACK companion-matrix QR), which
  shares nothing with mpmath's Durand–Kerner or sympy's Sturm sequences.

Also used while writing the module: ``mp.taylor(..., method='quad')``
reproduces the hand-rolled DFT λ_n to 5.7e-32 relative for n ≤ 8, and
``mp.diff(..., method='quad')`` reproduces γ(0..6) to ~1e-31.

Claims that an adversarial re-derivation found to be **false** and that are now
pinned the right way round, so they cannot come back:

* "the truncated zero sum must be below the true value", it overshoots at
  n_zeros = 400 (``test_zero_sum_truncation_error_shrinks_but_not_monotonically``);
* "the error falls like 1/T²": 800 zeros beat 1000 (same test);
* "T is chosen so that S(T) = −1/2 exactly", at the default 1000 zeros
  N(T) = 1001 and S(T) = **+1/2**
  (``test_the_truncation_height_does_not_have_S_of_T_equal_minus_one_half``);
* "max |arg ξ| stays below π/2, so the principal log is the analytic branch",
  it exceeds π/2 from r ≈ 0.915, and the old guard rejected legitimate radii
  (``test_arg_xi_needs_unwrapping_not_a_principal_branch_guard``);
* "the γ Cauchy path is radius-independent", with the old radius-blind node
  count ``2·n_max + 40`` it lost up to 45 digits at dps = 80, R = 300
  (``test_gamma_cauchy_node_count_is_radius_and_precision_aware``), and its
  radius-blind *working precision* returned γ(0) too large by 3e138 at
  R = 100 000 with no complaint
  (``test_gamma_cauchy_refuses_a_radius_it_cannot_resolve``);
* "the raw Jensen coefficients span ~40 orders by d = 16": 28.5, and the
  normalised ones span 5.9 rather than ~4
  (``test_balance_conditioning_spans_on_real_jensen_polynomials``).
"""

from __future__ import annotations

import math
import os

import pytest
from mpmath import mp

import zeta.li as li_lane
from zeta.li import (
    DATA_DIR,
    GAMMA1,
    RADIUS_MAX,
    _balance,
    _phi,
    _rs_theta,
    hyperbolicity_scan,
    is_hyperbolic,
    jensen_polynomial,
    jensen_roots_vs_gue,
    li_asymptotic,
    li_closed_form_lambda1,
    li_coefficient,
    li_coefficients,
    li_generating_function_defect,
    li_positivity_scan,
    xi_taylor_coefficients,
)

# ---------------------------------------------------------------------------
# Shared expensive results (computed once per module)
# ---------------------------------------------------------------------------

DPS = 25
N_CROSS = 8  # how far the two-method cross-check runs

LAMBDA_CAUCHY = li_coefficients(N_CROSS, dps=DPS)
LAMBDA_ZEROS = li_coefficients(N_CROSS, method="zeros", dps=DPS, n_zeros=1000)
GAMMAS = xi_taylor_coefficients(20, dps=30)

#: Reference values, from the Cauchy path, cross-checked against the zero sum
#: and (for n = 1) against the closed form.
LAMBDA_REF = [
    "0.02309570896612103381431024807",
    "0.09234573522804667038572848615",
    "0.2076389205543248037914920468",
    "0.3687904794922416385905114865",
    "0.5755427144611774524311064049",
    "0.8275660122823792974250028261",
    "1.124460117570959490582820116",
    "1.465755677147060632655514539",
]


# ---------------------------------------------------------------------------
# 1.  lambda_1 against the closed form
# ---------------------------------------------------------------------------


def test_lambda1_matches_closed_form_to_20_plus_digits():
    """λ₁ = 1 + γ/2 − log(4π)/2 = 0.0230957089661210338143102479065…

    The requirement is ≥ 20 digits; measured, the two agree to **all** the
    digits returned at dps = 30 (the difference is exactly 0), and to 1e-38 at
    dps = 40.
    """
    with mp.workdps(40):
        closed = li_closed_form_lambda1(dps=30)
        computed = li_coefficient(1, dps=30)
        assert abs(computed - closed) < mp.mpf(10) ** -29  # ≥ 20 digits, by far
        assert computed == closed  # in fact bit-identical at dps = 30

        closed40 = li_closed_form_lambda1(dps=40)
        computed40 = li_coefficient(1, dps=40)
        assert abs(computed40 - closed40) < mp.mpf(10) ** -38

    # the literal decimal, so a change of convention cannot pass silently
    assert mp.nstr(closed, 18) == "0.0230957089661210338"


def test_closed_form_lambda1_is_the_stated_expression():
    """The closed form is *derived* from ψ(1/2) = −γ − 2log2, not memorised."""
    with mp.workdps(40):
        # 1 + γ − ½log π + ½ψ(1/2)  ==  1 + γ/2 − ½log(4π)
        alt = 1 + mp.euler - mp.log(mp.pi) / 2 + mp.digamma(mp.mpf(1) / 2) / 2
        assert abs(alt - li_closed_form_lambda1(dps=40)) < mp.mpf(10) ** -38


def test_lambda1_from_the_zero_side_too():
    """The zero sum reproduces the closed form to the accuracy of its truncation."""
    with mp.workdps(30):
        assert abs(LAMBDA_ZEROS[0] - li_closed_form_lambda1(dps=DPS)) < 1e-9


# ---------------------------------------------------------------------------
# 2.  the load-bearing cross-check: Cauchy vs zero sum
# ---------------------------------------------------------------------------


def test_two_methods_agree():
    """λ_n from ξ alone vs λ_n from the zeros alone, n = 1 … 8.

    ``method="cauchy"`` evaluates only ξ on a circle around s = 1 and never
    looks at a zero; ``method="zeros"`` sums 2(1 − cos nφ(γ)) over the first
    1000 cached ordinates plus a density tail, and never evaluates ξ.  Their
    agreement is the numerical proof that Li's two formulae describe the same
    numbers.

    Measured at 1000 zeros: max |Δ| = 1.550e-8, max relative = 1.057e-8.  The
    error is dominated by the zero-sum truncation, so the tolerance below is
    stated as an *absolute* bound that a regression in either method would
    break.

    What is structural and what is not.  The residual is (to leading order) a
    multiple of f_n(T), so its **sign is the same for every n**, that is
    asserted.  Its sign as a function of ``n_zeros`` is *not* fixed: an earlier
    version of this test asserted "the truncated zero sum must be below the
    true value", which is false, at n_zeros = 400 the zero side overshoots for
    every n (see
    ``test_zero_sum_truncation_error_shrinks_but_not_monotonically``).
    """
    with mp.workdps(30):
        diffs = [abs(a - b) for a, b in zip(LAMBDA_CAUCHY, LAMBDA_ZEROS)]
        rels = [d / abs(a) for d, a in zip(diffs, LAMBDA_CAUCHY)]
        assert max(diffs) < 3.5e-8, [mp.nstr(d, 4) for d in diffs]
        assert max(rels) < 2.5e-8, [mp.nstr(r, 4) for r in rels]
        # the agreement is genuinely ~1e-8, not accidentally perfect
        assert min(diffs) > 1e-11, [mp.nstr(d, 4) for d in diffs]
        # ... and the discrepancy has one sign across n (it is c * f_n(T))
        signs = {a > b for a, b in zip(LAMBDA_CAUCHY, LAMBDA_ZEROS)}
        assert len(signs) == 1, signs
        assert signs == {True}  # at n_zeros = 1000, specifically, the zero side is low


def test_zero_sum_truncation_error_shrinks_but_not_monotonically():
    """More zeros helps *on average*, and the honest picture says only that.

    Measured max |cauchy − zeros| over n ≤ 8 at dps = 25:

        n_zeros    100        200        400        800        1000
        max |Δ|    1.913e-6   1.914e-7   1.469e-7   1.023e-8   1.550e-8
        sign       +          +          **−**      +          +

    Two facts an earlier version of this file got wrong.  (1) The zero side is
    *not* always below the true value: at n_zeros = 400 it overshoots, for
    every n.  (2) The error does *not* fall like a clean 1/T²: 800 zeros beat
    1000.  Over the decade 100 → 1000 the shrink factor is 123 against 36 for
    1/T², so the average trend is *faster* than 1/T² but the individual values
    oscillate.  This test pins the measured values and the sign reversal, and
    asserts only the decade-scale shrink.
    """
    measured = {}
    for n_zeros in (100, 200, 400, 800):
        z = li_coefficients(8, method="zeros", dps=DPS, n_zeros=n_zeros)
        with mp.workdps(30):
            d = [a - b for a, b in zip(LAMBDA_CAUCHY, z)]
            measured[n_zeros] = (max(abs(x) for x in d), {x > 0 for x in d})
    with mp.workdps(30):
        d1000 = [a - b for a, b in zip(LAMBDA_CAUCHY, LAMBDA_ZEROS)]
        measured[1000] = (max(abs(x) for x in d1000), {x > 0 for x in d1000})

    expected = {100: 1.913e-6, 200: 1.914e-7, 400: 1.469e-7,
                800: 1.023e-8, 1000: 1.550e-8}
    for n_zeros, want in expected.items():
        got, signs = measured[n_zeros]
        assert float(got) == pytest.approx(want, rel=0.05), (n_zeros, mp.nstr(got, 4))
        assert len(signs) == 1, (n_zeros, signs)  # one sign for all n
    # the sign reversal that disproves "the zero side is always low"
    assert measured[400][1] == {False}
    assert all(measured[k][1] == {True} for k in (100, 200, 800, 1000))
    # non-monotone: 800 zeros beat 1000
    assert measured[800][0] < measured[1000][0]
    # decade-scale shrink: 1000 zeros beat 100 by more than 10x
    assert measured[1000][0] * 10 < measured[100][0]


def test_the_truncation_height_does_not_have_S_of_T_equal_minus_one_half():
    """The boundary term's −1/2 is *not* the value of S(T).  Measured.

    ``_li_zeros`` picks T with ϑ(T)/π + 1 = n_zeros + 1/2 and applies the
    boundary correction −f_n(T)·(−1/2).  An earlier docstring justified that by
    "which makes S(T) = −1/2 exactly".  That is false: S(T) = N(T) − ϑ(T)/π − 1
    and N(T) is *not* forced to equal n_zeros.  Against ``mpmath.nzeros`` as an
    independent counting oracle:

        n_zeros   γ_{n_zeros}   T          N(T)    S(T)
        100       236.5242      237.7183   100     −1/2
        200       396.3819      398.2767   201     **+1/2**
        400       679.7422      681.2062   400     −1/2
        800       1183.7128     1185.0460  800     −1/2
        1000      1419.4225     1420.6769  1001    **+1/2**

    So at the module default (1000 zeros) the true S(T) is +1/2, the opposite
    of what was claimed, and the answer is still right to 1e-8, because the k
    zeros in (γ_{n_zeros}, T] omitted from the head cancel the k units of S(T)
    identically (see ``_li_zeros``).  This test pins both halves of that: the
    counts, and the fact that the value is unaffected.
    """
    from zeta.zeros import first_n_zeros
    from zeta.li import _rs_theta

    expected = {100: (236.5242, 237.7183, 100), 200: (396.3819, 398.2767, 201),
                400: (679.7422, 681.2062, 400), 800: (1183.7128, 1185.0460, 800),
                1000: (1419.4225, 1420.6769, 1001)}
    for n_zeros, (g_want, t_want, count_want) in expected.items():
        g = first_n_zeros(n_zeros, dps=30)
        with mp.workdps(40):
            target = mp.pi * (mp.mpf(n_zeros) - mp.mpf(1) / 2)
            T = mp.findroot(lambda t: _rs_theta(t) - target, g[-1] + 1)
            S_T = mp.mpf(n_zeros) - _rs_theta(T) / mp.pi - 1
            n_of_T = int(mp.nzeros(T))
            S_true = n_of_T - _rs_theta(T) / mp.pi - 1
        assert float(g[-1]) == pytest.approx(g_want, abs=1e-4)
        assert float(T) == pytest.approx(t_want, abs=1e-4)
        assert n_of_T == count_want, (n_zeros, n_of_T)
        assert float(S_T) == pytest.approx(-0.5, abs=1e-20)   # what the code uses
        assert float(S_true) == pytest.approx(count_want - n_zeros - 0.5, abs=1e-20)
    # the default really is one of the "+1/2" rows, and still lands within 1e-8
    with mp.workdps(30):
        assert max(abs(a - b) for a, b in zip(LAMBDA_CAUCHY, LAMBDA_ZEROS)) < 3.5e-8


def test_generating_function_equals_the_literal_definition():
    """n·[z^n] log ξ(1/(1−z)) == (1/(n−1)!) d^n/ds^n [s^{n−1} log ξ(s)]|_{s=1}.

    This is the identity that licenses the whole Cauchy path.  It is *checked*,
    not assumed: the right-hand side is differentiated by mpmath's own
    Cauchy-integral differentiator on a different radius, around a different
    point, of a different function.  Measured |defect|: 1.7e-52, 5.0e-52,
    1.0e-51, 1.1e-50 for n = 1 … 4 at dps = 20 (internal working precision 50),
    and 7.3e-63 … 7.4e-61 at dps = 30.  The values themselves are 0.023 … 0.37,
    so this is agreement to ~50 significant digits.
    """
    with mp.workdps(40):
        for n in (1, 2, 3, 4):
            d = li_generating_function_defect(n, dps=20)
            assert abs(d) < mp.mpf(10) ** -45, (n, mp.nstr(d, 6))


@pytest.mark.slow
def test_generating_function_defect_at_dps_30():
    """The dps = 30 row of ``li_generating_function_defect``'s docstring (11 s).

    |defect| = 7.29e-63, 2.92e-62, 1.75e-61, 7.39e-61 for n = 1 … 4.  Pinned to
    5% because these are the only place those four numbers appear, and a
    silently degraded quadrature would move them by orders of magnitude.
    """
    expected = (7.29e-63, 2.92e-62, 1.75e-61, 7.39e-61)
    for n, want in zip((1, 2, 3, 4), expected):
        d = li_generating_function_defect(n, dps=30)
        assert float(abs(d)) == pytest.approx(want, rel=0.05), (n, mp.nstr(d, 6))


def test_cauchy_radius_independence():
    """Different sampling circles must give the same coefficients.

    A radius-dependent answer would mean the branch of the logarithm, the node
    count, or the guard digits are wrong.  Measured: identical to all 25
    returned digits for r ∈ {0.3, 0.5, 0.7, 0.9}.
    """
    base = li_coefficients(6, dps=DPS, radius="0.5", cache=False)
    for r in ("0.3", "0.7", "0.9"):
        other = li_coefficients(6, dps=DPS, radius=r, cache=False)
        with mp.workdps(30):
            worst = max(abs(a - b) for a, b in zip(base, other))
        assert worst == 0, (r, mp.nstr(worst, 4))


def test_working_precision_and_node_counts():
    """The (work digits, nodes) numbers quoted in the module's docstrings.

    ``_li_cauchy`` carries n·log₁₀(1/r) extra digits for the r^{−n} division and
    uses work·ln10/ln(1/r) + n + 8 nodes to kill aliasing.  Pinned because
    ``_roots_of_unity`` and ``_real_checked`` quote them:

        request                       n passed to _li_cauchy   work   nodes
        li_coefficients(50,  dps=20)  64  (= _round_up(50))    60     272
        li_coefficients(300, dps=20)  304 (= _round_up(300))   132    751
        _li_cauchy(300, 20, 0.5)      300                      131    744

    The middle row is the one a caller actually gets for n = 300, the cache
    step rounds 300 up to 304, so quoting the third row for that call (as an
    earlier docstring did) is off by 7 nodes and a digit.
    """
    from zeta.li import _GUARD

    for n_pass, want_work, want_nodes in ((64, 60, 272), (304, 132, 751), (300, 131, 744)):
        work = int(math.ceil(20 + 2 * _GUARD + n_pass * math.log10(2)))
        with mp.workdps(work):
            R = mp.mpf("0.5")
            nodes = int(mp.ceil(work * mp.log(10) / mp.log(1 / R))) + n_pass + 8
        assert (work, nodes) == (want_work, want_nodes), (n_pass, work, nodes)


def test_arg_xi_needs_unwrapping_not_a_principal_branch_guard():
    """The branch of log ξ(1/(1−z)), measured properly.

    Sampled max |arg ξ| on |z| = r (256 nodes, this is a *lower bound* on the
    supremum, and a coarser 64-node sample genuinely understates it):

        r        0.3      0.5      0.7      0.9      0.92
        256 pts  0.0102   0.0311   0.1171   1.2657   1.9873
        64 pts   0.0102   0.0311   0.1171   1.1001,

    Two things follow, and both were wrong in an earlier version of the module.
    (1) "measured max at r = 0.9 is 1.10" is a 64-node artefact; 1024 nodes give
    1.2816.  (2) A guard demanding |arg ξ| < π/2 is *not* unreachable inside the
    admissible radius range, it fires from r ≈ 0.915 up, i.e. it rejected
    legitimate radii.  ``_unwrapped_log`` replaces it by continuation from
    z = r (where ξ is real positive) plus a winding-number check, so the whole
    documented range (0, RADIUS_MAX) now works, and r = 0.92, where the old
    guard raised, reproduces r = 0.5 exactly.
    """
    from zeta.core import xi

    sampled = {}
    with mp.workdps(30):
        for r, npts in (("0.3", 64), ("0.5", 64), ("0.7", 64), ("0.9", 256), ("0.92", 256)):
            R = mp.mpf(r)
            sampled[r] = float(
                max(
                    abs(mp.arg(xi(1 / (1 - R * mp.expjpi(mp.mpf(2 * j) / npts)), 30)))
                    for j in range(npts)
                )
            )
    assert sampled["0.3"] == pytest.approx(0.0102, rel=0.02)
    assert sampled["0.5"] == pytest.approx(0.0311, rel=0.02)
    assert sampled["0.7"] == pytest.approx(0.1171, rel=0.02)
    assert sampled["0.9"] == pytest.approx(1.2657, rel=0.02)
    assert sampled["0.92"] == pytest.approx(1.9873, rel=0.02)
    # the old |arg| < pi/2 guard would have rejected r = 0.92 ...
    assert sampled["0.92"] > math.pi / 2
    # ... yet r = 0.92 is inside the admissible range and gives the same answer
    assert float(RADIUS_MAX) > 0.92
    near = li_coefficients(3, dps=15, radius="0.92", cache=False)
    mid = li_coefficients(3, dps=15, radius="0.5", cache=False)
    with mp.workdps(25):
        assert max(abs(a - b) for a, b in zip(near, mid)) == 0


def test_unwrapped_log_recovers_the_analytic_branch_and_both_guards_fire():
    """The replacement guard is a real guard on synthetic controls.

    1.  **It unwraps.**  Sample f(θ) = e^{4i sin θ} at 64 points.  Its argument
        sweeps ±4 radians, so the *principal* logarithm jumps by 2π twice per
        loop, while the analytic branch is exactly 4i sin θ (winding 0, since
        f never encircles the origin).  ``_unwrapped_log`` must return the
        latter, to working precision.
    2.  **Undersampling is refused.**  e^{iθ} at 4 points moves arg by π/2 per
        step: the 2π ambiguity is unresolvable and it must raise.
    3.  **A nonzero winding number is refused.**  e^{iθ} at 64 points winds once,
        which for the real integrand would mean a zero inside the circle,
        contradicting ``RADIUS_MAX``, and it must raise.
    """
    from zeta.li import _unwrapped_log

    with mp.workdps(30):
        N = 64
        theta = [2 * mp.pi * j / N for j in range(N)]
        vals = [mp.expj(4 * mp.sin(t)) for t in theta]
        principal = [float(mp.im(mp.log(v))) for v in vals]
        assert max(abs(x) for x in principal) < math.pi  # principal is wrapped
        out = _unwrapped_log(vals)
        ims = [mp.im(v) for v in out]
        assert max(abs(a - 4 * mp.sin(t)) for a, t in zip(ims, theta)) < mp.mpf(10) ** -25
        assert max(float(abs(a)) for a in ims) == pytest.approx(4.0, rel=1e-9)
        # the principal branch really is a different function here
        assert max(abs(a - b) for a, b in zip(ims, principal)) > 1.0

        with pytest.raises(ValueError, match="undersampled"):
            _unwrapped_log([mp.expjpi(mp.mpf(2 * j) / 4) for j in range(4)])
        with pytest.raises(ValueError, match="winds"):
            _unwrapped_log([mp.expjpi(mp.mpf(2 * j) / N) for j in range(N)])


def test_dft_imaginary_residue_needs_the_scaled_tolerance():
    """Why ``_real_checked`` is passed the DFT round-off floor and not max(|Re|,1).

    This reproduces the inner loop of ``_li_cauchy`` for λ_50 at dps = 20
    (working precision 60 digits, 272 nodes) and measures the three quantities
    quoted in the ``_real_checked`` docstring:

        |Im c_50| = 5.11e-48,   naive tolerance = 1.0e-48,   DFT floor = 7.9e-34.

    The naive scale max(|Re c_n|, 1) would **reject** a perfectly good
    coefficient; the scaled one accepts it with 14 orders of margin.  The
    effect grows with n: at n = 300 (slow tier) the naive tolerance is 1.7e-120
    against a residue of 2.4e-45.
    """
    import math

    from zeta.core import xi
    from zeta.li import _GUARD, _roots_of_unity

    dps, n_max, n = 20, 64, 50  # n_max = _round_up(50), what the module computes
    work = int(math.ceil(dps + 2 * _GUARD + n_max * math.log10(2)))
    assert work == 60
    with mp.workdps(work):
        R = mp.mpf("0.5")
        n_points = int(mp.ceil(work * mp.log(10) / mp.log(1 / R))) + n_max + 8
        assert n_points == 272
        w = _roots_of_unity(n_points)
        vals = [mp.log(xi(1 / (1 - R * wj), work)) for wj in w]
        biggest = max(abs(v) for v in vals)
        acc = mp.fsum(vals[j] * w[(-(j * n)) % n_points] for j in range(n_points))
        inv = mp.power(R, -n)
        c_n = acc * inv / n_points

        residue = abs(mp.im(c_n))
        naive = mp.mpf(10) ** (-work + _GUARD + 2) * max(abs(mp.re(c_n)), 1)
        floor = mp.mpf(10) ** (-work + _GUARD + 2) * biggest * inv

        assert float(residue) == pytest.approx(5.11e-48, rel=0.05)
        assert float(naive) == pytest.approx(1.0e-48, rel=0.05)
        assert float(floor) == pytest.approx(7.9e-34, rel=0.05)
        # the point of the whole exercise:
        assert residue > naive  # the naive scale rejects a good coefficient
        assert residue < floor  # the scaled one accepts it
        assert float(floor / residue) > 1e13  # ... with 14 orders of margin

        # and the *reason* is the r^{-n} amplification, not a small c_n:
        # c_n = lambda_n/n is O(1) here (0.87), so the naive scale is ~1 and
        # simply cannot see the 2^n by which the DFT round-off was multiplied.
        assert float(abs(mp.re(c_n))) == pytest.approx(0.8706219, rel=1e-5)
        assert float(floor / naive) == pytest.approx(float(inv) * 0.7, rel=0.15)


@pytest.mark.slow
def test_dft_imaginary_residue_at_n_300_the_second_docstring_row():
    """The λ_300 row of ``_real_checked``'s table, the extreme of the r^{−n} story.

    Reproducing the real code path for ``li_coefficients(300, dps=20)``, which
    rounds up to n = 304 (so 132 working digits and 751 nodes):

        |Im c_300| = 2.376e-45,  naive tol = 1.732e-120,  DFT floor = 1.428e-30,
        floor/naive = 8.246e+89,  floor/residue = 6.011e+14.

    The naive scale is *87 orders* too small here, and the reason is visible in
    the ratio: floor/naive is exactly r^{−n}·max|log ξ|/|Re c_n| =
    2^300 · 0.7010/1.7323, i.e. the r^{−n} = 2^300 = 2.037e90 amplification the
    scaled tolerance carries and the naive one cannot see, times an O(1) factor.
    Re(c_300) is 1.732, O(1), not small, so no "the coefficient is tiny" story
    explains it.  The extracted λ_300 = 300·Re(c_300) is pinned here too.
    """
    from zeta.core import xi
    from zeta.li import _GUARD, _roots_of_unity

    dps, n_max, n = 20, 304, 300
    work = int(math.ceil(dps + 2 * _GUARD + n_max * math.log10(2)))
    assert work == 132
    with mp.workdps(work):
        R = mp.mpf("0.5")
        n_points = int(mp.ceil(work * mp.log(10) / mp.log(1 / R))) + n_max + 8
        assert n_points == 751
        w = _roots_of_unity(n_points)
        vals = [mp.log(xi(1 / (1 - R * wj), work)) for wj in w]
        biggest = max(abs(v) for v in vals)
        acc = mp.fsum(vals[j] * w[(-(j * n)) % n_points] for j in range(n_points))
        inv = mp.power(R, -n)
        c_n = acc * inv / n_points

        residue = abs(mp.im(c_n))
        naive = mp.mpf(10) ** (-work + _GUARD + 2) * max(abs(mp.re(c_n)), 1)
        floor = mp.mpf(10) ** (-work + _GUARD + 2) * biggest * inv

        assert float(residue) == pytest.approx(2.376e-45, rel=0.05)
        assert float(naive) == pytest.approx(1.732e-120, rel=0.05)
        assert float(floor) == pytest.approx(1.428e-30, rel=0.05)
        assert residue > naive and residue < floor
        assert float(floor / naive) == pytest.approx(8.246e89, rel=0.05)
        # ... and that ratio is r^{-n} up to an O(1) factor max|log xi| / |Re c_n|
        assert float(biggest) == pytest.approx(0.7010, rel=0.02)
        assert float(floor / naive) == pytest.approx(
            float(inv) * 0.7010 / 1.7323, rel=0.02
        )
        assert float(inv) == pytest.approx(2.0370e90, rel=0.01)  # 2^300
        assert float(floor / residue) == pytest.approx(6.011e14, rel=0.05)
        assert float(abs(mp.re(c_n))) == pytest.approx(1.7323399, rel=1e-5)
        assert abs(n * mp.re(c_n) - mp.mpf("519.70196561924964484")) < mp.mpf(10) ** -14


def test_lambda_50_pinned_and_cross_checked():
    """λ_50 = 43.531096488374019298…, from both sides and against the asymptotic.

    The two-method cross-check is run at n = 8 elsewhere; this extends it to
    n = 50, where the r^{−n} amplification in the Cauchy path is 2^50 ≈ 1.1e15
    and the zero sum needs its density tail.  Measured relative difference
    between the two methods: 1.39e-8, the same ~1e-8 zero-truncation floor
    seen at n ≤ 8, i.e. the Cauchy path has not degraded at all by n = 50.
    """
    cauchy = li_coefficients(50, dps=20)[-1]
    zeros = li_coefficient(50, method="zeros", dps=20, n_zeros=1000)
    with mp.workdps(30):
        assert abs(cauchy - mp.mpf("43.531096488374019298")) < mp.mpf(10) ** -17
        rel = abs(cauchy - zeros) / cauchy
        assert float(rel) == pytest.approx(1.39e-8, rel=0.05)
    # and it sits just above the asymptotic prediction, as the scan reports
    assert li_asymptotic(50) == pytest.approx(42.284040098, rel=1e-9)
    assert float(cauchy) > li_asymptotic(50)


def test_lambda_from_stieltjes_constants_a_third_independent_route():
    """λ_n from Stieltjes constants and polygamma, no ξ, no zeros, no Cauchy.

    Expand log ξ(1+x) in closed form from the *analytic* ingredients:

        ξ(1+x) = ½(1+x)π^{−(1+x)/2}Γ((1+x)/2)·[xζ(1+x)],
        xζ(1+x) = 1 + Σ_{j≥1} (−1)^{j−1} γ_{j−1} x^j/(j−1)!   (Stieltjes),
        log Γ(½ + x/2) = log Γ(½) + Σ_{m≥1} ψ^{(m−1)}(½)(x/2)^m/m!,

    take the logarithm of the power series by the standard recursion, and then
    push the substitution s = 1/(1−z) through *symbolically* rather than
    numerically: with x = s − 1 = z/(1−z),

        [z^n] log ξ(1/(1−z)) = Σ_{k=1}^{n} C(n−1, k−1)·[x^k] log ξ(1+x),

    so λ_n = n Σ_k C(n−1,k−1) a_k.  This shares **no code path** with either
    module method: mpmath's ``stieltjes`` and ``polygamma`` in place of
    ``zeta.core.xi``, a binomial transform in place of a trapezoid DFT, and no
    zero ordinates anywhere.

    Measured agreement with ``method="cauchy"`` at dps = 25: 8.5e-27 relative,
    i.e. the module's output is right to every digit it returns.
    """
    work = 60
    K = N_CROSS
    with mp.workdps(work):
        # log of P(x) = x*zeta(1+x), P(0) = 1
        p = [mp.mpf(1)] + [
            (-1) ** (j - 1) * mp.stieltjes(j - 1) / mp.factorial(j - 1)
            for j in range(1, K + 1)
        ]
        L = [mp.mpf(0)] * (K + 1)
        for m in range(1, K + 1):
            L[m] = p[m] - mp.fsum(k * L[k] * p[m - k] for k in range(1, m)) / m
        a = [mp.mpf(0)] * (K + 1)
        for k in range(1, K + 1):
            a[k] = (
                mp.mpf((-1) ** (k + 1)) / k                       # log(1+x)
                + mp.polygamma(k - 1, mp.mpf(1) / 2) / mp.factorial(k) / mp.power(2, k)
                + L[k]
            )
        a[1] -= mp.log(mp.pi) / 2                                 # −(1+x)/2·log π
        third = [
            n * mp.fsum(mp.binomial(n - 1, k - 1) * a[k] for k in range(1, n + 1))
            for n in range(1, K + 1)
        ]
        worst = max(abs((x - y) / x) for x, y in zip(third, LAMBDA_CAUCHY))
    assert float(worst) < 5e-26, mp.nstr(worst, 4)
    # ... and it reproduces the pinned decimals, so those are not module-internal
    with mp.workdps(30):
        for n, ref in enumerate(LAMBDA_REF, start=1):
            assert abs(third[n - 1] - mp.mpf(ref)) < mp.mpf(10) ** -24, n


def test_radius_bound_is_the_one_gamma1_certifies():
    """RADIUS_MAX = 1 − 1/γ₁, and γ₁ is what zeta.zeros says it is."""
    from zeta.zeros import first_n_zeros

    g1 = first_n_zeros(1, dps=30)[0]
    with mp.workdps(30):
        assert abs(g1 - mp.mpf(GAMMA1)) < mp.mpf(10) ** -28
        assert abs(mp.mpf(RADIUS_MAX) - (1 - 1 / g1)) < 1e-15
    assert 0.929 < RADIUS_MAX < 0.9293
    with pytest.raises(ValueError):
        li_coefficients(2, radius="0.95", cache=False)


def test_li_coefficient_matches_reference_decimals():
    """Pin the actual digits, so a silent convention change cannot pass."""
    with mp.workdps(30):
        for n, ref in enumerate(LAMBDA_REF, start=1):
            assert abs(LAMBDA_CAUCHY[n - 1] - mp.mpf(ref)) < mp.mpf(10) ** -24


def test_phi_puts_critical_line_zeros_on_the_unit_circle():
    """|1 − 1/ρ| = 1 exactly when Re ρ = 1/2, the reason λ_n ≥ 0 on RH."""
    with mp.workdps(40):
        for t in ("14.134725141734693790", "21.0220396387715549", "1000.5"):
            rho = mp.mpc(mp.mpf(1) / 2, mp.mpf(t))
            w = 1 - 1 / rho
            assert abs(abs(w) - 1) < mp.mpf(10) ** -38
            assert abs(mp.arg(w) - _phi(mp.mpf(t))) < mp.mpf(10) ** -38
        # off the line the modulus is NOT 1 (so the positivity argument fails)
        rho = mp.mpc(mp.mpf("0.7"), 30)
        assert abs(1 - 1 / rho) < 1 - 1e-6


def test_rs_theta_matches_mpmath_and_zeta_core():
    """The private ϑ used by the tail correction is the standard one."""
    from zeta.core import rs_theta as core_rs_theta

    with mp.workdps(30):
        for t in (20, 100, 1420.7):
            assert abs(_rs_theta(mp.mpf(t)) - core_rs_theta(t, dps=30)) < 1e-27


# ---------------------------------------------------------------------------
# 3.  positivity, phrased as "no violation found"
# ---------------------------------------------------------------------------


def test_no_violation_of_li_positivity_found_up_to_60():
    """**No counterexample to Li's criterion was found for n ≤ 60.**

    This is emphatically *not* evidence for RH (docs/08, Littlewood): Li's
    criterion quantifies over all n ≥ 1, and any finite scan is silent about
    the rest.  What the test does certify is that each computed λ_n is
    positive by a margin of many decimal digits, so no sign here is a rounding
    artefact.
    """
    rows = li_positivity_scan(60, dps=20)
    assert len(rows) == 60
    assert all(r["positive"] for r in rows), [r["n"] for r in rows if not r["positive"]]
    # every value sits at least 15 digits above the precision floor
    assert min(r["margin_digits"] for r in rows) > 15
    assert rows[0]["n"] == 1 and rows[-1]["n"] == 60
    assert rows[0]["margin"] == pytest.approx(0.0230957089661210338, rel=1e-15)
    # λ_n is increasing from n = 2 on, and grows like (n/2)log n
    assert all(
        rows[i]["margin"] < rows[i + 1]["margin"] for i in range(len(rows) - 1)
    )


def test_positivity_from_the_zero_side_as_well():
    """The zero-side λ_n are positive too, no violation found, from either side.

    Reuses the module-level zero-side computation (the scan wrapper is exercised
    on the Cauchy path above; here only the values matter).
    """
    assert all(v > 0 for v in LAMBDA_ZEROS)
    # each conjugate pair contributes 2(1 − cos nφ) ≥ 0, so on RH the partial
    # sums are nondecreasing in the number of zeros, positivity is structural
    partial = li_coefficients(1, method="zeros", dps=DPS, n_zeros=100)[0]
    assert partial > 0


def test_li_asymptotic_leading_term():
    """λ_n / [(n/2)(log n − log 2π + γ − 1) + 1] → 1, measured.

    Honest scope: only the *leading* term is verified.  The remainder is an
    oscillating O(√n log n) piece on RH and this test cannot and does not
    separate it from a constant.  Measured over 50 ≤ n ≤ 60: relative error
    ≤ 2.95e-2 (over the full 50 ≤ n ≤ 300 range in the slow tier, same bound).
    """
    lam = li_coefficients(60, dps=20)
    rel = [abs(float(lam[n - 1]) / li_asymptotic(n) - 1) for n in range(50, 61)]
    assert max(rel) < 0.05, max(rel)
    # and it really is converging: n = 60 is closer than n = 10
    assert abs(float(lam[59]) / li_asymptotic(60) - 1) < abs(
        float(lam[9]) / li_asymptotic(10) - 1
    )
    with pytest.raises(ValueError):
        li_asymptotic(0)


@pytest.mark.slow
def test_li_asymptotic_over_300_coefficients():
    """The full picture: envelope, mean, and the absence of a constant fit.

    Measured for 1 ≤ n ≤ 300: λ_n − li_asymptotic(n) ∈ [−2.606, +3.601], mean
    0.587; relative error ≤ 2.949e-2 for n ≥ 50 and ≤ 1.248e-2 for n ≥ 100.
    The envelope grows (±1.2 for n ≤ 50, ±3.6 by n = 300), which is why the
    docstring hedges the constant term instead of claiming it.
    """
    lam = li_coefficients(300, dps=20)
    # the far end of the range, pinned: the r^{-n} amplification here is 2^300
    with mp.workdps(30):
        assert abs(lam[299] - mp.mpf("519.70196561924964484")) < mp.mpf(10) ** -14
    resid = [float(lam[n - 1]) - li_asymptotic(n) for n in range(1, 301)]
    assert min(resid) > -3.0 and max(resid) < 4.5
    assert 0.4 < sum(resid) / len(resid) < 0.8
    rel = [abs(float(lam[n - 1]) / li_asymptotic(n) - 1) for n in range(1, 301)]
    assert max(rel[49:]) < 0.04
    assert max(rel[99:]) < 0.02
    # envelope grows: the late window is wider than the early one
    early = max(abs(x) for x in resid[:50])
    late = max(abs(x) for x in resid[200:])
    assert late > 1.5 * early
    assert all(v > 0 for v in lam)  # again: no violation found, not evidence


# ---------------------------------------------------------------------------
# 4.  the Xi Taylor coefficients gamma(n)
# ---------------------------------------------------------------------------


def test_gamma0_is_eight_xi_one_half():
    """γ(0) = 8·ξ(1/2) = 8·Ξ(0) = 3.9769662255065128793…"""
    from zeta.core import Xi

    with mp.workdps(35):
        assert abs(GAMMAS[0] - 8 * Xi(0, dps=30)) < mp.mpf(10) ** -28
    assert mp.nstr(GAMMAS[0], 17) == "3.9769662255065129"


def test_the_gorz_normalisation_bridge():
    """(−1 + 4z²)·Λ(1/2+z) = 8·ξ(1/2+z), the factor connecting us to GORZ.

    Griffin–Ono–Rolen–Zagier state the γ(n) via (−1+4z²)Λ(1/2+z) with
    Λ(s) = π^{−s/2}Γ(s/2)ζ(s); this module uses 8·ξ(1/2+z).  The module
    docstring claims the two are the same because ξ = ½s(s−1)Λ and
    (1/2+z)(z−1/2) = z²−1/4.  That is a factor-placement claim of exactly the
    kind CLAUDE.md says to derive numerically rather than remember, so here it
    is measured: agreement to ≤ 1e-28 at dps = 30 for real and complex z.
    """
    from zeta.core import completed_zeta, xi

    with mp.workdps(35):
        for zz in (mp.mpf("0.3"), mp.mpf("2.5"), mp.mpc("0.4", "1.3"), mp.mpc(0, 5)):
            lhs = (-1 + 4 * zz ** 2) * completed_zeta(mp.mpf(1) / 2 + zz, dps=30)
            rhs = 8 * xi(mp.mpf(1) / 2 + zz, 30)
            assert abs(lhs - rhs) < mp.mpf(10) ** -28 * max(abs(rhs), 1), zz

    # and therefore gamma(n) is what GORZ's own normalisation would produce:
    # gamma(n) = n! * [z^{2n}] of that left-hand side.
    with mp.workdps(40):
        g = lambda z: (-1 + 4 * z ** 2) * completed_zeta(mp.mpf(1) / 2 + z, dps=40)
        for n in (0, 1, 2, 3):
            coeff = mp.diff(g, mp.mpf(0), 2 * n, method="quad", radius=mp.mpf(3))
            oracle = mp.re(coeff) * mp.factorial(n) / mp.factorial(2 * n)
            assert abs(GAMMAS[n] - oracle) < abs(oracle) * mp.mpf(10) ** -25, n


def test_gamma_against_riemanns_other_integral_an_independent_oracle():
    """γ(n) from Riemann's *derivative* form of the Ξ integral (Titchmarsh 2.16).

        ξ(½+z) = 4 ∫_1^∞ d[x^{3/2}ω'(x)]/dx · x^{−1/4} cosh((z/2)log x) dx,

    which has **no** (z²−¼) prefactor and **no** boundary term, a structurally
    different representation from the one ``_gamma_integral`` uses (that one
    integrates ω itself and carries the prefactor).  Expanding the cosh,

        γ(n) = 32·n!/(4^n (2n)!) ∫_1^∞ d[x^{3/2}ω'(x)]/dx · x^{−1/4}(log x)^{2n} dx,

    with ω'(x) = −π Σ m² e^{−πm²x} and ω''(x) = π² Σ m⁴ e^{−πm²x} summed
    directly, no ``zeta.core.omega``, no ξ, no Cauchy circle.

    Measured max relative agreement with the module: 9.2e-32 for n ≤ 8 at
    dps = 30, i.e. the module's γ(n) are right to every returned digit.  Run
    out to n = 128 out of band (the size of the committed cache table) the
    agreement stays at ~4.6e-32.
    """
    work = 55
    with mp.workdps(work):
        profile: dict = {}

        def P(u):
            v = profile.get(u)
            if v is None:
                x = mp.exp(u)
                M = int(mp.ceil(mp.sqrt((work + 25) * mp.log(10) / (mp.pi * x)))) + 3
                w1 = -mp.pi * mp.fsum(m * m * mp.exp(-mp.pi * m * m * x) for m in range(1, M + 1))
                w2 = mp.pi ** 2 * mp.fsum(
                    m ** 4 * mp.exp(-mp.pi * m * m * x) for m in range(1, M + 1)
                )
                d = mp.mpf(3) / 2 * mp.sqrt(x) * w1 + mp.power(x, mp.mpf(3) / 2) * w2
                v = d * mp.power(x, mp.mpf(-1) / 4) * x   # the dx/du from x = e^u
                profile[u] = v
            return v

        pts = [0, mp.mpf(1) / 2, 1, 2, 3, 5, 9]
        oracle = []
        for n in range(9):
            I = mp.quad(lambda u, n=n: mp.power(u, 2 * n) * P(u), pts)
            oracle.append(32 * mp.factorial(n) * I / (mp.power(4, n) * mp.factorial(2 * n)))
        worst = max(abs((a - b) / a) for a, b in zip(oracle, GAMMAS[:9]))
        # the oracle also lands on the quoted decimals (see the test below for
        # the module's own values against the same strings)
        assert abs(oracle[1] - mp.mpf("0.09188777726058175014")) < mp.mpf(10) ** -20
        assert abs(oracle[2] - mp.mpf("0.001975232289125088110")) < mp.mpf(10) ** -21
    assert float(worst) < 5e-31, mp.nstr(worst, 4)


def test_gamma_docstring_decimals_including_the_far_tail():
    """γ(0), γ(1), γ(2), γ(10), γ(25) exactly as ``xi_taylor_coefficients`` quotes them.

    The quoted strings are truncations/roundings, so each is checked to the
    relative accuracy its own digit count supports (10^{−(d−1)} for d quoted
    significant digits), not to a blanket tolerance that the shortest entry
    would have to set.  Measured relative deviations: 7.6e-21, 1.1e-20,
    1.2e-19, 1.5e-20, 5.8e-21.
    """
    gam = xi_taylor_coefficients(25, dps=30)
    quoted = {
        0: "3.9769662255065128793",
        1: "0.09188777726058175014",
        2: "0.001975232289125088110",
        10: "1.6323380490301419585e-17",
        25: "5.8107957154993911706e-46",
    }
    with mp.workdps(40):
        for n, ref in quoted.items():
            digits = len("".join(c for c in ref.split("e")[0] if c.isdigit()).lstrip("0"))
            r = mp.mpf(ref)
            tol = abs(r) * mp.mpf(10) ** -(digits - 1)
            assert abs(gam[n] - r) < tol, (n, digits, mp.nstr(gam[n], 22))


def test_gamma_reproduces_xi_by_summing_the_series():
    """Σ γ(n) z^{2n}/n! must be 8·ξ(1/2+z), the definition, tested.

    Measured residual at dps = 30 with 21 terms: ≤ 1e-28 for |z| ≤ 1.5,
    ≤ 1e-26 at z = 3 (where the truncation of the series starts to show).
    """
    from zeta.core import xi

    with mp.workdps(40):
        for zz in ("0.3", "1.0", "1.5", "3.0"):
            z = mp.mpf(zz)
            series = mp.fsum(
                GAMMAS[n] * mp.power(z, 2 * n) / mp.factorial(n)
                for n in range(len(GAMMAS))
            )
            exact = 8 * xi(mp.mpf(1) / 2 + z, 35)
            assert abs(series - exact) < mp.mpf(10) ** -25, (zz, mp.nstr(series - exact, 4))


def test_gamma_two_independent_methods_agree():
    """Riemann's Mellin integral vs Cauchy integration of 8·ξ(1/2+√w).

    The two share nothing but ξ: one integrates a positive real integrand
    against ω on (0,∞), the other averages ξ over a circle of radius 30 in the
    w-plane.  Measured: **bit-identical** output at dps = 30 and dps = 50 for
    n ≤ 20.
    """
    for dps in (30, 50):
        a = xi_taylor_coefficients(20, dps=dps, cache=False)
        b = xi_taylor_coefficients(20, dps=dps, method="cauchy", cache=False)
        with mp.workdps(dps + 20):
            worst = max(abs((x - y) / x) for x, y in zip(a, b))
        assert worst == 0, (dps, mp.nstr(worst, 4))


def test_gamma_accuracy_is_only_the_final_rounding():
    """γ(n) carries every digit it returns, the error is the output rounding.

    Against a dps = 110 reference computed by the same integral path, the
    measured max relative error over n ≤ 12 is

        dps = 30 → 9.222e-32,   dps = 50 → 1.303e-51,   dps = 80 → 1.022e-81

    i.e. *below* the 1e-30 / 1e-50 / 1e-80 that rounding the result to ``dps``
    digits costs by itself, the returned values carry every digit they claim,
    and the quadrature is not the limiting factor anywhere in the range the
    Jensen scans use.
    """
    from zeta.li import _gamma_integral

    ref = _gamma_integral(12, 110)
    for dps, expected in ((30, 9.222e-32), (50, 1.303e-51), (80, 1.022e-81)):
        v = _gamma_integral(12, dps)
        with mp.workdps(140):
            worst = max(abs((a - b) / a) for a, b in zip(ref, v))
        assert float(worst) == pytest.approx(expected, rel=0.05), (dps, mp.nstr(worst, 4))
        assert worst < mp.mpf(10) ** (-dps)  # better than the output rounding


def test_gamma_cauchy_radius_independence():
    """The Cauchy γ path must not depend on the circle it samples.

    Bit-identical to the independent Mellin-integral path for every radius in
    {4, 10, 30, 100, 300} at dps = 30 and dps = 80, at n_max = 4 and 12.  The
    remaining n_max ∈ {20, 30} rows of the grid quoted in ``_gamma_cauchy``'s
    docstring are in ``test_gamma_cauchy_radius_grid`` (slow).

    **Two of these cells used to fail**, silently: with the old radius-blind
    node count ``2·n_max + 40`` the errors were 2.92e-35 at (dps 80, n_max 4,
    R = 300) and 2.36e-57 at (dps 80, n_max 12, R = 300), a function asked for
    80 digits returning 34.  ``_gamma_cauchy_nodes`` now derives the count from
    an aliasing bound instead.
    """
    from zeta.li import _gamma_cauchy, _gamma_integral

    for dps in (30, 80):
        for n_max in (4, 12):
            ref = _gamma_integral(n_max, dps)
            for radius in (4, 10, 30, 100, 300):
                v = _gamma_cauchy(n_max, dps, radius=radius)
                with mp.workdps(dps + 40):
                    worst = max(abs((a - b) / a) for a, b in zip(ref, v))
                assert worst == 0, (dps, n_max, radius, mp.nstr(worst, 4))


def test_gamma_cauchy_node_count_is_radius_and_precision_aware():
    """``_gamma_cauchy_nodes``: the derived aliasing bound, pinned.

    The rule is N ≥ [work + log₁₀(F(ρ)/γ(0))]/log₁₀(ρ/R) minimised over
    ρ = λR, floored at 2·n_max + 40.  Measured (work = dps + 20 + ⌈2.6 n_max⌉):

        dps  n_max  R=4   R=10  R=30  R=100  R=300      old rule
        30   4      48    48    48    52     68         48
        30   12     64    64    64    64     83         64
        80   4      48    52    61    77     102        48
        80   12     64    64    70    88     112        64

    Two properties are asserted beyond the pinned numbers: the count is
    nondecreasing in the radius and in the working precision (it must be, both
    make the alias term bigger), and it strictly exceeds the old radius-blind
    rule exactly where that rule was measured to lose digits.
    """
    from zeta.li import _gamma_cauchy_nodes

    expected = {
        (30, 4): (48, 48, 48, 52, 68),
        (30, 12): (64, 64, 64, 64, 83),
        (80, 4): (48, 52, 61, 77, 102),
        (80, 12): (64, 64, 70, 88, 112),
    }
    radii = (4, 10, 30, 100, 300)
    for (dps, n_max), want in expected.items():
        work = dps + 20 + math.ceil(2.6 * n_max)
        got = tuple(_gamma_cauchy_nodes(n_max, work, r) for r in radii)
        assert got == want, (dps, n_max, got)
        assert all(b >= a for a, b in zip(got, got[1:]))   # grows with radius
        assert got[-1] >= 2 * n_max + 40                   # never below the floor
    # monotone in the working precision, at fixed radius
    for r in radii:
        counts = [_gamma_cauchy_nodes(4, w, r) for w in (60, 100, 140, 200)]
        assert all(b >= a for a, b in zip(counts, counts[1:])), (r, counts)
    # and it beats the old rule precisely in the cells that used to be wrong
    assert expected[(80, 4)][-1] > 2 * 4 + 40
    assert expected[(80, 12)][-1] > 2 * 12 + 40


def test_gamma_cauchy_refuses_a_radius_it_cannot_resolve():
    """The cancellation audit: the working precision is radius-blind, so guard it.

    ``work = dps + 20 + ⌈2.6·n_max⌉`` was calibrated at R ≈ 30 and does not
    know about the radius.  The round-off floor of the DFT sum, carried through
    the R^{−n} division, is max|F|·R^{−n}·10^{−work}, and because F(w) =
    8ξ(½+√w) has **positive** coefficients, max|F| on |w| = R is exactly F(R),
    which this test computes independently from a single ξ evaluation rather
    than from the module's sampled maximum.

    Measured spare digits beyond the requested ``dps`` (dps-independent, since
    ``work`` tracks dps):

        n_max   R=4    R=10   R=30   R=100  R=300   R=1000
        4       25.3   26.8   28.5   30.0   28.4    23.8
        12      29.4   34.2   39.7   45.3   49.4,

    At R = 10 000 the margin goes negative and the function must raise.  Before
    the check existed it returned γ(0) too large by a factor of 3e138 at
    R = 100 000, with no complaint at all.
    """
    from zeta.core import xi
    from zeta.li import _gamma_cauchy, _gamma_cauchy_nodes

    def spare(n_max, dps, radius):
        """log10(|c_n| / floor_n) − dps, minimised over n, computed here."""
        work = dps + 20 + math.ceil(2.6 * n_max)
        gam = xi_taylor_coefficients(n_max, dps=dps)
        with mp.workdps(work + 40):
            R = mp.mpf(radius)
            maxF = 8 * xi(mp.mpf(1) / 2 + mp.sqrt(R), work)
            worst = min(
                float(
                    mp.log10(
                        (gam[n] / mp.factorial(n))
                        / (maxF * mp.power(R, -n) * mp.mpf(10) ** (-work))
                    )
                )
                for n in range(n_max + 1)
            )
        return worst - dps

    for n_max, want in ((4, (25.3, 26.8, 28.5, 30.0, 28.4)),
                        (12, (29.4, 34.2, 39.7, 45.3, 49.4))):
        for radius, expected in zip((4, 10, 30, 100, 300), want):
            assert spare(n_max, 30, radius) == pytest.approx(expected, abs=0.15), (
                n_max, radius, spare(n_max, 30, radius)
            )
            # dps-independence of the margin
            assert spare(n_max, 80, radius) == pytest.approx(expected, abs=0.15)
    assert spare(4, 30, 1000) == pytest.approx(23.8, abs=0.15)
    assert spare(4, 30, 10000) < 0

    # ... and the guard acts on exactly that boundary
    assert _gamma_cauchy(4, 30, radius=1000)[0] > 0
    with pytest.raises(ValueError, match="round-off floor"):
        _gamma_cauchy(4, 30, radius=10000)
    with pytest.raises(ValueError, match="round-off floor"):
        _gamma_cauchy(6, 30, radius=100000)
    with pytest.raises(ValueError, match="radius must be positive"):
        _gamma_cauchy(3, 20, radius=0)
    # the node count is still finite and sane at the boundary
    assert _gamma_cauchy_nodes(4, 66, 1000) < 200


def test_gamma_cauchy_starved_precision_tradeoff_table():
    """The radius/node trade-off table in ``_gamma_cauchy``'s docstring, measured.

    Re-runs that function's inner loop by hand at a *fixed* working precision of
    80 digits with a *fixed* node count, against a dps = 110 reference from the
    independent Mellin path, max relative error over n ≤ 20:

        radius   nodes   max rel err
        30       80      1.24e-58
        10       30      1.11e-47
        30       30      1.54e-44
        4        30      1.24e-39
        100      30      7.48e-29

    Both a too-small and a too-large radius cost digits (small R shrinks R^n
    against max|F|; large R inflates max|F| = max|8ξ(½+√w)| much faster), and
    starving the node count costs ~14 digits on its own.  The default R = 30
    with 2n+40 nodes sits at the flat bottom, which is *why* the guard budget
    is 2.6 digits per coefficient, and this is the only place those numbers are
    pinned.  (An earlier version of the docstring quoted a different table that
    did not reproduce; this one does, row for row.)
    """
    from zeta.core import xi
    from zeta.li import _gamma_integral, _roots_of_unity

    ref = _gamma_integral(20, 110)

    def starved(work, radius, n_points):
        with mp.workdps(work):
            Rw = mp.mpf(radius)
            w = _roots_of_unity(n_points)
            F = [8 * xi(mp.mpf(1) / 2 + mp.sqrt(Rw * wj), work) for wj in w]
            return [
                mp.factorial(n)
                * mp.re(
                    mp.fsum(F[j] * w[(-(j * n)) % n_points] for j in range(n_points))
                    * mp.power(Rw, -n)
                    / n_points
                )
                for n in range(21)
            ]

    table = ((30, 80, 1.24e-58), (10, 30, 1.11e-47), (30, 30, 1.54e-44),
             (4, 30, 1.24e-39), (100, 30, 7.48e-29))
    for radius, n_points, expected in table:
        v = starved(80, radius, n_points)
        with mp.workdps(130):
            worst = max(abs((a - b) / a) for a, b in zip(ref, v))
        assert float(worst) == pytest.approx(expected, rel=0.05), (
            radius, n_points, mp.nstr(worst, 4)
        )
    # and the flat bottom really is the best row of the five
    assert min(r[2] for r in table) == table[0][2]


def test_gamma_positive_and_decaying():
    """All γ(n) > 0, and γ(n+1) < γ(n), the sequence is a genuine LP candidate."""
    assert all(g > 0 for g in GAMMAS)
    assert all(GAMMAS[i + 1] < GAMMAS[i] for i in range(len(GAMMAS) - 1))
    assert mp.nstr(GAMMAS[10], 16) == "1.632338049030142e-17"


def test_gamma_satisfies_the_turan_inequality():
    """γ(n)² − γ(n−1)γ(n+1) > 0 for every n scanned.

    This is exactly the hyperbolicity of J^{2,n−1} (the discriminant of a
    quadratic), i.e. the Csordas–Norfolk–Varga Turán inequalities for Ξ.  It is
    a theorem for all n; here it is *measured*, and the measured margin says
    the sign is not a rounding artefact.
    """
    with mp.workdps(50):
        for n in range(1, len(GAMMAS) - 1):
            lhs = GAMMAS[n] ** 2 - GAMMAS[n - 1] * GAMMAS[n + 1]
            assert lhs > 0, n
            # relative margin: not a near-miss anywhere in range
            assert lhs / (GAMMAS[n] ** 2) > 0.01, (n, float(lhs / GAMMAS[n] ** 2))


def test_lambda_cache_is_bit_exact_not_merely_close(tmp_path, monkeypatch):
    """A cached λ table must reload **bit-identically**, not just to ``dps``.

    CLAUDE.md's standing hazard: "if you change numerical internals, delete the
    affected cache files, or stale numbers will pass".  The defence is that a
    reload is bit-exact, so a genuine change of internals shows up as a
    difference rather than hiding inside a tolerance.  ``_save_table`` writes
    ``repr_dps(mp.prec)`` digits (28 at dps = 25) precisely so the decimal
    round-trips the binary value exactly.

    Checked here for the file this test writes, and verified out of band for
    every committed ``data/li_*.json`` table:

    * the five small tables (n_max ≤ 70, 145 entries) recompute bit-identically;
    * ``li_lambda_dps20_methodcauchy_n304_radius0.5.json`` (304 entries) was
      re-derived from scratch **at radius 0.3**, a different circle, a
      different working precision and a different node count, and agrees to
      4.4e-23 relative, three orders better than the dps = 20 it advertises;
    * ``li_gamma_dps30_methodintegral_n128.json`` (129 entries) was checked at
      n = 0, 1, 2, 10, 25, 64, 100, 120, 128 against Riemann's ω′ integral (see
      ``test_gamma_against_riemanns_other_integral_an_independent_oracle``) and
      agrees to ≤ 4.7e-32 relative throughout.
    """
    from zeta.li import _li_cauchy, _load_table

    monkeypatch.setattr(li_lane, "DATA_DIR", str(tmp_path))
    computed = li_coefficients(16, dps=25, cache=True)  # computes and saves
    reloaded = _load_table("lambda", 16, 25, method="cauchy", radius="0.5")
    assert reloaded is not None
    assert all(a == b for a, b in zip(computed, reloaded[:16]))  # bit-exact

    # and both equal a genuinely from-scratch run, bit for bit
    scratch = _li_cauchy(16, 25, "0.5")
    assert all(a == b for a, b in zip(scratch, computed))


def test_gamma_cache_roundtrip(tmp_path, monkeypatch):
    """The cached table must reproduce the computed one exactly."""
    monkeypatch.setattr(li_lane, "DATA_DIR", str(tmp_path))
    fresh = xi_taylor_coefficients(6, dps=25, cache=True)
    assert any(p.name.startswith("li_gamma_") for p in tmp_path.iterdir())
    again = xi_taylor_coefficients(6, dps=25, cache=True)
    assert all(a == b for a, b in zip(fresh, again))
    # a larger cached table is reused (truncated) for a smaller request
    smaller = xi_taylor_coefficients(3, dps=25, cache=True)
    assert len(smaller) == 4
    assert all(a == b for a, b in zip(smaller, fresh))


# ---------------------------------------------------------------------------
# 5.  Jensen polynomials and hyperbolicity
# ---------------------------------------------------------------------------


def test_jensen_polynomial_coefficients():
    """J^{d,n}(X) = Σ_j C(d,j) γ(n+j) X^j, ascending order."""
    c = jensen_polynomial(3, 2, dps=30, gammas=GAMMAS)
    with mp.workdps(35):
        for j, expected in enumerate([1, 3, 3, 1]):
            assert abs(c[j] - expected * GAMMAS[2 + j]) < mp.mpf(10) ** -28
    # the normalised form is the same polynomial in a rescaled variable
    nrm = jensen_polynomial(3, 2, dps=30, gammas=GAMMAS, normalise=True)
    assert nrm[0] == 1
    with mp.workdps(30):
        assert abs(nrm[1] - 3) < mp.mpf(10) ** -28
    with pytest.raises(ValueError):
        jensen_polynomial(0, 0, gammas=GAMMAS)
    with pytest.raises(ValueError):
        jensen_polynomial(3, 40, gammas=GAMMAS)  # not enough gammas supplied


def test_is_hyperbolic_control_polynomials():
    """A deliberately non-hyperbolic control must be flagged False.

    X² + 1 has roots ±i: ``hyperbolic`` False, ``max_abs_imag`` 1.0, and the
    exact Sturm count of real roots 0.  The two independent verdicts agree.
    """
    bad = is_hyperbolic([1, 0, 1], dps=30)
    assert bad["hyperbolic"] is False
    assert bad["max_abs_imag"] == pytest.approx(1.0, rel=1e-12)
    assert bad["n_real_exact"] == 0
    assert bad["agree"] is True

    # and a hyperbolic control: (X-1)(X-2) = 2 - 3X + X^2
    good = is_hyperbolic([2, -3, 1], dps=30)
    assert good["hyperbolic"] is True
    assert good["n_real_exact"] == 2
    assert good["max_abs_imag"] < 1e-25
    roots = sorted(float(mp.re(r)) for r in good["roots"])
    assert roots == pytest.approx([1.0, 2.0], rel=1e-20)

    # a mixed case: (X^2+1)(X-3), one real root, two complex
    mixed = is_hyperbolic([3, -1, 3, -1][::-1], dps=30)
    assert mixed["hyperbolic"] is False
    assert mixed["n_real_exact"] == 1

    # degree-1 is trivially hyperbolic
    assert is_hyperbolic([1, 2], dps=30)["hyperbolic"] is True
    with pytest.raises(ValueError):
        is_hyperbolic([3.0], dps=30)
    with pytest.raises(ValueError):
        is_hyperbolic([1, 0, 1], dps=30, method="nonsense")
    # a genuinely complex coefficient must be refused up front: hyperbolicity
    # is a statement about real polynomials, and the Sturm branch used to die
    # with an opaque "cannot create mpf from mpc" deep inside _to_rational.
    with pytest.raises(ValueError, match="real coefficients"):
        is_hyperbolic([mp.mpc(1, 1), 0, 1], dps=30)
    # a complex type carrying a zero imaginary part is fine, though
    assert is_hyperbolic([mp.mpc(2, 0), -3, 1], dps=30)["n_real_exact"] == 2


def test_is_hyperbolic_tolerance_test_can_be_fooled_but_sturm_cannot():
    """Honesty about the tolerance test, made concrete.

    (X − 1 − iδ)(X − 1 + iδ) = X² − 2X + (1 + δ²) has a complex pair with
    imaginary parts ±δ.  With δ = 1e-18 the *relative* imaginary part is 1e-18,
    below the default tolerance 10^{−dps/2} = 1e-15, so ``method="roots"``
    calls it hyperbolic, wrongly.  The exact Sturm count (discriminant −4δ²)
    does not.  This is why ``method="both"`` is the default, why the Sturm
    verdict wins, and why ``max_rel_imag`` and ``agree`` are returned.

    (Note the roots here survive the internal balancing: |roots| ≈ 1 already,
    so this is not a conditioning artefact.  The naive example X² + δ², by
    contrast, is *rescued* by balancing: X ↦ δX turns it into X² + 1.)
    """
    with mp.workdps(60):
        delta = mp.mpf(10) ** -18
        coeffs = [1 + delta ** 2, mp.mpf(-2), mp.mpf(1)]
    loose = is_hyperbolic(coeffs, dps=30, method="roots")
    strict = is_hyperbolic(coeffs, dps=30, method="both")
    assert loose["hyperbolic"] is True  # the tolerance test is fooled
    assert loose["max_rel_imag"] == pytest.approx(1e-18, rel=1e-3)
    assert strict["hyperbolic"] is False  # Sturm is not
    assert strict["n_real_exact"] == 0
    assert strict["agree"] is False  # and the disagreement is reported

    # the naive near-miss X^2 + delta^2 IS caught by the tolerance test,
    # because balancing normalises its roots to +-i
    naive = is_hyperbolic([delta ** 2, mp.mpf(0), mp.mpf(1)], dps=30)
    assert naive["hyperbolic"] is False
    assert naive["max_rel_imag"] == pytest.approx(1.0, rel=1e-9)


def test_balance_preserves_the_root_set_up_to_scale():
    """The internal rescaling is X ↦ sX, s > 0, a bijection of ℝ."""
    coeffs = [mp.mpf(6), mp.mpf(-11), mp.mpf(6), mp.mpf(-1)]  # -(X-1)(X-2)(X-3)
    scaled, s = _balance(coeffs)
    assert s > 0
    info = is_hyperbolic(coeffs, dps=30, method="roots")
    roots = sorted(float(mp.re(r)) for r in info["roots"])
    assert roots == pytest.approx([1.0, 2.0, 3.0], rel=1e-20)
    # balancing brings the coefficients within a couple of orders of magnitude
    span = max(abs(c) for c in scaled) / min(abs(c) for c in scaled)
    assert span < 10


def test_balance_conditioning_spans_on_real_jensen_polynomials():
    """The conditioning numbers quoted in ``_balance``'s docstring, measured.

    Coefficient span = log₁₀(max|c| / min|c|) for J^{d,0}:

        d = 8:   raw 10^13.8  →  normalised 10^2.4  →  after _balance 10^2.0
        d = 16:  raw 10^28.5  →  normalised 10^5.9  →  after _balance 10^4.6

    This is why the scan works in the normalised variable and why the root
    finder is given a balanced polynomial: 28 orders of magnitude of
    coefficient spread is what a naive Durand–Kerner would have to swallow.
    """
    def span(coeffs):
        return float(mp.log10(max(abs(c) for c in coeffs) / min(abs(c) for c in coeffs)))

    with mp.workdps(40):
        for d, raw_x, nrm_x, bal_x in ((8, 13.8, 2.4, 2.0), (16, 28.5, 5.9, 4.6)):
            raw = jensen_polynomial(d, 0, dps=30, gammas=GAMMAS)
            nrm = jensen_polynomial(d, 0, dps=30, gammas=GAMMAS, normalise=True)
            bal, s = _balance(nrm)
            assert span(raw) == pytest.approx(raw_x, abs=0.05), (d, span(raw))
            assert span(nrm) == pytest.approx(nrm_x, abs=0.05), (d, span(nrm))
            assert span(bal) == pytest.approx(bal_x, abs=0.05), (d, span(bal))
            assert s > 0  # a positive rescaling: hyperbolicity is untouched


def test_jensen_polynomials_are_hyperbolic_no_violation_found():
    """**No non-hyperbolic J^{d,n} was found for 1 ≤ d ≤ 8, 0 ≤ n ≤ 12.**

    Pólya's criterion is an equivalence, so a single ``False`` would refute RH;
    correspondingly an all-``True`` table means only "no violation found in
    this range" and is not evidence for RH (docs/08).

    Measured at dps = 30 over this 104-row block: max relative |Im root|
    1.706e-105 and smallest relative root gap 0.08914, the roots are real to
    far beyond working precision and are well separated, so the verdicts are
    not borderline.  The bound below is 1e-90, not the 1e-60 an earlier version
    used: 45 orders of slack is a tolerance that cannot fail, and the root
    finder's ``extraprec=40·degree+200`` makes 1e-90 a real constraint while
    leaving 15 orders for a change of mpmath's Durand–Kerner internals.
    """
    rows = hyperbolicity_scan(8, 12, dps=30)
    assert len(rows) == 8 * 13
    bad = [(r["d"], r["n"]) for r in rows if not r["hyperbolic"]]
    assert bad == []
    worst_imag = max(r["max_rel_imag"] for r in rows)
    tightest = min(r["min_gap"] for r in rows)
    assert worst_imag < 1e-90, worst_imag
    assert tightest == pytest.approx(0.08914, rel=0.02), tightest


def test_hyperbolicity_agrees_with_an_independent_numpy_root_finder():
    """A third root finder, in double precision, sharing no code with the module.

    ``numpy.roots`` builds a companion matrix and runs LAPACK's QR iteration,
    nothing in common with mpmath's Durand–Kerner or sympy's Sturm sequences.
    On the normalised Jensen polynomials it returns roots whose imaginary parts
    are **exactly** 0.0 in double precision for every (d, n) spot-checked here,
    which is the strongest form the double-precision statement can take.
    """
    numpy = pytest.importorskip("numpy")

    gam = xi_taylor_coefficients(30, dps=30)
    for d in (2, 3, 5, 8, 12):
        for n in (0, 3, 10, 17):
            coeffs = jensen_polynomial(d, n, dps=30, gammas=gam, normalise=True)
            roots = numpy.roots([float(c) for c in coeffs][::-1])  # descending
            assert len(roots) == d
            assert float(numpy.max(numpy.abs(roots.imag))) == 0.0, (d, n)
            assert bool(numpy.all(roots.real < 0)), (d, n)  # and all negative
            # ... and the module agrees, by both of its own methods
            assert is_hyperbolic(coeffs, dps=30, method="both")["hyperbolic"]


def test_hyperbolicity_scan_sturm_agrees_with_the_root_test():
    """The exact Sturm count agrees with the tolerance test on a sub-block."""
    rows = hyperbolicity_scan(4, 4, dps=30, method="both")
    assert all(r["hyperbolic"] for r in rows)
    for r in rows:
        assert r["n_real_exact"] == r["d"]


def test_low_degree_jensen_by_hand():
    """d = 2 hyperbolicity IS the Turán inequality; check the discriminant."""
    for n in (0, 3, 7, 15):
        c = jensen_polynomial(2, n, dps=30, gammas=GAMMAS)
        with mp.workdps(50):
            disc = c[1] ** 2 - 4 * c[0] * c[2]
            assert disc > 0
            # C(2,1)^2 γ(n+1)^2 − 4 γ(n) γ(n+2) = 4[γ(n+1)^2 − γ(n)γ(n+2)]
            turan = GAMMAS[n + 1] ** 2 - GAMMAS[n] * GAMMAS[n + 2]
            assert abs(disc - 4 * turan) < abs(disc) * mp.mpf(10) ** -25
        assert is_hyperbolic(c, dps=30)["hyperbolic"] is True


def test_jensen_roots_are_all_negative():
    """All γ(n) > 0 ⟹ a hyperbolic J^{d,n} has only *negative* roots.

    That is the shape the Laguerre–Pólya class demands of F(w) = Σ γ(n)w^n/n!,
    whose zeros on RH are w = −γ² < 0.
    """
    for d, n in ((3, 0), (5, 4), (8, 10)):
        info = is_hyperbolic(
            jensen_polynomial(d, n, dps=30, gammas=GAMMAS, normalise=True),
            dps=30,
            method="roots",
        )
        assert info["hyperbolic"]
        assert all(mp.re(r) < 0 for r in info["roots"])


def test_jensen_roots_approach_hermite_roots():
    """GORZ: the renormalised roots of J^{d,n} converge to the roots of H_d.

    Compared after standardising both root vectors (mean 0, sd 1), which
    removes the affine normalisation entirely.  Measured max deviation:

        d = 3:  0.0339 (n=10) → 0.0223 (n=110)
        d = 4:  0.0350 (n=10) → 0.0226 (n=110)
        d = 6:  0.0681 (n=10) → 0.0434 (n=110)

    The convergence is slow, that is the honest picture.  Every cell of the
    docstring table in ``jensen_roots_vs_gue`` is pinned here (n = 10, 20, 40,
    110), together with monotonicity in n.
    """
    gam = xi_taylor_coefficients(120, dps=30)
    table = {
        3: (0.03385, 0.03293, 0.02938, 0.02231),
        4: (0.03498, 0.03373, 0.02997, 0.02265),
        6: (0.06808, 0.06484, 0.05742, 0.04337),
    }
    for d, expected in table.items():
        got = [
            jensen_roots_vs_gue(d, n, dps=30, gammas=gam) for n in (10, 20, 40, 110)
        ]
        devs = [r["max_deviation"] for r in got]
        for want, have, n in zip(expected, devs, (10, 20, 40, 110)):
            assert have == pytest.approx(want, rel=0.02), (d, n, have)
        assert all(b < a for a, b in zip(devs, devs[1:]))  # monotone in n
        assert all(r["hyperbolic"] for r in got)
        assert len(got[0]["roots"]) == d == len(got[0]["hermite_roots"])

    # d = 2 is exact for every n by symmetry: measured 0 ... 1.6e-15
    for n in (7, 10, 20, 40, 110):
        assert jensen_roots_vs_gue(2, n, dps=30, gammas=gam)["max_deviation"] < 5e-15
    with pytest.raises(ValueError):
        jensen_roots_vs_gue(1, 0, gammas=gam)


@pytest.mark.slow
def test_gamma_cauchy_radius_grid():
    """The full 40-cell radius grid quoted in ``_gamma_cauchy``'s docstring (~48 s).

    dps ∈ {30, 80} × n_max ∈ {4, 12, 20, 30} × radius ∈ {4, 10, 30, 100, 300}:
    every cell bit-identical to the independent Mellin-integral path.
    """
    from zeta.li import _gamma_cauchy, _gamma_integral

    for dps in (30, 80):
        for n_max in (4, 12, 20, 30):
            ref = _gamma_integral(n_max, dps)
            for radius in (4, 10, 30, 100, 300):
                v = _gamma_cauchy(n_max, dps, radius=radius)
                with mp.workdps(dps + 60):
                    worst = max(abs((a - b) / a) for a, b in zip(ref, v))
                assert worst == 0, (dps, n_max, radius, mp.nstr(worst, 4))


@pytest.mark.slow
def test_hyperbolicity_scan_to_degree_16():
    """The wider table: 1 ≤ d ≤ 16, 0 ≤ n ≤ 25 (416 rows, ~55 s).

    Measured: all hyperbolic, max relative |Im root| 3.722e-104, smallest
    relative root gap 0.04316.  Again: "no violation found", not evidence
    for RH.
    """
    rows = hyperbolicity_scan(16, 25, dps=30)
    assert len(rows) == 16 * 26
    assert all(r["hyperbolic"] for r in rows)
    assert max(r["max_rel_imag"] for r in rows) < 1e-90
    assert min(r["min_gap"] for r in rows) == pytest.approx(0.04316, rel=0.02)


# ---------------------------------------------------------------------------
# 6.  hygiene
# ---------------------------------------------------------------------------


def test_no_global_mpmath_state_is_modified():
    """House rule: every entry point restores mp.dps."""
    before = mp.dps
    li_closed_form_lambda1(dps=45)
    li_coefficients(3, dps=20)
    xi_taylor_coefficients(4, dps=20)
    is_hyperbolic([1, 0, 1], dps=20)
    jensen_roots_vs_gue(3, 2, dps=20)
    li_positivity_scan(3, dps=20)
    assert mp.dps == before


def test_data_dir_is_derived_from_the_package_not_hardcoded():
    """No username may appear in a committed path, in the module *or* here.

    The needles are assembled at run time so that this file does not itself
    contain the literal strings a repo-wide grep for hardcoded paths looks for;
    the previous version tripped its own check.
    """
    assert DATA_DIR.endswith(os.path.join("Zeta", "data")) or DATA_DIR.endswith("data")
    assert os.path.isabs(DATA_DIR)
    needles = ("/" + "Users" + "/", "/" + "home" + "/", "C:" + chr(92))
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for rel in (("zeta", "li.py"), ("tests", "test_li.py")):
        with open(os.path.join(root, *rel)) as fh:
            text = fh.read()
        for needle in needles:
            assert needle not in text, (rel, needle)


def test_the_logarithmic_integral_still_works():
    """Importing this module shadows ``zeta.li`` the *function*.

    ``zeta.explicit.li`` is the logarithmic integral and ``zeta/__init__.py``
    re-exports it as ``zeta.li``; ``import zeta.li`` rebinds that attribute to
    this module.  Nothing in the package reaches the function that way, but the
    collision is real, so it is pinned here rather than left to be discovered.
    """
    import zeta
    import zeta.explicit

    assert zeta.explicit.li(2) == pytest.approx(1.0451637801174927848, rel=1e-14)
    # after `import zeta.li`, the package attribute is the module
    assert zeta.li is li_lane
    assert callable(zeta.explicit.li)


def test_bad_arguments():
    with pytest.raises(ValueError):
        li_coefficient(0)
    with pytest.raises(ValueError):
        li_coefficients(3, method="nope")
    with pytest.raises(ValueError):
        xi_taylor_coefficients(3, method="nope", cache=False)
    with pytest.raises(ValueError):
        xi_taylor_coefficients(-1)
    assert li_coefficients(0) == []
