"""Tests for :mod:`zeta.rigor` — certified (ball-arithmetic) computation.

The point of this module is that its outputs are *proofs*, so the tests are
mostly containment and agreement statements rather than tolerance checks:

* every enclosure must **contain** mpmath's independently computed value —
  that is a hard, tolerance-free assertion, and the only way it can fail is if
  the enclosure is wrong;
* ``proven_sign`` must agree with ``mp.siegelz``'s sign at every point where it
  commits, and must return 0 (not a guess) where it cannot;
* the two backends (Arb via python-flint, and mpmath's interval context with a
  hand-rolled Euler–Maclaurin ζ) are entirely independent implementations, so
  their enclosures of the same quantity must **overlap**.

Ground truth: N(100) = 29, N(1000) = 649, and mpmath's ``siegelz``,
``backlunds`` and ``nzeros`` as the independent (non-rigorous) oracle.
"""

from __future__ import annotations

import math
import os
import random
import subprocess
import sys
import time
from fractions import Fraction

import pytest
from mpmath import iv, mp

from zeta import rigor
from zeta.rigor import (
    BACKEND,
    BACKEND_REASON,
    available_backends,
    certified_sign_changes,
    certified_zero_count,
    enclose_Z,
    enclosure_width_report,
    proven_sign,
    verify_rh_certified,
)

HAVE_FLINT = "python-flint" in available_backends()
BOTH = [pytest.param(b, id=b) for b in available_backends()]

#: A spread of ordinates: small, near γ₁, at a Gram point, at the first Gram-law
#: failure, and high.  Deliberately includes t where |Z| is small.
SAMPLE_TS = [
    0.0,
    0.5,
    3.0,
    9.666908056130195,
    14.5,
    17.845599540410095,
    20.0,
    50.0,
    100.0,
    282.4547208234623,
    300.5,
    1000.0,
]


# ---------------------------------------------------------------------------
# backend reporting
# ---------------------------------------------------------------------------


def test_backend_is_named_honestly():
    assert BACKEND in {"python-flint", "mpmath.iv"}
    assert BACKEND in available_backends()
    assert "mpmath.iv" in available_backends()  # always present
    assert isinstance(BACKEND_REASON, str) and BACKEND_REASON


def test_backend_default_prefers_flint_when_available():
    assert BACKEND == ("python-flint" if HAVE_FLINT else "mpmath.iv")


def test_unknown_backend_rejected():
    with pytest.raises(ValueError, match="unknown backend"):
        enclose_Z(20.0, 64, backend="not-a-backend")


# ---------------------------------------------------------------------------
# exact input conversion
# ---------------------------------------------------------------------------


def test_exact_conversion_is_exact():
    assert rigor._exact(3) == Fraction(3)
    assert rigor._exact(0.5) == Fraction(1, 2)
    assert rigor._exact("14.5") == Fraction(29, 2)
    assert rigor._exact(Fraction(7, 3)) == Fraction(7, 3)
    # a float is the dyadic rational it really is, not the decimal it prints as
    assert rigor._exact(0.1) == Fraction(3602879701896397, 36028797018963968)
    with mp.workdps(40):
        assert rigor._exact(mp.mpf(1) / 4) == Fraction(1, 4)
        assert rigor._exact(mp.mpf(0)) == Fraction(0)
    with pytest.raises(TypeError):
        rigor._exact(True)


def test_same_point_written_four_ways_gives_the_same_enclosure():
    ref = enclose_Z(Fraction(29, 2), 128)
    for spelling in (14.5, "14.5", mp.mpf("14.5"), Fraction(29, 2)):
        assert enclose_Z(spelling, 128) == ref


# ---------------------------------------------------------------------------
# enclosures contain the truth
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("backend", BOTH)
def test_enclosures_contain_mpmath_value(backend):
    """The defining property: lo ≤ Z(t) ≤ hi, checked against mpmath.

    The oracle is evaluated at dps = 70, comfortably beyond the ~48 digits of
    the widest enclosure tested here.  That margin is not decoration: a 160-bit
    enclosure of θ(3) is 2.2e-47 wide, and ``mp.siegeltheta`` at dps = 45 misses
    it — the *enclosure* is the sharper object, and the oracle has to be asked
    for more digits to keep up.
    """
    with mp.workdps(70):
        for t in SAMPLE_TS:
            for bits in (64, 160):
                lo, hi = enclose_Z(t, bits, backend=backend)
                truth = mp.siegelz(mp.mpf(t))
                assert lo <= truth <= hi, f"backend={backend} t={t} bits={bits}"
                assert lo <= hi


def test_enclosures_contain_mpmath_value_at_many_random_points():
    """200 random ordinates in (0, 400) — none may escape its enclosure."""
    rng = random.Random(20260801)
    with mp.workdps(50):
        for _ in range(200):
            t = rng.uniform(0.0, 400.0)
            lo, hi = enclose_Z(t, 96)
            assert lo <= mp.siegelz(mp.mpf(t)) <= hi, t


@pytest.mark.parametrize("backend", BOTH)
def test_enclosures_contain_the_repo_s_own_Z(backend):
    """Containment against a *second* oracle: ``zeta.core.Z``, not ``siegelz``.

    ``mp.siegelz`` uses the Riemann–Siegel asymptotic expansion; ``zeta.core.Z``
    forms e^{iϑ}ζ from ``mp.loggamma`` and ``mp.zeta`` directly.  If the module
    had inherited a convention error from one of them, the other would catch it.
    The oracle runs at dps 80 because a 160-bit enclosure is ~48 digits wide and
    a dps-45 oracle is the *less* accurate object of the two.
    """
    from zeta.core import Z as core_Z

    for t in (0.0, 3.0, 14.5, 50.0, 100.0, 300.5, 1000.0):
        lo, hi = enclose_Z(t, 160, backend=backend)
        value = core_Z(t, dps=80)
        with mp.workdps(90):
            assert lo <= value <= hi, f"backend={backend} t={t}"


@pytest.mark.parametrize("backend", BOTH)
def test_Z_is_even_so_mirrored_enclosures_agree(backend):
    """Z(−t) = Z(t): a symmetry the code never uses, so it is a real test.

    ϑ(−t) = −ϑ(t) and ζ(1/2 − it) = conj ζ(1/2 + it), so Z is even.  Nothing in
    ``enclose_Z`` exploits that — the two sides are computed independently — and
    their enclosures must therefore overlap, and must both contain the truth.
    """
    with mp.workdps(70):
        for t in (3.0, 14.5, 100.0, 282.4547208234623):
            a_lo, a_hi = enclose_Z(t, 128, backend=backend)
            b_lo, b_hi = enclose_Z(-t, 128, backend=backend)
            assert a_lo <= b_hi and b_lo <= a_hi, f"{backend} t={t}"
            truth = mp.siegelz(mp.mpf(t))
            assert a_lo <= truth <= a_hi and b_lo <= truth <= b_hi


@pytest.mark.parametrize("backend", BOTH)
def test_theta_enclosure_contains_siegeltheta(backend):
    with mp.workdps(70):
        for t in (3.0, 20.0, 100.0, 1000.0):
            lo, hi = rigor.enclose_rs_theta(t, 160, backend=backend)
            assert lo <= mp.siegeltheta(mp.mpf(t)) <= hi


@pytest.mark.skipif(not HAVE_FLINT, reason="needs both backends installed")
def test_two_independent_backends_overlap():
    """Arb and the hand-rolled Euler–Maclaurin must enclose the same number.

    They share no code and no algorithm: Arb uses its own ζ implementation,
    ``mpmath.iv`` uses the Euler–Maclaurin series with an explicit remainder
    bound written in this repo.  Disjoint enclosures would mean one of them is
    wrong.
    """
    for t in (0.0, 3.0, 14.5, 50.0, 100.0, 300.5):
        a_lo, a_hi = enclose_Z(t, 160, backend="python-flint")
        b_lo, b_hi = enclose_Z(t, 160, backend="mpmath.iv")
        assert a_lo <= b_hi and b_lo <= a_hi, f"disjoint enclosures at t={t}"


def test_euler_maclaurin_remainder_bound_holds_when_it_dominates(monkeypatch):
    """Stress the mpmath.iv backend's ζ remainder bound with tiny N and M.

    At the module's own choice of N and M the remainder is astronomically small,
    so a *wrong* bound would never be noticed.  Forcing N = 8, M = 4 makes the
    remainder the dominant term — the enclosure of ζ(1/2+100i) is then over a
    thousand units wide — and the truth must still be inside it.  Widening N, M
    walks the enclosure down.  Measured widths at t = 100, prec = 160 bits, for
    (N,M) = (8,4), (12,6), (20,8), (30,10), (60,20):

        σ = 1/2 : 1.18e3, 56.0, 1.84e-2, 1.07e-6, 1.50e-24
        σ = 2   : 45.3,   1.23, 1.95e-4, 6.29e-9, 3.54e-27

    always containing ζ.  (The σ = 2 row is the narrower one — the remainder
    carries a factor N^{−σ}.)
    """
    B = rigor._MPIntervalBackend
    misses = []
    widths = {}  # (N, M) -> {sigma: enclosure width of zeta(sigma + 100i)}
    with mp.workdps(60):
        for N, M in [(8, 4), (12, 6), (20, 8), (30, 10), (60, 20)]:
            monkeypatch.setattr(
                B, "_em_params", staticmethod(lambda prec, abs_s, N=N, M=M: (N, M))
            )
            widths[(N, M)] = {}
            for sig in (Fraction(1, 2), Fraction(1), Fraction(2)):
                for t in (3, 10, 25, 50, 100):
                    rl, rh, il, ih = B.zeta_box(sig, sig, Fraction(t), 160)
                    x = mp.mpf(sig.numerator) / sig.denominator
                    v = mp.zeta(mp.mpc(x, t))
                    if not (rl <= v.real <= rh and il <= v.imag <= ih):
                        misses.append((N, M, sig, t))
                    if t == 100:
                        widths[(N, M)][sig] = rh - rl
        half, two = Fraction(1, 2), Fraction(2)
        # the (8,4) enclosure must be uselessly wide on both abscissae ...
        assert widths[(8, 4)][half] > 100, widths[(8, 4)][half]
        assert widths[(8, 4)][two] > 1, widths[(8, 4)][two]
        # ... and must shrink monotonically as N and M grow ...
        for sig in (half, two):
            seq = [widths[k][sig] for k in [(8, 4), (12, 6), (20, 8), (30, 10), (60, 20)]]
            assert all(seq[i + 1] < seq[i] for i in range(len(seq) - 1)), seq
        # ... down to the values quoted above, to within a factor of 10.
        assert mp.mpf("1.5e-25") < widths[(60, 20)][half] < mp.mpf("1.5e-23")
        assert mp.mpf("3.5e-28") < widths[(60, 20)][two] < mp.mpf("3.5e-26")
    assert misses == []


def test_euler_maclaurin_remainder_bound_holds_at_absurd_N_and_M(monkeypatch):
    """The same bound where it is most likely to be wrong: N < 2M, N as low as 2.

    ``_em_params`` never chooses these, so nothing in normal operation would
    expose a mis-stated validity condition.  The bound
    ``|E| ≤ |(s+2M+1)/(σ+2M+1)|·|B_{2M+2}/(2M+2)!·(s)_{2M+1}·N^{−s−2M−1}|``
    needs only σ + 2M + 1 > 0, so it must hold here too — and it does, at the
    price of enclosures up to ~7e12 wide.
    """
    B = rigor._MPIntervalBackend
    misses = []
    with mp.workdps(80):
        for N, M in [(2, 1), (3, 1), (2, 2), (5, 2), (4, 10), (16, 3), (200, 5)]:
            monkeypatch.setattr(
                B, "_em_params", staticmethod(lambda prec, abs_s, N=N, M=M: (N, M))
            )
            for sig in (Fraction(1, 4), Fraction(1, 2), Fraction(2), Fraction(7, 3)):
                for t in (1, 30, 100, 1000):
                    rl, rh, il, ih = B.zeta_box(sig, sig, Fraction(t), 200)
                    x = mp.mpf(sig.numerator) / sig.denominator
                    v = mp.zeta(mp.mpc(x, t))
                    if not (rl <= v.real <= rh and il <= v.imag <= ih):
                        misses.append((N, M, sig, t))
    assert misses == []


def test_bernoulli_coefficients_match_sympy():
    """B_{2k}/(2k)! — the E-M coefficients — against sympy's exact rationals."""
    sympy = pytest.importorskip("sympy")
    for k in range(1, 21):
        b = sympy.Rational(sympy.bernoulli(2 * k))
        want = Fraction(int(b.p), int(b.q) * math.factorial(2 * k))
        assert rigor._bern_coeff(k) == want, k


@pytest.mark.parametrize("backend", BOTH)
def test_enclosure_narrows_with_precision(backend):
    """More bits, narrower ball — and every ball nested in the previous one."""
    prev_width = None
    prev = None
    for bits in (32, 64, 128, 256):
        lo, hi = enclose_Z(100.0, bits, backend=backend)
        with mp.workdps(90):
            width = hi - lo
        assert width > 0
        if prev_width is not None:
            assert width < prev_width / 100, f"{bits} bits barely improved on the last"
            assert prev[0] <= lo and hi <= prev[1], "enclosures must nest"
        prev_width, prev = width, (lo, hi)


# ---------------------------------------------------------------------------
# proven signs
# ---------------------------------------------------------------------------


def test_proven_sign_agrees_with_mpmath_everywhere_it_decides():
    """400 random points: no disagreement is tolerated, at all, ever."""
    rng = random.Random(4242)
    decided = 0
    with mp.workdps(50):
        for _ in range(400):
            t = rng.uniform(0.05, 300.0)
            s = proven_sign(t, prec_bits=64, max_escalations=4)
            if s == 0:
                continue
            decided += 1
            truth = mp.siegelz(mp.mpf(t))
            assert s == (1 if truth > 0 else -1), t
    assert decided == 400, "every one of these points is decided at 64 bits"


@pytest.mark.parametrize("backend", BOTH)
def test_proven_sign_agrees_on_the_landmark_points(backend):
    with mp.workdps(60):
        for t in SAMPLE_TS:
            s = proven_sign(t, prec_bits=64, max_escalations=5, backend=backend)
            truth = mp.siegelz(mp.mpf(t))
            assert s == (1 if truth > 0 else -1), f"{backend} t={t}"


def test_proven_sign_refuses_to_guess_at_low_precision():
    """The safe failure mode: 4 bits decides nothing, and says so."""
    assert proven_sign(100.0, prec_bits=4, max_escalations=0) == 0
    assert proven_sign(20.0, prec_bits=4, max_escalations=0) == 0
    # ... and escalation rescues it
    assert proven_sign(100.0, prec_bits=4, max_escalations=8) == 1


def test_proven_sign_undecided_next_to_a_zero_then_decided():
    """A hair off γ₁, |Z| ≈ 2.3e-36: 64 bits cannot decide, 512 bits can.

    γ₁ rounded to 35 digits is *not* a zero of Z, so a sign does exist there —
    it is just far too small to see at low precision.  This is the whole
    behaviour of the module in one test: refuse, then decide, and never be
    wrong about which.
    """
    with mp.workdps(35):
        g1 = mp.mpf(mp.im(mp.zetazero(1)))
    with mp.workdps(80):
        truth = mp.siegelz(g1)
        assert 0 < abs(truth) < mp.mpf("1e-30")
        want = 1 if truth > 0 else -1
    assert proven_sign(g1, prec_bits=32, max_escalations=0) == 0
    assert proven_sign(g1, prec_bits=64, max_escalations=0) == 0
    assert proven_sign(g1, prec_bits=512, max_escalations=0) == want


# ---------------------------------------------------------------------------
# certified sign-change counting
# ---------------------------------------------------------------------------


def test_certified_sign_changes_finds_29_below_100():
    """The headline: 29 *proven* sign changes below T = 100, nothing undecided."""
    out = certified_sign_changes(0, 100, prec_bits=64)
    assert out["changes"] == 29
    assert out["certified"] is True
    assert out["undecided_points"] == []
    assert out["backend"] == BACKEND
    assert out["n_samples"] > 100
    assert out["wall_seconds"] >= 0


def test_certified_sign_changes_matches_the_known_ordinate_count_lower_down():
    # γ_1..γ_3 = 14.134…, 21.022…, 25.010… — three zeros below 30.
    out = certified_sign_changes(0, 30, prec_bits=64)
    assert out["changes"] == 3 and out["certified"]


@pytest.mark.skipif(not HAVE_FLINT, reason="mpmath.iv leg is exercised on a shorter range")
def test_certified_sign_changes_agrees_across_backends():
    a = certified_sign_changes(0, 30, n_samples=151, prec_bits=64, backend="python-flint")
    b = certified_sign_changes(0, 30, n_samples=151, prec_bits=64, backend="mpmath.iv")
    assert a["changes"] == b["changes"] == 3
    assert a["certified"] and b["certified"]


def test_absurdly_low_precision_produces_undecided_points():
    """The failure mode must be *safe*: refuse, do not guess.

    At 2 bits the enclosure of Z(t) is far too wide to exclude 0 anywhere, so
    every sample is undecided, the certificate is withheld, and the reported
    change count collapses — it never invents a proven sign.
    """
    out = certified_sign_changes(0, 100, n_samples=200, prec_bits=2, max_escalations=0)
    assert out["certified"] is False
    assert len(out["undecided_points"]) >= 190
    assert out["changes"] == 0

    # 8 bits: some points decide, most do not — still not certified, and the
    # count is a genuine lower bound (never above the truth).
    mid = certified_sign_changes(0, 100, n_samples=200, prec_bits=8, max_escalations=0)
    assert mid["certified"] is False
    assert mid["undecided_points"]
    assert 0 <= mid["changes"] <= 29

    # 64 bits on the same grid: fully certified.
    good = certified_sign_changes(0, 100, n_samples=200, prec_bits=64, max_escalations=0)
    assert good["certified"] is True
    assert good["undecided_points"] == []
    assert good["changes"] == 29


def test_undecided_points_are_reported_as_real_abscissae():
    out = certified_sign_changes(0, 50, n_samples=40, prec_bits=2, max_escalations=0)
    assert out["undecided_points"]
    for t in out["undecided_points"]:
        assert isinstance(t, float) and 0.0 <= t <= 50.0


def test_coarse_grids_undercount_but_never_overcount():
    """The docstring's load-bearing claim: the count is a rigorous *lower* bound.

    A sign-change scan can miss a pair of zeros inside one cell; it can never
    manufacture one, because every counted change sits between two *proven*
    signs and Z is continuous.  So on any grid the count must be ≤ N(100) = 29,
    and it must be non-decreasing as the grid is refined until it saturates.
    Measured: 7, 17, 29, 29, 29, 29 at 20/37/61/90/151/400 samples.

    Phrased the house way: no violation of ``changes ≤ N(T)`` was found in this
    range — that is a statement about the scan, not about RH.
    """
    counts = []
    for n in (20, 37, 61, 90, 151, 400):
        out = certified_sign_changes(0, 100, n_samples=n, prec_bits=64)
        assert out["certified"] is True
        assert out["changes"] <= 29, (n, out["changes"])
        counts.append(out["changes"])
    assert counts == sorted(counts), counts
    assert counts[0] < 29, "a 20-point grid over (0,100) cannot resolve 29 zeros"
    assert counts[-1] == 29, counts


def test_empty_and_degenerate_ranges():
    out = certified_sign_changes(10, 10)
    assert out["changes"] == 0 and out["certified"] and out["n_samples"] == 0
    out = certified_sign_changes(30, 10)
    assert out["changes"] == 0 and out["certified"]


# ---------------------------------------------------------------------------
# certified N(T)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("T,expected", [(100.0, 29), (300.0, 138), (1000.0, 649)])
def test_certified_zero_count(T, expected):
    """N(T) certified, and the enclosure pinned at the width actually achieved.

    Measured widths of the N(T) enclosure at the default 192 bits —
    python-flint 6.5e-56 / 2.1e-55 / 1.1e-54 and mpmath.iv 1.3e-54 / 1.6e-52 /
    1.8e-51 at T = 100 / 300 / 1000.  The assertion is ``< 1e-46``: five decades
    of headroom over the worst measured value, and forty-six decades tighter
    than the "enclosure contains a unique integer" requirement that actually
    certifies the count — so a regression that widened the enclosure would fail
    here long before it could produce a wrong answer.
    """
    out = certified_zero_count(T)
    assert out["N_T"] == expected
    assert out["certified"] is True
    assert out["uncertified_steps"] == []
    lo, hi = out["N_T_enclosure"]
    assert lo <= expected <= hi
    with mp.workdps(60):
        width = hi - lo
        assert width > 0, "a genuine ball, not a point masquerading as one"
        assert width < mp.mpf("1e-46"), mp.nstr(width, 6)


def test_certified_zero_count_S_matches_mpmath_backlunds():
    """S(T) is enclosed; mpmath's ``backlunds`` (non-rigorous) must land inside."""
    with mp.workdps(70):
        for T in (100.0, 300.0, 1000.0):
            out = certified_zero_count(T)
            s_lo, s_hi = out["S_T_enclosure"]
            assert s_lo <= mp.backlunds(mp.mpf(T)) <= s_hi
            th_lo, th_hi = out["theta_enclosure"]
            assert th_lo <= mp.siegeltheta(mp.mpf(T)) <= th_hi


@pytest.mark.skipif(not HAVE_FLINT, reason="requires Arb's zeta_nzeros")
def test_certified_zero_count_matches_arb_turing_method():
    """Cross-check against Arb's own rigorous zero count (Turing's method).

    Two rigorous routes to the same integer: the argument-principle contour
    implemented here, and Arb's ``acb_dirichlet_zeta_nzeros``.
    """
    for T in (100.0, 300.0, 1000.0):
        out = certified_zero_count(T)
        assert out["cross_checks"]["arb_zeta_nzeros"] == out["N_T"]
        assert out["cross_checks"]["arb_zeta_nzeros_rigorous"] is True
        assert out["cross_checks"]["mpmath_nzeros"] == out["N_T"]
        assert out["cross_checks"]["mpmath_rigorous"] is False


@pytest.mark.skipif(not HAVE_FLINT, reason="needs both backends installed")
def test_certified_zero_count_agrees_across_backends():
    a = certified_zero_count(100.0, backend="python-flint")
    b = certified_zero_count(100.0, backend="mpmath.iv")
    assert a["N_T"] == b["N_T"] == 29
    assert a["certified"] and b["certified"]
    assert a["S_T_enclosure"][0] <= b["S_T_enclosure"][1]
    assert b["S_T_enclosure"][0] <= a["S_T_enclosure"][1]


def test_certified_zero_count_below_the_first_zero_and_at_zero():
    assert certified_zero_count(10.0)["N_T"] == 0
    out = certified_zero_count(0)
    assert out["N_T"] == 0 and out["certified"]


def test_certified_zero_count_reports_failure_rather_than_faking_it():
    """Starved of segments, it must say so — not return a number anyway."""
    out = certified_zero_count(100.0, max_segments=1)
    assert out["certified"] is False
    assert out["N_T"] is None
    assert any("horizontal leg" in s for s in out["uncertified_steps"])


def test_certified_zero_count_agrees_with_the_floating_point_N_of_T():
    from zeta.zeros import N_of_T

    for T in (100.0, 300.0, 1000.0):
        assert certified_zero_count(T)["N_T"] == N_of_T(T)


def test_certified_zero_count_brackets_the_zetazero_ordinates():
    """A third, wholly independent check on N(T): mpmath's ``zetazero`` table.

    Neither the argument principle implemented here nor Turing's method is
    involved: if N(T) = n then the n-th ordinate is below T and the (n+1)-st is
    above it.  (mpmath's ``zetazero`` is itself non-rigorous — this is a
    cross-check, not a second proof.)
    """
    with mp.workdps(30):
        for T, n in [(100.0, 29), (300.0, 138), (1000.0, 649)]:
            assert certified_zero_count(T)["N_T"] == n
            assert mp.im(mp.zetazero(n)) < T < mp.im(mp.zetazero(n + 1))


def test_certified_zero_count_reports_a_wide_enclosure_instead_of_enumerating_it(
    monkeypatch,
):
    """A useless-but-valid enclosure must fail *fast*, not be enumerated.

    Counting the integers in [lo, hi] by listing them is O(hi − lo); a low
    precision at a large height can easily make that 10¹² entries, which would
    look like a hang instead of the honest answer "not certified".  The count is
    therefore arithmetic.  Here θ(T) is replaced by a ball 2·10¹² wide and the
    call has to come back promptly with ``certified=False``.
    """
    adapter = rigor._pick(None)
    monkeypatch.setattr(
        adapter,
        "rs_theta",
        classmethod(lambda cls, lo, hi, prec: (mp.mpf("-1e12"), mp.mpf("1e12"))),
    )
    started = time.time()
    out = certified_zero_count(100.0, cross_check=False)
    assert time.time() - started < 20.0, "the candidate scan is enumerating"
    assert out["N_T"] is None and out["certified"] is False
    assert any("contains" in s and "integers" in s for s in out["uncertified_steps"])


def test_certified_zero_count_survives_an_unbounded_enclosure(monkeypatch):
    """An infinite ball is a true enclosure that decides nothing — say so.

    ``[-inf, +inf]`` is what a backend returns when it cannot bound a step at
    all.  The correct response is ``certified=False``, not an exception.
    """
    adapter = rigor._pick(None)
    monkeypatch.setattr(
        adapter,
        "rs_theta",
        classmethod(lambda cls, lo, hi, prec: (mp.mpf("-inf"), mp.mpf("inf"))),
    )
    out = certified_zero_count(100.0, cross_check=False)
    assert out["N_T"] is None and out["certified"] is False
    assert any("unbounded" in s for s in out["uncertified_steps"])


# ---------------------------------------------------------------------------
# the flagship
# ---------------------------------------------------------------------------


def test_verify_rh_certified_at_100(tmp_path, monkeypatch):
    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    out = verify_rh_certified(100.0, compare_floating=False)
    assert out["T"] == 100.0
    assert out["N_T"] == 29
    assert out["certified_sign_changes"] == 29
    assert out["all_on_line"] is True
    assert out["certified"] is True
    assert out["uncertified_steps"] == []
    assert out["undecided_points"] == []
    assert out["backend"] == BACKEND
    assert out["wall_seconds"] > 0
    assert out["from_cache"] is False


def test_verify_rh_certified_caches_and_replays(tmp_path, monkeypatch):
    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    first = verify_rh_certified(50.0, compare_floating=False)
    files = os.listdir(tmp_path)
    assert any(f.startswith("rigor_verify_50") for f in files), files
    second = verify_rh_certified(50.0, compare_floating=False)
    assert second["from_cache"] is True
    assert second["N_T"] == first["N_T"] == 10
    assert second["certified_sign_changes"] == first["certified_sign_changes"]


def test_cache_never_replays_a_certificate_for_different_settings(tmp_path, monkeypatch):
    """A certificate is only reusable for the *exact* request that produced it.

    ``max_escalations`` is the dangerous one: at 8 bits, twelve escalations
    certify T = 30 and zero escalations leave 74 samples undecided.  If the two
    runs share a cache file the second one inherits ``certified: True`` for a
    computation that was never performed — a manufactured certificate, which is
    the one failure this module must not have.  Both directions are checked,
    together with the file's recorded parameters being re-verified on load
    (a renamed file must be rejected, not trusted).
    """
    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    kw = dict(T=30.0, prec_bits=8, n_samples=200, compare_floating=False)

    generous = verify_rh_certified(max_escalations=12, **kw)
    assert generous["certified"] is True and generous["from_cache"] is False

    stingy = verify_rh_certified(max_escalations=0, **kw)
    assert stingy["from_cache"] is False, "the 12-escalation file was replayed"
    assert stingy["certified"] is False
    assert stingy["undecided_points"]

    truth = verify_rh_certified(max_escalations=0, cache=False, **kw)
    assert stingy["certified"] == truth["certified"]
    assert stingy["certified_sign_changes"] == truth["certified_sign_changes"]
    assert len(stingy["undecided_points"]) == len(truth["undecided_points"])

    # each run got its own file, and an identical request does replay
    assert len(os.listdir(tmp_path)) == 2
    assert verify_rh_certified(max_escalations=12, **kw)["from_cache"] is True

    # every parameter that can change the answer is recorded inside the file
    for name in rigor._CACHE_KEYS:
        assert name in generous, name

    # a file whose recorded parameters do not match is rejected, not trusted
    import json

    path = rigor._cache_path(
        rigor._cache_key(30.0, generous["backend"], 8, generous["count_prec_bits"],
                         200, 12, generous["max_samples"])
    )
    blob = json.load(open(path))
    blob["max_escalations"] = 99
    with open(path, "w") as fh:
        json.dump(blob, fh)
    again = verify_rh_certified(max_escalations=12, **kw)
    assert again["from_cache"] is False, "a tampered file was accepted"
    assert again["certified"] is True


@pytest.mark.slow
def test_verify_rh_certified_matches_the_non_rigorous_version(tmp_path, monkeypatch):
    """Both routines must produce the same numbers; only the status differs."""
    from zeta.zeros import verify_rh_up_to

    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    out = verify_rh_certified(100.0, compare_floating=True)
    ref = verify_rh_up_to(100.0)
    assert out["N_T"] == ref["N_T"] == 29
    assert out["certified_sign_changes"] == ref["n_sign_changes"] == 29
    assert out["agrees_with_floating_point"] is True
    assert out["floating_point"]["rigorous"] is False
    assert out["certified"] is True


@pytest.mark.slow
@pytest.mark.skipif(not HAVE_FLINT, reason="needs both backends installed")
def test_verify_rh_certified_on_the_mpmath_iv_backend(tmp_path, monkeypatch):
    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    out = verify_rh_certified(30.0, backend="mpmath.iv", compare_floating=False)
    assert out["backend"] == "mpmath.iv"
    assert out["N_T"] == 3
    assert out["certified_sign_changes"] == 3
    assert out["certified"] is True


def test_verify_rh_certified_withholds_the_certificate_at_low_precision(
    tmp_path, monkeypatch
):
    monkeypatch.setattr(rigor, "DATA_DIR", str(tmp_path))
    out = verify_rh_certified(
        50.0,
        prec_bits=4,
        max_escalations=0,
        n_samples=120,
        max_samples=120,
        compare_floating=False,
        cache=False,
    )
    assert out["certified"] is False
    assert out["undecided_points"]
    assert any("undecided" in s for s in out["uncertified_steps"])


# ---------------------------------------------------------------------------
# the cost curve
# ---------------------------------------------------------------------------


def test_enclosure_width_report_shape_and_monotonicity():
    bits = [32, 64, 128, 256]
    rows = enclosure_width_report([20.0, 100.0], bits)
    assert len(rows) == 2 * len(bits)
    assert [r["t"] for r in rows] == [20.0] * 4 + [100.0] * 4
    for chunk in (rows[:4], rows[4:]):
        assert [r["prec_bits"] for r in chunk] == bits
        widths = [r["width"] for r in chunk]
        assert all(widths[i + 1] < widths[i] for i in range(len(widths) - 1))
        digits = [r["proven_digits"] for r in chunk]
        assert all(digits[i + 1] > digits[i] for i in range(len(digits) - 1))
        assert all(r["sign_proven"] for r in chunk)
        assert all(r["lo"] <= r["hi"] for r in chunk)
        assert all(r["backend"] == BACKEND and r["error"] is None for r in chunk)


def test_enclosure_width_costs_about_one_digit_per_3_3_bits():
    """log₁₀(width) falls by ≈ 1 per 3.32 bits — the price of a proven digit.

    Measured on the Arb backend at t = 100: 8.16 proven digits at 32 bits,
    17.95 at 64, 37.21 at 128, 75.69 at 256 (≈ 0.30 digits per bit, i.e.
    log₁₀2 = 0.301).
    """
    rows = enclosure_width_report([100.0], [64, 256])
    gained = rows[1]["proven_digits"] - rows[0]["proven_digits"]
    expected = (256 - 64) * math.log10(2)
    assert abs(gained - expected) < 3.0, (gained, expected)


@pytest.mark.parametrize(
    "backend,widths",
    [
        pytest.param("python-flint", [-7.7, -17.5, -36.8, -75.3], id="python-flint"),
        pytest.param("mpmath.iv", [-5.6, -15.3, -34.5, -70.7], id="mpmath.iv"),
    ],
)
def test_measured_enclosure_widths_match_the_docstring_table(backend, widths):
    """Pin the width table quoted in ``enclose_Z``'s docstring.

    Measured log₁₀(width) of the Z(100) enclosure: python-flint −7.73, −17.52,
    −36.78, −75.26 at 32/64/128/256 bits; mpmath.iv −5.61, −15.25, −34.51,
    −70.75.  The assertion allows half a decade of slack in the *tighter*
    direction only — a suddenly wider enclosure is a regression worth failing on.
    """
    if backend not in available_backends():
        pytest.skip(f"{backend} not installed")
    rows = enclosure_width_report([100.0], [32, 64, 128, 256], backend=backend)
    for row, claimed in zip(rows, widths):
        got = float(row["width_log10"])
        assert claimed - 0.5 <= got <= claimed + 0.5, (row["prec_bits"], got, claimed)


def test_enclosure_width_report_low_precision_cannot_prove_the_sign():
    rows = enclosure_width_report([100.0], [2, 4])
    assert not any(r["sign_proven"] for r in rows)


# ---------------------------------------------------------------------------
# hygiene
# ---------------------------------------------------------------------------


def test_no_global_precision_state_leaks():
    """House rule: nothing may leave mpmath's or Arb's global precision moved."""
    before_mp, before_iv = mp.dps, iv.prec
    flint_before = None
    if HAVE_FLINT:
        import flint

        flint_before = flint.ctx.prec

    enclose_Z(20.0, 300)
    proven_sign(20.0, prec_bits=17)
    certified_sign_changes(0, 20, n_samples=8, prec_bits=64)
    certified_zero_count(50.0)
    enclosure_width_report([20.0], [64])
    for backend in available_backends():
        enclose_Z(20.0, 128, backend=backend)

    assert mp.dps == before_mp
    assert iv.prec == before_iv
    if HAVE_FLINT:
        import flint

        assert flint.ctx.prec == flint_before


def test_public_api_is_exported():
    for name in rigor.__all__:
        assert hasattr(rigor, name), name


def test_importing_rigor_does_not_pull_in_matplotlib():
    """House rule: only ``zeta.plots`` may import matplotlib."""
    code = (
        "import sys, zeta.rigor; "
        "assert 'matplotlib' not in sys.modules, sorted(sys.modules)"
    )
    subprocess.run([sys.executable, "-c", code], check=True, cwd=os.path.dirname(
        os.path.dirname(os.path.abspath(rigor.__file__))
    ))


def test_data_dir_is_derived_from_file_not_hardcoded():
    """No absolute home-directory path may appear in either committed file.

    The forbidden prefixes are assembled at run time rather than written out,
    so that this test does not trip over its own source text.
    """
    forbidden = ["/" + p + "/" for p in ("Users", "home", "root")]
    for path in (
        os.path.join(os.path.dirname(rigor.__file__), "rigor.py"),
        os.path.abspath(__file__),
    ):
        with open(path) as fh:
            src = fh.read()
        for bad in forbidden:
            assert bad not in src, (path, bad)
        if path.endswith(os.sep + "rigor.py"):
            assert "__file__" in src
