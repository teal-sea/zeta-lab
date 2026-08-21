"""PARI/GP as a second oracle.

Why this file exists
--------------------
Almost every numerical claim in this laboratory is cross-checked against
mpmath: ``tests/test_zeros.py`` hunts a zero by sign change and then asserts it
agrees with ``mp.zetazero``, ``tests/test_core.py`` checks Euler-Maclaurin
against ``mp.zeta``, and so on.  That is the right habit, but it leaves one
structural weakness: **mpmath is the only oracle**.  A defect shared between
our code and mpmath, or a defect in mpmath alone, is invisible to a suite whose
every reference value comes from the same library.

PARI/GP is an independent implementation.  It is a C library written by a
different community over roughly forty years, with different algorithms
(``lfunzeros`` locates zeros through the L-function machinery rather than by
Riemann-Siegel sign changes; ``ellap`` counts points by Shanks-Mestre/SEA
rather than by a Legendre-symbol table), and it shares no code with mpmath.
Agreement between the two is therefore evidence about the mathematics; a
disagreement is a defect in one of three places, and that is worth knowing.

What this file is not
---------------------
It is not a certificate.  PARI computes with floating point at a requested
precision, exactly as mpmath does, so a check here raises a claim's confidence
without moving it up the certainty ladder.  The rung-2 machinery is
``zeta/rigor.py``; the one test below that touches it
(:func:`test_arb_enclosure_contains_pari_value`) asks only whether PARI's value
falls inside an enclosure Arb already proved, which is a check *of the oracle
against the certificate*, not a new certificate.

One honest caveat about Hardy's Z.  PARI exposes ``lfunhardy``, but its
normalisation carries an internal factor (empirically Z_pari/Z -> 1.7437585...
rather than 1), so this file does not use it.  Instead Z is rebuilt from PARI's
own ``zeta`` and ``lngamma`` through the defining identity
``Z(t) = e^{i*theta(t)} * zeta(1/2 + i*t)``.  That is the same *identity*
``zeta/rigor.py`` uses, so the two agree on mathematics by construction; what
is genuinely independent is every transcendental function underneath it.  The
zero locations, the zero counts, the point counts and the special values below
carry no such caveat.

Skipped entirely when ``cypari2`` is not installed, in the same spirit as the
``HAVE_FLINT`` guards in ``tests/test_rigor.py``: an absent optional oracle
must never read as a passing cross-check.
"""

from __future__ import annotations

import math

import mpmath as mp
import pytest

try:  # pragma: no cover - depends on the environment
    from cypari2 import Pari

    _pari = Pari()
    _pari.set_real_precision(60)
    HAVE_PARI = True
    PARI_VERSION = tuple(_pari.version())
except Exception:  # pragma: no cover - cypari2 absent or broken
    _pari = None
    HAVE_PARI = False
    PARI_VERSION = ()

pytestmark = pytest.mark.skipif(
    not HAVE_PARI,
    reason="needs cypari2 (the PARI/GP oracle) installed",
)

# PARI's internal working precision, in bits, for every call below.  Generous:
# the point of an oracle is that it is not the thing under test, so it is
# cheaper to over-compute than to reason about how much precision it needs.
PREC = 256

# Reference values computed at this many decimal digits.
DPS = 40

# Decimal digits PARI is asked to *print*, and therefore the accuracy of every
# oracle value once it has been through a string.  Deliberately well above
# ``DPS``: an Arb enclosure at 192 bits can be narrower than 1e-57, and an
# oracle value coarser than the interval it is being tested against fails a
# correct containment check purely on rounding.
ORACLE_DPS = 60


# --------------------------------------------------------------------------
# thin adapters: PARI -> mpmath types
# --------------------------------------------------------------------------


def _mpf(value) -> mp.mpf:
    """A PARI real as an mpmath ``mpf`` at the current working precision.

    PARI prints small magnitudes as ``1.234 E-59`` -- with a space before the
    exponent, which no float parser accepts -- so the spaces come out first.

    Parsed at :data:`ORACLE_DPS` rather than at the ambient precision, so an
    oracle value never silently inherits a caller's ``workdps`` and arrives
    blunter than whatever it is about to be compared against.
    """
    with mp.workdps(ORACLE_DPS):
        return +mp.mpf(str(value).replace(" ", ""))


def _mpc(value) -> mp.mpc:
    """A PARI complex as an mpmath ``mpc``, at :data:`ORACLE_DPS`.

    The ``workdps`` matters: ``mp.mpc`` rounds its arguments to the *ambient*
    precision, so building the complex outside this block would quietly undo
    the care :func:`_mpf` took.
    """
    with mp.workdps(ORACLE_DPS):
        return mp.mpc(_mpf(_pari.real(value)), _mpf(_pari.imag(value)))


def pari_zeta(s):
    """zeta(s) computed by PARI, for real or complex ``s``, as an mpmath number."""
    if mp.im(s) == 0:
        return _mpf(_pari.zeta(_pari(mp.nstr(mp.mpf(mp.re(s)), DPS + 5)), precision=PREC))
    expr = "(%s) + (%s)*I" % (
        mp.nstr(mp.mpf(mp.re(s)), DPS + 5),
        mp.nstr(mp.mpf(mp.im(s)), DPS + 5),
    )
    return _mpc(_pari.zeta(_pari(expr), precision=PREC))


def pari_hardy_Z(t) -> mp.mpf:
    """Hardy's Z(t) rebuilt from PARI's own ``zeta`` and ``lngamma``.

    Z(t) = e^{i*theta(t)} * zeta(1/2 + i*t),
    theta(t) = Im log Gamma(1/4 + i*t/2) - (t/2) log pi.

    Deliberately not ``lfunhardy``: see the module docstring.  The imaginary
    part of the product must vanish (Z is real for real t) and is asserted to,
    which doubles as a check that the identity was applied correctly.
    """
    with mp.workdps(ORACLE_DPS):
        ts = mp.nstr(mp.mpf(t), ORACLE_DPS)
    theta = _pari.imag(
        _pari.lngamma(_pari("1/4 + (%s)/2*I" % ts), precision=PREC)
    ) - _pari(ts) / 2 * _pari.log(_pari.pi(precision=PREC), precision=PREC)
    z = _pari.exp(_pari.complex(_pari(0), theta), precision=PREC) * _pari.zeta(
        _pari("1/2 + (%s)*I" % ts), precision=PREC
    )
    with mp.workdps(ORACLE_DPS):
        value = _mpc(z)
        assert abs(value.imag) < mp.mpf(10) ** (-DPS), (
            f"Z({t}) must be real; PARI route left Im = {value.imag}"
        )
        return +value.real


def pari_zeros(t0: float, t1: float) -> list[mp.mpf]:
    """Ordinates of the zeros of zeta with ``t0 < gamma < t1``, located by PARI.

    ``lfunzeros`` searches the critical line through the generic L-function
    machinery, which is a different algorithm from this repository's
    Riemann-Siegel sign hunt and from mpmath's ``zetazero``.
    """
    raw = _pari.lfunzeros(1, [t0, t1], precision=PREC)
    return [_mpf(g) for g in raw]


# --------------------------------------------------------------------------
# the oracle itself
# --------------------------------------------------------------------------


def test_pari_oracle_is_live():
    """Fail loudly rather than skip silently once cypari2 imports at all."""
    assert PARI_VERSION >= (2, 15), f"PARI too old for lfun*: {PARI_VERSION}"
    assert _mpf(_pari.zeta(2, precision=PREC)) != 0


# --------------------------------------------------------------------------
# zeta itself
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "s",
    ["2", "4", "6", "3", "0", "-1", "-3", "0.5", "1.5", "10"],
)
def test_zeta_real_axis_matches_pari(s):
    """zeta on the real axis: our Euler-Maclaurin against PARI's zeta."""
    from zeta.core import zeta

    with mp.workdps(DPS):
        s_val = mp.mpf(s)
        ours = mp.mpf(zeta(s_val, dps=DPS))
        theirs = pari_zeta(s_val)
        assert mp.almosteq(ours, theirs, abs_eps=mp.mpf(10) ** (-DPS + 5)), (
            f"zeta({s}): ours={ours} pari={theirs}"
        )


def test_zeta_ground_truth_against_pari():
    """The three constants CLAUDE.md pins, re-derived by the second oracle."""
    with mp.workdps(DPS):
        assert mp.almosteq(pari_zeta(mp.mpf(2)), mp.pi**2 / 6, abs_eps=mp.mpf(10) ** -35)
        assert mp.almosteq(pari_zeta(mp.mpf(0)), mp.mpf(-1) / 2, abs_eps=mp.mpf(10) ** -35)
        assert mp.almosteq(pari_zeta(mp.mpf(-1)), mp.mpf(-1) / 12, abs_eps=mp.mpf(10) ** -35)


@pytest.mark.parametrize("t", ["14.0", "25.5", "100.0", "1000.0"])
def test_zeta_critical_line_matches_pari(t):
    """zeta(1/2 + i t): our value against PARI's, real and imaginary parts."""
    from zeta.core import zeta

    with mp.workdps(DPS):
        s = mp.mpc(mp.mpf(1) / 2, mp.mpf(t))
        ours = mp.mpc(zeta(s, dps=DPS))
        theirs = pari_zeta(s)
        assert mp.almosteq(ours, theirs, abs_eps=mp.mpf(10) ** (-DPS + 8)), (
            f"zeta(1/2+{t}i): ours={ours} pari={theirs}"
        )


def test_alternate_zeta_routes_agree_with_pari():
    """The repo's *other* two routes to zeta, checked against the second oracle.

    ``zeta_via_eta`` (alternating series) and ``zeta_euler_maclaurin`` are
    independent of each other inside this repository; PARI makes a third.
    """
    from zeta.core import zeta_via_eta, zeta_euler_maclaurin

    with mp.workdps(DPS):
        for s in [mp.mpf(2), mp.mpf("1.5"), mp.mpc(mp.mpf(1) / 2, 14), mp.mpc(2, 3)]:
            theirs = pari_zeta(s)
            eta_route = mp.mpc(zeta_via_eta(s, dps=DPS))
            em_route = mp.mpc(zeta_euler_maclaurin(s, N=40, M=20, dps=DPS))
            assert mp.almosteq(eta_route, theirs, abs_eps=mp.mpf(10) ** (-DPS + 10)), (
                f"zeta_via_eta({s}): {eta_route} vs pari {theirs}"
            )
            assert mp.almosteq(em_route, theirs, abs_eps=mp.mpf(10) ** (-DPS + 10)), (
                f"zeta_euler_maclaurin({s}): {em_route} vs pari {theirs}"
            )


def test_functional_equation_corroborated_by_pari():
    """Our measured defect is ~0, and PARI's own FE self-check agrees.

    ``lfuncheckfeq`` returns roughly log2 of the residual error in the
    functional equation as PARI has it set up; a strongly negative number means
    the equation holds to near full precision.  That is a check of PARI, but it
    also confirms the two libraries mean the same functional equation.
    """
    from zeta.core import functional_equation_defect

    with mp.workdps(DPS):
        for s in [mp.mpc(2, 3), mp.mpc("0.3", 5), mp.mpc(mp.mpf(1) / 2, 14)]:
            assert abs(functional_equation_defect(s, dps=DPS)) < mp.mpf(10) ** (-DPS + 8)

    assert int(_pari.lfuncheckfeq(1, precision=PREC)) < -40


# --------------------------------------------------------------------------
# Hardy's Z and the zeros
# --------------------------------------------------------------------------


@pytest.mark.parametrize("t", ["14.0", "20.0", "50.0", "100.0", "1000.0"])
def test_hardy_Z_matches_pari(t):
    """Z(t) from this repo against Z(t) rebuilt on PARI's transcendentals."""
    from zeta.core import Z

    with mp.workdps(DPS):
        ours = mp.mpf(Z(mp.mpf(t), dps=DPS))
    theirs = pari_hardy_Z(t)
    with mp.workdps(DPS):
        assert mp.almosteq(ours, theirs, abs_eps=mp.mpf(10) ** (-DPS + 8)), (
            f"Z({t}): ours={ours} pari={theirs}"
        )


def test_first_zeros_match_pari_lfunzeros():
    """The first twenty ordinates, ours vs PARI's L-function zero search."""
    from zeta.zeros import first_n_zeros

    n = 20
    ours = first_n_zeros(n, dps=30)
    theirs = pari_zeros(0, 80)
    assert len(theirs) >= n, f"PARI found only {len(theirs)} zeros below 80"

    with mp.workdps(30):
        for k, (a, b) in enumerate(zip(ours, theirs[:n]), start=1):
            assert mp.almosteq(mp.mpf(a), b, abs_eps=mp.mpf(10) ** -20), (
                f"gamma_{k}: ours={a} pari={b}"
            )


def test_pinned_ground_truth_ordinates_against_pari():
    """gamma_1, gamma_2, gamma_3 as CLAUDE.md pins them, from the second oracle."""
    expected = [
        "14.134725141734694",
        "21.022039638771555",
        "25.010857580145689",
    ]
    theirs = pari_zeros(0, 30)
    assert len(theirs) == 3
    with mp.workdps(ORACLE_DPS):
        for want, got in zip(expected, theirs):
            assert abs(mp.mpf(want) - got) < mp.mpf("1e-15"), f"{want} vs {got}"


def test_sign_change_hunt_finds_exactly_the_pari_zeros():
    """Our Riemann-Siegel sign hunt on a window, against PARI's zero search.

    Different algorithms entirely: we bracket sign changes of Z and bisect;
    PARI works from the L-function's approximate functional equation.  They
    must return the same set, with the same cardinality -- a missed zero here
    would be a defect the mpmath oracle cannot see, because our hunt and
    mpmath's ``zetazero`` are only ever compared zero-by-zero, never as sets.
    """
    from zeta.zeros import zeros_by_sign_change

    t0, t1 = 100.0, 150.0
    ours = zeros_by_sign_change(t0, t1, dps=25)
    theirs = pari_zeros(t0, t1)

    assert len(ours) == len(theirs), (
        f"cardinality mismatch on ({t0}, {t1}): ours={len(ours)} pari={len(theirs)}"
    )
    with mp.workdps(25):
        for a, b in zip(ours, theirs):
            assert mp.almosteq(mp.mpf(a), b, abs_eps=mp.mpf("1e-15")), f"{a} vs {b}"


@pytest.mark.parametrize("T", [100, 200])
def test_N_of_T_matches_pari_zero_count(T):
    """N(T) by the argument principle, against PARI's count of found zeros.

    These agree only if every zero below T is on the critical line *and* our
    contour integral is right; the second is what is under test, since the
    first is verified independently up to far greater heights.
    """
    from zeta.zeros import N_of_T

    ours = N_of_T(T, dps=25)
    theirs = len(pari_zeros(0, T))
    assert ours == theirs, f"N({T}): ours={ours} pari={theirs}"


def test_N_of_100_is_29():
    """The number CLAUDE.md pins, from the second oracle."""
    assert len(pari_zeros(0, 100)) == 29


# --------------------------------------------------------------------------
# the certified arm: does the oracle land inside the proof?
# --------------------------------------------------------------------------


# Every t below is an exact binary fraction.  ``enclose_Z`` encloses Z at
# precisely the dyadic rational its argument really is, so a t like 101.7 --
# which no binary float represents -- would have Arb and PARI evaluating at
# points ~1e-16 apart and the containment check failing on that alone.
@pytest.mark.parametrize("t", ["14.5", "23.0", "101.75", "500.25"])
def test_arb_enclosure_contains_pari_value(t):
    """Arb proved Z(t) lies in [lo, hi]; PARI's Z(t) had better be in there.

    This does not certify anything PARI computed.  It is the other direction: a
    rigorous enclosure is a theorem about the true value, so an independent
    library landing outside it would mean the enclosure is wrong -- a critical
    defect in the one module allowed to say "certified".
    """
    from zeta.rigor import enclose_Z

    lo, hi = enclose_Z(mp.mpf(t), prec_bits=192)
    theirs = pari_hardy_Z(t)
    assert lo <= theirs <= hi, f"PARI Z({t})={theirs} outside proven [{lo}, {hi}]"


@pytest.mark.parametrize("t", ["14.5", "23.0", "101.75"])
def test_proven_sign_matches_pari_sign(t):
    """A *proven* sign must match the sign the oracle observes."""
    from zeta.rigor import proven_sign

    ours = proven_sign(mp.mpf(t), prec_bits=96)
    theirs = pari_hardy_Z(t)
    assert ours != 0, f"sign of Z({t}) should be decidable at 96 bits"
    assert ours == (1 if theirs > 0 else -1), (
        f"proven sign {ours} contradicts PARI value {theirs}"
    )


# --------------------------------------------------------------------------
# the prime side
# --------------------------------------------------------------------------


@pytest.mark.parametrize("x", [10.0, 100.0, 1000.0, 10000.0])
def test_logarithmic_integral_matches_pari(x):
    """li(x) against PARI's exponential integral: li(x) = -E_1(-log x).

    PARI's ``eint1`` returns a complex value for negative argument (the
    principal value picks up an i*pi); the real part is li.
    """
    from zeta.explicit import li

    ours = li(x)
    raw = -_pari.eint1(-_pari.log(_pari(str(x)), precision=PREC), precision=PREC)
    theirs = float(_mpf(_pari.real(raw)))
    assert ours == pytest.approx(theirs, rel=1e-12), f"li({x}): {ours} vs {theirs}"


@pytest.mark.parametrize("x", [10, 100, 1000, 10000, 100000])
def test_prime_counting_matches_pari(x):
    """pi(x) and Chebyshev's theta(x), against PARI's own prime machinery."""
    from zeta.explicit import pi_true, theta_cheb

    assert pi_true(x) == int(_pari.primepi(x))

    primes = _pari.primes([2, x])
    theirs = float(sum(math.log(int(p)) for p in primes))
    assert theta_cheb(x) == pytest.approx(theirs, rel=1e-12)


# --------------------------------------------------------------------------
# the RH that is a theorem: curves over finite fields
# --------------------------------------------------------------------------

CURVES = [
    (1, 1, 101),
    (0, 1, 103),
    (2, 3, 1009),
    (-1, 0, 1013),
    (3, 5, 10007),
]


@pytest.mark.parametrize("a,b,p", CURVES)
def test_point_counts_match_pari_ellcard(a, b, p):
    """#E(F_p) and the Frobenius trace, against PARI's ``ellcard``/``ellap``.

    Wholly different algorithms: this repository sums Legendre symbols over
    every x in F_p, PARI uses Shanks-Mestre or SEA.  Same answer or somebody is
    wrong.
    """
    from zeta.finitefield import count_points, trace_of_frobenius

    E = _pari.ellinit([0, 0, 0, a, b], p)
    assert count_points(a, b, p) == int(_pari.ellcard(E))
    assert trace_of_frobenius(a, b, p) == int(_pari.ellap(E))


@pytest.mark.parametrize("a,b,p", CURVES[:4])
def test_extension_point_counts_match_pari(a, b, p):
    """#E(F_{p^n}) from Frobenius eigenvalues, against PARI over F_{p^n}.

    The Lefschetz formula N_n = p^n + 1 - (alpha^n + alphabar^n) is the whole
    content of the Weil conjectures for a curve; PARI counting directly in the
    extension field is the check that we applied it correctly.
    """
    from zeta.finitefield import point_counts_over_extensions

    n_max = 4
    ours = point_counts_over_extensions(a, b, p, n_max)
    g = _pari.ffgen(p, "x")
    for n in range(1, n_max + 1):
        gn = _pari.ffgen(_pari.ffinit(p, n, "x"), "x") if n > 1 else g
        En = _pari.ellinit([0, 0, 0, a * gn**0, b * gn**0], gn)
        assert ours[n - 1] == int(_pari.ellcard(En)), (
            f"E({a},{b})/F_{{{p}^{n}}}: ours={ours[n - 1]} pari={_pari.ellcard(En)}"
        )
