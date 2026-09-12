"""Tests for the certified Weil functional, ``rigor.enclose_weil_functional``.

Same philosophy as ``test_rigor.py``: the outputs are proofs, so the tests
are containment statements, not tolerance checks.  Specifically:

* every enclosure must **contain** the value computed independently by
  ``zeta.weil.weil_functional`` (mpmath, no balls, different quadrature);
* ``sign`` must be 1 only when [lo, hi] genuinely excludes 0, and must come
  back 0, not a guess, when the enclosure straddles it;
* enclosures of the same W(h) at different precisions must **overlap**
  (both contain the same true value);
* the archimedean tail lemma |Re ψ(1/4+ir/2) − log π| ≤ log(r+2) + 8 is
  spot-checked in ball arithmetic (the derivation in the docstring is the
  proof; this pins against a transcription error in the constant).

The headline test is ``test_near_tight_gaussian_positivity_proven``: the
Gaussian a = 0.2 member has W ≈ 8.86e-18 emerging from pieces of size ~2,
about 18 digits of cancellation, exactly where floating point can lie, and
its positivity comes back *certified*.

Everything here is flint-only (Arb's certified quadrature has no mpmath.iv
analogue), so the whole module is skipped without python-flint.  That skip is
loud by design: a suite reporting it is not exercising the certified Weil arm.
"""

from __future__ import annotations

from fractions import Fraction

import pytest
from mpmath import mp

from zeta import rigor
from zeta.rigor import (
    available_backends,
    certified_autocorrelation_pair,
    certified_fejer_pair,
    certified_gaussian_pair,
    enclose_weil_functional,
)
from zeta.weil import (
    autocorrelation_pair,
    fejer_pair,
    gaussian_pair,
    weil_functional,
)

HAVE_FLINT = "python-flint" in available_backends()

pytestmark = pytest.mark.skipif(
    not HAVE_FLINT,
    reason="certified Weil positivity is flint-only (Arb certified quadrature)",
)


# ---------------------------------------------------------------------------
# containment against the independent float implementation
# ---------------------------------------------------------------------------


def test_gaussian_enclosure_contains_float_value():
    h, g = certified_gaussian_pair("0.01")
    r = enclose_weil_functional(h, g, prec_bits=128)
    lo, hi = r["W_enclosure"]
    assert r["certified"] and not r["uncertified_steps"]
    assert r["sign"] == 1 and r["positivity_proven"]
    # independent computation: mpmath quadrature, no balls anywhere
    with mp.workdps(30):
        v = weil_functional(*gaussian_pair("0.01"), dps=30)
    # the enclosure is exact about *its* h; the float route carries its own
    # ~10^-30 noise, so containment is asserted with that slack only (and the
    # interval arithmetic must run at high dps, at the ambient 15 the
    # rounding of lo - slack would swamp the slack itself)
    with mp.workdps(40):
        slack = mp.mpf(10) ** -25
        assert lo - slack <= v <= hi + slack
        assert hi - lo < mp.mpf(10) ** -30
    assert r["cross_checks"]["mpmath_rigorous"] is False
    assert r["cross_checks"]["consistent"]


def test_gaussian_pole_term_closed_form():
    # pole = h(i/2) + h(-i/2) = 2 e^{a/4} for the Gaussian pair
    h, g = certified_gaussian_pair("0.04")
    r = enclose_weil_functional(
        h, g, n_max=200, R=40, prec_bits=96, cross_check=False
    )
    plo, phi = r["pieces"]["pole"]
    with mp.workdps(40):
        v = 2 * mp.e ** (mp.mpf("0.04") / 4)
    assert plo <= v <= phi


def test_fejer_certified_positive_and_contains_float():
    h, g = certified_fejer_pair(1)
    r = enclose_weil_functional(h, g, R=4096, prec_bits=96, cross_check=False)
    lo, hi = r["W_enclosure"]
    assert r["certified"] and r["sign"] == 1 and r["positivity_proven"]
    # compact support: the prime sum is exactly finite, cutoff floor(e^2) = 7
    assert r["n_max"] == 7
    assert r["pieces"]["prime_tail_bound"] == 0
    # W(fejér b=1) ≈ 0.0253; the enclosure is honestly wide (arch tail
    # ~1.3e-3 at R=4096) but must still contain the float value
    with mp.workdps(20):
        v = weil_functional(*fejer_pair(1), dps=20)
    assert lo <= v <= hi
    assert lo > mp.mpf("0.02") and hi < mp.mpf("0.03")


@pytest.mark.slow
def test_near_tight_gaussian_positivity_proven():
    # THE headline: a = 0.2, W ≈ 8.86e-18 out of pieces of size ~2 (about
    # 18 digits of cancellation).  Certified positive.
    h, g = certified_gaussian_pair("0.2")
    r = enclose_weil_functional(
        h, g, n_max=20000, prec_bits=256, cross_check=False
    )
    lo, hi = r["W_enclosure"]
    assert r["certified"] and r["sign"] == 1 and r["positivity_proven"]
    assert lo > mp.mpf("8.8e-18") and hi < mp.mpf("8.9e-18")
    # and it brackets the value the float machinery reports at high dps
    with mp.workdps(45):
        v = weil_functional(*gaussian_pair("0.2"), dps=45)
    assert lo <= v <= hi


def test_autocorrelation_certified_positive_and_contains_float():
    # the two-bump h(0) = 0 member the float probes scan: W ≈ 1.45e-10.
    # its g changes sign, so the evaluator must use the symmetric
    # majorant tail (the gaussian one-sided sharpening would be unsound)
    h, g = certified_autocorrelation_pair([1, -1], spacing=2, sigma="0.35")
    r = enclose_weil_functional(h, g, n_max=25000, prec_bits=160, cross_check=False)
    lo, hi = r["W_enclosure"]
    assert r["certified"] and r["sign"] == 1 and r["positivity_proven"]
    assert lo > mp.mpf("1.4e-10") and hi < mp.mpf("1.5e-10")
    with mp.workdps(30):
        v = weil_functional(
            *autocorrelation_pair([1, -1], spacing=2, sigma=0.35), dps=30
        )
    # sigma = 0.35 parses identically on both routes (dyadic float vs the
    # exact 7/20 differ, but _param reads the float at 60 dps and the
    # discrepancy enters far below the containment slack)
    with mp.workdps(40):
        slack = mp.mpf(10) ** -22
        assert lo - slack <= v <= hi + slack
    assert r["family_params"]["coeffs"] == [1.0, -1.0]


def test_autocorrelation_cap_guard():
    # a bump train centred beyond the prime-power cap cannot certify its
    # tail: the evaluator must refuse loudly, not truncate silently
    h, g = certified_autocorrelation_pair([1, 1], spacing=20, sigma="0.35")
    with pytest.raises(ValueError, match="raise n_max"):
        enclose_weil_functional(h, g, R=40, prec_bits=64, cross_check=False)


@pytest.mark.slow
def test_certified_collapse_along_the_gaussian_family():
    # the near-tightness story (zeta.weil.near_tightness_report) with
    # enclosures: W collapses like 2e^{-a*gamma1^2} as h concentrates on
    # the zero-free gap.  Here that is a chain of CERTIFIED strict
    # inequalities W(0.02) > W(0.08) > W(0.2) > 0 spanning sixteen orders
    # of magnitude, and the two-point log-slope lands on -gamma1^2
    # (~-199.79, measured -199.84), the lowest zero speaking through
    # certified arithmetic.
    import math

    rows = []
    for a in ("0.02", "0.08", "0.2"):
        h, g = certified_gaussian_pair(a)
        r = enclose_weil_functional(
            h, g, n_max=20000, prec_bits=192, cross_check=False
        )
        assert r["certified"] and r["sign"] == 1, f"a={a}"
        rows.append(r["W_enclosure"])
    # enclosure-to-enclosure comparisons: each lo beats the next hi
    assert rows[0][0] > rows[1][1] > 0
    assert rows[1][0] > rows[2][1] > 0
    slope = (math.log(float(rows[2][0])) - math.log(float(rows[0][1]))) / (
        0.2 - 0.02
    )
    assert -202 < slope < -197  # gamma1^2 = 199.79...


# ---------------------------------------------------------------------------
# the safe failure mode: undecided is 0, never a guess
# ---------------------------------------------------------------------------


def test_undecided_sign_is_zero_not_a_guess():
    # at 48 bits the enclosure width (~1e-12) dwarfs W ≈ 8.86e-18: the
    # enclosure is still TRUE (certified), it just decides nothing
    h, g = certified_gaussian_pair("0.2")
    r = enclose_weil_functional(
        h, g, n_max=2000, prec_bits=48, cross_check=False
    )
    lo, hi = r["W_enclosure"]
    assert lo < 0 < hi
    assert r["sign"] == 0
    assert not r["positivity_proven"]
    assert r["certified"]  # a wide truth is still a truth


def test_enclosures_at_different_precisions_overlap():
    h, g = certified_gaussian_pair("0.05")
    r1 = enclose_weil_functional(h, g, n_max=500, R=60, prec_bits=64, cross_check=False)
    r2 = enclose_weil_functional(h, g, n_max=500, R=60, prec_bits=160, cross_check=False)
    lo1, hi1 = r1["W_enclosure"]
    lo2, hi2 = r2["W_enclosure"]
    assert max(lo1, lo2) <= min(hi1, hi2)  # both contain the same truth
    assert hi2 - lo2 < hi1 - lo1  # more bits, tighter enclosure


# ---------------------------------------------------------------------------
# refusals: nothing rigorous can be built on a float pair or without Arb
# ---------------------------------------------------------------------------


def test_iv_backend_refuses():
    h, g = certified_gaussian_pair("0.01")
    with pytest.raises(NotImplementedError, match="flint-only"):
        enclose_weil_functional(h, g, backend="mpmath.iv")


def test_plain_float_pair_refused():
    h, g = gaussian_pair("0.01")  # zeta.weil's pair: floats, no cert_hints
    with pytest.raises(TypeError, match="ball-valued"):
        enclose_weil_functional(h, g)


def test_mismatched_pair_refused():
    # h and g must come from the SAME constructor call, two calls with the
    # same parameter carry distinct cert_hints objects, and are refused
    h1, _ = certified_gaussian_pair("0.01")
    _, g2 = certified_gaussian_pair("0.01")
    with pytest.raises(TypeError, match="SAME call"):
        enclose_weil_functional(h1, g2)


def test_pair_constructor_validation():
    with pytest.raises(ValueError):
        certified_gaussian_pair(0)
    with pytest.raises(ValueError):
        certified_fejer_pair(-1)
    # fejér support e^{2b} beyond the prime-power cap is an honest refusal
    h, g = certified_fejer_pair(8)
    with pytest.raises(ValueError, match="cap"):
        enclose_weil_functional(h, g, R=64, prec_bits=64, cross_check=False)


def test_exports():
    for name in (
        "certified_gaussian_pair",
        "certified_fejer_pair",
        "enclose_weil_functional",
    ):
        assert name in rigor.__all__


# ---------------------------------------------------------------------------
# the archimedean tail lemma, spot-checked in ball arithmetic
# ---------------------------------------------------------------------------


def test_arch_tail_lemma_spot_check():
    # |Re psi(1/4 + ir/2) - log pi| <= log(r+2) + 8 for r >= 6.  The
    # docstring derivation is the proof; this pins the constant against a
    # transcription error, rigorously at each sampled r.
    from flint import acb, arb, ctx, fmpq

    old = ctx.prec
    try:
        ctx.prec = 96
        logpi = arb.pi().log()
        for r in (6, 8, 20, 100, 1000, 100_000):
            w = ((acb(fmpq(1, 4)) + acb(0, fmpq(1, 2)) * r).digamma() - logpi).real
            bound = (arb(r) + 2).log() + 8
            assert (abs(w) - bound).upper() < 0, f"lemma fails at r={r}"
    finally:
        ctx.prec = old


# ---------------------------------------------------------------------------
# dict hygiene: the flint-only caveat is stated, assumptions are named
# ---------------------------------------------------------------------------


def test_result_dict_states_its_limits():
    h, g = certified_gaussian_pair("0.04")
    r = enclose_weil_functional(
        h, g, n_max=200, R=40, prec_bits=96, cross_check=False
    )
    assert "mpmath.iv has no certified quadrature" in r["two_backend_cross_check"]
    rosser = next(a for a in r["assumptions"] if "Rosser" in a)
    assert "gaussian and autocorrelation" in rosser
    assert any("lemma" in a for a in r["assumptions"])
    assert r["backend"] == "python-flint"
    assert r["param_exact"] == "1/25"


def test_an_unprovable_step_forces_sign_to_zero_not_merely_uncertified():
    """**Regression, 2026-08-11.** ``sign`` is documented as *proven*.

    The Fejér path proves its prime cutoff is complete by the ball comparison
    ``log(n_max+1) > 2b``.  When that comparison cannot be closed, here with
    ``b`` a 60-digit rational just below ``log(7)/2``, so the two sides
    straddle at 192 bits, the code records the failure in
    ``uncertified_steps`` and then continues with ``prime_tail = 0``: an
    enclosure asserting the prime sum is exactly complete, which is precisely
    what it just failed to prove.  ``sign`` was read off that enclosure and
    came back ``1``.  It must be ``0``: the module's safe failure mode is
    "not decided", and a step that was not established may not contribute a
    proven sign.
    """
    b = Fraction(str(mp.log(7) / 2)) if mp.dps >= 15 else None
    with mp.workdps(60):
        b = Fraction(str(mp.log(7) / 2))
    h, g = certified_fejer_pair(b)
    r = enclose_weil_functional(h, g, prec_bits=192, cross_check=False)
    assert r["uncertified_steps"], "this b is chosen to leave the cutoff unproven"
    assert r["certified"] is False
    assert r["sign"] == 0
    assert r["positivity_proven"] is False
