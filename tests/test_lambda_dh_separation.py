"""Pins for the lambda_dh_bounds separation claim and the kappa closed form.

Two groups of tests share this file.

Separation pins (exact rational arithmetic and JSON re-checks, no flint
needed beyond the module-level dependency below): the rational core of
Lambda_DH > Lambda_zeta (144/625 > 11/50, SEPARATION.md section 2), the
frame-dictionary factor 4 between the narrow and wide headline endpoints as
printed in FRAME.md section 6 and carried in results.json, and a containment
re-check that winding_results.json still decides N = 1 at both t values with
the exact rationals the floor rests on.

Upper-bound pins added 2026-08-18, when the hardening pass replaced the
coefficient-domination strip constant with the phase-obstruction one: the
headline upper endpoint is now the EXACT rational Delta^2/2 at the decided
abscissa sigma_0' = 112036249819/100000000000, so the pins here check exact
rational identities rather than a printed rounding, and they check that the
superseded value is still recorded rather than deleted. The pin that the
separation is unaffected by the sharpening is the point of
test_the_sharpened_upper_bound_does_not_touch_the_separation: the floor and
the cited zeta bound carry the whole claim, and neither appears in the
sharpened arithmetic.

Kappa closed-form pins (enclosure grade, python-flint):
kappa = tau_+ = -phi + sqrt(1 + phi^2), Bombieri-Ghosh's identity.

kappa, the Davenport-Heilbronn functional-equation constant, equals
tau_+ = -phi + sqrt(1 + phi^2) with phi the golden ratio (1 + sqrt 5)/2.
The identity is Bombieri-Ghosh's (Russian Math. Surveys 66:2 (2011),
section 6); the radical value is Titchmarsh's. The derivation of the
quadratic kappa^2 + 2 phi kappa - 1 = 0 from the theta-matching
self-duality condition, and the containment record these tests pin, live in
hunts/lambda_dh_bounds/KAPPA-CLOSED-FORM.md.

Naming note: this file is test_lambda_dh_separation.py because no
tests/test_lambda_dh_bounds.py existed when it was added; if that file
ever appears, these tests belong there.

The hunt's instrument is loaded under a unique module name via importlib
rather than a bare ``import instrument``, so it cannot collide in
``sys.modules`` with another hunt's instrument.py when tests share a
worker process.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

flint = pytest.importorskip(
    "flint", reason="python-flint is pinned in requirements.txt; kappa_ball is flint-only"
)
from flint import arb, ctx  # noqa: E402
from mpmath import iv, mp, mpf  # noqa: E402

_HUNT = Path(__file__).resolve().parents[1] / "hunts" / "lambda_dh_bounds"

_spec = importlib.util.spec_from_file_location(
    "lambda_dh_bounds_instrument", _HUNT / "instrument.py"
)
instrument = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(instrument)

PREC = 500


def _closed_form_balls():
    """(phi, target) at the ambient ctx.prec, from exact input balls."""
    sqrt5 = arb(5).sqrt()
    phi = (1 + sqrt5) / 2
    return phi, (1 + phi * phi).sqrt() - phi


def test_kappa_ball_contains_the_closed_form_ball():
    """kappa_ball(500) vs sqrt(1+phi^2) - phi in balls at 500 bits.

    Tolerance as recorded in KAPPA-CLOSED-FORM.md section 4: the two balls
    overlap (their difference ball contains 0) and the midpoints agree to
    40 digits. The 2026-08-16 run decides far more (midpoint gap 1.3e-149,
    strict one-sided containment of the target ball), but the pin here is
    the stated tolerance, not the observed margin.
    """
    k = instrument.kappa_ball(PREC)
    old = ctx.prec
    ctx.prec = PREC
    try:
        _, target = _closed_form_balls()
        diff = k - target
        assert diff.contains(arb(0)), "kappa ball and closed-form ball do not overlap"
        mid_gap = arb(k.mid()) - arb(target.mid())
        assert mid_gap * mid_gap < arb(10) ** -80, (
            "midpoints of kappa_ball(500) and the closed form differ beyond 40 digits"
        )
    finally:
        ctx.prec = old


def test_kappa_satisfies_the_golden_quadratic():
    """The residual kappa^2 + 2 phi kappa - 1 contains 0, in balls at 500 bits.

    This is the quadratic derived in KAPPA-CLOSED-FORM.md section 3 from the
    self-duality condition alpha = conj(alpha) (-i tau(conj chi) 5^{-1/2}).
    """
    k = instrument.kappa_ball(PREC)
    old = ctx.prec
    ctx.prec = PREC
    try:
        phi, _ = _closed_form_balls()
        resid = k * k + 2 * phi * k - 1
        assert resid.contains(arb(0)), "quadratic residual ball excludes 0"
        assert resid.rad() < arb(10) ** -100, "quadratic residual ball is too wide to decide anything"
    finally:
        ctx.prec = old


def test_kappa_closed_form_on_the_iv_leg():
    """mpmath.iv at dps 40: trig form of the solve vs the closed form.

    The iv context has no interval Hurwitz zeta, so the linear solve itself
    is flint-only; the iv leg encloses the trig reduction
    2 sin(pi/5) / (sqrt5 + 2 sin(2 pi/5)) instead (the reduction step is
    decided on the flint leg, KAPPA-CLOSED-FORM.md section 4). Cross-backend,
    the flint midpoint agrees with the iv enclosure to 40 digits.
    """
    old_dps = iv.dps
    iv.dps = 40
    try:
        phi_i = (1 + iv.sqrt(5)) / 2
        target_i = iv.sqrt(1 + phi_i ** 2) - phi_i
        k_i = 2 * iv.sin(iv.pi / 5) / (iv.sqrt(5) + 2 * iv.sin(2 * iv.pi / 5))
        assert 0 in (k_i - target_i), "iv trig form and iv closed form do not overlap"
        resid_i = k_i ** 2 + 2 * phi_i * k_i - 1
        assert 0 in resid_i, "iv quadratic residual excludes 0"

        k = instrument.kappa_ball(PREC)
        with mp.workdps(60):
            mid_flint = mpf(k.mid().str(70, radius=False))
            mid_iv = (mpf(target_i.a) + mpf(target_i.b)) / 2
            assert abs(mid_flint - mid_iv) < mpf(10) ** -40, (
                "flint and iv midpoints differ beyond 40 digits"
            )
    finally:
        iv.dps = old_dps


# ---------------------------------------------------------------------------
# Separation pins (SEPARATION.md; results.json; winding_results.json)
# ---------------------------------------------------------------------------

import json
import re
from fractions import Fraction

_RESULTS = json.loads((_HUNT / "results.json").read_text(encoding="utf-8"))
_WINDING = json.loads((_HUNT / "winding_results.json").read_text(encoding="utf-8"))


def test_separation_exact_rational_core():
    """144/625 > 11/50, cross-multiplied, in exact rationals in both frames.

    The wide-frame core of the separation chain (SEPARATION.md section 2):
    the decided floor 4 * 36/625 = 144/625 strictly exceeds Polymath 15's
    11/50 = 0.22. The narrow-frame reading divides both sides by 4, so the
    cross-multiplication is literally the same integers.
    """
    floor_wide = Fraction(4 * 36, 625)
    zeta_wide = Fraction(11, 50)
    assert floor_wide == Fraction(144, 625)
    assert floor_wide > zeta_wide
    assert 144 * 50 == 7200 and 11 * 625 == 6875 and 7200 > 6875

    # Narrow frame: same inequality, same integers after the factor 4 cancels.
    floor_narrow = Fraction(36, 625)
    zeta_narrow = Fraction(11, 200)
    assert floor_narrow > zeta_narrow
    assert 36 * 200 == 7200 and 11 * 625 == 6875
    assert floor_wide / floor_narrow == 4 == zeta_wide / zeta_narrow


def _headline_endpoints(claim_key):
    """(lower, upper) as Fractions from a results.json headline string."""
    text = _RESULTS["claims"][claim_key]["value_or_interval"]
    m = re.fullmatch(r"([0-9.]+) < Lambda_DH <= ([0-9.]+)", text)
    assert m, f"unexpected headline shape in {claim_key}: {text!r}"
    return Fraction(m.group(1)), Fraction(m.group(2))


#: The decided phase-obstruction abscissa of STRIP2.md section 5.2, as the
#: exact rational the bisection settled on, and the constants it forces.
SIGMA_0_PRIME = Fraction(112036249819, 100000000000)
DELTA_PRIME = SIGMA_0_PRIME - Fraction(1, 2)
DELTA_SQ_OVER_2_NARROW = DELTA_PRIME * DELTA_PRIME / 2

#: The headline the coefficient-domination route carried through 2026-08-17.
#: It is still correct and still decided (strip_results.json, STRIP.md); it is
#: pinned here so a silent deletion of the superseded record fails a test.
SUPERSEDED_NARROW_HI = Fraction("0.4006343708899557")
SUPERSEDED_WIDE_HI = Fraction("1.6025374835598228")


def test_frame_dictionary_factor_on_the_headline_endpoints():
    """4 * narrow bracket endpoints equal the wide ones, as printed.

    FRAME.md section 6 prints the two headlines; results.json carries them
    as headline_narrow and headline_wide. The dictionary Lambda(wide) =
    4 * Lambda(narrow) must hold exactly on both printed endpoints: the
    lower endpoints are the exact rationals 36/625 and 144/625, and since
    2026-08-18 the upper endpoints are exact too, because the abscissa is
    decided at an exact rational (STRIP2.md section 5.2) rather than at a
    bisection endpoint that had to be rounded outward.
    """
    narrow_lo, narrow_hi = _headline_endpoints("headline_narrow")
    wide_lo, wide_hi = _headline_endpoints("headline_wide")
    assert narrow_lo == Fraction(36, 625)
    assert wide_lo == Fraction(144, 625)
    assert 4 * narrow_lo == wide_lo
    assert narrow_hi == DELTA_SQ_OVER_2_NARROW
    assert wide_hi == 4 * DELTA_SQ_OVER_2_NARROW
    assert 4 * narrow_hi == wide_hi


def test_the_sharpened_upper_endpoint_is_exact_delta_squared_over_two():
    """The headline upper endpoint is Delta^2/2 at the decided abscissa.

    STRIP2.md decides Theta(sigma) < pi - 2 arctan(kappa) at the exact
    rational sigma_0' = 112036249819/100000000000, so every zero of the
    completed F has |Im z| < Delta = sigma_0' - 1/2 = 0.62036249819 and de
    Bruijn 1950 Theorem 13 gives Lambda_DH <= Delta^2/2. Because the
    abscissa is an exact rational the bound terminates, and the check here
    is an identity between rationals rather than a comparison against a
    printed rounding.
    """
    assert DELTA_PRIME == Fraction("0.62036249819")
    assert DELTA_SQ_OVER_2_NARROW == Fraction(
        3848496291605377532761, 20000000000000000000000
    )
    assert DELTA_SQ_OVER_2_NARROW == Fraction("0.19242481458026887663805")
    assert 4 * DELTA_SQ_OVER_2_NARROW == Fraction("0.7696992583210755065522")

    # STRIP2.md section 5.2 also displays it rounded outward to 22 decimals.
    # That display must be a valid bound, i.e. at or above the exact value.
    assert Fraction("0.1924248145802688766381") >= DELTA_SQ_OVER_2_NARROW

    _, narrow_hi = _headline_endpoints("headline_narrow")
    assert narrow_hi == DELTA_SQ_OVER_2_NARROW


def test_the_sharpening_is_the_recorded_factor_and_is_recorded_as_such():
    """The improvement over the superseded headline is 2.082030697360155.

    The superseded value must still be visible, per the repo's correction
    style: results.json carries it in the headline claims' `superseded`
    fields and in the retained decided intervals, and this test fails if it
    is deleted rather than superseded.
    """
    factor = SUPERSEDED_NARROW_HI / DELTA_SQ_OVER_2_NARROW
    assert abs(float(factor) - 2.082030697360155) < 1e-12

    narrow = _RESULTS["claims"]["headline_narrow"]
    wide = _RESULTS["claims"]["headline_wide"]
    assert "0.4006343708899557" in narrow["superseded"]
    assert "1.6025374835598228" in wide["superseded"]

    # The superseded strip constant is still carried as a decided claim.
    old = _RESULTS["claims"]["delta_sq_over_2_narrow_flint"]
    assert old["grade"] == "decided"
    lo, hi = (Fraction(x) for x in old["value_or_interval"])
    assert lo < hi, "the retained decided interval must still be an interval"
    assert SUPERSEDED_NARROW_HI > hi, (
        "the superseded headline was an outward rounding and must still sit "
        "above its own decided upper endpoint"
    )
    assert 4 * SUPERSEDED_NARROW_HI == SUPERSEDED_WIDE_HI


def test_the_sharpened_upper_bound_does_not_touch_the_separation():
    """The separation rests on the floor, so sharpening the ceiling is inert.

    SEPARATION.md's chain uses `0 <= Lambda_zeta`, `Lambda_zeta <= 0.22`,
    `11/50 < 144/625` and `144/625 < Lambda_DH`. The upper endpoint appears
    in the chain only so the claim travels with the whole bracket. This test
    states that formally: the separation inequality holds for either upper
    endpoint, and the decided floor is unchanged.
    """
    floor_wide = Fraction(144, 625)
    zeta_wide = Fraction(11, 50)
    for ceiling in (SUPERSEDED_WIDE_HI, 4 * DELTA_SQ_OVER_2_NARROW):
        assert zeta_wide < floor_wide < ceiling

    # And the floor itself is still the exact rational the winding count
    # decided, in both the JSON and the keyed claim.
    assert Fraction(_WINDING["decided_floor_t"]) == Fraction(36, 625)
    claim = _RESULTS["claims"]["separation_lambda_dh_gt_lambda_zeta"]
    assert "144/625" in claim["value_or_interval"]
    assert "0.7696992583210755065522" in claim["value_or_interval"]


def test_the_sharpened_abscissa_is_recorded_with_both_backends():
    """sigma_0' carries a decided grade and two backends, per the contract.

    Every decided number in this repository travels with its backend and
    precision. The claim must also name the exact rational it was decided
    at, because that is what makes Delta^2/2 exact.
    """
    claim = _RESULTS["claims"]["sigma_0_prime_headline"]
    assert claim["grade"] == "decided"
    assert "112036249819/100000000000" in claim["value_or_interval"]
    assert "python-flint" in claim["backend"] and "mpmath.iv" in claim["backend"]
    assert "192 bits" in claim["precision"]


def test_the_m2_lemma_is_recorded_as_proved_with_its_one_cited_input():
    """M2 moved from prose to a proved lemma, and what it rests on is named.

    RESULTS.md section 5.1a and GATE.md assumption 6 record the change. The
    pin here is that the record does not overstate it: the lemma claim must
    exist, and the claim naming its single cited input (the evenness of
    Phi_DH) must still be graded `cited`, since that is what keeps the
    composite grade of the bracket unchanged.
    """
    proved = _RESULTS["claims"]["m2_lemma_proved"]
    assert "Lemma M2" in proved["value_or_interval"]
    assert "not kernel-checked" in proved["grade"]

    rests = _RESULTS["claims"]["m2_lemma_what_it_rests_on"]
    assert rests["grade"] == "cited"
    assert "Phi_DH(-u) = Phi_DH(u)" in rests["value_or_interval"]

    # The composite headline grade is still the weakest step, a citation.
    assert _RESULTS["claims"]["headline_narrow"]["grade"] == "cited"


def test_m2_lemma_values_do_not_exceed_the_bound_the_count_consumed():
    """The re-derived M2 must be at most winding.py's, or the count is stale.

    M2-LEMMA.md section 5: the lemma's own value is 1.1886319406143055e-78
    at t1 against winding.py's 1.1886642645115153e-78, a relative -2.7e-05
    traced to one panel of 800 where winding.py keeps the larger of two
    valid majorants. Larger is safe; smaller would mean the consumed bound
    was not justified by the lemma.
    """
    m2 = json.loads((_HUNT / "m2_lemma_results.json").read_text(encoding="utf-8"))
    winding_m2 = {"t1": 1.1886642645115153e-78, "t2": 1.1370829034005339e-78}
    for box, consumed in winding_m2.items():
        lemma = m2[box]["R1_shifted_bound"]["M2_upper_float"]
        assert lemma <= consumed, (
            f"{box}: the lemma's M2 {lemma!r} exceeds the {consumed!r} the "
            "winding count consumed, so the decided integer is not covered"
        )
    assert m2["verdict"] == "PASS"


def test_separation_claim_is_recorded_with_frame_and_grade():
    """The keyed separation claim exists and carries what must travel with it."""
    claim = _RESULTS["claims"]["separation_lambda_dh_gt_lambda_zeta"]
    assert "Lambda_DH > Lambda_zeta" in claim["value_or_interval"]
    assert "144/625" in claim["value_or_interval"]
    assert claim["grade"] == "cited", "weakest-step rule: the composite takes the cited grade"
    assert "wide" in claim["frame"]
    assert "SEPARATION.md" in claim["source_file"]


def test_decided_floor_containment_in_winding_results():
    """winding_results.json still decides N = 1 at both exact rational t.

    The separation's decided link is the winding count at t = 36/625
    (narrow); the pre-registered t = 23/400 run rides along. Both runs must
    carry status decided, N = 1, and the exact rationals, and the decided
    floor must be the stretch value 36/625 whose quadruple is 144/625.
    """
    t1 = _WINDING["t1_run"]
    t2 = _WINDING["t2_stretch_run"]
    assert t1["status"] == "decided" and t1["N"] == 1
    assert t2["status"] == "decided" and t2["N"] == 1
    assert Fraction(t1["t"]) == Fraction(23, 400)
    assert Fraction(t2["t"]) == Fraction(36, 625)
    assert Fraction(_WINDING["decided_floor_t"]) == Fraction(36, 625)
    assert 4 * Fraction(_WINDING["decided_floor_t"]) == Fraction(144, 625)
    # The box interior sits strictly off the real axis, in exact rationals.
    assert Fraction(t2["box"]["im_lo"]) == Fraction(3, 1024) > 0
