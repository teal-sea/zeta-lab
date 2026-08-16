"""Pins for the lambda_dh_bounds separation claim and the kappa closed form.

Two groups of tests share this file.

Separation pins (exact rational arithmetic and JSON re-checks, no flint
needed beyond the module-level dependency below): the rational core of
Lambda_DH > Lambda_zeta (144/625 > 11/50, SEPARATION.md section 2), the
frame-dictionary factor 4 between the narrow and wide headline endpoints as
printed in FRAME.md section 6 and carried in results.json, and a containment
re-check that winding_results.json still decides N = 1 at both t values with
the exact rationals the floor rests on.

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


def test_frame_dictionary_factor_on_the_headline_endpoints():
    """4 * narrow bracket endpoints equal the wide ones, as printed.

    FRAME.md section 6 prints the two headlines; results.json carries them
    as headline_narrow and headline_wide. The dictionary Lambda(wide) =
    4 * Lambda(narrow) must hold exactly on both printed endpoints: the
    lower endpoints are the exact rationals 36/625 and 144/625, and the
    upper headline decimals were rounded outward once, in the narrow frame,
    then multiplied by exactly 4 (FRAME.md section 6, GATE.md upper bound).
    """
    narrow_lo, narrow_hi = _headline_endpoints("headline_narrow")
    wide_lo, wide_hi = _headline_endpoints("headline_wide")
    assert narrow_lo == Fraction(36, 625)
    assert wide_lo == Fraction(144, 625)
    assert 4 * narrow_lo == wide_lo
    assert narrow_hi == Fraction("0.4006343708899557")
    assert wide_hi == Fraction("1.6025374835598228")
    assert 4 * narrow_hi == wide_hi


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
