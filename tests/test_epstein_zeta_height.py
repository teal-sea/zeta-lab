"""``epstein_zeta`` keeps its digits at height (issue #217).

The Mellin split behind ``epstein_completed`` cancels about ``0.6822 |t|``
digits at height ``t``.  Commit 3b746ea gave the zero count a height floor
(``epstein_count_dps``) but left ``epstein_zeta`` itself at ``dps + 20``
working digits whatever the height, so above a height set by ``dps`` it
returned a number with no correct digit and said nothing.  It now raises its
working precision by ``ceil(EPSTEIN_DIGITS_PER_UNIT_HEIGHT * |t|)``.

Two oracles that share no code with the lattice sums:

* at ``Re s = 5`` the defining sum ``sum Q(m,k)^{-s}`` converges absolutely
  and is summed directly over the box ``|m|, |k| <= 40``.  The omitted tail
  is estimated, not bounded, by the integral ``2 pi lambda^-5 40^-8 / 8``
  (``lambda`` the form's least eigenvalue): about ``2e-13`` in absolute
  terms for ``(1,1,4)`` against a value of modulus near 2, under the
  ``1e-12`` relative tolerance.  The fixed routine measured agreement
  below ``1e-15`` in the three cells below, so the estimate is not what
  binds;
* on the critical line, the class-group identity
  ``sum_Q zeta_Q(s) = w zeta(s) L(s, chi_D)`` built from mpmath's ``zeta``
  and a Hurwitz character sum.

A cross-check that cannot fail is not one, so the planted fault is pinned
too: with the height lift switched off, the same calls are wrong.
"""
from __future__ import annotations

import pytest
from mpmath import mp

from zeta import epstein


def _defining_sum(form, s, box: int = 40):
    a, b, c = form
    with mp.workdps(30):
        s = mp.mpmathify(s)
        return mp.fsum(
            mp.power(a * m * m + b * m * k + c * k * k, -s)
            for m in range(-box, box + 1)
            for k in range(-box, box + 1)
            if (m, k) != (0, 0)
        )


def _relative_error(form, s, dps):
    reference = _defining_sum(form, s)
    value = epstein.epstein_zeta(s, form, dps=dps)
    with mp.workdps(30):
        return abs(value - reference) / abs(reference)


# Issue #217 measured, at dps = 15: 3.1 correct digits for (1,1,4) at t = 60,
# none at t = 80 or for (2,1,3) at t = 120, before the lift.  The t = 60 cell
# runs in the fast tier (about 8 s); the higher ones are slow-tier.
FAST = ((1, 1, 4), 60)
SLOW = [((1, 1, 4), 80), ((2, 1, 3), 120)]
CELLS = [FAST] + [pytest.param(*cell, marks=pytest.mark.slow) for cell in SLOW]


@pytest.mark.parametrize("form, t", CELLS)
def test_epstein_zeta_matches_the_defining_sum_at_height(form, t):
    assert _relative_error(form, mp.mpc(5, t), dps=15) < mp.mpf("1e-12")


@pytest.mark.parametrize("form, t", [FAST] + SLOW)
def test_without_the_lift_the_same_call_is_wrong(monkeypatch, form, t):
    """The planted fault: the old behaviour, reproduced by zeroing the rule.

    Unlifted, these calls are cheap; each misses the tolerance above by at
    least six orders of magnitude, so the main test is able to fail.
    """
    monkeypatch.setattr(epstein, "EPSTEIN_DIGITS_PER_UNIT_HEIGHT", 0.0)
    assert _relative_error(form, mp.mpc(5, t), dps=15) > mp.mpf("1e-6")


@pytest.mark.slow
def test_class_group_identity_holds_on_the_critical_line_at_height():
    """sigma = 1/2 is where the loss is largest; the identity shares no code.

    Run against the pre-fix module (no height lift), this cell measured a
    defect of ``2.3e-15``, above the bound, so it fails there; with the lift
    it passes.  That red run is recorded in the commit that fixed #217
    rather than repeated here, since it costs a second slow evaluation.
    """
    s = mp.mpc(mp.mpf(1) / 2, 40)
    assert abs(epstein.epstein_class_group_defect(s, -15, dps=10)) < mp.mpf("1e-17")
