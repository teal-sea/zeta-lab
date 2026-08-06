"""Department #1, pinned: the zeta department's specific wiring and its limits.

``tests/test_department_conformance.py`` audits every department against the
protocol. This file pins the facts that are true of *this* department and would
otherwise live only in prose — including the one instrument that looked like it
qualified and does not.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from harness import get_department  # noqa: E402
from harness.departments import load  # noqa: E402
from harness.protocol import run_battery  # noqa: E402
from zeta.factorization import factorization_defect  # noqa: E402


@pytest.fixture(scope="module")
def zeta_department():
    load("zeta")
    return get_department("zeta")


def test_the_rivals_are_the_three_gate_3_counterexamples(zeta_department) -> None:
    assert tuple(r.name for r in zeta_department.battery.rivals) == (
        "davenport_heilbronn",
        "epstein_2_1_3",
        "epstein_1_1_6",
    )


def test_the_functional_equation_is_shared_with_every_rival(zeta_department) -> None:
    """The claim is *true* of zeta, and worthless as a step toward RH."""
    reference = next(
        r for r in zeta_department.reference_claims if r.name == "functional_equation"
    )
    verdict = run_battery(zeta_department.battery, reference.claim)
    assert verdict.target is True
    assert verdict.shared_with == ("davenport_heilbronn", "epstein_1_1_6", "epstein_2_1_3")


def test_multiplicativity_is_the_one_that_distinguishes(zeta_department) -> None:
    reference = next(
        r for r in zeta_department.reference_claims if r.name == "multiplicativity"
    )
    verdict = run_battery(zeta_department.battery, reference.claim)
    assert verdict.distinguishes is True
    assert verdict.errors == {}


# ---------------------------------------------------------------------------
# The instrument that does not qualify — pinned so the doc cannot drift
# ---------------------------------------------------------------------------

_N_MAX = 60


def _coefficient_array(iface, n_max: int = _N_MAX) -> np.ndarray:
    a = np.zeros(n_max + 1)
    for n in range(1, n_max + 1):
        a[n] = float(iface["coefficient"](n))
    return a


def test_the_euler_product_statistic_separates_zeta_from_two_of_three_rivals(
    zeta_department,
) -> None:
    """D(f) = 0 exactly when f has an Euler product — where it is defined."""
    battery = zeta_department.battery
    by_name = {s.name: s for s in (battery.target, *battery.rivals)}

    zeta_D = factorization_defect(_coefficient_array(by_name["riemann_zeta"].payload()), _N_MAX)
    assert zeta_D < 1e-20, zeta_D

    dh_D = factorization_defect(
        _coefficient_array(by_name["davenport_heilbronn"].payload()), _N_MAX
    )
    assert 0.9 < dh_D < 1.1, dh_D

    epstein_D = factorization_defect(
        _coefficient_array(by_name["epstein_1_1_6"].payload()), _N_MAX
    )
    assert 1.5 < epstein_D < 2.0, epstein_D


def test_the_statistic_is_undefined_on_the_epstein_form_that_omits_one(
    zeta_department,
) -> None:
    """2x^2 + xy + 3y^2 does not represent 1, so that series has a_1 = 0.

    The logarithmic-derivative recursion has nothing to normalise by, and the
    statistic raises rather than returning a number it cannot justify.
    """
    battery = zeta_department.battery
    epstein = next(r for r in battery.rivals if r.name == "epstein_2_1_3")
    a = _coefficient_array(epstein.payload())
    assert a[1] == 0.0
    with pytest.raises(ValueError, match="a_1 must be nonzero"):
        factorization_defect(a, _N_MAX)


def test_a_claim_built_on_it_is_refused_rather_than_credited(zeta_department) -> None:
    """The safe failure mode: a rival that raised has not been excluded.

    This is the check that stops the harness from promoting an instrument which
    works on three of four subjects into a decision procedure. If this test ever
    reports ``distinguishes is True``, a crashed rival is being counted as
    refuted, which is a critical defect and not a rounding detail.
    """

    def claim_euler_product(iface) -> bool:
        return factorization_defect(_coefficient_array(iface), _N_MAX) < 1e-20

    verdict = run_battery(zeta_department.battery, claim_euler_product)
    assert verdict.target is True
    assert "epstein_2_1_3" in verdict.errors
    assert "ValueError" in verdict.errors["epstein_2_1_3"]
    assert verdict.distinguishes is False
    assert "inconclusive" in verdict.summary()
