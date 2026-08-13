"""Controls for `arm_identification`.

The load-bearing claim is `ghat(z) = Phi2(-i z)`.  If it is false, the
reuse map is worthless; if it is true, the k=1 formalisation inherits
~2300 lines of already kernel-checked interval machinery.
"""

from __future__ import annotations

import cmath
import math
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from arm_identification import (  # noqa: E402
    A_CONST, IDENTIFICATION_POINTS, REMAINING, REUSE_MAP, damage_route_residual,
    damage_via_ghat, damage_via_phi2, ghat, identification_residual, phi2,
    sfun,
)


def test_identification_holds_to_machine_precision():
    assert identification_residual() < 1e-13


@pytest.mark.parametrize("z", IDENTIFICATION_POINTS)
def test_identification_pointwise(z):
    assert abs(ghat(z) - phi2(-1j * z)) < 1e-13


def test_identification_on_a_random_sweep():
    """Not just the curated points: a grid over the strip and beyond."""
    worst = 0.0
    for i in range(40):
        for j in range(40):
            z = complex(-5 + 0.4 * i, -40 + 2.0 * j)
            worst = max(worst, abs(ghat(z) - phi2(-1j * z)))
    assert worst < 1e-11, worst


def test_A_is_phi2_at_zero():
    """The two arms' normalising constants coincide."""
    assert phi2(0).real == pytest.approx(A_CONST, abs=1e-15)
    assert A_CONST == pytest.approx(0.9187253698655684, abs=1e-15)


def test_phi_r_is_the_paper_field_on_the_real_axis():
    """`phi_r(v) = Re ghat(i v) = Phi2(v)` — BandCert's `phiR`."""
    for v in (0.0, 1.0, 3.7, 6.516999776, 12.755, 30.0, 59.9):
        assert ghat(complex(0, v)).real == pytest.approx(phi2(v).real, abs=1e-14)


def test_damage_routes_agree_over_the_obligation_box():
    assert damage_route_residual() < 1e-13


def test_damage_route_agrees_at_the_named_constants():
    """Against the numbers the ledger and EForm3 carry."""
    assert damage_via_ghat(0.5, 6.516999776) == pytest.approx(0.004396424, abs=1e-8)
    assert damage_via_phi2(0.5, 6.516999776) == pytest.approx(0.004396424, abs=1e-8)
    # no damage inside the near field
    assert damage_via_phi2(0.5, 5.6) <= 0.0
    assert damage_via_phi2(0.5, 0.0) <= 0.0


def test_sfun_branch_identity():
    """`sinh(i w/2)/(i w) = s(w)` — the one line the derivation turns on."""
    for w in (0.3, 1.0, 7.5, -4.2):
        lhs = cmath.sinh(1j * w / 2) / (1j * w)
        assert abs(lhs - sfun(w)) < 1e-14


def test_sfun_is_continuous_at_zero():
    assert sfun(0) == pytest.approx(0.5, abs=1e-15)
    assert abs(sfun(1e-8) - 0.5) < 1e-15


# -- the map itself ---------------------------------------------------------

def test_reuse_map_is_honest_about_what_is_new():
    """It must not claim everything is covered, nor hide the real cost."""
    statuses = [st for _, _, st in REUSE_MAP]
    assert "COVERED" in statuses
    assert any(st.startswith("NEW") for st in statuses)
    # exactly one obligation may be called the real cost
    real = [ob for ob, _, st in REUSE_MAP if "the real cost" in st]
    assert len(real) == 1, real
    assert "table" in real[0]


def test_every_covered_obligation_names_a_lean_theorem_or_module():
    for ob, by, st in REUSE_MAP:
        if st == "COVERED":
            assert "BandCert" in by, (ob, by)


def test_remaining_gaps_are_stated():
    joined = " ".join(REMAINING).lower()
    assert "not written" in joined
    assert "not built" in joined
    assert "rh" in joined
    assert "k >= 2" in joined


def test_module_claims_no_reserved_vocabulary():
    text = (Path(__file__).resolve().parent / "arm_identification.py").read_text()
    for word in ("certi" + "fied", "veri" + "fied", "confir" + "med",
                 "defini" + "tively", "pro" + "ves"):
        assert word not in text.lower(), word
