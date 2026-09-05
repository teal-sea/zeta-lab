"""Adversarial checks of the finite witness, not tests of LP success."""

import importlib.util
import json
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("reversal_verifier", HERE / "verify.py")
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def artifact():
    return json.loads((HERE / "adversary.json").read_text())


def test_upper_bound_refutes_both_recorded_targets():
    data = artifact()
    for bits in (96, 192):
        result = verifier.check(data, bits)
        assert Fraction(result["rational_upper"]) < Fraction(19791, 2500000)
        assert Fraction(result["rational_upper"]) < Fraction(data["reported_lower_endpoint"])


def test_probability_mass_lesion_is_rejected():
    data = artifact()
    data["orbits"][0]["weight"] = "0"
    with pytest.raises(ValueError, match="exactly one"):
        verifier.check(data)


def test_invalid_gap_lesion_is_rejected():
    data = artifact()
    data["orbits"][0]["gaps"][0] = "-1"
    with pytest.raises(ValueError, match="Invalid"):
        verifier.check(data)


def test_unattained_upper_target_is_rejected():
    data = artifact()
    data["upper_target"] = "79/10000"
    with pytest.raises(ValueError):
        verifier.check(data)


def test_an_unrelated_geometry_cannot_inherit_the_target():
    data = artifact()
    # Preserve every probability but move the support to very large gaps.
    # The pressure alone then makes this a useless upper-bound witness.
    for orbit in data["orbits"]:
        orbit["gaps"] = ["100"] * 6
    with pytest.raises(ValueError):
        verifier.check(data)


def test_a_false_leaf_bound_is_rejected():
    data = artifact()
    data["span_caps"][0] = "0"
    with pytest.raises(ValueError, match="span cap"):
        verifier.check(data)


def test_every_orbit_is_closed_with_exact_probability():
    points = verifier.rational_points(artifact())
    assert sum(p for p, _ in points) == 1
    for (p, g), (q, h) in zip(points[::2], points[1::2]):
        assert p == q and g == h[::-1]
