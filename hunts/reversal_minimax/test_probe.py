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


def test_the_doors_active_set_against_the_adversary():
    # Pins RESULTS.md section 9: equal mean gaps, the ranked budget terms and
    # the three pair coordinates that sit strictly below their span maximum.
    data = artifact()
    points = verifier.rational_points(data)
    mean_gaps = [sum(p * g[r] for p, g in points) for r in range(6)]
    assert max(mean_gaps) - min(mean_gaps) < Fraction(2, 10**13)
    caps = list(map(Fraction, data["span_caps"]))
    terms = {"pressure": Fraction(data["pressure_budget"]) * Fraction(data["mean_gap_cap"])}
    terms.update({f"span-{s}": 2 * cap for s, cap in enumerate(caps, 1)})
    total = sum(terms.values())
    assert total == Fraction(182022320819207, 23 * 10**15)
    order = sorted(terms, key=terms.get, reverse=True)
    assert order == ["pressure", "span-1", "span-5", "span-3", "span-6", "span-4", "span-2"]
    assert round(float(terms["pressure"] / total), 3) == 0.771
    assert round(float(terms["span-1"] / total), 3) == 0.160
    with verifier.ctx.workprec(96):
        k0 = verifier.window_transform(verifier.arb(0), data)
        moments = {(i, j): verifier.arb(0) for i in range(7) for j in range(i + 1, 7)}
        for probability, gaps in points:
            position = [Fraction(0)]
            for gap in gaps:
                position.append(position[-1] + gap)
            for i, j in moments:
                transform = verifier.window_transform(verifier.ball(position[j] - position[i]), data)
                moments[i, j] += verifier.ball(probability) * (transform / k0) ** 2
        middle = {key: float(value.mid()) for key, value in moments.items()}
    strictly_lower = {(0, 2): 0.0284, (4, 6): 0.0284, (1, 5): 0.0222}
    for span in range(1, 7):
        row = {(i, i + span): middle[i, i + span] for i in range(7 - span)}
        top = max(row.values())
        for key, value in row.items():
            if key in strictly_lower:
                assert abs(1 - value / top - strictly_lower[key]) < 5e-4
            else:
                assert abs(value - top) <= 1e-9 * top
