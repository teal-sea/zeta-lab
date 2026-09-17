"""The staged prime-tower pilot matches the kernel mirror and emits the real shape."""
from __future__ import annotations

import importlib.util
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))


def _load_pilot():
    path = SCRIPTS / "68_rung3_ball_tower_pilot.py"
    spec = importlib.util.spec_from_file_location("rung3_ball_tower_pilot", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_pilot_emits_the_30_product_prime_tower_without_mulA():
    pilot = _load_pilot()
    text, stats = pilot.render_prime_tower(2)

    assert stats["product_atoms"] == 30
    assert text.count("private lemma ev_mul_") == 30
    assert "mulA" not in text
    assert "absUpper" not in text
    assert "theorem pilot_contains_cpow" in text


def test_pilot_final_literal_is_bit_identical_to_the_ball_mirror():
    pilot = _load_pilot()
    ball = pilot.ball
    _, stats = pilot.render_prime_tower(2)
    S = ball.C(F(808517, 10**6), F(85699348, 10**6), 0)
    expected = ball.dirichletTermBox2(
        pilot.NLOG, pilot.NEXP, pilot.P, (2).bit_length(), pilot.KE, 2, S
    )

    assert stats["final"].cre == expected.cre
    assert stats["final"].cim == expected.cim
    assert stats["final"].rad == expected.rad


def test_each_product_uses_two_literal_modulus_bounds():
    pilot = _load_pilot()
    text, _ = pilot.render_prime_tower(2)
    product_lines = [line for line in text.splitlines()
                     if line.startswith("private lemma ev_mul_")]

    assert len(product_lines) == 30
    assert all("sqrtUpperQ" not in line for line in product_lines)
    assert all("absUpper" not in line for line in product_lines)


def test_pilot_accepts_a_positive_radius_site_ball():
    pilot = _load_pilot()
    ball = pilot.ball
    S = ball.from_box(
        F(589767, 10**6), F(589767, 10**6),
        F(21916392463, 256000000), F(21918579963, 256000000),
    )
    _, stats = pilot.render_prime_tower(2, S=S)
    expected = ball.dirichletTermBox2(
        pilot.NLOG, pilot.NEXP, pilot.P, (2).bit_length(), pilot.KE, 2, S
    )

    assert S.rad > 0
    assert stats["final"].cre == expected.cre
    assert stats["final"].cim == expected.cim
    assert stats["final"].rad == expected.rad
