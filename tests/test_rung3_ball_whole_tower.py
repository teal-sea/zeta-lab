"""The opt-in whole-tower emission (`--tower whole`) of the rung-3 generator.

Each prime tower is proved by one `decide +kernel` of `dirichletTermBallB ... = Sq_10`
plus `contains_dirichletTermBallB` (hunt #145's pilot).  These tests pin that the default
emission is untouched, that the whole mode keeps the names callers use, and that its
literal is the bit-exact mirror's and equals the staged chain's last ball.  The kernel
side (compiles, planted faults refused) is recorded in hunts/rung3_ball_production.
"""
from __future__ import annotations

import importlib.util
import json
import re
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


gen = _load("rung3_generate_whole", "60_rung3_generate.py")
back = gen._ball_backend()
ball = back.ball
PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())


def _site(sid: str):
    site = dict(next(x for x in PLAN["big"]["boxes"] if x["id"] == sid))
    site["M"] = PLAN["M"]
    return site


def _box(sid: str):
    s = _site(sid)
    return ball.from_box(F(s["re_lo"]), F(s["re_hi"]), F(s["im_lo"]), F(s["im_hi"]))


def test_default_is_staged_and_explicit_staged_is_identical():
    site = _site("B_right_06")
    default, _ = gen.emit_site_modules(site, "big")
    staged, _ = gen.emit_site_modules(site, "big", tower="staged")
    assert default == staged
    assert gen.parse_args(["p.json", "out"]).tower == "staged"


def test_whole_mode_exports_the_names_the_power_lemmas_use():
    text, _ = gen.emit_site(_site("B_right_06"), "big", arith="ball", tower="whole")
    assert text.count("theorem pilot_contains_cpow") == 23
    assert text.count("decide +kernel") == 2 * 23
    assert "contains_dirichletTermBallB" in text
    assert "private lemma ev_mul_" not in text and "Pow_19" not in text
    for p in (2, 3, 89):
        assert f"Prime_{p}.pilot_contains_cpow hSp" in text
        assert f"dirichletTermBallB 32 20 64 {p.bit_length()} 10 {p} S = Sq_10" in text


@pytest.mark.parametrize("prime", [2, 3, 89, 1801])
def test_whole_literal_is_the_mirror_and_the_staged_chain(prime):
    S = _box("B_right_06")
    text, value = back._tower_fragment(prime, S, f"Prime_{prime}", "whole")
    _, staged = back._tower_fragment(prime, S, f"Prime_{prime}", "staged")
    mirror = ball.dirichletTermBox2(32, 20, 64, prime.bit_length(), 10, prime, S)
    assert (value.cre, value.cim, value.rad) == (staged.cre, staged.cim, staged.rad)
    assert (value.cre, value.cim, value.rad) == (mirror.cre, mirror.cim, mirror.rad)
    assert f"def Sq_10 : ComplexBall := {back.lit(mirror)}" in text


def test_whole_mode_refuses_a_mirror_that_disagrees(monkeypatch):
    S = _box("B_right_06")
    real = ball.dirichletTermBox2

    def off_by_one(*args):
        v = real(*args)
        return ball.C(v.cre, v.cim, v.rad - F(1, 2**64))

    monkeypatch.setattr(ball, "dirichletTermBox2", off_by_one)
    with pytest.raises(AssertionError, match="disagrees"):
        back._tower_fragment(2, S, "Prime_2", "whole")


def test_unknown_tower_mode_and_rect_whole_are_refused():
    with pytest.raises(ValueError):
        back._tower_fragment(2, _box("B_right_06"), "Prime_2", "fast")
    with pytest.raises(SystemExit):
        gen.parse_args(["p.json", "out", "--arith", "rect", "--tower", "whole"])
    with pytest.raises(SystemExit):
        gen.parse_args(["p.json", "out", "--tower", "nope"])


def test_whole_mode_shards_are_small_and_keep_the_site_theorem():
    files, stats = gen.emit_site_modules(_site("B_right_06"), "big", tower="whole")
    names = [rel for rel, _ in files]
    assert names[-1] == "CB_right_06.lean"
    assert "theorem upper_B_right_06" in files[-1][1]
    primes = [t for rel, t in files if re.match(r"CB_right_06/Primes\d*\.lean$", rel)]
    assert sum(t.count("theorem pilot_contains_cpow") for t in primes) == 23
    assert stats["max_file_bytes"] < 200_000
