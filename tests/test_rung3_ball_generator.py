"""The production rung-3 generator emits ball-shaped certificates."""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "rung3_generate", ROOT / "scripts" / "60_rung3_generate.py")
assert SPEC is not None and SPEC.loader is not None
gen = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gen)
PLAN = json.loads((ROOT / "lean" / "cert" / "rung3_plan2.json").read_text())


def _site(sid: str):
    site = dict(next(x for x in PLAN["big"]["boxes"] if x["id"] == sid))
    site["M"] = PLAN["M"]
    return site


def test_ball_generator_emits_literal_bound_products_and_ball_assembly():
    text, stats = gen.emit_site(_site("B_right_06"), "big", arith="ball")

    assert "import ZetaLean.BallCertSupport" in text
    assert "ComplexBall.mul" in text
    assert "mulA" not in text
    assert "DH_mem_of_partial_enclosure_order2_ball" in text
    assert "contains_dhBlock_of_terms_ball" in text
    assert "contains_dhAnti_of_terms_ball" in text
    assert stats["normBound"] <= F(PLAN["M"])


def test_ball_generator_reuses_one_tower_per_prime():
    text, _ = gen.emit_site(_site("B_right_06"), "big", arith="ball")
    # 23 needed primes occur among bases 1..89.  Prime 5 is skipped because
    # every multiple of 5 has zero DH coefficient; composites reuse the rest.
    assert text.count("theorem pilot_contains_cpow") == 23
    assert "private lemma hp_B_right_06_84" in text
    assert "contains_cpow_mulB_coarsen_lit" in text


def test_ball_generator_qualifies_ball_lemmas_and_emits_valid_simp_sets():
    text, _ = gen.emit_site(_site("B_right_06"), "big", arith="ball")

    assert "ComplexBall.contains_coeff_term_zero" in text
    assert "ComplexBall.contains_coeff_term_ne" in text
    assert "[(coeffBall" not in text
    assert "convert h using 1 <;> norm_num [S_B_right_06" in text
    assert "apply Complex.ext <;> norm_num" in text
    assert "((0 : ℕ) : ℂ) ^ (-s)" in text
    assert "ComplexBall.contains_corrected" in text
    assert "ComplexBall.contains_half_of" in text
    assert ".neg) = B_B_right_06" not in text
    assert "(17 * 5 + 2 : ℚ)" in text
    assert "  have hev := evanti_B_right_06\n  norm_num at hev" in text
    assert "  rw [hev] at h" in text
    assert "(by norm_num [B_B_right_06, ComplexBall.inflate])" in text


def test_emit_site_rect_emits_rectangle_certificate_surface_not_ball_backend():
    site = _site("B_right_06")
    # Planned M is ball-tight; widen it so the rectangle control can finish.
    site["M"] = "10"
    text, stats = gen.emit_site(site, "big", arith="rect")

    assert "import ZetaLean.DHCertSupport" in text
    assert "import ZetaLean.BallCertSupport" not in text
    assert "ComplexInterval.mul" in text
    assert "ComplexBall" not in text
    assert "DH_mem_of_partial_enclosure_order2_boxed" in text
    assert "DH_mem_of_partial_enclosure_order2_ball" not in text
    assert "contains_dhBlock_of_terms_ball" not in text
    assert "contains_dhAnti_of_terms_ball" not in text
    assert "dhSumBoxes" in text
    assert "namespace Prime_" not in text
    assert "theorem upper_B_right_06" in text
    assert stats["normBound"] <= F(site["M"])


def _cli(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "60_rung3_generate.py"), *args],
        capture_output=True, text=True)


def test_cli_parse_preserves_current_invocations_and_defaults():
    args = gen.parse_args(["plan.json", "outdir"])
    assert args.only is None
    assert args.beta == "measured"
    assert args.arith == "ball"
    assert args.shard is False
    assert args.max_bytes is None

    args = gen.parse_args([
        "plan.json", "outdir", "--only", "B_right_06", "--arith", "ball",
        "--shard", "--max-bytes", "2000000",
    ])
    assert args.only == "B_right_06"
    assert args.beta == "measured"
    assert args.arith == "ball"
    assert args.shard is True
    assert args.max_bytes == 2000000

    args = gen.parse_args(["plan.json", "outdir", "--beta", "plan", "--arith", "rect"])
    assert args.beta == "plan"
    assert args.arith == "rect"
    assert args.shard is False

    args = gen.parse_args(["plan.json", "outdir", "--max-bytes", "100"])
    assert args.shard is True
    assert args.max_bytes == 100


@pytest.mark.parametrize("flag", ["--only", "--beta", "--arith", "--max-bytes"])
def test_missing_flag_values_exit_clearly_not_indexerror(flag):
    out = _cli("plan.json", "outdir", flag)
    err = out.stderr + out.stdout
    assert out.returncode != 0
    assert "IndexError" not in err
    assert "expected one argument" in err
    assert flag in err


def test_invalid_arith_exits_clearly():
    out = _cli("plan.json", "outdir", "--arith", "boxes")
    err = out.stderr + out.stdout
    assert out.returncode != 0
    assert "IndexError" not in err
    assert "invalid choice" in err
    assert "boxes" in err


@pytest.mark.parametrize("extra", [
    ("--arith", "rect", "--shard"),
    ("--shard", "--arith", "rect"),
    ("--arith", "rect", "--max-bytes", "2000000"),
])
def test_sharded_rectangle_exits_clearly(extra):
    out = _cli("plan.json", "outdir", *extra)
    err = out.stderr + out.stdout
    assert out.returncode != 0
    assert "IndexError" not in err
    assert "sharded emission requires --arith ball" in err
