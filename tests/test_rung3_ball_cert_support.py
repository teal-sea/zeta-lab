"""The ball certificate support layer exposes the generator's proof combinators."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUPPORT = ROOT / "lean" / "ZetaLean" / "BallCertSupport.lean"


def test_ball_certificate_support_exports_the_required_surface():
    text = SUPPORT.read_text()
    for name in (
        "dhSumBalls",
        "contains_dhSumBalls",
        "contains_inv5sBall",
        "contains_dhBlock_of_terms_ball",
        "contains_dhAnti_of_terms_ball",
        "DH_mem_of_partial_enclosure_order2_ball",
        "norm_lt_of_ball_enclosure",
        "norm_le_of_ball_enclosure",
        "le_norm_of_ball_enclosure",
    ):
        assert f"{name}" in text
