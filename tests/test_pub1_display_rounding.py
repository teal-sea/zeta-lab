"""Regression guard for the Pub 1 manuscript's displayed certificate arithmetic.

A referee added up the four decimal upper bounds printed in the manuscript for
the terms of the ``z''`` certificate and found that they summed to
0.0060608998731, which *exceeds* the printed total bound 0.006060899845.  The
exact certificate was fine; the outward rounding was published at a precision
coarser than the certificate's own 3.63e-13 margin.

These tests assert the property that failure violated, so it cannot recur:
every printed addend is a genuine upper bound for its term, and the printed
addends sum to strictly less than the printed total.  They also check that the
downstream strict-concavity conclusion survives at *display* precision, not
merely at exact precision.

Stdlib + pytest only, in line with the repository's fast CI tier.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

certify_display = pytest.importorskip("pub1_certify_display")


@pytest.fixture(scope="module")
def built():
    return certify_display.build()


# ---------------------------------------------------------------- z'' display


def test_every_displayed_term_is_an_upper_bound(built):
    z = built["z"]
    for name, exact in z["exact"].items():
        assert z["shown"][name] >= exact, (
            f"displayed value for {name} is not an upper bound for its exact value"
        )


def test_displayed_addends_sum_strictly_below_the_printed_bound(built):
    """The exact failure the referee caught."""
    z = built["z"]
    assert z["shown_total"] < z["bound"], (
        f"printed addends sum to {z['shown_total']} which is not < {z['bound']}"
    )


def test_exact_certificate_still_holds(built):
    z = built["z"]
    assert z["exact_total"] < z["bound"]


def test_the_old_ten_decimal_display_would_now_fail(built):
    """Pin the regression itself: the published-then-corrected rounding."""
    z = built["z"]
    coarse = sum(certify_display.round_up(v, 10) for v in z["exact"].values())
    assert coarse > z["bound"], (
        "the historical 10-decimal display no longer reproduces the failure; "
        "the guard above may no longer be testing anything"
    )


def test_concavity_conclusion_survives_at_display_precision(built):
    z = built["z"]
    assert z["uSecondDerivBound"] + z["shown_total"] < z["concavity_bound"]


def test_display_precision_is_minimal(built):
    """Guards against silently inflating precision to paper over a real change."""
    z = built["z"]
    p = z["places"]
    coarser = sum(certify_display.round_up(v, p - 1) for v in z["exact"].values())
    assert coarser >= z["bound"], "a coarser display precision would also work"


# ------------------------------------------------------------- constants sync


def test_constants_are_parsed_from_the_lean_sources(built):
    """If the Lean constants move or change, this fails loudly rather than
    letting the manuscript drift away from the formalisation."""
    k = built["k"]
    assert k["residualC2"] == Fraction(6060899845, 10 ** 12)
    assert k["concavityBound"] == Fraction(-59326318, 10 ** 8)
    assert k["uSecondDerivBound"] == Fraction(-410178, 684401)


# -------------------------------------------------------------- enclosures


def test_enclosure_digit_count_matches_what_the_manuscript_claims(built):
    e = built["e"]
    assert e["H_digits"] == 17, "manuscript claims 17 certified decimals for H*"
    assert e["D_digits"] == 17
    assert e["c_digits"] == 17


def test_H_upper_is_below_the_wu_benchmark(built):
    e = built["e"]
    assert e["H_upper"] < e["target"]


def test_distinct_ceiling_is_half_of_one_plus_H(built):
    e = built["e"]
    assert e["D_lower"] == (1 + e["H_lower"]) / 2
    assert e["D_upper"] == (1 + e["H_upper"]) / 2


# ------------------------------------------------- source comparison values


def test_flat_and_quartic_reproduce_the_source_constants(built):
    """[7, Remark 7.1] reports 0.85838 / 0.92919 flat and 0.86864 / 0.93432
    quartic.  Our functional must reproduce them to the displayed precision."""
    for key, h_src, d_src in (("flat", "0.85838", "0.92919"),
                              ("quart", "0.86864", "0.93432")):
        d = built[key]
        h_lo = certify_display.round_down(d["H"], 5)
        d_lo = certify_display.round_down(d["D"], 5)
        assert h_lo == Fraction(h_src), f"{key}: H rounds to {h_lo}, source says {h_src}"
        assert d_lo == Fraction(d_src), f"{key}: D rounds to {d_lo}, source says {d_src}"


def test_quartic_gaps_match_the_manuscript_claims(built):
    assert built["gap_simple"] < Fraction(1, 10 ** 6)
    assert built["gap_distinct"] < Fraction(5, 10 ** 7)
    # and they are not vacuously small
    assert built["gap_simple"] > Fraction(9, 10 ** 7)
    assert built["gap_distinct"] > Fraction(4, 10 ** 7)


# --------------------------------------------- manuscript gap display pair


def test_gap_display_pair_is_consistent_and_bounding(built):
    """The manuscript prints one pair of quartic-to-ceiling gaps. They must be
    upper bounds for the exact gaps, and must preserve the exact identity
    gap_D = gap_H / 2 at display precision, so the paper cannot print a pair
    that fails a reader's halving check."""
    gh, gd = built["gap_simple_display"], built["gap_distinct_display"]
    assert gh >= built["gap_simple"]
    assert gd >= built["gap_distinct"]
    assert gd == gh / 2
    assert built["gap_distinct"] == built["gap_simple"] / 2


def test_gap_display_matches_the_values_printed_in_the_manuscript(built):
    assert certify_display.sci(built["gap_simple_display"], 4) == "9.854e-7"
    assert certify_display.sci(built["gap_distinct_display"], 4) == "4.927e-7"


# ------------------------------------------- outward-rounded directional decimals


def test_negative_upper_bound_is_not_rounded_to_nearest(built):
    """The exact defect: uSecondDerivBound = -410178/684401 has exact value
    -0.599324080473289781867..., and round-to-nearest at 18 places yields
    -0.599324080473289782, which is BELOW it and therefore not a valid upper
    bound.  A negative upper bound must round toward +infinity."""
    z = built["z"]
    exact = z["uSecondDerivBound"]
    assert exact == Fraction(-410178, 684401)
    places = z["conc_places"]

    shown = z["u_display"]
    assert shown >= exact, (
        f"displayed u'' bound {shown} is not an upper bound for {exact}"
    )

    # the historical bug, pinned so it cannot silently return
    from decimal import Decimal, localcontext
    with localcontext() as ctx:
        ctx.prec = 60
        nearest = Fraction(
            f"{Decimal(exact.numerator) / Decimal(exact.denominator):.{places}f}"
        )
    assert nearest < exact, "round-to-nearest no longer reproduces the defect"
    assert shown != nearest, "the displayed value is still the round-to-nearest one"


def test_dec_up_and_dec_down_are_outward_for_negatives_and_positives():
    up, down = certify_display.dec_up, certify_display.dec_down
    for x in (Fraction(-410178, 684401), Fraction(410178, 684401),
              Fraction(-1, 3), Fraction(1, 3), Fraction(-59326318, 10 ** 8)):
        for places in (2, 8, 18):
            assert Fraction(up(x, places)) >= x, f"dec_up({x},{places}) not >= x"
            assert Fraction(down(x, places)) <= x, f"dec_down({x},{places}) not <= x"


def test_printed_concavity_chain_is_valid_and_self_consistent(built):
    """Each printed decimal is a valid bound in its direction, the printed
    conclusion is the exact sum of the printed summands, and the printed chain
    is strict -- so a reader adding the printed numbers reaches the printed
    result and the true statement follows."""
    z = built["z"]
    assert z["u_display"] >= z["uSecondDerivBound"]
    assert z["shown_total"] >= z["exact_total"]
    assert z["lhs_display"] == z["u_display"] + z["shown_total"]
    assert z["lhs_display"] >= z["concavity_lhs"]
    assert z["bound_display"] <= z["concavity_bound"]
    assert z["lhs_display"] < z["bound_display"]


def test_enclosure_endpoints_are_rounded_outward(built):
    """L <= c* <= U printed at 20 places must not narrow the interval."""
    e = built["e"]
    for lo_key, hi_key in (("c_lower", "c_upper"), ("H_lower", "H_upper"),
                           ("D_lower", "D_upper")):
        lo, hi = e[lo_key], e[hi_key]
        assert Fraction(certify_display.dec_down(lo, 20)) <= lo, lo_key
        assert Fraction(certify_display.dec_up(hi, 20)) >= hi, hi_key
