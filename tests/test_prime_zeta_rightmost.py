"""Pins for every number stated in docs/28-prime-zeta-rightmost-zeros.md.

Two kinds of pin, matching how the doc sources its figures:

* the decided constants and sign decisions are *recomputed* here through the
  hunt's own instrument (`hunts/prime_zeta_rightmost/instrument.py`) on the
  flint (arb) leg at a reduced working precision (120 bits instead of the
  hunt's 350), against loose hardcoded brackets and the digit prefixes the
  doc prints. Reduced precision keeps every test cheap; the hunt's own
  precision-response control (`controls_results.json`) shows the 120-bit run
  of the same code path reaches width ~6e-34, far below what these pins need;
* the figures the doc quotes from the hunt's recorded artifacts (screen
  minima, heuristic expected heights, control verdicts, backend widths) are
  checked against those JSON records, so the doc cannot drift from the
  record it summarizes.

Vocabulary as in the hunt's contract: decided means an interval or ball
enclosure whose exact rational endpoints settle a sign. The bisection
bookkeeping is exact Fractions, so a pin here is a sign decision at 120
bits, not a float comparison.
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from math import floor
from pathlib import Path

import pytest

flint = pytest.importorskip(
    "flint", reason="python-flint is pinned in requirements.txt; the hunt's flint leg needs it"
)
import mpmath  # noqa: E402

HUNT = Path(__file__).resolve().parents[1] / "hunts" / "prime_zeta_rightmost"
sys.path.insert(0, str(HUNT))

import decide  # noqa: E402
import instrument  # noqa: E402

DOC = Path(__file__).resolve().parents[1] / "docs" / "28-prime-zeta-rightmost-zeros.md"

PREC_BITS = 120
K = 120
MU = instrument.mobius_sieve(K + 1)
TARGET = Fraction(1, 10**32)

# The digit prefixes the doc states (31 digits for the two headline
# constants, matching the "digits on which both enclosure endpoints agree"
# convention of the hunt's 350-bit run; 17 for sigma_3).
SIGMA_C_PREFIX = "1779544653546994116445898786965"
X_STAR_PREFIX = "1728647238998183618135103010297"
SIGMA_3_PREFIX = "18252259560738457"


def _with_prec(bits: int, fn):
    """Run fn with flint.ctx.prec set to bits, restoring the old value."""
    old = flint.ctx.prec
    flint.ctx.prec = bits
    try:
        return fn()
    finally:
        flint.ctx.prec = old


def _prefix_agrees(lo: Fraction, hi: Fraction, prefix: str) -> bool:
    """Both endpoints share the decimal expansion `prefix` (one integer
    digit, the rest decimal places). Exact integer arithmetic."""
    scale = 10 ** (len(prefix) - 1)
    return floor(lo * scale) == floor(hi * scale) == int(prefix)


def _bisect_arb(f_arb, lo, hi, target=TARGET):
    def f(q: Fraction):
        return instrument.arb_endpoints(f_arb(instrument.arb_from_fraction(q)))

    r = instrument.bisect_decreasing(f, Fraction(*lo), Fraction(*hi), target)
    assert not r["sign_stalled"], "sign stalled before the target width at 120 bits"
    return r["lo"], r["hi"]


# ----------------------------------------------------------------------
# recomputed enclosures, shared across tests
# ----------------------------------------------------------------------


@pytest.fixture(scope="module")
def sigma_c_interval():
    """sigma_c re-decided at 120 bits through the hunt's own h(s) machinery."""
    return _with_prec(
        PREC_BITS, lambda: _bisect_arb(lambda s: instrument.h_arb(s, K, MU), (17, 10), (19, 10))
    )


@pytest.fixture(scope="module")
def x_star_interval():
    """x* re-decided at 120 bits: bisection on zeta(x) - 2 with arb zeta."""
    return _with_prec(
        PREC_BITS, lambda: _bisect_arb(lambda s: flint.arb.zeta(s) - 2, (17, 10), (18, 10))
    )


@pytest.fixture(scope="module")
def sigma_3_interval():
    """sigma_3 re-decided at 120 bits through the hunt's u(s) machinery."""
    return _with_prec(
        PREC_BITS,
        lambda: _bisect_arb(
            lambda s: instrument.u_arb(s, K, MU), (9, 5), (37, 20), Fraction(1, 10**25)
        ),
    )


# ----------------------------------------------------------------------
# (a) sigma_c
# ----------------------------------------------------------------------


def test_sigma_c_enclosure_and_decided_digits(sigma_c_interval):
    lo, hi = sigma_c_interval
    assert Fraction("1.77954465") <= lo and hi <= Fraction("1.77954466")
    assert _prefix_agrees(lo, hi, SIGMA_C_PREFIX)


def test_sigma_c_window_compares(sigma_c_interval):
    """W2, W3, W4 of theorem_inputs.json, re-decided from the 120-bit run."""
    lo, hi = sigma_c_interval
    assert lo > Fraction(7, 4)
    assert lo > Fraction(177, 100)
    assert hi < Fraction(89, 50)


# ----------------------------------------------------------------------
# (b) x* and the calibration control
# ----------------------------------------------------------------------


def test_x_star_enclosure_and_decided_digits(x_star_interval):
    lo, hi = x_star_interval
    assert Fraction("1.72864723") <= lo and hi <= Fraction("1.72864724")
    assert _prefix_agrees(lo, hi, X_STAR_PREFIX)
    assert hi < Fraction(173, 100)  # W1: any zero with Re s >= 1.73 exceeds x*


def test_calibration_same_solver_reproduces_partial_sums_constant():
    """The doc's section 6: the solver object decide.py uses, pointed at the
    zeta-partial-sums balance (leading term 1 against sum_{n>=2} n^(-s)),
    reproduces the Borwein-Fee-Ferguson-van der Waall constant to 31 digits
    of the OEIS A107311 expansion. Cheap version of the WP5 control."""
    assert decide.bisect_decreasing is instrument.bisect_decreasing
    assert len(decide.OEIS_DIGITS) == 102
    lo, hi = _with_prec(
        PREC_BITS,
        lambda: _bisect_arb(lambda s: (flint.arb.zeta(s) - 1) - 1, (17, 10), (19, 10)),
    )
    assert _prefix_agrees(lo, hi, decide.OEIS_DIGITS[:31])


# ----------------------------------------------------------------------
# (c) separation and margin, as sign decisions
# ----------------------------------------------------------------------


def test_separation_sigma_c_minus_x_star_exceeds_one_twentieth(sigma_c_interval, x_star_interval):
    sep_lo = sigma_c_interval[0] - x_star_interval[1]
    sep_hi = sigma_c_interval[1] - x_star_interval[0]
    assert sep_lo > Fraction(1, 20)
    # the doc states the difference as 0.0508974145...
    assert sep_lo > Fraction("0.0508974145")
    assert sep_hi < Fraction("0.0508974146")


def test_margin_h_at_x_star_exceeds_one_sixtieth(x_star_interval):
    def run():
        ball = instrument.arb_interval(*x_star_interval)
        return instrument.arb_endpoints(instrument.h_arb(ball, K, MU))

    lo, hi = _with_prec(PREC_BITS, run)
    assert lo > Fraction(1, 60)
    # the doc states the value as 0.0169073772138...
    assert Fraction("0.0169073772138") < lo and hi < Fraction("0.0169073772139")


# ----------------------------------------------------------------------
# (d) sigma_3
# ----------------------------------------------------------------------


def test_sigma_3_enclosure_and_decided_digits(sigma_3_interval):
    lo, hi = sigma_3_interval
    assert Fraction("1.82522") <= lo and hi <= Fraction("1.82523")
    assert _prefix_agrees(lo, hi, SIGMA_3_PREFIX)
    assert lo > Fraction(91, 50)  # W5: the window (1.78, 1.82) sits below sigma_3


def test_subset_wall_exceeds_full_series_wall(sigma_c_interval, sigma_3_interval):
    """The doc's subset gap: sigma_3 - sigma_c > 0.0456813, decided."""
    assert sigma_3_interval[0] - sigma_c_interval[1] > Fraction("0.0456813")


# ----------------------------------------------------------------------
# ring margins D1, D2 (Theorem B / C1 instances)
# ----------------------------------------------------------------------


def test_ring_margins_d1_and_d2():
    def run():
        d1 = instrument.arb_endpoints(
            instrument.h_arb(instrument.arb_from_fraction(Fraction(7, 4)), K, MU)
        )
        d2 = instrument.arb_endpoints(
            instrument.u_arb(instrument.arb_from_fraction(Fraction(9, 5)), K, MU)
        )
        return d1, d2

    (d1_lo, d1_hi), (d2_lo, d2_hi) = _with_prec(PREC_BITS, run)
    # D1: h(7/4) = 0.0094656372937... > 1/128
    assert d1_lo > Fraction(1, 128)
    assert Fraction("0.0094656372937") < d1_lo and d1_hi < Fraction("0.0094656372938")
    # D2: u(9/5) = 0.0043124917294... > 1/256
    assert d2_lo > Fraction(1, 256)
    assert Fraction("0.0043124917294") < d2_lo and d2_hi < Fraction("0.0043124917295")


# ----------------------------------------------------------------------
# (e) the C2 instance, decided on both backends
# ----------------------------------------------------------------------


def test_c2_instance_wall_of_p_ge_23_exceeds_17_eighths():
    """D3: log2(69/(5 log 23)) = 2.1379035036560028... > 17/8, on both the
    arb leg and the mpmath.iv leg (direct interval arithmetic, no series)."""

    def run():
        a = flint.arb
        val = (a(69) / (5 * a(23).log())).log() / a(2).log()
        return instrument.arb_endpoints(val)

    lo, hi = _with_prec(PREC_BITS, run)
    assert lo > Fraction(17, 8)
    assert Fraction("2.1379035036560028") < lo and hi < Fraction("2.1379035036560029")

    iv = mpmath.iv
    old_dps = iv.dps
    iv.dps = 40
    try:
        val = iv.log(iv.mpf(69) / (5 * iv.log(iv.mpf(23)))) / iv.log(iv.mpf(2))
        ilo, ihi = instrument.iv_endpoints(val)
    finally:
        iv.dps = old_dps
    assert ilo > Fraction(17, 8)
    assert Fraction("2.1379035036560028") < ilo and ihi < Fraction("2.1379035036560029")


# ----------------------------------------------------------------------
# the doc's remaining figures, pinned against the hunt's recorded artifacts
# ----------------------------------------------------------------------


def _load(name: str) -> dict:
    with open(HUNT / name, encoding="utf-8") as fh:
        return json.load(fh)


def test_doc_constants_match_decided_json():
    decided = _load("decided.json")
    consts = decided["constants"]

    for key, prefix in (
        ("x_star", "1.728647238998183618135103010297"),
        ("sigma_c", "1.779544653546994116445898786965"),
        ("sigma_3", "1.8252259560738457"),
    ):
        rec = consts[key]["flint"]
        assert rec["interval"][0].startswith(prefix)
        assert rec["interval"][1].startswith(prefix)
        assert rec["width"] == "7.889e-32"
        assert rec["precision"] == "350 bits"

    assert consts["x_star"]["mpmath_iv"]["width"] == "8.882e-17"
    assert consts["sigma_c"]["mpmath_iv"]["width"] == "9.095e-14"
    assert consts["sigma_3"]["mpmath_iv"]["width"] == "9.313e-11"
    for key in ("x_star", "sigma_c", "sigma_3"):
        assert consts[key]["cross_checks"]["flint_interval_inside_iv_interval"] is True
    assert consts["x_star"]["cross_checks"]["oeis_value_interval_inside_flint_interval"] is True
    assert consts["x_star"]["cross_checks"]["oeis_value_interval_inside_iv_interval"] is True

    assert all(decided["preregistered_checks"].values())

    sep = decided["decisions"]["separation_sigma_c_minus_x_star_gt_1_over_20"]
    assert sep["flint"]["decided"] is True and sep["mpmath_iv"]["decided"] is True
    assert sep["flint"]["lower_bound_of_difference"].startswith("0.05089741454881")

    margin = decided["decisions"]["margin_P_at_x_star_minus_2_pow_1_minus_x_star_gt_1_over_60"]
    assert margin["flint"]["decided"] is True and margin["mpmath_iv"]["decided"] is True
    assert margin["flint"]["h_enclosure"][0].startswith("0.016907377213856")


def test_doc_theorem_inputs_match_record():
    ti = _load("theorem_inputs.json")
    d = ti["decisions"]
    assert d["D1_h_at_7_over_4_gt_1_over_128"]["flint"]["interval"][0].startswith(
        "0.009465637293734518"
    )
    assert d["D2_u_at_9_over_5_gt_1_over_256"]["flint"]["interval"][0].startswith(
        "0.004312491729413063"
    )
    assert d["D3_log2_69_over_5log23_gt_17_over_8"]["flint"]["interval"][0].startswith(
        "2.137903503656002856"
    )
    for key in d:
        assert d[key]["flint"]["decided"] is True
        assert d[key]["mpmath_iv"]["decided"] is True
    for name, row in ti["window_comparisons"].items():
        if name == "note":
            continue
        assert row["flint"] is True and row["mpmath_iv"] is True
    assert ti["all_decided"] is True


def test_doc_control_figures_match_record():
    controls = _load("controls_results.json")
    cal = controls["calibration_zeta_partial_sums"]
    assert cal["oeis_digits_reproduced_flint"] == 31
    assert cal["oeis_digits_reproduced_iv"] == 13
    assert cal["pass"] is True

    les1 = controls["lesion_1_drop_p3_from_tail"]
    assert les1["flint"]["interval"][0].startswith("1.42931613566780")
    assert les1["shift_from_sigma_c"]["interval"][0].startswith("0.35022851787919")
    assert les1["pass"] is True

    les2 = controls["lesion_2_wrong_leading_term"]
    assert les2["flint"]["interval"][0].startswith("2.42411125091340")
    assert les2["pass"] is True

    prec = controls["precision_response_sigma_c"]
    widths = [run["achieved_width"] for run in prec["runs"]]
    assert widths == ["1.421e-15", "6.163e-34", "1.020e-57"]
    assert prec["strictly_shrinking"] is True

    assert controls["decide_rerun_reproducibility"]["identical_outside_time_s"] is True
    assert controls["summary"]["overall"] == "PASS"


def test_doc_witness_figures_match_record():
    witness = _load("witness_results.json")

    margin = witness["margin_analysis"]["flint"]
    assert margin["eps0_budget_R_minus_r2"]["interval"][0].startswith("0.00946563729373")
    assert margin["R_total_modulus_p_ge_3"]["interval"][0].startswith("0.306767416044")
    assert margin["r2"]["interval"][0].startswith("0.297301778750")

    expected = witness["expected_t"]
    assert expected["grade"].startswith("heuristic")
    assert expected["on_line_sigma1_budget_eps0"] == 1.6376823600773134e16
    assert expected["window_wide_budget_h_at_x_star"] == 16851710604.191057

    screen = witness["screen"]
    assert screen["coverage"]["t_range"] == [0.0, 1e8]
    assert screen["candidate_threshold_absP"] == 0.0001
    assert screen["candidates_found"] == 0
    gmin = witness["screen"]["global_min_refined"]
    assert gmin["absP_head_1e6"] == 0.010021062926148282
    assert gmin["t"] == 56316681.50996085

    assert witness["box_counter"]["both_controls_pass"] is True
    assert witness["verdict"]["witness_decided_exists"] is False
    assert witness["verdict"]["P4_outcome"].startswith("confirmed")


def test_doc_quotes_the_pinned_conjecture_text_verbatim():
    """The doc's section 1 quote must match SOURCE.md's pinned bytes: the
    refutation attacks the served words, not a paraphrase, and so must the
    reading-course page."""
    lines = (
        "From _Artur Jasinski_, Dec 21 2024: (Start)",
        "Borwein et al. (2007) proved (Theorem 3.1) that the real parts of the "
        "zeros of the partials sums of the Riemman zeta functions are not "
        "greater than this constant.",
        "Conjecture 1: the real parts of the zeros of the prime zeta function "
        "are not greater than this constant.",
        "Conjecture 2: the real parts of the zeros of the anyone subset of the "
        "prime zeta function are not greater than this constant. (End)",
    )
    doc = DOC.read_text(encoding="utf-8")
    source = (HUNT / "SOURCE.md").read_text(encoding="utf-8")
    for line in lines:
        assert line in doc, f"doc dropped or altered the quoted line: {line!r}"
        assert line in source, f"quote not pinned in SOURCE.md: {line!r}"
