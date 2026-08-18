"""WP4: the control battery for the lambda_dh_bounds hunt.

Five controls.  Four are the pre-registered MISSION.md WP4 battery; the
fifth was added on 2026-08-16 as gate closure item (c), because the gate
found that the single load-bearing analytic step no control touched was
also the one whose health metric moves the wrong way when it breaks.  All
five run against the route-1 machinery (``winding.py``) and the ball
instrument (``instrument.py``), imported and never duplicated.

Read control 5 before reading the verdicts: it does not pass, it is not
meant to pass, and it is recorded as a named blind spot rather than
quietly repaired.  ``all_pass`` is therefore False from 2026-08-16
onward, and ``controls_1_to_4_pass`` carries the older statement
unchanged.

1. LESION, mis-centred box: the route-1 winding on a same-size rectangle
   displaced by +2 in Re (empty per the measured census of the
   neighbourhood; the decided N = 0 is itself the statement that it is
   empty).  The detector must tell empty from occupied: N = 0 decided.

2. LESION, box edge on a zero: (a) a box with y_lo = 0 (bottom edge on the
   real axis, where the argument-principle hypothesis "H never vanishes on
   the boundary" cannot be pre-checked and the mirror-symmetry framing
   collapses) must fail loudly before any arithmetic; (b) a box whose top
   edge passes through the measured pair-5 zero (y_hi set to the bit-exact
   float of the measured Im, within ~2e-18 of the true zero) must return
   status "undecided", never an integer.

3. PRECISION RESPONSE: at one fixed boundary point the H_ball radius must
   shrink strictly as prec rises 320 -> 420 -> 520, by a large factor per
   step; the winding N ball width must likewise shrink across precisions.

4. ARTIFACT CHECK (the standing rule: an artifact does not respond to
   precision, MISSION.md kill condition 3): at fixed box geometry the
   route-1 minimum ball sign margin must GROW in digits as prec rises.
   The chord-tube margin is excluded by design: adaptive subdivision stops
   at the first decided pass, so that margin measures the stopping rule,
   not the instrument.

5. LESION, M2 deflated (added 2026-08-16, gate closure item c): M2, the
   uniform bound on |H_t''| that makes every chord-tube decision a
   decision, is divided by a factor and the route-1 winding re-run on the
   unchanged t1 geometry.  A detector that could see this lesion would
   refuse.  It does not: at factor 100 it returns status "decided" with
   the WRONG integer N = 0 after four segments, and reports
   ``min_chord_margin_digits`` = 0.11 against the correct run's 0.02, so
   its own health metric looks five times better while the answer is
   wrong.  Recorded as a blind spot with its numbers, not repaired.

Plus the two no-compute notes MISSION.md WP4 asks for: the rival framing
(zeta gets no positive floor from this pipeline) and the battery
non-applicability note.

Vocabulary per MISSION.md: decided quantities are Arb balls with backend
and precision stated; everything float-grade is labelled measured.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from flint import acb  # noqa: E402,F401  (backend presence check)

from instrument import H_ball, _prec_guard  # noqa: E402
from winding import (  # noqa: E402
    BACKEND,
    _fr_str,
    measured_h2_guard,
    second_derivative_bound,
    winding_rectangle,
)

RESULTS_PATH = os.path.join(HERE, "controls_results.json")
WINDING_PATH = os.path.join(HERE, "winding_results.json")

PRECS = (320, 420, 520)


def _load_t1_geometry() -> dict:
    """The route-1 t1 box and measured zero, read from winding_results.json.

    The box is the exact-dyadic rectangle route 1 decided N = 1 on; reusing
    it byte-for-byte is what makes the lesions lesions (same detector, same
    geometry, one deliberate change each).
    """
    with open(WINDING_PATH) as f:
        w = json.load(f)
    b = w["t1_run"]["box"]
    loc = w["locating_pass_measured"]["0.0575"]
    return {
        "t": Fraction(w["t1_run"]["t"]),
        "box": (
            Fraction(b["re_lo"]),
            Fraction(b["re_hi"]),
            Fraction(b["im_lo"]),
            Fraction(b["im_hi"]),
        ),
        "zstar_re_measured": loc["zstar_re"],
        "zstar_im_measured": loc["zstar_im"],
        "reference_min_ball_margin_digits": w["t1_run"]["min_ball_margin_digits"],
        "reference_N": w["t1_run"].get("N"),
    }


def _strip_segments(res: dict) -> dict:
    """The winding result without its per-segment table (kept small here;
    the full table convention lives in winding_results.json)."""
    return {k: v for k, v in res.items() if k != "segments"}


def _ball_radius(ball) -> float:
    """max over components of the half-width of the ball (same convention
    as winding.py's ball-margin computation)."""
    return max(
        float((ball.real.upper() - ball.real.lower()) / 2),
        float((ball.imag.upper() - ball.imag.lower()) / 2),
    )


# ---------------------------------------------------------------------------
# control 1: lesion, mis-centred box
# ---------------------------------------------------------------------------


def lesion_displaced(geom: dict, prec: int = 420) -> dict:
    """Same-size rectangle displaced by +2 in Re: must decide N = 0.

    The measured census (flow_repair quadruple table and the locating pass:
    single Newton basin at Re ~ 240.345, no real-axis sign changes within
    +/- 0.7) puts no zero of H_t1 in the displaced window; the decided
    N = 0 is the enclosure-grade confirmation that the detector tells empty
    from occupied rather than manufacturing its expected answer.
    """
    x_lo, x_hi, y_lo, y_hi = geom["box"]
    box = (x_lo + 2, x_hi + 2, y_lo, y_hi)
    m2 = second_derivative_bound(box[0], y_hi, geom["t"], prec=300)
    res = winding_rectangle(box, geom["t"], prec, m2)
    passed = res["status"] == "decided" and res.get("N") == 0
    return {
        "expectation": "N = 0 decided (empty box, detector tells empty from occupied)",
        "displacement_re": "+2",
        "result": _strip_segments(res),
        "verdict": "PASS" if passed else "FAIL",
    }


# ---------------------------------------------------------------------------
# control 2: lesion, boundary on a zero
# ---------------------------------------------------------------------------


def lesion_on_axis(geom: dict, prec: int = 420, m2: dict | None = None) -> dict:
    """y_lo = 0: the machinery must fail loudly, before any arithmetic."""
    x_lo, x_hi, _y_lo, y_hi = geom["box"]
    box = (x_lo, x_hi, Fraction(0), y_hi)
    if m2 is None:
        m2 = second_derivative_bound(x_lo, y_hi, geom["t"], prec=300)
    try:
        res = winding_rectangle(box, geom["t"], prec, m2)
    except ValueError as e:
        return {
            "expectation": "loud failure or undecided, never an integer",
            "box_im_lo": "0",
            "failure_mode": (
                "ValueError raised by the box validator before any H "
                "evaluation (n_H_evals = 0)"
            ),
            "exception_message": str(e),
            "verdict": "PASS",
        }
    return {
        "expectation": "loud failure or undecided, never an integer",
        "box_im_lo": "0",
        "failure_mode": "NONE: an integer or a quiet result came back",
        "result": _strip_segments(res),
        "verdict": "FAIL" if res.get("N") is not None else "PASS",
    }


def lesion_edge_through_zero(geom: dict, prec: int = 420,
                             m2: dict | None = None) -> dict:
    """Top edge through the measured zero: must return undecided.

    y_hi is set to the bit-exact dyadic of the measured Im(z*) (float of
    the dps-112 Newton value, so the edge passes within ~2e-18 of the true
    zero; measured).  Near the crossing, |H| on the edge falls below the
    chord-tube threshold at every subdividable scale (dist(0, chord) ~
    |H'| * 2e-18 ~ 6e-100 against tube M2 h^2 / 2 ~ 6e-79 h^2, so decision
    would need h < ~4e-11, far below any sane floor), and the routine's
    contract is to return status "undecided" naming the failing segment,
    never an integer.  min_halflen is set to 1/2^18 to cap the cost of
    watching it fail.
    """
    x_lo, x_hi, y_lo, _y_hi = geom["box"]
    y_star = Fraction(geom["zstar_im_measured"])  # bit-exact dyadic of the float
    box = (x_lo, x_hi, y_lo, y_star)
    if m2 is None:
        m2 = second_derivative_bound(x_lo, geom["box"][3], geom["t"], prec=300)
    res = winding_rectangle(
        box, geom["t"], prec, m2,
        min_halflen=Fraction(1, 2 ** 18),
        max_segments=3000,
        max_wall=420.0,
    )
    passed = res["status"] == "undecided" and res.get("N") is None
    return {
        "expectation": "undecided, never an integer",
        "box_im_hi": _fr_str(y_star),
        "box_im_hi_float": float(y_star),
        "edge_to_zero_distance_measured": "~2e-18 (float rounding of the dps-112 Newton value)",
        "m2_note": (
            "M2 bound reused from the parent geometry (scope Re z >= x_lo, "
            "|Im z| <= 61/1024 covers this smaller box)"
        ),
        "failure_mode": (res.get("failure") or {}).get("reason"),
        "result": _strip_segments(res),
        "verdict": "PASS" if passed else "FAIL",
    }


# ---------------------------------------------------------------------------
# control 3: precision response
# ---------------------------------------------------------------------------


def precision_response_point(geom: dict) -> dict:
    """H_ball radius at one fixed boundary point across PRECS.

    The point is the box's lower-left corner (an exact dyadic on the
    route-1 boundary).  The radii must be strictly decreasing with a
    factor > 1e10 per 100-bit step (1e10 is far below the ~1e30 a 100-bit
    step should buy; the loose gate keeps the control about response, not
    about the constant).
    """
    x_lo, _x_hi, y_lo, _y_hi = geom["box"]
    point = (x_lo, y_lo)
    radii: dict[str, float] = {}
    absH: dict[str, float] = {}
    for prec in PRECS:
        ball = H_ball(point, geom["t"], prec)
        # readout inside a guard at the SAME precision: upper()/lower() round
        # at the ambient ctx.prec, and a coarse readout would flatten the
        # radius to the midpoint's rounding granularity (observed before this
        # guard was added: 420 and 520 read out identically)
        with _prec_guard(prec):
            radii[str(prec)] = _ball_radius(ball)
            absH[str(prec)] = float(abs(ball).lower())
    ratios = {
        f"{a}->{b}": radii[str(a)] / radii[str(b)]
        for a, b in zip(PRECS, PRECS[1:])
    }
    passed = all(r > 1e10 for r in ratios.values()) and all(
        radii[str(a)] > radii[str(b)] for a, b in zip(PRECS, PRECS[1:])
    )
    return {
        "point": [_fr_str(point[0]), _fr_str(point[1])],
        "t": _fr_str(geom["t"]),
        "backend": BACKEND,
        "H_ball_radius_by_prec": radii,
        "absH_lower_by_prec": absH,
        "shrink_factors": ratios,
        "expectation": "strictly decreasing, factor > 1e10 per 100-bit step",
        "verdict": "PASS" if passed else "FAIL",
    }


def winding_across_precisions(geom: dict) -> dict:
    """The route-1 winding at fixed geometry across PRECS.

    Feeds both control 3 (the N ball width must shrink) and control 4 (the
    minimum ball sign margin must grow in digits; a stuck margin marks the
    instrument as the artifact, MISSION.md kill condition 3).
    """
    x_lo, _x_hi, _y_lo, y_hi = geom["box"]
    m2 = second_derivative_bound(x_lo, y_hi, geom["t"], prec=300)
    runs: dict[str, dict] = {}
    for prec in PRECS:
        res = winding_rectangle(geom["box"], geom["t"], prec, m2)
        entry = _strip_segments(res)
        if "winding_sum_over_2pi" in res:
            entry["N_ball_width"] = res["winding_sum_over_2pi"]["width"]
        runs[str(prec)] = entry
    return {"m2_prec_bits": 300, "runs": runs}


def assess_precision_winding(runs: dict) -> dict:
    """Control 3b: N ball width shrinks across precisions."""
    widths = {p: runs["runs"][p].get("N_ball_width") for p in map(str, PRECS)}
    ok = all(w is not None and w > 0 for w in widths.values())
    ratios = {}
    if ok:
        ratios = {
            f"{a}->{b}": widths[str(a)] / widths[str(b)]
            for a, b in zip(PRECS, PRECS[1:])
        }
        ok = all(r > 1e10 for r in ratios.values())
    return {
        "N_ball_width_by_prec": widths,
        "shrink_factors": ratios,
        "expectation": "strictly shrinking N ball width, factor > 1e10 per step",
        "verdict": "PASS" if ok else "FAIL",
    }


# ---------------------------------------------------------------------------
# control 4: artifact check
# ---------------------------------------------------------------------------


def assess_artifact(runs: dict) -> dict:
    """Control 4: min ball sign margin grows in digits with prec.

    A 100-bit step is ~30.1 digits; the gate asks for > 10 digits of
    growth per step, generous enough that only a genuinely stuck margin
    (an artifact) fails it.  The chord-tube margin is recorded but not
    gated: adaptive subdivision stops at the first decided pass, so that
    margin reflects the stopping rule at any precision.
    """
    margins = {
        p: runs["runs"][p].get("min_ball_margin_digits") for p in map(str, PRECS)
    }
    chord = {
        p: runs["runs"][p].get("min_chord_margin_digits") for p in map(str, PRECS)
    }
    ok = all(m is not None for m in margins.values())
    growth = {}
    if ok:
        growth = {
            f"{a}->{b}": round(margins[str(b)] - margins[str(a)], 2)
            for a, b in zip(PRECS, PRECS[1:])
        }
        ok = all(g > 10 for g in growth.values())
    return {
        "min_ball_margin_digits_by_prec": margins,
        "margin_growth_digits": growth,
        "min_chord_margin_digits_by_prec": chord,
        "chord_margin_note": (
            "the chord-tube margin is excluded from the gate by design: "
            "adaptive subdivision stops at the first decided pass, so it "
            "measures the stopping rule, not the instrument"
        ),
        "expectation": "> 10 digits of ball-margin growth per 100-bit step "
                       "(~30 expected)",
        "verdict": "PASS" if ok else "FAIL",
    }


# ---------------------------------------------------------------------------
# control 5: lesion, M2 deflated (the recorded blind spot)
# ---------------------------------------------------------------------------


DEFLATION_FACTORS = (1, 10, 72, 75, 100, 1000)


def lesion_m2_deflated(geom: dict, prec: int = 420,
                       factors: tuple = DEFLATION_FACTORS) -> dict:
    """Divide M2 by a factor and re-run the route-1 winding: what breaks, and how.

    M2 is the uniform bound for |H_t''| over the box.  It enters exactly
    one place, the chord tube of radius M2 h^2 / 2 that a segment's image
    must clear before its argument increment is accepted, so a wrongly
    SMALL M2 accepts segments whose true argument variation may exceed pi,
    and the per-segment congruence Delta == Arg q (mod 2pi) is then
    resolved to the wrong branch.  Deflation is the honest lesion for it:
    the derivation in ``winding.py`` was prose when this control was
    written, and prose is what an error would live in.

    Updated 2026-08-18.  ``M2-LEMMA.md`` proves the bound, with every
    constant a reported ball and every hypothesis a decided predicate, so
    the lesion no longer stands in for "the derivation might be wrong".
    It now stands in for "the implementation might be wrong", which is a
    narrower and still live risk, and the rows are unchanged.

    Everything else is held fixed: the same t1 box the route decided N = 1
    on, the same precision, the same instrument, the same subdivision
    rule.  Only the number M2 changes.

    The M2 guard (``winding.measured_h2_guard``) is evaluated against each
    deflated M2 too, so the table shows which lesions the cheap necessary
    check would have caught.  It is measured once, on the honest M2, and
    then compared arithmetically per factor: the measured sup of |H_t''|
    does not depend on M2.

    This control does not pass and is not meant to.  Its verdict was
    "BLIND SPOT" through 2026-08-17 and is "SENSITIVITY MEASURED (not a
    pass)" from 2026-08-18; its output is a map of the failure either way,
    in the repo's habit of pinning a weakness where it is.
    """
    t0 = time.time()
    m2_honest = second_derivative_bound(geom["box"][0], geom["box"][3],
                                        geom["t"], prec=300)
    guard = measured_h2_guard(m2_honest, geom["box"], geom["t"])
    measured_sup = guard["measured_sup_absH2"]

    rows = []
    for factor in factors:
        with _prec_guard(300):
            lesioned = dict(m2_honest)
            lesioned["M2"] = m2_honest["M2"] / factor
            lesioned["M2_upper_float"] = float(lesioned["M2"].abs_upper())
        res = winding_rectangle(geom["box"], geom["t"], prec, lesioned)
        rows.append({
            "deflation_factor": factor,
            "M2_upper_float": lesioned["M2_upper_float"],
            "status": res["status"],
            "N": res.get("N"),
            "N_correct": res.get("N") == geom["reference_N"],
            "n_segments": res["n_segments"],
            "min_chord_margin_digits": res.get("min_chord_margin_digits"),
            "min_ball_margin_digits": res.get("min_ball_margin_digits"),
            "failure_reason": (res.get("failure") or {}).get("reason"),
            "m2_guard_verdict": (
                "PASS" if lesioned["M2_upper_float"] >= measured_sup else "FAIL"
            ),
        })

    wrong = [r for r in rows if r["status"] == "decided" and not r["N_correct"]]
    silent_wrong = [r for r in wrong if r["failure_reason"] is None]
    caught = [r for r in wrong if r["m2_guard_verdict"] == "FAIL"]
    onset = min((r["deflation_factor"] for r in wrong), default=None)

    return {
        "expectation_as_written": (
            "a detector that could see this lesion would refuse (status "
            "undecided), never return an integer"
        ),
        "observed": (
            "it returns integers.  Deflating M2 by 100 gives status "
            "'decided' with N = 0 after four segments, and it is not the "
            "quiet kind of wrong: min_chord_margin_digits reads 0.11 "
            "against the correct run's 0.02, so the routine's own health "
            "metric looks about five times better while the answer is "
            "wrong."
        ),
        "held_fixed": (
            "t1 box, t = 23/400, prec 420, instrument, subdivision rule; "
            "only the number M2 is changed"
        ),
        "reference_N": geom["reference_N"],
        "what_this_table_measures": (
            "Through 2026-08-17 this table recorded the exposure of an "
            "unproven assumption: M2 was prose, and the rows showed what a "
            "wrong M2 buys.  From 2026-08-18 M2 is a proved lemma "
            "(M2-LEMMA.md), so the same rows measure something narrower and "
            "still worth knowing: the detector's sensitivity to a corrupted "
            "M2, that is, to an implementation fault in "
            "winding.second_derivative_bound.  The numbers are unchanged and "
            "the detector is still unable to see the lesion by itself, which "
            "is why the guard and its refusal path stay in place."
        ),
        "table": rows,
        "wrong_answer_onset_factor": onset,
        "n_wrong_and_silent": len(silent_wrong),
        "m2_measured_guard_on_honest_M2": guard,
        "guard_catches_all_observed_wrong_rows": bool(wrong) and len(caught) == len(wrong),
        "blind_spot": BLIND_SPOT_M2,
        "verdict": "SENSITIVITY MEASURED (not a pass)",
        "verdict_note": (
            "Not PASS: the expectation as written is still unmet, because "
            "the detector returns integers under the lesion instead of "
            "refusing.  Not BLIND SPOT either, which is what this field read "
            "through 2026-08-17: the thing it named as blind, M2's "
            "derivation, is now proved with decided constants and exercised "
            "by four routes.  See blind_spot.what_closed_it and "
            "blind_spot.what_is_still_open."
        ),
        "seconds": round(time.time() - t0, 1),
    }


BLIND_SPOT_M2 = {
    "name": (
        "closed 2026-08-18 in the form it was recorded: M2 is a proved "
        "lemma, and this table now measures the detector's sensitivity to a "
        "corrupted M2 rather than the exposure of an unproven assumption"
    ),
    "status": "CLOSED at source, NARROWED residual named below",
    "what_was_blind": (
        "Through 2026-08-17: M2, the uniform bound for |H_t''| on the box, "
        "was the single load-bearing analytic step in the lower-bound route "
        "whose derivation was prose rather than an enclosure or a cited "
        "theorem (its numerical ingredients were ball-computed; the "
        "shifted-contour argument that assembles them was not), and it was "
        "exercised by no cross-route.  Controls 1 to 4 do not touch it: the "
        "displaced and edge-on-zero lesions move geometry, the precision "
        "controls move prec, and M2 is held fixed by all four."
    ),
    "what_closed_it": (
        "M2-LEMMA.md states the bound as Lemma M2 and proves it: "
        "differentiation under the integral sign with an explicit dominating "
        "function, Cauchy's theorem on the shifted contour with the far side "
        "bounded rather than asserted to vanish, the vertical-leg "
        "cancellation, separate proofs of both majorants for the theta-like "
        "sum, and the panel-plus-tail split.  Every constant is a reported "
        "Arb ball and every hypothesis is a decided predicate, so no step of "
        "the proof rests on an unverified numerical claim.  Four routes now "
        "exercise it (m2_lemma.py): an independent re-implementation, an "
        "unshifted majorant that needs neither Cauchy's theorem nor the "
        "evenness, a pointwise Arb enclosure of H_t'' that makes the cushion "
        "decided, and this file's float guard.  Two attacks stand beside "
        "them: the identity for H_t'' against second central differences of "
        "H_ball (worst relative gap 7.66e-07 against h^2 = 9.54e-07), and "
        "both Omega majorants against a sharp truncated enclosure at 24 "
        "probe points, no refutation."
    ),
    "why_it_mattered": (
        "M2 too large costs only compute (more subdivision).  M2 too small "
        "silently licenses a segment whose true argument variation exceeds "
        "pi, and the branch resolution Delta = Arg q is then wrong by 2pi, "
        "which lands in the sum as a whole unit of winding.  The failure "
        "mode is a wrong integer with status 'decided', which is the one "
        "output this routine promises never to produce.  That failure mode "
        "is unchanged; what changed is that a wrong M2 now requires an "
        "implementation fault rather than a wrong derivation."
    ),
    "the_perverse_metric": (
        "Unchanged and still true.  min_chord_margin_digits is "
        "log10(dist(0, chord) / tube radius) minimised over accepted "
        "segments.  Deflating M2 shrinks the tube, so the ratio grows: the "
        "correct run reports 0.02 and the N = 0 run at factor 100 reports "
        "0.11, at factor 1000 reports 1.11.  The metric therefore reads "
        "HEALTHIER exactly as the detector gets more wrong, and it may not "
        "be used as a guard on M2.  min_ball_margin_digits is no better "
        "here: it moves from 40.32 to 42.61 across the same lesion, because "
        "the wrong runs accept fewer and larger segments and never sample "
        "the tight ones."
    ),
    "countermeasure_still_in_place": (
        "winding.measured_h2_guard: M2 must dominate a directly measured "
        "sup |H_t''| sampled on the box by quadrature of the defining "
        "integral, sharing no code with the shifted-contour derivation.  It "
        "is NECESSARY, NOT SUFFICIENT and it is measured, not decided.  It "
        "is kept because the detector still cannot see a corrupted M2 by "
        "itself, so the guard is now the defence against an implementation "
        "fault rather than against a wrong derivation.  winding.py's main() "
        "still refuses the floor when it fails."
    ),
    "the_ordering_question_answered": (
        "The recorded worry was that the guard trips at deflation 55.7 while "
        "the first wrong integer appears at 75, so the guard fires first on "
        "THIS box by luck rather than structure.  That is now partly "
        "answered and partly not.  Answered: the trip point is the cushion "
        "M2 / sup |H_t''|, and the cushion is a structural constant of the "
        "bound rather than a property of these rectangles.  M2 depends on "
        "x_lo only through e^{-x_lo v} with v = pi/4 - 1/256 against the "
        "strip half-width pi/4, and across a 40-unit span of Re z over which "
        "|H_t''| falls by 14 orders of magnitude the decided cushion stays "
        "between 33 and 204 (m2_lemma_results.json, R6_decay_rate_probe).  "
        "Not answered: nothing proves the ordering itself on an arbitrary "
        "box, and the wrong-answer onset depends on the subdivision rule as "
        "well as on M2.  The ordering matters less than it did, because with "
        "M2 proved the guard defends against a coding error, not against the "
        "mathematics."
    ),
    "what_is_still_open": (
        "Three things, all named, none of them an unverified numerical "
        "claim.  (1) The proof needs one cited classical input, the evenness "
        "Phi_DH(-u) = Phi_DH(u), which is Hecke's theta transformation plus "
        "F(s) = F(1-s) transported; it is GATE.md assumption 5 and it is "
        "load-bearing for M2, since without it the vertical legs do not "
        "cancel and no bound of this size exists.  M2-LEMMA.md section 3 "
        "step 2 shows there is no numerical substitute: the quantity that "
        "must vanish is identically zero, so enclosing it to 1e-78 would "
        "take of order 1e78 subdivisions.  (2) The proof is written prose "
        "plus decided arithmetic, at the hardened rung; it is not "
        "kernel-checked and it has been read by no human.  (3) The guard "
        "remains a finite grid of a smooth function, so a peak between nodes "
        "is invisible to it; the decided sup lower bound of section 7 of "
        "M2-LEMMA.md has the same finite-grid limitation, and by design, "
        "since a uniform enclosure over the box is impossible (a z-ball of "
        "radius 1e-24 already returns an enclosure containing 0)."
    ),
    "cushion_now_decided": (
        "The published cushion was measured: sup |H_t''| = 2.1357e-80 by "
        "float quadrature against M2 = 1.1887e-78, ratio 55.7.  It is now "
        "decided: an Arb enclosure at the same point reproduces "
        "2.1357367685579024e-80 to all 17 digits, and a 433-point grid of "
        "enclosures gives a decided sup >= 2.1358117413634282e-80 at t1 and "
        ">= 2.1139544551457620e-80 at t2, hence a decided cushion of at most "
        "55.65 and 53.79.  The published numbers stand and move only in the "
        "third digit."
    ),
    "artifact": "M2-LEMMA.md, m2_lemma.py, m2_lemma_results.json",
    "superseded_record_kept_verbatim": {
        "note": (
            "The record below is the 2026-08-16 state, preserved unedited.  "
            "It was accurate when written and is retained because the "
            "repository's correction style is to keep superseded text rather "
            "than delete it."
        ),
        "name": "M2 is unguarded prose, and the health metric moves the wrong way",
        "what_is_blind": (
            "M2, the uniform bound for |H_t''| on the box, is the single "
            "load-bearing analytic step in the lower-bound route whose "
            "derivation is prose rather than an enclosure or a cited theorem "
            "(its numerical ingredients are ball-computed; the "
            "shifted-contour argument that assembles them is not).  Controls "
            "1 to 4 do not touch it: the displaced and edge-on-zero lesions "
            "move geometry, the precision controls move prec, and M2 is held "
            "fixed by all four."
        ),
        "what_is_still_blind": (
            "Three things.  (1) The guard is a finite grid of a smooth "
            "function; a peak between nodes is invisible to it.  (2) The "
            "guard is float grade, so it cannot upgrade M2 from prose to "
            "decided; only an in-tree or Lean derivation of the "
            "shifted-contour step would do that.  (3) The ordering that "
            "makes the guard useful on THIS box is luck, not structure: the "
            "guard fires once M2 falls below the measured sup 2.14e-80 "
            "(deflation past 55.7), while the first wrong integer observed "
            "here appears at deflation 75, so the guard happens to trip "
            "before the failure.  Nothing guarantees that ordering on "
            "another box, and a derivation wrong by a factor under 55 would "
            "pass the guard and could still be wrong."
        ),
        "recorded_rather_than_repaired": (
            "This is a standing blind spot in the lower-bound route, not a "
            "closed defect.  Any statement of the bound carries it."
        ),
    },
}


# ---------------------------------------------------------------------------
# the no-compute notes
# ---------------------------------------------------------------------------


RIVAL_FRAMING = (
    "The same pipeline pointed at zeta yields no positive floor: the lower "
    "bound needs a box around a zero strictly off the real axis of the "
    "corresponding H_t, and no off-line zero of zeta is known; every box "
    "this detector could honestly place for zeta would decide N = 0 (as the "
    "displaced-box lesion here does for an empty window).  The number "
    "produced by this hunt therefore separates DH from zeta only through "
    "the already-known off-line zeros (Davenport-Heilbronn 1936; computed "
    "by Spira 1994), which is exactly flow_repair's P5 moral.  Nothing here "
    "is evidence about RH."
)

BATTERY_NA = (
    "zeta.epstein.battery referees structural claims that purport to "
    "explain RH by distinguishing zeta from an RH-violating rival; DH is "
    "that rival.  This hunt makes no RH-explaining structural claim (see "
    "MISSION.md: the deliverable is a pair of numbers about DH itself, and "
    "WP4 names its controls as lesion, precision response and rival "
    "framing), so the battery has no claim to referee here; its subject "
    "matter is instead this hunt's object of study."
)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    t_all = time.time()
    geom = _load_t1_geometry()
    print(f"t1 box: {[_fr_str(q) for q in geom['box']]}  t = {_fr_str(geom['t'])}",
          flush=True)

    print("control 1: lesion, box displaced +2 in Re ...", flush=True)
    c1 = lesion_displaced(geom)
    print(f"  {c1['verdict']}: status = {c1['result']['status']}, "
          f"N = {c1['result'].get('N')}", flush=True)

    print("control 2a: lesion, y_lo = 0 ...", flush=True)
    c2a = lesion_on_axis(geom)
    print(f"  {c2a['verdict']}: {c2a['failure_mode']}", flush=True)

    print("control 2b: lesion, top edge through the measured zero ...", flush=True)
    c2b = lesion_edge_through_zero(geom)
    print(f"  {c2b['verdict']}: status = {c2b['result']['status']}, "
          f"reason = {c2b['failure_mode']}, "
          f"evals = {c2b['result']['n_H_evals']}", flush=True)

    print("control 3a: H_ball radius at a fixed point, prec "
          f"{PRECS} ...", flush=True)
    c3a = precision_response_point(geom)
    print(f"  {c3a['verdict']}: radii = {c3a['H_ball_radius_by_prec']}",
          flush=True)

    print(f"controls 3b + 4: winding at fixed geometry, prec {PRECS} ...",
          flush=True)
    wruns = winding_across_precisions(geom)
    c3b = assess_precision_winding(wruns)
    print(f"  3b {c3b['verdict']}: widths = {c3b['N_ball_width_by_prec']}",
          flush=True)
    c4 = assess_artifact(wruns)
    print(f"  4  {c4['verdict']}: margins = "
          f"{c4['min_ball_margin_digits_by_prec']}", flush=True)

    print(f"control 5: lesion, M2 deflated by {DEFLATION_FACTORS} ...", flush=True)
    c5 = lesion_m2_deflated(geom)
    print(f"  {c5['verdict']}: " + ", ".join(
        f"/{r['deflation_factor']} -> {r['status']} N={r['N']} "
        f"chord={r['min_chord_margin_digits']}" for r in c5["table"]), flush=True)
    print(f"  wrong-answer onset at deflation {c5['wrong_answer_onset_factor']}; "
          f"guard catches every wrong row observed: "
          f"{c5['guard_catches_all_observed_wrong_rows']}", flush=True)

    out = {
        "hunt": "lambda_dh_bounds",
        "wp": "WP4 control battery",
        "date": "2026-08-16",
        "backend": BACKEND,
        "geometry_source": "winding_results.json t1_run (t = 23/400)",
        "controls": {
            "1_lesion_displaced_box": c1,
            "2a_lesion_on_axis_box": c2a,
            "2b_lesion_edge_through_zero": c2b,
            "3a_precision_response_fixed_point": c3a,
            "3b_precision_response_winding_width": c3b,
            "4_artifact_check_ball_margin": c4,
            "5_lesion_m2_deflated": c5,
        },
        "winding_runs_by_prec": wruns,
        "notes": {
            "rival_framing": RIVAL_FRAMING,
            "battery_not_applicable": BATTERY_NA,
        },
        "wall_seconds_total": round(time.time() - t_all, 1),
    }
    verdicts = {k: c["verdict"] for k, c in out["controls"].items()}
    out["verdicts"] = verdicts
    out["controls_1_to_4_pass"] = all(
        v == "PASS" for k, v in verdicts.items() if not k.startswith("5_")
    )
    out["all_pass"] = all(v == "PASS" for v in verdicts.values())
    out["all_pass_note"] = (
        "all_pass was True through 2026-08-16 over controls 1 to 4, and "
        "controls_1_to_4_pass preserves that statement unchanged: their "
        "verdicts and numbers did not move.  all_pass is False from "
        "2026-08-16 because control 5 was added and the detector does not "
        "survive it.  Control 5 is not a control the battery is expected to "
        "pass: see controls.5_lesion_m2_deflated.  Reporting only "
        "controls_1_to_4_pass would be the flattering read and is not the "
        "headline.  Amended 2026-08-18: control 5's verdict changed from "
        "'BLIND SPOT' to 'SENSITIVITY MEASURED (not a pass)' when M2 became "
        "a proved lemma (M2-LEMMA.md).  all_pass stays False, because the "
        "detector still cannot see the lesion by itself and the expectation "
        "as written is still unmet.  Nothing in the table moved."
    )

    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=1)
    print(f"wrote {RESULTS_PATH}  all_pass = {out['all_pass']}  "
          f"(controls 1-4 pass = {out['controls_1_to_4_pass']}; control 5 "
          f"measures the detector's sensitivity to a corrupted M2 and is not "
          f"expected to pass)  ({out['wall_seconds_total']} s)", flush=True)


if __name__ == "__main__":
    main()
