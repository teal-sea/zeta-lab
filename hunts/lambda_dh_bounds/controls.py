"""WP4: the control battery for the lambda_dh_bounds hunt.

Four controls, per MISSION.md WP4, run against the route-1 machinery
(``winding.py``) and the ball instrument (``instrument.py``), imported and
never duplicated.

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
        },
        "winding_runs_by_prec": wruns,
        "notes": {
            "rival_framing": RIVAL_FRAMING,
            "battery_not_applicable": BATTERY_NA,
        },
        "wall_seconds_total": round(time.time() - t_all, 1),
    }
    verdicts = [c["verdict"] for c in out["controls"].values()]
    out["all_pass"] = all(v == "PASS" for v in verdicts)

    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=1)
    print(f"wrote {RESULTS_PATH}  all_pass = {out['all_pass']}  "
          f"({out['wall_seconds_total']} s)", flush=True)


if __name__ == "__main__":
    main()
