"""The measured independence radius of this hunt's verification routes.

Gate closure item (e).  Until 2026-08-16 the hunt said "two independent
winding routes" (MISSION.md WP1, prediction P2).  The gate measured that
sentence with ``harness/independence.py`` and found it much weaker than it
sounds: the two winding routes share the whole evaluator and differ only in
the bookkeeping that turns H-balls into an integer.  This module replaces
the adjective with the measurement.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/independence_decl.py

It writes ``independence_results.json`` next to this file and prints the
same content.  Nothing here computes any mathematics; it declares, for four
routes to the same integer N, which named implementation each one runs at
each stage, and hands the declarations to ``harness.independence.compare``.

Read ``harness/independence.py`` and ``docs/25-the-director-run.md`` before
trusting any number this prints.  The standing caveat is theirs and it is
not a formality: **a declaration is not an attestation.**  Nothing checks
that a layer list is complete, and an undeclared shared layer is exactly
what the structure cannot see.  Two anchors below are pinned by assertion
(the declared attribute names must still exist in the modules that own
them), which is a check on drift, not a completeness proof.

Granularity, stated up front because the headline count depends on it.  A
layer here is one identifiable implementation stage between an exact input
coordinate and an integer.  The gate's own declaration merged the period-5
coefficient table with the theta recurrence that consumes it, and reported
8 shared of 11; the finer split below reports 9 shared of 12.  The two
declarations differ by one merge and by nothing else, and
``merge_check_matches_gate`` below re-runs the coarse version to show that
the difference is bookkeeping rather than disagreement.  What neither count
depends on is the load-bearing sentence: **the routes duplicate none of the
evaluator.**
"""

from __future__ import annotations

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
if REPO not in sys.path:
    sys.path.insert(0, REPO)

from harness.independence import (  # noqa: E402
    VerificationPath,
    agreement_bounds,
    compare,
)

OUT = os.path.join(HERE, "independence_results.json")

# ---------------------------------------------------------------------------
# the evaluator: nine layers, one implementation each, run by BOTH winding
# routes.  Everything from an exact rational coordinate to an Arb ball for
# H_t(z) at that point lives here.
# ---------------------------------------------------------------------------

EVALUATOR = (
    "exact rational input conversion (instrument._exact_q / _q_to_arb / _as_acb)",
    "kappa by the self-duality linear solve at s0 = 3/4 + 3i/2 "
    "(instrument.kappa_ball, Arb Hurwitz zeta)",
    "period-5 coefficient table a_n = (1, kappa, -kappa, -1, 0) "
    "(instrument._truncated_integrand)",
    "truncated omega by the theta recurrence q^{n^2} "
    "(instrument._truncated_integrand)",
    "series truncation tail bound (instrument._series_tail_finite via "
    "_omega_tail_upper)",
    "discarded-u-tail bound on [U, inf) (instrument._u_tail)",
    "integration limit policy U (instrument.default_U)",
    "rigorous adaptive integrator (flint acb.integral)",
    "ball arithmetic backend: python-flint 0.9.0 (Arb)",
)

# The coarse variant the gate declared: the coefficient table and the
# recurrence that consumes it counted as one layer.
EVALUATOR_COARSE = (
    EVALUATOR[0],
    EVALUATOR[1],
    "Phi_DH truncated series, coefficients and theta recurrence together "
    "(instrument._truncated_integrand)",
) + EVALUATOR[4:]

ROUTE1 = VerificationPath(
    name="route 1: segment-argument winding (winding.py)",
    layers=EVALUATOR
    + (
        "uniform second-derivative bound M2 by the shifted u-contour "
        "(winding.second_derivative_bound)",
        "chord-tube segment decision with dyadic subdivision "
        "(winding._chord_clearance, winding.winding_rectangle)",
        "integer from the sum of per-segment Arg q divided by 2 pi "
        "(winding.winding_rectangle)",
    ),
)

ROUTE2 = VerificationPath(
    name="route 2: H'/H ball quadrature (winding_quad.py)",
    layers=EVALUATOR
    + (
        "panel-local Taylor models of H and H' with explicit remainder balls "
        "(winding_quad.moment_integrals, winding_quad.taylor_remainders)",
        "contour quadrature of H'/H along the four edges (winding_quad.main)",
        "integer from the contour-integral ball (winding_quad.main)",
    ),
)

ROUTE1_COARSE = VerificationPath(
    name="route 1 (gate granularity)",
    layers=EVALUATOR_COARSE + ROUTE1.layers[len(EVALUATOR):],
)
ROUTE2_COARSE = VerificationPath(
    name="route 2 (gate granularity)",
    layers=EVALUATOR_COARSE + ROUTE2.layers[len(EVALUATOR):],
)

# ---------------------------------------------------------------------------
# the two legs the gate ran, which are the ones that carry real independence
# ---------------------------------------------------------------------------

ROUTE3 = VerificationPath(
    name="route 3: DHFlow argument-principle count "
         "(crosscheck_dhflow_winding.py)",
    layers=(
        "float input conversion (mpmath mpf/mpc from the exact box rationals)",
        "kappa by the zeta.epstein mpmath linear solve "
        "(different implementation, SAME equation as instrument.kappa_ball)",
        "omega_dh direct summation with a term-size stopping rule "
        "(flow_repair.probe.omega_dh)",
        "Phi_DH memoised at fixed quadrature nodes "
        "(flow_repair.probe.phi_dh_raw)",
        "composite Gauss-Legendre rule on [0, U] with an oscillation-resolving "
        "panel count (flow_repair.probe.DHFlow)",
        "float arithmetic backend: mpmath at dps 130",
        "uniform boundary sampling with continuous-argument tracking and step "
        "refinement (crosscheck_dhflow_winding.winding_sampled)",
        "integer from the total argument divided by 2 pi "
        "(crosscheck_dhflow_winding.winding_sampled)",
    ),
)

ROUTE4 = VerificationPath(
    name="route 4: quadrature-free ball evaluator (crosscheck_quadfree.py)",
    layers=(
        "exact rational input conversion (crosscheck_quadfree.q, its own)",
        "kappa from the Gauss sum tau(chi) of the odd character mod 5 "
        "(crosscheck_quadfree.kappa_gauss, a DIFFERENT equation)",
        "F(s) by Hurwitz zeta, no series in u and no quadrature "
        "(crosscheck_quadfree.F_ball)",
        "Taylor in t from dH/dt = -d^2H/dz^2, coefficients by acb_series "
        "(crosscheck_quadfree.F_taylor)",
        "explicit Taylor truncation remainder bound "
        "(crosscheck_quadfree.taylor_remainder)",
        "ball arithmetic backend: python-flint 0.9.0 (Arb)",
    ),
)

# ---------------------------------------------------------------------------
# anchors: the declaration names attributes, and the attributes must exist
# ---------------------------------------------------------------------------

ANCHORS = (
    ("instrument", "kappa_ball"),
    ("instrument", "_truncated_integrand"),
    ("instrument", "_series_tail_finite"),
    ("instrument", "_u_tail"),
    ("instrument", "default_U"),
    ("winding", "second_derivative_bound"),
    ("winding", "_chord_clearance"),
    ("winding", "winding_rectangle"),
    ("winding_quad", "moment_integrals"),
    ("winding_quad", "taylor_remainders"),
)


def check_anchors() -> dict:
    """Every module attribute the declaration names must still exist.

    A drift check, not a completeness proof: it catches a rename that would
    silently make a layer name a fiction, and sees nothing about a shared
    layer nobody wrote down.
    """
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    rows = []
    ok = True
    for mod_name, attr in ANCHORS:
        try:
            mod = __import__(mod_name)
            present = hasattr(mod, attr)
        except Exception as exc:  # pragma: no cover - import failure is a result
            present = False
            rows.append({"module": mod_name, "attribute": attr,
                         "present": False, "error": repr(exc)})
            ok = False
            continue
        rows.append({"module": mod_name, "attribute": attr, "present": present})
        ok = ok and present
    return {"all_present": ok, "rows": rows,
            "strength": "drift check only: a declaration is not an "
                        "attestation, and an undeclared shared layer stays "
                        "invisible to it"}


def _report_row(a: VerificationPath, b: VerificationPath) -> dict:
    rep = compare(a, b)
    return {
        "path_a": rep.path_a,
        "path_b": rep.path_b,
        "n_layers_a": len(rep.layers_a),
        "n_layers_b": len(rep.layers_b),
        "radius": rep.radius,
        "n_shared": len(rep.shared),
        "shared": list(rep.shared),
        "reconvergent": list(rep.reconvergent),
        "distinct_a": list(rep.distinct_a),
        "distinct_b": list(rep.distinct_b),
        "describe": rep.describe(),
        "agreement_bounds": list(agreement_bounds(rep)),
    }


def main() -> None:
    anchors = check_anchors()

    pairs = [
        ("route1_vs_route2", ROUTE1, ROUTE2),
        ("route1_vs_route3_dhflow", ROUTE1, ROUTE3),
        ("route1_vs_route4_quadfree", ROUTE1, ROUTE4),
        ("route3_vs_route4", ROUTE3, ROUTE4),
    ]
    reports = {key: _report_row(a, b) for key, a, b in pairs}

    coarse = _report_row(ROUTE1_COARSE, ROUTE2_COARSE)
    gate_match = bool(coarse["n_shared"] == 8 and coarse["n_layers_a"] == 11
                      and coarse["radius"] == 8)

    r12 = reports["route1_vs_route2"]
    out = {
        "hunt": "lambda_dh_bounds",
        "item": "GATE.md closure item (e): the independence story, measured",
        "tool": "harness/independence.py (docs/25, docs/26 section 1)",
        "granularity_note": (
            "a layer is one identifiable implementation stage between an "
            "exact input coordinate and an integer; the headline count "
            "depends on that choice and the invariant does not"
        ),
        "anchors": anchors,
        "paths": {
            p.name: list(p.layers)
            for p in (ROUTE1, ROUTE2, ROUTE3, ROUTE4)
        },
        "reports": reports,
        "gate_granularity_recheck": {
            "report": coarse,
            "matches_gate_8_of_11": gate_match,
            "note": (
                "the gate declared the coefficient table and the theta "
                "recurrence as one layer and reported 8 shared of 11; the "
                "finer split reports "
                f"{r12['n_shared']} shared of {r12['n_layers_a']}.  The two "
                "declarations differ by that one merge and agree on every "
                "layer's status."
            ),
        },
        "headline": (
            f"routes 1 and 2 share {r12['n_shared']} of {r12['n_layers_a']} "
            f"declared layers with independence radius {r12['radius']}: the "
            "whole evaluator is one implementation run twice, and their "
            "agreement is evidence about the bookkeeping that turns H-balls "
            "into an integer and about nothing else.  Route 3 shares no "
            "layer with route 1 (radius 0) and route 4 shares only the ball "
            "arithmetic backend, reconvergent."
        ),
        "what_route1_route2_agreement_is_NOT_evidence_about": list(
            r12["shared"]),
        "caveat": (
            "harness/independence.py measures a declaration, not the code.  "
            "Nothing here verifies that these layer lists are complete.  An "
            "undeclared shared layer is precisely the fault this structure "
            "cannot see, which is the standing lesson of docs/25."
        ),
    }

    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")

    print(out["headline"])
    print()
    for key, rep in reports.items():
        print(f"{key}: {rep['describe']}")
    print()
    print(f"gate granularity recheck: {coarse['n_shared']} shared of "
          f"{coarse['n_layers_a']}, radius {coarse['radius']}; "
          f"matches the gate's 8 of 11: {gate_match}")
    print(f"anchors all present: {anchors['all_present']}")
    print(f"\nwrote {OUT}")


if __name__ == "__main__":
    main()
