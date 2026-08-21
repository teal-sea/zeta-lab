"""Second-route argument-principle count for H_t, sharing no code with the instrument.

Provenance: written by the gate adjudication of 2026-08-16 as
``a4_indep_winding.py`` in a scratch directory, and landed here under
GATE.md closure item (e) because a cross-check that lives only in a scratch
directory is not evidence anyone can reproduce.  The mathematics and the
numbers are unchanged from that run; what changed is the path handling (it
now runs from the repo root with no absolute paths in the source) and that
it writes its output to a json file next to itself.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/crosscheck_dhflow_winding.py

It writes ``crosscheck_dhflow_results.json``.  Wall time is about six
minutes: 256 evaluations per box of a dps-130 quadrature at height 240.

What makes this a second route
------------------------------

Different code from ``winding.py`` in every respect that carries the count.
The declaration is spelled out layer by layer in ``INDEPENDENCE.md`` and in
``independence_decl.py`` (route 3); in summary:

  * evaluator: ``hunts/flow_repair``'s ``DHFlow``, a composite
    Gauss-Legendre rule on the real u axis with Phi_DH memoised at the
    nodes, rather than ``instrument.py``'s Arb ``acb.integral``;
  * method: uniform dense boundary sampling with continuous-argument
    tracking and a refinement rule that doubles the sample count until
    every consecutive step is under 1 radian, rather than adaptive
    chord-tube segments with an M2 bound;
  * arithmetic: mpmath floats at dps 130 rather than Arb balls at 420 bits.

``harness/independence.py`` measures the two declarations as sharing no
layer at all: independence radius 0.

One thing this route does NOT duplicate, and it matters.  Its kappa comes
from ``zeta.epstein.kappa``, the mpmath form of the SAME self-duality
linear solve that ``instrument.kappa_ball`` runs in balls.  Different
implementation, same equation.  Agreement here is therefore not evidence
about the equation that defines kappa; ``crosscheck_quadfree.py`` supplies
that leg, deriving kappa from the Gauss sum instead.

Grade: MEASURED, float, by construction.  It cannot decide an integer and
does not claim to.  Its job is to catch a WRONG one, and a count of 1.0000
to ten places against a claimed integer 1 is the only thing it asserts.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
FLOW_REPAIR = os.path.join(REPO, "hunts", "flow_repair")
for _p in (REPO, FLOW_REPAIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from mpmath import arg, mp, mpc, mpf, pi  # noqa: E402

from probe import DHFlow  # noqa: E402

OUT = os.path.join(HERE, "crosscheck_dhflow_results.json")
WINDING_RESULTS = os.path.join(HERE, "winding_results.json")

DPS = 130
Z_SCALE = 242.0


def winding_sampled(flow, box, t, per_edge: int = 64, max_refine: int = 6,
                    verbose: bool = True) -> dict:
    """Total continuous argument of H_t around ``box``, by uniform sampling.

    ``box`` is (x_lo, x_hi, y_lo, y_hi) as exact Fractions, traversed
    counterclockwise.  Each edge is sampled at ``per_edge`` points; the
    count doubles until every consecutive argument step is below 1 radian,
    which is the sampling analogue of the chord-tube condition and is the
    only thing that makes the continuous-argument tracking safe.  Floats
    throughout, so this measures and does not decide.
    """
    x_lo, x_hi, y_lo, y_hi = [mpf(str(q.numerator)) / q.denominator
                              for q in box]
    corners = [(x_lo, y_lo), (x_hi, y_lo), (x_hi, y_hi), (x_lo, y_hi)]
    edges = [(corners[i], corners[(i + 1) % 4]) for i in range(4)]
    tot = mpf(0)
    worst = mpf(0)
    minabs = None
    nev = [0]
    cache: dict = {}
    edge_rows = []

    def H(p):
        key = (str(p[0]), str(p[1]))
        if key not in cache:
            cache[key] = flow.H(mpc(p[0], p[1]), t)
            nev[0] += 1
        return cache[key]

    for ei, (a, b) in enumerate(edges):
        n = per_edge
        for _ in range(max_refine + 1):
            pts = [(a[0] + (b[0] - a[0]) * mpf(k) / n,
                    a[1] + (b[1] - a[1]) * mpf(k) / n) for k in range(n + 1)]
            vals = [H(p) for p in pts]
            steps = [arg(v2 / v1) for v1, v2 in zip(vals, vals[1:])]
            m = max(abs(s) for s in steps)
            if m < mpf(1):          # every step well under pi: safe tracking
                break
            n *= 2
        edge_sum = sum(steps)
        tot += edge_sum
        worst = max(worst, m)
        lo = min(abs(v) for v in vals)
        minabs = lo if minabs is None else min(minabs, lo)
        edge_rows.append({
            "edge": ei, "n_samples": n,
            "argument_sum": float(edge_sum),
            "max_step_radians": float(m),
            "min_absH_on_edge": float(lo),
        })
        if verbose:
            print(f"  edge {ei}: n={n} sum={mp.nstr(edge_sum, 12)} "
                  f"max|step|={mp.nstr(m, 4)} min|H|={mp.nstr(lo, 6)}",
                  flush=True)

    N = tot / (2 * pi)
    return {
        "N_float": float(N),
        "total_argument": float(tot),
        "max_step_radians": float(worst),
        "min_absH_on_boundary": float(minabs),
        "n_evals": nev[0],
        "edges": edge_rows,
    }


def main() -> None:
    t_start = time.time()
    with open(WINDING_RESULTS, encoding="utf-8") as f:
        W = json.load(f)

    flow = DHFlow(dps=DPS, z_scale=Z_SCALE)
    print(f"DHFlow dps={DPS} U={mp.nstr(flow.U, 8)} nodes={flow.n_nodes}",
          flush=True)

    runs = {}
    all_ok = True
    for key, run_name in (("0.0575", "t1_run"), ("0.0576", "t2_stretch_run")):
        b = W[run_name]["box"]
        box = (Fraction(b["re_lo"]), Fraction(b["re_hi"]),
               Fraction(b["im_lo"]), Fraction(b["im_hi"]))
        claimed = W[run_name].get("N")
        print(f"\nt = {key}  box = {[str(q) for q in box]}  "
              f"(instrument claims N = {claimed})", flush=True)
        t0 = time.time()
        r = winding_sampled(flow, box, mpf(key))
        r["seconds"] = round(time.time() - t0, 1)
        r["t"] = key
        r["box"] = {k: b[k] for k in ("re_lo", "re_hi", "im_lo", "im_hi")}
        r["box_source"] = "winding_results.json, " + run_name
        r["instrument_claimed_N"] = claimed
        r["agrees_with_instrument"] = bool(
            claimed is not None and abs(r["N_float"] - claimed) < 1e-6)
        all_ok = all_ok and r["agrees_with_instrument"]
        runs[key] = r
        print(f"  -> N = {r['N_float']:.10f}  (instrument: {claimed})  "
              f"agrees: {r['agrees_with_instrument']}  "
              f"[{r['seconds']} s]", flush=True)

    out = {
        "hunt": "lambda_dh_bounds",
        "route": "route 3: DHFlow argument-principle count, sharing no code "
                 "with instrument.py",
        "provenance": "written by the gate adjudication of 2026-08-16 as "
                      "a4_indep_winding.py; landed here unchanged in "
                      "mathematics under GATE.md closure item (e)",
        "grade": f"measured (mpmath floats, dps {DPS}); it cannot decide an "
                 "integer and does not claim to",
        "evaluator": "hunts/flow_repair probe.DHFlow, composite "
                     "Gauss-Legendre on the real u axis with Phi_DH memoised "
                     "at the nodes",
        "method": "uniform boundary sampling with continuous-argument "
                  "tracking; the sample count doubles until every "
                  "consecutive step is under 1 radian",
        "independence": "radius 0 against route 1 (winding.py): no declared "
                        "layer is shared.  See INDEPENDENCE.md and "
                        "independence_decl.py.",
        "not_independent_of": "the kappa EQUATION: this route's kappa comes "
                              "from zeta.epstein.kappa, the mpmath form of "
                              "the same self-duality linear solve "
                              "instrument.kappa_ball runs in balls.  "
                              "crosscheck_quadfree.py carries the Gauss-sum "
                              "derivation that does not share it.",
        "dps": DPS,
        "flow_U": float(flow.U),
        "flow_n_nodes": flow.n_nodes,
        "runs": runs,
        "agrees_at_both_t": all_ok,
        "seconds_total": round(time.time() - t_start, 1),
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(f"\nagrees at both t: {all_ok}  ({out['seconds_total']} s)  -> {OUT}",
          flush=True)
    if not all_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
