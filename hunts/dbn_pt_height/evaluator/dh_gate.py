"""The Davenport-Heilbronn refusal gate (DH.md; preregistered in DH_GATE_PREREG.md).

The question the gate answers: does the barrier decision this evaluator makes
for zeta (``effective.barrier_rectangle``, Section 8.4 of arXiv:1904.12438v2)
refuse to call a rectangle zero-free when the rectangle holds a zero of the
Davenport-Heilbronn heat flow?

``dh_barrier`` is that decision with the function swapped.  Its rule is the one
at ``effective.py`` (the acceptance test near the line ``need = E + D * h / 2``
and the winding sum near ``tot += (fb / fa).arg()``):

* mesh each edge of R with dyadic points; a segment of length h is accepted
  when both endpoint values satisfy |f(z_j)| > E + D h / 2, else it is bisected,
  down to ``max_depth`` levels;
* when every segment is accepted, the winding number is the integer contained
  in the ball (1/2pi) sum Arg(f_{j+1}/f_j), or None when the ball holds none.

What changes for DH: f is H_t itself, enclosed by hunt #61's instrument
(``dh.H_ball``), so the error term E is zero and the enclosure radius is
carried by the balls; D bounds |H'| on the segment by max |H'| at the two ends
(``dh.Hprime_ball``) plus M2 h / 2, with M2 hunt #61's decided bound on |H''|
(``winding.second_derivative_bound``), converted to the wide frame
(H_wide(z) = H_61(z/2), so M2 is divided by 4).

The ground truth for each gate rectangle is hunt #61's own decided count
(``winding.winding_rectangle``), which uses a different rule (chord clearance
against M2 h^2 / 2 and Re(H_b / H_a) > 0), so the gate does not grade its own
homework.

Faults (the preregistered list; each is a way a pipeline could be too
permissive, and the gate has to catch it) are switched on by name in
``faults``.
"""

from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import dh  # noqa: E402
from effective import workprec  # noqa: E402

FAULTS = (
    "one_corner",        # row-2 style: |f| checked at one corner (N0, y0) and the box called zero-free
    "no_margin",         # accept a segment when its endpoint balls exclude 0; no D h/2, no refinement
    "narrow_frame",      # wide-frame coordinates handed to the narrow-frame instrument unconverted
    "main_terms_only",   # f = A + B (sharp main terms, no correction), E = 0
    "no_M2",             # D = max |H'| at the two ends, without the M2 h/2 term
)


def _winding(box=None, t=None):
    if str(dh._LDB) not in sys.path:
        sys.path.insert(0, str(dh._LDB))
    import winding  # noqa: PLC0415 - hunt #61's module, read-only

    return winding


def M2_wide(box: tuple[Fraction, Fraction, Fraction, Fraction], t: Fraction, narrow: bool = False) -> arb:
    """Hunt #61's decided bound on sup |H''| over Re z >= x_lo, |Im z| <= y_hi, wide frame."""
    W = _winding(box, t)
    x_lo, _, _, y_hi = box
    if narrow:  # the frame fault: the box is read as if it were already narrow
        info = W.second_derivative_bound(x_lo, y_hi, t)
        return info["M2"]
    info = W.second_derivative_bound(x_lo / 2, y_hi / 2, t / 4)
    return info["M2"] / 4


def truth(box: tuple[Fraction, Fraction, Fraction, Fraction], t: Fraction, prec: int = 420) -> dict:
    """Hunt #61's decided zero count in the wide-frame box (its route, its rule)."""
    W = _winding(box, t)
    x_lo, x_hi, y_lo, y_hi = box
    nbox = (x_lo / 2, x_hi / 2, y_lo / 2, y_hi / 2)
    m2 = W.second_derivative_bound(nbox[0], nbox[3], t / 4)
    r = W.winding_rectangle(nbox, t / 4, prec, m2)
    return {"status": r["status"], "N": r.get("N"), "n_segments": r.get("n_segments"),
            "wall_seconds": r.get("wall_seconds")}


def _point(box, edge: int, u: Fraction) -> tuple[Fraction, Fraction]:
    x_lo, x_hi, y_lo, y_hi = box
    corners = [(x_lo, y_lo), (x_hi, y_lo), (x_hi, y_hi), (x_lo, y_hi)]
    (xa, ya), (xb, yb) = corners[edge], corners[(edge + 1) % 4]
    return xa + (xb - xa) * u, ya + (yb - ya) * u


def dh_barrier(box: tuple[Fraction, Fraction, Fraction, Fraction], t: Fraction, prec: int | None = None,
               initial_per_edge: int = 8, max_depth: int = 6, max_evaluations: int = 600,
               faults: frozenset = frozenset()) -> dict[str, Any]:
    """The zeta pipeline's barrier decision, run on the DH heat flow (module docstring).

    Returns ``winding`` (an int, or None when undecided) with the counts behind
    it.  A winding of 0 is the pipeline calling the box zero-free."""
    unknown = set(faults) - set(FAULTS)
    if unknown:
        raise ValueError(f"unknown faults {unknown}")
    t0 = time.perf_counter()
    x_lo, x_hi, y_lo, y_hi = box
    if prec is None:  # |H| ~ e^{-pi x / 8}: the enclosures need that many bits and more
        prec = dh.split_prec(x_hi)
    narrow = "narrow_frame" in faults
    cache: dict[tuple, tuple[acb, acb]] = {}

    def f_and_df(z: tuple[Fraction, Fraction]) -> tuple[acb, acb]:
        if z not in cache:
            x, y = z
            if narrow:  # H_61(z, t) read as if it were H_wide(z, t): x, y, t not converted
                I = dh._instrument()
                with workprec(prec):
                    cache[z] = (I.H_ball((x, y), t, prec), I.Hprime_ball((x, y), t, prec))
            elif "main_terms_only" in faults:
                m = dh.main_terms(str(x), str(y), str(t), prec=prec)
                cache[z] = (m["H_main"], dh.Hprime_ball(x, y, t, prec))
            else:
                cache[z] = (dh.H_ball(x, y, t, prec), dh.Hprime_ball(x, y, t, prec))
        return cache[z]

    with workprec(prec):
        if "one_corner" in faults:
            v, _ = f_and_df((x_lo, y_lo))
            ok = abs(v).lower() > 0
            return {"winding": 0 if ok else None, "n_evaluations": len(cache), "n_failed": 0 if ok else 1,
                    "seconds": round(time.perf_counter() - t0, 2), "faults": sorted(faults)}
        M2 = arb(0) if "no_M2" in faults else M2_wide(box, t, narrow=narrow)
        per_edge = 4 if "no_margin" in faults else initial_per_edge
        depth_cap = 0 if "no_margin" in faults else max_depth
        lengths = [x_hi - x_lo, y_hi - y_lo, x_hi - x_lo, y_hi - y_lo]
        accepted: list[tuple[int, Fraction, Fraction, acb, acb]] = []
        n_failed = 0
        for edge in range(4):
            stack = [(Fraction(k + 1, per_edge), Fraction(k, per_edge), 0) for k in reversed(range(per_edge))]
            while stack:
                u1, u0, d = stack.pop()
                if len(cache) >= max_evaluations:  # budget spent: the box stays undecided
                    n_failed += 1 + len(stack)
                    stack.clear()
                    break
                fa, da = f_and_df(_point(box, edge, u0))
                fb, db = f_and_df(_point(box, edge, u1))
                h = arb(lengths[edge].numerator) / lengths[edge].denominator * (arb((u1 - u0).numerator) / (u1 - u0).denominator)
                if "no_margin" in faults:
                    need = arb(0)
                else:
                    D = (abs(da).upper() if abs(da).upper() > abs(db).upper() else abs(db).upper()) + M2 * h / 2
                    need = D * h / 2
                if abs(fa).lower() > need and abs(fb).lower() > need:
                    accepted.append((edge, u0, u1, fa, fb))
                elif d < depth_cap:
                    um = (u0 + u1) / 2
                    stack.append((u1, um, d + 1))
                    stack.append((um, u0, d + 1))
                else:
                    n_failed += 1
        winding = None
        wind_ball = None
        if n_failed == 0:
            accepted.sort(key=lambda s: (s[0], s[1]))
            tot = arb(0)
            for (_, _, _, fa, fb) in accepted:
                tot += (fb / fa).arg()
            wind_ball = tot / (2 * arb.pi())
            try:
                winding = int(wind_ball.unique_fmpz())
            except Exception:  # the ball holds no integer, or more than one
                winding = None
        return {"winding": winding, "winding_ball": None if wind_ball is None else wind_ball.str(6),
                "n_evaluations": len(cache), "n_segments": len(accepted), "n_failed": n_failed,
                "M2": M2.str(4), "seconds": round(time.perf_counter() - t0, 2), "faults": sorted(faults)}


# --------------------------------------------------------------------------- #
#  The preregistered gate (DH_GATE_PREREG.md is the authority; this mirrors it)
# --------------------------------------------------------------------------- #

def _F(s: str) -> Fraction:
    return Fraction(s)


GATE_BOXES = {
    # zero boxes: each is expected to hold one zero; truth() decides how many
    "Z1": {"t": _F("144/625"), "box": (_F("245909/512"), _F("123159/256"), _F("3/512"), _F("35/512")),
           "kind": "zero", "why": "2 x hunt #61's decided t = 36/625 box, wide frame"},
    "Z2": {"t": _F("0"), "box": (_F("1712/10"), _F("1716/10"), _F("5/10"), _F("7/10")), "kind": "zero",
           "why": "t = 0, the pinned zero 0.80852 + 85.69935i (zeta.epstein), z = 171.399 + 0.617i"},
    "Z3": {"t": _F("0"), "box": (_F("2281/10"), _F("2285/10"), _F("2/10"), _F("4/10")), "kind": "zero",
           "why": "t = 0, Spira's 0.650830 + 114.163343i, z = 228.327 + 0.302i"},
    "Z4": {"t": _F("0"), "box": (_F("3532/10"), _F("3536/10"), _F("35/100"), _F("55/100")), "kind": "zero",
           "why": "t = 0, Spira's 0.724258 + 176.702461i, z = 353.405 + 0.449i"},
    # controls: boxes next to the zeros, expected zero-free; truth() decides
    "C1": {"t": _F("144/625"), "box": (_F("245909/512"), _F("123159/256"), _F("1/5"), _F("3/5")),
           "kind": "control", "why": "above Z1"},
    "C2": {"t": _F("0"), "box": (_F("1712/10"), _F("1716/10"), _F("8/10"), _F("1")),
           "kind": "control", "why": "above Z2"},
}


def classify(kind: str, truth_N: int | None, out_winding: int | None) -> str:
    """The preregistered decision table, one row."""
    if truth_N is None:
        return "TRUTH_UNAVAILABLE"
    if kind == "zero" and truth_N == 0:
        return "TRUTH_EMPTY"          # the box holds no zero after all: excluded, reported
    if kind == "control" and truth_N != 0:
        return "CONTROL_NOT_EMPTY"    # the control holds a zero: excluded, reported
    if kind == "zero":
        if out_winding is None:
            return "REFUSE_WEAK"
        if out_winding == 0:
            return "ACCEPT"
        return "REFUSE" if out_winding == truth_N else "INCONSISTENT"
    if out_winding is None:
        return "NON_DISCRIMINATING"
    return "DISCRIMINATES" if out_winding == truth_N else "INCONSISTENT"


def verdict(rows: dict[str, str]) -> str:
    """PASS, FAIL or INCONCLUSIVE from the per-box classes (DH_GATE_PREREG.md)."""
    vals = list(rows.values())
    if any(v in ("ACCEPT", "INCONSISTENT") for v in vals):
        return "FAIL"
    excluded = ("TRUTH_UNAVAILABLE", "TRUTH_EMPTY", "CONTROL_NOT_EMPTY")
    zero = [v for k, v in rows.items() if k.startswith("Z") and v not in excluded]
    ctrl = [v for k, v in rows.items() if k.startswith("C") and v not in excluded]
    if zero and ctrl and "REFUSE" in zero and all(v in ("REFUSE", "REFUSE_WEAK") for v in zero) \
            and all(v == "DISCRIMINATES" for v in ctrl):
        return "PASS"
    return "INCONCLUSIVE"


def main() -> None:  # pragma: no cover - the gate run itself, recorded in RUNS.md
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / "dh_gate_results.json"
    res: dict[str, Any] = {"preregistration": "DH_GATE_PREREG.md", "truth": {}, "runs": {}}
    for name, g in GATE_BOXES.items():
        res["truth"][name] = truth(g["box"], g["t"])
        print(name, "truth", res["truth"][name], flush=True)
    for fault in (None,) + FAULTS:
        key = fault or "clean"
        rows, outs = {}, {}
        for name, g in GATE_BOXES.items():
            r = dh_barrier(g["box"], g["t"], faults=frozenset([fault]) if fault else frozenset())
            outs[name] = r
            rows[name] = classify(g["kind"], res["truth"][name]["N"] if res["truth"][name]["status"] == "decided" else None,
                                  r["winding"])
        res["runs"][key] = {"rows": rows, "verdict": verdict(rows), "outputs": outs}
        print(key, res["runs"][key]["verdict"], rows, flush=True)
        out_path.write_text(json.dumps(res, indent=1, default=str) + "\n")


# --------------------------------------------------------------------------- #
#  Stage 2 (DH_GATE_PREREG_2.md, added 2026-10-31).  Everything above this line
#  is stage 1 as preregistered at 2ba8cbba3 and is not changed: its boxes, its
#  parameters, its decision table and its verdict rule.  Stage 2 adds two boxes
#  at hunt #61's close zero pair (z = 480.6903 +- 0.0204i, wide t = 144/625),
#  placed so that one segment of the four-point mesh of the ``no_margin`` fault
#  is centred over the pair: the zeros on one side of that segment subtend
#  about 296 degrees, more than the half turn a principal argument can carry.
# --------------------------------------------------------------------------- #

GATE_BOXES_2 = {
    "Z5": {"t": _F("144/625"), "box": (_F("48039/100"), _F("48119/100"), _F("1/100"), _F("3/100")),
           "kind": "zero", "why": "hunt #61's zero 480.6903 + 0.0204i; top edge 0.0096 above it"},
    "C3": {"t": _F("144/625"), "box": (_F("48039/100"), _F("48119/100"), _F("3/100"), _F("1/5")),
           "kind": "control", "why": "above Z5; bottom edge 0.0096 above the zero, 0.0504 above its conjugate"},
}


def run_stage2_boxes(names: list[str]) -> dict[str, Any]:
    """Truth and every run (clean and each fault) on the named stage-2 boxes; no verdicts."""
    part: dict[str, Any] = {"truth": {}, "outputs": {}}
    for name in names:
        g = GATE_BOXES_2[name]
        part["truth"][name] = truth(g["box"], g["t"])
        print(name, "truth", part["truth"][name], flush=True)
        for fault in (None,) + FAULTS:
            key = fault or "clean"
            r = dh_barrier(g["box"], g["t"], faults=frozenset([fault]) if fault else frozenset())
            part["outputs"].setdefault(key, {})[name] = r
            print(name, key, r["winding"], r["n_evaluations"], r["seconds"], flush=True)
    return part


def assemble_stage2(parts: list[dict[str, Any]]) -> dict[str, Any]:
    """The stage-2 record from per-box parts: rows and verdicts by the stage-1 rules, unchanged."""
    res: dict[str, Any] = {"preregistration": "DH_GATE_PREREG_2.md", "truth": {}, "runs": {}}
    outputs: dict[str, dict[str, Any]] = {}
    for p in parts:
        res["truth"].update(p["truth"])
        for key, by_box in p["outputs"].items():
            outputs.setdefault(key, {}).update(by_box)
    assert set(res["truth"]) == set(GATE_BOXES_2), "stage 2 needs every one of its boxes"
    for key in ("clean",) + FAULTS:
        rows = {}
        for name, g in GATE_BOXES_2.items():
            tr = res["truth"][name]
            rows[name] = classify(g["kind"], tr["N"] if tr["status"] == "decided" else None,
                                  outputs[key][name]["winding"])
        res["runs"][key] = {"rows": rows, "verdict": verdict(rows), "outputs": outputs[key]}
    return res


def combined_verdicts(stage1: dict[str, Any], stage2: dict[str, Any]) -> dict[str, str]:
    """The preregistered verdict rule over the union of both stages' rows, per run."""
    return {key: verdict({**stage1["runs"][key]["rows"], **stage2["runs"][key]["rows"]})
            for key in stage1["runs"]}


def main_stage2(argv: list[str]) -> None:  # pragma: no cover - the stage-2 run, recorded in RUNS.md (E8)
    """``dh_gate.py stage2 PART.json BOX...`` runs boxes; ``dh_gate.py stage2 OUT.json --assemble PART...``
    writes the record."""
    out_path = Path(argv[0])
    if argv[1] == "--assemble":
        parts = [json.loads(Path(p).read_text()) for p in argv[2:]]
        res = assemble_stage2(parts)
        for key, run in res["runs"].items():
            print(key, run["verdict"], run["rows"], flush=True)
    else:
        res = run_stage2_boxes(argv[1:])
    out_path.write_text(json.dumps(res, indent=1, default=str) + "\n")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "stage2":
        main_stage2(sys.argv[2:])
    else:
        main()
