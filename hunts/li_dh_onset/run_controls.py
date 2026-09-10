"""Every oracle this hunt promised, run before any Davenport-Heilbronn number
is believed.

The order matters and is the order of the file.  The positive control comes
first because it is the one that can fail for a reason that invalidates
everything after it: if the pipeline in :mod:`dhli`, pointed at Riemann's xi,
does not reproduce the coefficients ``zeta.li`` has pinned since long before
this hunt existed, then nothing it says about a different function is worth
reading.  ``zeta/li.py``'s committed table ``data/li_lambda_*_radius0.5.json``
is read as a file, so the reference is the artifact the repository's own tests
pin and not a value recomputed by the same session that is being checked.

Then the evaluator: the fast completed-DH evaluator against
``zeta.epstein.completed_dh`` on the actual sampling contour, and the two defect
functions ``zeta.epstein`` exposes for exactly this purpose.

Then radius independence, which is ``zeta.li``'s own argument that the analytic
branch is right: a branch error or a missed winding is a function of the
contour, so three contours that agree to the returned digits have no room for
one.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zeta.epstein import completed_dh, dh_functional_equation_defect, dh_mean_value_defect
from zeta.li import li_closed_form_lambda1

from dhli import (
    completed_dh_fast,
    li_coefficients_cauchy,
    node_count,
    sample_circle,
    coefficients_from_samples,
    work_digits,
)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ART = os.path.join(HERE, "artifacts")

#: The pinned reference table: zeta's Li coefficients, radius 0.5, as committed.
REFERENCE_TABLE = os.path.join(ROOT, "data", "li_lambda_dps25_methodcauchy_n400_radius0.5.json")


def _rel(a, b):
    scale = max(abs(a), abs(b), mp.mpf(1))
    return abs(a - b) / scale


def xi_positive_control(n_max: int, dps: int, radii, processes: int) -> dict:
    """The pipeline pointed at xi, against the committed zeta table.

    A control that cannot fail is not a control, so the comparison is made at
    every index rather than at a hand-picked few, and the worst index is
    reported next to the worst value.
    """
    with open(REFERENCE_TABLE) as fh:
        blob = json.load(fh)
    ref_dps = int(blob["dps"])
    rows = []
    with mp.workdps(ref_dps + 10):
        ref = [mp.mpf(v) for v in blob["values"][:n_max]]
        lam1_closed = li_closed_form_lambda1(ref_dps + 10)
        rows.append(
            {
                "check": "committed table lambda_1 against the closed form",
                "worst_rel": mp.nstr(_rel(ref[0], lam1_closed), 8),
            }
        )
    out = {"reference_file": os.path.relpath(REFERENCE_TABLE, ROOT),
           "reference_dps": ref_dps, "n_max": n_max, "notes": rows, "radii": []}
    for r in radii:
        rep: dict = {}
        t0 = time.time()
        lam = li_coefficients_cauchy("xi", n_max, dps=dps, radius=r,
                                     processes=processes, report=rep)
        rep["seconds"] = round(time.time() - t0, 2)
        with mp.workdps(ref_dps + 10):
            diffs = [(_rel(mp.mpf(lam[i]), ref[i]), i + 1) for i in range(n_max)]
            worst, where = max(diffs)
            rep["worst_relative_vs_committed_table"] = mp.nstr(worst, 8)
            rep["worst_index"] = where
            rep["lambda_1"] = mp.nstr(mp.mpf(lam[0]), 22)
            rep["lambda_50"] = mp.nstr(mp.mpf(lam[49]), 16)
            rep["lambda_300"] = mp.nstr(mp.mpf(lam[299]), 16)
        out["radii"].append(rep)
        print("xi control", rep, flush=True)
    return out


def evaluator_control(radius: float, dps: int, n_probe: int = 12) -> dict:
    """The fast evaluator against ``zeta.epstein.completed_dh`` on the contour,
    plus the two defects that test the completion itself rather than my use of
    it.
    """
    R = mp.mpf(str(radius))
    rows = []
    with mp.workdps(dps + 15):
        for j in range(n_probe):
            z = R * mp.expjpi(mp.mpf(2 * j) / n_probe)
            s = 1 / (1 - z)
            fast = completed_dh_fast(s)
            ref = completed_dh(s, dps + 15)
            rows.append(
                {
                    "s": mp.nstr(s, 12),
                    "abs_F": mp.nstr(abs(fast), 12),
                    "rel_fast_vs_reference": mp.nstr(_rel(fast, ref), 6),
                }
            )
    worst = max(float(r["rel_fast_vs_reference"]) for r in rows)
    fe = [
        mp.nstr(abs(dh_functional_equation_defect(mp.mpc(a, b), 40)), 6)
        for a, b in ((0.3, 1.7), (2.2, -0.9), (0.6, 4.4), (5.0, 2.0))
    ]
    mv = mp.nstr(abs(dh_mean_value_defect(mp.mpf("1.001"), "0.25", 30)), 6)
    return {
        "radius": radius,
        "contour_probe": rows,
        "worst_relative_fast_vs_reference": worst,
        "functional_equation_defects_dps40": fe,
        "mean_value_defect_at_1.001_dps30": mv,
        "min_distance_from_contour_to_s_eq_1": radius / (1 + radius),
    }


def radius_independence(n_max: int, dps: int, radii, processes: int) -> dict:
    """The same lambda_n(DH) off three different contours.

    ``zeta.li`` uses exactly this as its evidence that the analytic branch is
    right, and the reason it works is that a branch error is a property of the
    contour: an unwrap that took a wrong 2 pi somewhere on |z| = 0.9 has no
    reason to take the matching wrong turn on |z| = 0.5.
    """
    tables = {}
    reports = []
    for r in radii:
        rep: dict = {}
        t0 = time.time()
        lam = li_coefficients_cauchy("dh", n_max, dps=dps, radius=r,
                                     processes=processes, report=rep)
        rep["seconds"] = round(time.time() - t0, 2)
        tables[str(r)] = lam
        reports.append(rep)
        print("dh radius", rep, flush=True)
    keys = list(tables)
    pairs = []
    with mp.workdps(dps + 10):
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                a, b = tables[keys[i]], tables[keys[j]]
                diffs = [(_rel(a[k], b[k]), k + 1) for k in range(n_max)]
                worst, where = max(diffs)
                pairs.append(
                    {
                        "radii": [keys[i], keys[j]],
                        "worst_relative": mp.nstr(worst, 8),
                        "worst_index": where,
                    }
                )
    return {
        "n_max": n_max,
        "dps": dps,
        "runs": reports,
        "pairwise": pairs,
        "bar": "1e-25 relative; the working-precision rule carries dps + 2*guard "
               "digits past the r^{-n} amplification at n = n_max",
        "passed": all(float(p["worst_relative"]) < 1e-25 for p in pairs),
        "lambda_1_by_radius": {k: mp.nstr(v[0], 22) for k, v in tables.items()},
        "lambda_n_max_by_radius": {k: mp.nstr(v[-1], 22) for k, v in tables.items()},
    }


def parallel_identity(n_max: int, dps: int, radius, processes: int) -> dict:
    """A parallel run and a serial run of the same circle, compared bit for bit.

    Splitting the sampling across processes is the only thing in this hunt that
    could quietly reorder or re-round a number, so it is checked rather than
    argued.
    """
    work = work_digits(n_max, dps, radius)
    npts = node_count(n_max, work, radius)
    a = sample_circle("dh", work, radius, npts, processes=1)
    b = sample_circle("dh", work, radius, npts, processes=processes)
    same = all(x.real._mpf_ == y.real._mpf_ and x.imag._mpf_ == y.imag._mpf_
               for x, y in zip(a, b))
    la = coefficients_from_samples(a, n_max, work, radius, processes=1)
    lb = coefficients_from_samples(b, n_max, work, radius, processes=processes)
    same_lam = all(x._mpf_ == y._mpf_ for x, y in zip(la, lb))
    return {"n_points": npts, "work_digits": work, "processes": processes,
            "samples_bit_identical": bool(same),
            "coefficients_bit_identical": bool(same_lam)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--processes", type=int, default=3)
    ap.add_argument("--xi-n", type=int, default=400)
    ap.add_argument("--dh-n", type=int, default=200)
    args = ap.parse_args()

    out: dict = {"generated": time.strftime("%Y-%m-%dT%H:%M:%S")}
    t0 = time.time()

    out["xi_positive_control"] = xi_positive_control(
        args.xi_n, 25, ["0.5", "0.9"], args.processes
    )
    out["evaluator_control"] = evaluator_control(0.9, 30)
    print("evaluator", out["evaluator_control"]["worst_relative_fast_vs_reference"],
          out["evaluator_control"]["mean_value_defect_at_1.001_dps30"], flush=True)
    out["parallel_identity"] = parallel_identity(64, 30, "0.9", args.processes)
    print("parallel", out["parallel_identity"], flush=True)
    out["radius_independence"] = radius_independence(
        args.dh_n, 30, ["0.5", "0.7", "0.9"], args.processes
    )
    out["seconds_total"] = round(time.time() - t0, 1)

    os.makedirs(ART, exist_ok=True)
    path = os.path.join(ART, "controls.json")
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", path)


if __name__ == "__main__":
    main()
