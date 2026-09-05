"""Discover a finite adversary. Numerical discovery assigns no lower bound."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "amtopa_ceiling"
sys.path.insert(0, str(SOURCE))
from family import PAIR_LIST, PAIR_SPAN, amtopa_coeffs, frequencies, kernel
from ceiling import W_matrix


def discover():
    pool_path = SOURCE / "artifacts" / "cut_pool.npy"
    original = np.load(pool_path)
    reflected = np.vstack([original, original[:, ::-1]])
    coeffs = amtopa_coeffs()
    freq = frequencies(len(coeffs))
    k0 = kernel(0, coeffs, freq)[0]
    eq = np.zeros((7, 28))
    for span in range(1, 7):
        eq[span - 1, np.flatnonzero(PAIR_SPAN == span)] = 1
    eq[6, 21:27] = 1
    rhs = np.r_[np.full(6, 2.0), 93 / 23000]
    objectives = {}
    for label, gaps in (("original", original), ("reversal_closed", reflected)):
        weights = W_matrix(gaps, coeffs, freq, k0, chunk=1000)
        result = linprog(
            np.r_[np.zeros(27), -1.0],
            A_ub=np.c_[-weights, -gaps, np.ones(len(gaps))],
            b_ub=np.zeros(len(gaps)), A_eq=eq, b_eq=rhs,
            bounds=[(0, None)] * 27 + [(None, None)], method="highs",
            options={"dual_feasibility_tolerance": 1e-9,
                     "primal_feasibility_tolerance": 1e-9},
        )
        if not result.success:
            raise RuntimeError(result.message)
        objectives[label] = float(-result.fun)
    probabilities = -result.ineqlin.marginals
    # Fold both members of each orbit into one weight, then enforce exact
    # symmetry ourselves. None of the solver's feasibility claims is trusted.
    orbit_mass = probabilities[:len(original)] + probabilities[len(original):]
    active = np.flatnonzero(orbit_mass > 1e-10)
    counts = [max(0, round(float(orbit_mass[i]) * 10**12)) for i in active]
    total = sum(counts)
    orbits = [{"source_row": int(i), "weight": str(Fraction(count, total)),
               "gaps": [str(Fraction(format(float(g), ".15g"))) for g in original[i]]}
              for i, count in zip(active, counts)]
    return {
        "status": "finite adversary; validate with verify.py",
        "source_sha256": hashlib.sha256(pool_path.read_bytes()).hexdigest(),
        "source_rows": len(original), "float_lp_objectives": objectives,
        "window_numerators": [1000000000, 12378982, -12602495, 4164033,
                              5741405, -1724025, 6219280, -8047828, 6321519,
                              -5241981, -892658, 560544, -431207, 357969,
                              -310433, 100000, -100000],
        "window_denominator": 10**9,
        "pressure_budget": "93/23000", "span_budget": "2",
        "upper_target": "7914014/1000000000",
        "span_caps": ["0.000634884759717", "0.000010127109795", "0.000073116002704",
                      "0.000045872037949", "0.000083018119185", "0.000058811254374"],
        "mean_gap_cap": "1.509184664171",
        "reported_lower_endpoint": "791685781/100000000000",
        "orbits": orbits,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "adversary.json")
    args = parser.parse_args()
    artifact = discover()
    args.output.write_text(json.dumps(artifact, indent=2) + "\n")
    print(json.dumps({k: artifact[k] for k in ("source_sha256", "float_lp_objectives")}))
    print(f"Wrote {len(artifact['orbits'])} reversal orbits to {args.output}")
