"""The density failure of `ontology/06_the_polya_hilbert_prototype.py`, counted.

`docs/15` §6 reports the prototype's Mode 20 at `1.937` against the target
`77.145`, and its Reality Check adds that "we have dozens of frequencies
below 17.7, where zeta only has one zero".  Both are true.  Neither is a
number you can watch move, and the direction it moves in is the part that
matters: this is the hunts checklist's precision-response control, which says
an artifact does not respond to refinement while a real quantity does.

What is measured here is the counting function.  Write `N_M(T)` for the
number of positive modes of the prototype below `T`, and `N(T)` for the
number of ordinates of zeta below `T`.  At `T = gamma_1 = 14.1347...`,
`N(T) = 0` by definition, so every mode the prototype puts below that height
is a mode zeta does not have.

The refinement knob is the truncation `N`, the number of nodes.  Refining it
does not thin the low-frequency crowd.  It adds to it, roughly in proportion
to `N`, while the top of the spectrum creeps up like `log N`.  The gap is not
a finite-size effect waiting for a bigger matrix; growing the matrix widens
it.

Nothing in `ontology/` is modified: the prototype is imported by path.

Run:  .venv/bin/python hunts/f1_engine_controls/density.py --sizes 100,200,400,800
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
from pathlib import Path

import numpy as np

from zeta.zeros import N_of_T

_REPO_ROOT = Path(__file__).resolve().parents[2]
_PROTOTYPE = _REPO_ROOT / "ontology" / "06_the_polya_hilbert_prototype.py"

#: zeta's first ordinate.  `N(T) = 0` for every `T` below it.
GAMMA_1 = 14.134725141734694

#: The height `docs/15` names in the Reality Check, where zeta has one zero.
DOCS15_HEIGHT = 17.7

#: The 20th ordinate, the target `docs/15` §6 compares Mode 20 against.
GAMMA_20 = 77.14484


def load_prototype():
    """Import `ontology/06_the_polya_hilbert_prototype.py` by path."""
    spec = importlib.util.spec_from_file_location("f1_prototype_06", _PROTOTYPE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def spectrum(n_nodes: int) -> np.ndarray:
    """The positive modes of the prototype at truncation `n_nodes`, sorted."""
    matrix = load_prototype().build_polya_hilbert_operator(n_nodes)
    gammas = np.imag(np.linalg.eigvals(matrix))
    return np.sort(gammas[gammas > 1e-9])


def counts(n_nodes: int) -> dict:
    """Counting-function comparison at one truncation."""
    gammas = spectrum(n_nodes)
    top = float(gammas[-1])
    return {
        "n_nodes": n_nodes,
        "n_modes": int(gammas.size),
        "top_mode": top,
        "modes_below_gamma_1": int((gammas < GAMMA_1).sum()),
        "zeta_zeros_below_gamma_1": 0,
        "modes_below_docs15_height": int((gammas < DOCS15_HEIGHT).sum()),
        "zeta_zeros_below_docs15_height": int(N_of_T(DOCS15_HEIGHT)),
        "zeta_zeros_below_top_mode": int(N_of_T(top)),
        "mode_20": float(gammas[19]) if gammas.size >= 20 else None,
    }


def nodes_needed_for(target: float, rows: list[dict]) -> float | None:
    """Extrapolated truncation at which the top mode would reach `target`.

    A two-point fit of `top_mode` against `log2(n_nodes)` over the measured
    range, extended well past it.  This is an extrapolation of a trend, not a
    law: read it as an order of magnitude and nothing finer.
    """
    if len(rows) < 2:
        return None
    first, last = rows[0], rows[-1]
    span = math.log2(last["n_nodes"] / first["n_nodes"])
    if span <= 0:
        return None
    per_doubling = (last["top_mode"] - first["top_mode"]) / span
    if per_doubling <= 0:
        return None
    doublings = (target - last["top_mode"]) / per_doubling
    return last["n_nodes"] * 2.0**doublings


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--sizes", default="100,200,400,800")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args()

    rows = [counts(int(s)) for s in args.sizes.split(",")]
    print(f"{'nodes':>7} {'modes':>7} {'top mode':>10} {'below g1':>9} {'zeta below g1':>14}")
    for row in rows:
        print(
            f"{row['n_nodes']:>7} {row['n_modes']:>7} {row['top_mode']:>10.4f} "
            f"{row['modes_below_gamma_1']:>9} {row['zeta_zeros_below_gamma_1']:>14}"
        )
    needed = nodes_needed_for(GAMMA_20, rows)
    print(f"\ntop mode grows like log(nodes); extrapolated nodes to reach gamma_20 = "
          f"{GAMMA_20}: ~1e{math.log10(needed):.1f}" if needed else "")
    print("modes below gamma_1 per node: "
          + ", ".join(f"{r['modes_below_gamma_1'] / r['n_nodes']:.3f}" for r in rows))
    if args.json:
        args.json.write_text(
            json.dumps({"rows": rows, "extrapolated_nodes_for_gamma_20": needed}, indent=2),
            encoding="utf-8",
        )
        print(f"wrote {args.json}")


if __name__ == "__main__":
    main()
