"""What `ontology/07_the_imposter_gauntlet.py` actually rejects.

Three statements are in play, and they cannot all be right.

`07` itself concludes: "The Polya-Hilbert Prototype structurally REJECTS the
imposter.  The F1 Geometry we discovered is IMMUNE to false positives."

The `docs/15` Reality Check answers: "The claim that our matrix
'structurally rejects' Davenport-Heilbronn is mathematically empty.  The
construction never actually consults zeta; it just hardcodes the prime
numbers.  A predicate that ignores its input will return the same verdict for
anything."

Measured here, all three parts separately:

1. **The geometry is input-free, and the Reality Check is right about that.**
   `06`'s operator is a function of the truncation `N` and nothing else.
   There is no argument through which a candidate function could enter, so
   "the geometry rejects the imposter" is not a statement about the geometry.

2. **The predicate in `07` is not the geometry, and it does consult its
   input.**  What `07` runs is a multiplicativity test on Dirichlet
   coefficients, and the repository already owns that test as
   `zeta.epstein.claim_multiplicativity`, with the standing rival set behind
   `zeta.epstein.battery`.  Put through it, the predicate passes zeta and
   fails Davenport-Heilbronn and both discriminant -23 Epstein rivals.  The
   Reality Check's "returns the same verdict for anything" is therefore too
   strong: aimed at the operator it lands, aimed at `07` it does not.

3. **"Immune to false positives" is still false.**  The two Dirichlet
   L-functions of the quartic characters mod 5, whose linear combination
   *is* the Davenport-Heilbronn function, pass the same predicate.  So does
   every other primitive L-function with an Euler product.  What the test
   separates is Euler products from linear combinations of them, which is
   what `zeta.epstein.battery`'s docstring says it separates and which is the
   answer `docs/11` gate #3 asks for.  It is not immunity, and it does not
   single out zeta.

Run:  .venv/bin/python hunts/f1_engine_controls/gauntlet.py
"""

from __future__ import annotations

import argparse
import importlib.util
import inspect
import json
from pathlib import Path

import numpy as np
from mpmath import mp

from zeta.epstein import battery, chi5, claim_multiplicativity

_REPO_ROOT = Path(__file__).resolve().parents[2]
_PROTOTYPE_06 = _REPO_ROOT / "ontology" / "06_the_polya_hilbert_prototype.py"


def _load(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def geometry_is_input_free(n_nodes: int = 60) -> dict:
    """The operator of `06` depends on the truncation and nothing else."""
    build = _load(_PROTOTYPE_06, "f1_prototype_06").build_polya_hilbert_operator
    parameters = list(inspect.signature(build).parameters)
    first, second = build(n_nodes), build(n_nodes)
    return {
        "parameters": parameters,
        "takes_only_the_truncation": parameters == ["N"],
        "rebuild_is_identical": bool(np.array_equal(first, second)),
    }


def l_function_interface(conjugate: bool = False) -> dict:
    """A coefficient-only interface for `L(s, chi)` mod 5.

    `claim_multiplicativity` reads `iface["coefficient"]` and nothing else, so
    this is the whole interface the predicate needs.  `chi` is completely
    multiplicative, which is the point: these two L-functions are the
    summands of the Davenport-Heilbronn function, each with an Euler product
    of its own.
    """
    name = "L_chi5_conjugate" if conjugate else "L_chi5"

    def coefficient(n: int):
        if int(n) < 1:
            raise ValueError("Dirichlet coefficients are indexed from n = 1")
        value = chi5(int(n))
        return mp.conj(value) if conjugate else value

    return {"name": name, "coefficient": coefficient}


def measure() -> dict:
    """The three measurements, in the order of the module docstring."""
    verdict = battery(claim_multiplicativity)
    summands = {
        iface["name"]: bool(claim_multiplicativity(iface))
        for iface in (l_function_interface(False), l_function_interface(True))
    }
    return {
        "geometry": geometry_is_input_free(),
        "battery": {k: (list(v) if isinstance(v, tuple) else v) for k, v in verdict.items()},
        "dh_summands": summands,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args()

    result = measure()
    geometry = result["geometry"]
    print("1. the operator of 06 takes only", geometry["parameters"],
          "-> input-free:", geometry["takes_only_the_truncation"])
    print("2. battery(claim_multiplicativity):")
    for key, value in result["battery"].items():
        print(f"     {key}: {value}")
    print("3. the Davenport-Heilbronn summands, against the same predicate:")
    for name, passed in result["dh_summands"].items():
        print(f"     {name}: {passed}")
    print("\nso the predicate separates Euler products from linear combinations "
          "of them, and admits every primitive L-function, zeta included.")
    if args.json:
        args.json.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"wrote {args.json}")


if __name__ == "__main__":
    main()
