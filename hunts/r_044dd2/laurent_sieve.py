#!/usr/bin/env python3
"""Exact signed-lattice sieve for a Krenn-Gu support survivor.

Each zero binomial ``x^a + x^b = 0`` gives the torus relation
``x^(a-b) = -1``.  An odd integer combination that equals the exponent
difference of two terms in a zero trinomial forces those two terms to cancel,
leaving a nonzero monomial equal to zero.

The method follows the signed-Laurent certificate architecture published in
``algal/krenn-gu-6x3-certificate``.  This implementation deduplicates the
8x3 relations and emits the small integer combination for direct replay.
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
from pathlib import Path

from ortools.sat.python import cp_model
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

HERE = Path(__file__).resolve().parent


def load_elementary_module():
    spec = importlib.util.spec_from_file_location(
        "krenn_elementary_sieve", HERE / "algebraic_sieve.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load algebraic_sieve.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def exponent(monomial: tuple[int, ...], active_lookup: dict[int, int]) -> tuple[int, ...]:
    out = [0] * len(active_lookup)
    for variable in monomial:
        out[active_lookup[variable]] += 1
    return tuple(out)


def subtract(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a - b for a, b in zip(left, right, strict=True))


def signed_membership_tester(deltas: tuple[tuple[int, ...], ...]):
    active_coordinates = tuple(
        i for i in range(len(deltas[0])) if any(delta[i] for delta in deltas)
    )
    inactive = set(range(len(deltas[0]))) - set(active_coordinates)
    augmented = Matrix(
        [[delta[i] for delta in deltas] + [0] for i in active_coordinates]
        + [[1] * len(deltas) + [2]]
    )
    basis = hermite_normal_form(augmented)
    _, pivot_rows = basis.T.rref()
    coordinates = basis.extract(pivot_rows, range(basis.cols)).inv()

    def member(delta: tuple[int, ...], parity: int) -> bool:
        if any(delta[i] for i in inactive):
            return False
        vector = Matrix([delta[i] for i in active_coordinates] + [parity])
        coeffs = coordinates * vector.extract(pivot_rows, [0])
        return all(value.q == 1 for value in coeffs) and basis * coeffs == vector

    return active_coordinates, member


def find_short_combination(
    deltas: tuple[tuple[int, ...], ...],
    target: tuple[int, ...],
    active_coordinates: tuple[int, ...],
    max_size: int,
    seconds: float,
) -> tuple[int, ...] | None:
    model = cp_model.CpModel()
    coefficients = [
        model.new_int_var(-max_size, max_size, f"c_{i}") for i in range(len(deltas))
    ]
    absolutes = [model.new_int_var(0, max_size, f"a_{i}") for i in range(len(deltas))]
    for coefficient, absolute in zip(coefficients, absolutes, strict=True):
        model.add_abs_equality(absolute, coefficient)
    model.add(sum(absolutes) <= max_size)
    for coordinate in active_coordinates:
        model.add(
            sum(
                delta[coordinate] * coefficient
                for delta, coefficient in zip(deltas, coefficients, strict=True)
                if delta[coordinate]
            )
            == target[coordinate]
        )
    parity_quotient = model.new_int_var(-max_size, max_size, "parity")
    model.add(sum(coefficients) == 2 * parity_quotient + 1)
    model.minimize(sum(absolutes))
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 8
    status = solver.solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None
    return tuple(solver.value(coefficient) for coefficient in coefficients)


def sieve(census: Path, orbit: int, max_size: int, seconds: float) -> dict[str, object]:
    elementary = load_elementary_module()
    payload = json.loads(census.read_text(encoding="utf-8"))
    row = next(item for item in payload["rows"] if item["orbit"] == orbit)
    support = {tuple(item) for item in row["support_keys"]}
    keys = elementary.all_keys()
    global_lookup = {key: index for index, key in enumerate(keys)}
    active_globals = tuple(sorted(global_lookup[key] for key in support))
    active_lookup = {variable: i for i, variable in enumerate(active_globals)}
    pms = elementary.matchings(tuple(range(8)))

    relation_by_delta = {}
    trinomials = []
    for coloring in itertools.product(range(3), repeat=8):
        if len(set(coloring)) == 1:
            continue
        signature = elementary.supported_signature(
            coloring, support, pms, keys, global_lookup
        )
        vectors = tuple(exponent(term, active_lookup) for term in signature)
        if len(vectors) == 2:
            delta = subtract(vectors[0], vectors[1])
            reverse = tuple(-value for value in delta)
            if reverse < delta:
                delta = reverse
                oriented_terms = (signature[1], signature[0])
            else:
                oriented_terms = signature
            relation_by_delta.setdefault(
                delta,
                {"coloring": coloring, "terms": oriented_terms},
            )
        elif len(vectors) == 3:
            trinomials.append((coloring, signature, vectors))

    deltas = tuple(sorted(relation_by_delta))
    relations = tuple(relation_by_delta[delta] for delta in deltas)
    active_coordinates, member = signed_membership_tester(deltas)
    lattice_candidates = 0
    for coloring, signature, vectors in trinomials:
        for left, right in ((0, 1), (0, 2), (1, 2)):
            target = subtract(vectors[left], vectors[right])
            if not member(target, 1):
                continue
            lattice_candidates += 1
            coefficients = find_short_combination(
                deltas, target, active_coordinates, max_size, seconds
            )
            if coefficients is None:
                continue
            combined = tuple(
                sum(coefficient * delta[i] for coefficient, delta in zip(coefficients, deltas, strict=True))
                for i in range(len(active_globals))
            )
            if combined != target or sum(coefficients) % 2 != 1:
                raise AssertionError("constructed Laurent certificate failed replay")
            used = [
                {
                    "coefficient": coefficient,
                    "binomial_coloring": relations[i]["coloring"],
                    "left_monomial": relations[i]["terms"][0],
                    "right_monomial": relations[i]["terms"][1],
                }
                for i, coefficient in enumerate(coefficients)
                if coefficient
            ]
            remaining = next(i for i in range(3) if i not in (left, right))
            return {
                "format": 1,
                "orbit": orbit,
                "support_size": len(support),
                "unique_binomial_relations": len(deltas),
                "zero_trinomials": len(trinomials),
                "lattice_candidates_examined": lattice_candidates,
                "certificate": {
                    "trinomial_coloring": coloring,
                    "trinomial_terms": signature,
                    "canceling_indices": [left, right],
                    "forced_zero_monomial_index": remaining,
                    "combination_l1": sum(abs(value) for value in coefficients),
                    "relations": used,
                },
                "verified": True,
                "interpretation": "exact contradiction for this support only",
            }
    return {
        "format": 1,
        "orbit": orbit,
        "support_size": len(support),
        "unique_binomial_relations": len(deltas),
        "zero_trinomials": len(trinomials),
        "lattice_candidates_examined": lattice_candidates,
        "certificate": None,
        "verified": False,
        "interpretation": "no short certificate found; not evidence of realizability",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census", type=Path)
    parser.add_argument("--orbit", type=int, required=True, choices=range(31))
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--seconds", type=float, default=5.0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = sieve(args.census, args.orbit, args.max_size, args.seconds)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "orbit": result["orbit"],
                "support_size": result["support_size"],
                "unique_binomial_relations": result["unique_binomial_relations"],
                "zero_trinomials": result["zero_trinomials"],
                "lattice_candidates_examined": result["lattice_candidates_examined"],
                "certificate_found": result["certificate"] is not None,
                "combination_l1": (
                    result["certificate"]["combination_l1"]
                    if result["certificate"] is not None
                    else None
                ),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
