#!/usr/bin/env python3
"""Sparse fixed-degree ideal-membership screen for Krenn-Gu supports.

The earlier Laurent screen uses literal zero binomials. This screen retains
multi-term zero equations, strips their nonzero support-torus factors, and
tests whether a product of monochromatic target brackets lies in the exact
fixed-degree span of monomial multiples of those equations.

A negative result narrows this certificate method only. A positive result is
also only a candidate until an explicit identity is emitted and replayed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import time
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Mapping

HERE = Path(__file__).resolve().parent
Monomial = tuple[int, ...]


def emit_progress(stage: str, started_at: float, **counts: int) -> None:
    print(
        json.dumps(
            {
                "stage": stage,
                "elapsed_seconds": round(time.monotonic() - started_at, 1),
                **counts,
            },
            sort_keys=True,
        ),
        flush=True,
    )


@dataclass(frozen=True)
class Relation:
    coloring: tuple[int, ...]
    terms: tuple[Monomial, ...]


def load_elementary_module():
    spec = importlib.util.spec_from_file_location(
        "krenn_polynomial_elementary", HERE / "algebraic_sieve.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load algebraic_sieve.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def multiply_monomials(left: Monomial, right: Monomial) -> Monomial:
    return tuple(sorted((*left, *right)))


def divide_monomials(dividend: Monomial, divisor: Monomial) -> Monomial:
    remaining = list(dividend)
    for variable in divisor:
        remaining.remove(variable)
    return tuple(remaining)


def strip_common_factor(terms: tuple[Monomial, ...]) -> tuple[Monomial, ...]:
    common = Counter(terms[0])
    for term in terms[1:]:
        common &= Counter(term)
    factor = tuple(sorted(common.elements()))
    return tuple(divide_monomials(term, factor) for term in terms)


def multiply_polynomials(
    left: Mapping[Monomial, int], right: Iterable[Monomial]
) -> dict[Monomial, int]:
    result: dict[Monomial, int] = defaultdict(int)
    for left_monomial, coefficient in left.items():
        for right_monomial in right:
            result[multiply_monomials(left_monomial, right_monomial)] += coefficient
    return dict(result)


def build_system(support_path: Path):
    elementary = load_elementary_module()
    payload = json.loads(support_path.read_text(encoding="utf-8"))
    support = tuple(sorted(tuple(item) for item in payload["support_keys"]))
    support_lookup = {key: index for index, key in enumerate(support)}
    keys = elementary.all_keys()
    global_lookup = {key: index for index, key in enumerate(keys)}
    matchings = elementary.matchings(tuple(range(8)))
    targets = []
    relations = []
    histogram: Counter[int] = Counter()
    for coloring in itertools.product(range(3), repeat=8):
        signature = elementary.supported_signature(
            coloring, set(support), matchings, keys, global_lookup
        )
        if not signature:
            continue
        terms = tuple(
            tuple(sorted(support_lookup[keys[variable]] for variable in term))
            for term in signature
        )
        stripped = strip_common_factor(terms)
        if len(set(coloring)) == 1:
            targets.append((coloring, stripped))
        elif len(stripped) >= 2:
            relations.append(Relation(coloring, stripped))
            histogram[len(stripped)] += 1
    return support, tuple(targets), tuple(relations), dict(sorted(histogram.items()))


def monomial_divisors(monomial: Monomial, degree: int):
    if degree > len(monomial):
        return
    seen = set()
    for positions in itertools.combinations(range(len(monomial)), degree):
        divisor = tuple(monomial[position] for position in positions)
        if divisor not in seen:
            seen.add(divisor)
            yield divisor


def reachable_closure(
    relations: tuple[Relation, ...],
    target: Mapping[Monomial, int],
    *,
    max_processed: int | None = None,
    progress_every: int | None = None,
):
    relation_index: dict[Monomial, list[int]] = defaultdict(list)
    relation_degrees = set()
    for index, relation in enumerate(relations):
        degree = len(relation.terms[0])
        relation_degrees.add(degree)
        for term in relation.terms:
            relation_index[term].append(index)

    reachable = set(target)
    queue = deque(target)
    columns: set[tuple[int, Monomial]] = set()
    processed = 0
    complete = True
    started_at = time.monotonic()
    while queue:
        if max_processed is not None and processed >= max_processed:
            complete = False
            break
        node = queue.popleft()
        processed += 1
        for degree in relation_degrees:
            for divisor in monomial_divisors(node, degree):
                for index in relation_index.get(divisor, ()):
                    multiplier = divide_monomials(node, divisor)
                    column = (index, multiplier)
                    if column in columns:
                        continue
                    columns.add(column)
                    for term in relations[index].terms:
                        neighbor = multiply_monomials(term, multiplier)
                        if neighbor not in reachable:
                            reachable.add(neighbor)
                            queue.append(neighbor)
        if progress_every and processed % progress_every == 0:
            emit_progress(
                "closure",
                started_at,
                processed_monomials=processed,
                queued_monomials=len(queue),
                reachable_monomials=len(reachable),
                relation_multiples=len(columns),
            )
    return (
        tuple(sorted(reachable)),
        tuple(sorted(columns)),
        processed,
        len(queue),
        complete,
    )


def _add_scaled_modular(
    destination: dict[int, int],
    source: Mapping[int, int],
    scale: int,
    prime: int,
) -> None:
    for row, coefficient in source.items():
        updated = (destination.get(row, 0) + scale * coefficient) % prime
        if updated:
            destination[row] = updated
        else:
            destination.pop(row, None)


def modular_membership(
    relations: tuple[Relation, ...],
    target: Mapping[Monomial, int],
    reachable: tuple[Monomial, ...],
    columns: tuple[tuple[int, Monomial], ...],
    prime: int,
    progress_every: int | None = None,
) -> tuple[bool, int, int]:
    row_lookup = {monomial: row for row, monomial in enumerate(reachable)}
    basis: dict[int, dict[int, int]] = {}
    started_at = time.monotonic()
    for column_number, (relation_index, multiplier) in enumerate(columns, start=1):
        vector: dict[int, int] = defaultdict(int)
        for term in relations[relation_index].terms:
            vector[row_lookup[multiply_monomials(term, multiplier)]] += 1
        vector = {
            row: coefficient % prime
            for row, coefficient in vector.items()
            if coefficient % prime
        }
        while vector:
            pivot = min(vector)
            basis_vector = basis.get(pivot)
            if basis_vector is None:
                inverse = pow(vector[pivot], -1, prime)
                basis[pivot] = {
                    row: coefficient * inverse % prime
                    for row, coefficient in vector.items()
                }
                break
            _add_scaled_modular(vector, basis_vector, -vector[pivot], prime)
        if progress_every and column_number % progress_every == 0:
            emit_progress(
                "modular_elimination",
                started_at,
                processed_columns=column_number,
                total_columns=len(columns),
                rank=len(basis),
            )

    residual = {
        row_lookup[monomial]: coefficient % prime
        for monomial, coefficient in target.items()
        if coefficient % prime
    }
    while residual:
        pivot = min(residual)
        basis_vector = basis.get(pivot)
        if basis_vector is None:
            return False, len(basis), len(residual)
        _add_scaled_modular(residual, basis_vector, -residual[pivot], prime)
    return True, len(basis), 0


def _add_scaled_exact(
    destination: dict[int, Fraction],
    source: Mapping[int, Fraction],
    scale: Fraction,
) -> None:
    for row, coefficient in source.items():
        updated = destination.get(row, Fraction(0)) + scale * coefficient
        if updated:
            destination[row] = updated
        else:
            destination.pop(row, None)


def exact_membership(
    relations: tuple[Relation, ...],
    target: Mapping[Monomial, int],
    reachable: tuple[Monomial, ...],
    columns: tuple[tuple[int, Monomial], ...],
    progress_every: int | None = None,
) -> tuple[bool, int, int]:
    row_lookup = {monomial: row for row, monomial in enumerate(reachable)}
    basis: dict[int, dict[int, Fraction]] = {}
    started_at = time.monotonic()
    for column_number, (relation_index, multiplier) in enumerate(columns, start=1):
        vector: dict[int, Fraction] = defaultdict(Fraction)
        for term in relations[relation_index].terms:
            vector[row_lookup[multiply_monomials(term, multiplier)]] += 1
        vector = dict(vector)
        while vector:
            pivot = min(vector)
            basis_vector = basis.get(pivot)
            if basis_vector is None:
                inverse = Fraction(1) / vector[pivot]
                basis[pivot] = {
                    row: coefficient * inverse
                    for row, coefficient in vector.items()
                }
                break
            _add_scaled_exact(vector, basis_vector, -vector[pivot])
        if progress_every and column_number % progress_every == 0:
            emit_progress(
                "exact_elimination",
                started_at,
                processed_columns=column_number,
                total_columns=len(columns),
                rank=len(basis),
            )

    residual = {
        row_lookup[monomial]: Fraction(coefficient)
        for monomial, coefficient in target.items()
        if coefficient
    }
    while residual:
        pivot = min(residual)
        basis_vector = basis.get(pivot)
        if basis_vector is None:
            return False, len(basis), len(residual)
        _add_scaled_exact(residual, basis_vector, -residual[pivot])
    return True, len(basis), 0


def screen(
    support_path: Path,
    *,
    target_indices: tuple[int, ...],
    max_relation_terms: int | None,
    exact: bool,
    prime: int = 2_147_483_647,
    max_processed: int | None = None,
    progress_every: int | None = None,
) -> dict[str, object]:
    support, targets, all_relations, histogram = build_system(support_path)
    if not target_indices or any(index not in range(len(targets)) for index in target_indices):
        raise ValueError("target indices must select the three monochromatic equations")
    relations = tuple(
        relation
        for relation in all_relations
        if max_relation_terms is None or len(relation.terms) <= max_relation_terms
    )
    target: dict[Monomial, int] = {(): 1}
    for index in target_indices:
        target = multiply_polynomials(target, targets[index][1])
    reachable, columns, processed, queued, complete = reachable_closure(
        relations,
        target,
        max_processed=max_processed,
        progress_every=progress_every,
    )
    result: dict[str, object] = {
        "format": 1,
        "orbit": 18,
        "support_input": {
            "path": str(support_path),
            "sha256": file_sha256(support_path),
        },
        "support_size": len(support),
        "target_indices": list(target_indices),
        "target_colorings": [list(targets[index][0]) for index in target_indices],
        "target_terms": len(target),
        "target_degree": len(next(iter(target))),
        "max_relation_terms": max_relation_terms,
        "all_relation_term_histogram": {str(key): value for key, value in histogram.items()},
        "retained_relations": len(relations),
        "reachable_monomials": len(reachable),
        "relation_multiples": len(columns),
        "processed_monomials": processed,
        "queued_monomials": queued,
        "closure_complete": complete,
    }
    if not complete:
        result.update(
            {
                "status": "RESOURCE_LIMIT",
                "interpretation": "incomplete closure; no algebraic conclusion",
            }
        )
        return result
    modular, modular_rank, modular_residual = modular_membership(
        relations, target, reachable, columns, prime, progress_every
    )
    result.update(
        {
            "modular_prime": prime,
            "modular_membership": modular,
            "modular_rank": modular_rank,
            "modular_residual_terms": modular_residual,
        }
    )
    if exact:
        membership, rank, residual = exact_membership(
            relations, target, reachable, columns, progress_every
        )
        result.update(
            {
                "exact_membership": membership,
                "exact_rank": rank,
                "exact_residual_terms": residual,
                "status": (
                    "MEMBERSHIP_CANDIDATE_REQUIRES_IDENTITY"
                    if membership
                    else "NO_FIXED_DEGREE_MEMBERSHIP"
                ),
                "interpretation": (
                    "an explicit identity must be emitted and replayed before excluding the support"
                    if membership
                    else "exact absence in this retained fixed-degree span; not evidence of realizability"
                ),
            }
        )
    else:
        result.update(
            {
                "status": "MODULAR_SCREEN_ONLY",
                "interpretation": "modular prioritization only; no algebraic conclusion",
            }
        )
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("support", type=Path)
    parser.add_argument("--targets", default="0,1,2")
    parser.add_argument("--max-relation-terms", type=int)
    parser.add_argument("--modular-only", action="store_true")
    parser.add_argument("--prime", type=int, default=2_147_483_647)
    parser.add_argument("--max-processed", type=int)
    parser.add_argument("--progress-every", type=int)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    target_indices = tuple(int(value) for value in args.targets.split(","))
    result = screen(
        args.support,
        target_indices=target_indices,
        max_relation_terms=args.max_relation_terms,
        exact=not args.modular_only,
        prime=args.prime,
        max_processed=args.max_processed,
        progress_every=args.progress_every,
    )
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
