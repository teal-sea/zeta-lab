#!/usr/bin/env python3
"""Independent replay of a signed-Laurent support contradiction."""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_elementary_module():
    spec = importlib.util.spec_from_file_location(
        "krenn_elementary_audit", HERE / "algebraic_sieve.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load algebraic_sieve.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def exponent(monomial: tuple[int, ...], variable_count: int) -> tuple[int, ...]:
    out = [0] * variable_count
    for variable in monomial:
        out[variable] += 1
    return tuple(out)


def subtract(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a - b for a, b in zip(left, right, strict=True))


def audit(support_result: Path, certificate_result: Path) -> dict[str, object]:
    elementary = load_elementary_module()
    support_payload = json.loads(support_result.read_text(encoding="utf-8"))
    payload = json.loads(certificate_result.read_text(encoding="utf-8"))
    certificate = payload["certificate"]
    if certificate is None:
        return {"verified": False, "reason": "no certificate"}
    support = {tuple(item) for item in support_payload["support_keys"]}
    keys = elementary.all_keys()
    lookup = {key: index for index, key in enumerate(keys)}
    pms = elementary.matchings(tuple(range(8)))

    relation_deltas = []
    coefficient_sum = 0
    relation_failures = []
    for relation in certificate["relations"]:
        coloring = tuple(relation["binomial_coloring"])
        expected = tuple(
            sorted(
                (
                    tuple(relation["left_monomial"]),
                    tuple(relation["right_monomial"]),
                )
            )
        )
        actual = elementary.supported_signature(coloring, support, pms, keys, lookup)
        if actual != expected:
            relation_failures.append(coloring)
        left = exponent(tuple(relation["left_monomial"]), len(keys))
        right = exponent(tuple(relation["right_monomial"]), len(keys))
        relation_deltas.append(
            (int(relation["coefficient"]), subtract(left, right))
        )
        coefficient_sum += int(relation["coefficient"])

    tri_coloring = tuple(certificate["trinomial_coloring"])
    tri_terms = tuple(sorted(tuple(term) for term in certificate["trinomial_terms"]))
    actual_tri = elementary.supported_signature(
        tri_coloring, support, pms, keys, lookup
    )
    left_index, right_index = certificate["canceling_indices"]
    target = subtract(
        exponent(tuple(certificate["trinomial_terms"][left_index]), len(keys)),
        exponent(tuple(certificate["trinomial_terms"][right_index]), len(keys)),
    )
    combined = tuple(
        sum(coefficient * delta[i] for coefficient, delta in relation_deltas)
        for i in range(len(keys))
    )
    forced_index = int(certificate["forced_zero_monomial_index"])
    forced = tuple(certificate["trinomial_terms"][forced_index])
    forced_supported = all(keys[index] in support for index in forced)
    checks = {
        "support_size_matches": len(support) == payload["support_size"],
        "relations_are_exact_zero_binomials": not relation_failures,
        "trinomial_is_exact": actual_tri == tri_terms and len(actual_tri) == 3,
        "exponent_identity": combined == target,
        "odd_sign": coefficient_sum % 2 == 1,
        "forced_monomial_supported": forced_supported,
    }
    return {
        "verified": all(checks.values()),
        "checks": checks,
        "relation_failures": relation_failures,
        "combination_l1": sum(abs(item[0]) for item in relation_deltas),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("support", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = audit(args.support, args.certificate)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["verified"] else 1)


if __name__ == "__main__":
    main()
