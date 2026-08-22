#!/usr/bin/env python3
"""Map a Laurent pattern certificate through a branch stabilizer element."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from stabilizer import nonidentity_element

N = 8
D = 3

Permutation = tuple[int, ...]

KEYS = tuple(
    (u, v, a, b)
    for u in range(N)
    for v in range(u + 1, N)
    for a in range(D)
    for b in range(D)
)
KEY_TO_INDEX = {key: index for index, key in enumerate(KEYS)}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def transform_coloring(
    coloring: list[int],
    pi: Permutation,
    sigma: Permutation,
) -> list[int]:
    pi_inverse = {pi[index]: index for index in range(N)}
    return [sigma[coloring[pi_inverse[index]]] for index in range(N)]


def transform_key_index(
    key_index: int,
    pi: Permutation,
    sigma: Permutation,
) -> int:
    u, v, a, b = KEYS[key_index]
    new_u, new_v = pi[u], pi[v]
    new_a, new_b = sigma[a], sigma[b]
    if new_u > new_v:
        new_u, new_v = new_v, new_u
        new_a, new_b = new_b, new_a
    return KEY_TO_INDEX[(new_u, new_v, new_a, new_b)]


def transform_monomial(
    monomial: list[int],
    pi: Permutation,
    sigma: Permutation,
) -> list[int]:
    return sorted(transform_key_index(index, pi, sigma) for index in monomial)


def expand_certificate(
    certificate_path: Path,
    pi: Permutation,
    sigma: Permutation,
    output_path: Path,
) -> None:
    data = json.loads(certificate_path.read_text(encoding="utf-8"))
    certificate = data.get("certificate")
    if not isinstance(certificate, dict):
        raise ValueError("input has no Laurent certificate")

    certificate["trinomial_coloring"] = transform_coloring(
        certificate["trinomial_coloring"], pi, sigma
    )
    certificate["trinomial_terms"] = [
        transform_monomial(term, pi, sigma)
        for term in certificate["trinomial_terms"]
    ]
    for relation in certificate["relations"]:
        relation["binomial_coloring"] = transform_coloring(
            relation["binomial_coloring"], pi, sigma
        )
        relation["left_monomial"] = transform_monomial(
            relation["left_monomial"], pi, sigma
        )
        relation["right_monomial"] = transform_monomial(
            relation["right_monomial"], pi, sigma
        )

    data["symmetry_expansion"] = {
        "source": certificate_path.name,
        "source_sha256": file_sha256(certificate_path),
        "vertex_permutation": pi,
        "color_permutation": sigma,
    }
    output_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--orbit", type=int, default=18, choices=range(31))
    args = parser.parse_args()
    pi, sigma = nonidentity_element(args.orbit)
    expand_certificate(args.certificate, pi, sigma, args.output)


if __name__ == "__main__":
    main()
