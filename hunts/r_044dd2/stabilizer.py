#!/usr/bin/env python3
"""Enumerate the exact ``S8 x S3`` stabilizer of a target branch."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

N = 8
D = 3
HERE = Path(__file__).resolve().parent
CENSUS = HERE.parent / "r_322dae" / "results.json"

Permutation = tuple[int, ...]
Matching = tuple[tuple[int, int], ...]
Triple = tuple[Matching, Matching, Matching]


def apply_vertex_permutation(pi: Permutation, matching: Matching) -> Matching:
    return tuple(sorted(tuple(sorted((pi[u], pi[v]))) for u, v in matching))


def target_triple(orbit_id: int, census: Path = CENSUS) -> Triple:
    payload = json.loads(census.read_text(encoding="utf-8"))
    orbit = next(
        row
        for row in payload["census_8x3"]["orbits"]
        if row["orbit_id"] == orbit_id
    )
    return tuple(
        tuple(tuple(edge) for edge in matching)
        for matching in orbit["canonical_triple_matchings"]
    )


def stabilizes(triple: Triple, pi: Permutation, sigma: Permutation) -> bool:
    sigma_inverse = {sigma[index]: index for index in range(D)}
    return all(
        apply_vertex_permutation(pi, triple[sigma_inverse[color]]) == triple[color]
        for color in range(D)
    )


def get_stabilizer(
    orbit_id: int,
    census: Path = CENSUS,
) -> tuple[tuple[Permutation, Permutation], ...]:
    triple = target_triple(orbit_id, census)
    return tuple(
        (pi, sigma)
        for pi in itertools.permutations(range(N))
        for sigma in itertools.permutations(range(D))
        if stabilizes(triple, pi, sigma)
    )


def nonidentity_element(
    orbit_id: int,
    census: Path = CENSUS,
) -> tuple[Permutation, Permutation]:
    identity = (tuple(range(N)), tuple(range(D)))
    nonidentity = [item for item in get_stabilizer(orbit_id, census) if item != identity]
    if len(nonidentity) != 1:
        raise ValueError(
            f"orbit {orbit_id} has {len(nonidentity)} nonidentity stabilizer elements"
        )
    return nonidentity[0]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orbit", type=int, default=18, choices=range(31))
    args = parser.parse_args()
    stabilizer = get_stabilizer(args.orbit)
    print(json.dumps({"orbit": args.orbit, "size": len(stabilizer), "elements": stabilizer}))


if __name__ == "__main__":
    main()
