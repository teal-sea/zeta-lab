#!/usr/bin/env python3
"""Find elementary exact algebraic contradictions inside a support survivor.

The two checks are deliberately small and independently replayable:

* the same supported polynomial cannot equal both one and zero;
* if a zero binomial is exactly two terms of a zero trinomial, the remaining
  supported monomial would have to vanish, contradicting support nonzeroness.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path

N = 8
D = 3
EdgeKey = tuple[int, int, int, int]
Monomial = tuple[int, ...]
Signature = tuple[Monomial, ...]


def matchings(vertices: tuple[int, ...]):
    if not vertices:
        return ((),)
    head = vertices[0]
    answer = []
    for i, mate in enumerate(vertices[1:]):
        rest = vertices[1 : i + 1] + vertices[i + 2 :]
        for tail in matchings(rest):
            answer.append(((head, mate),) + tail)
    return tuple(answer)


def edge_key(u: int, v: int, a: int, b: int) -> EdgeKey:
    return (u, v, a, b) if u < v else (v, u, b, a)


def all_keys() -> tuple[EdgeKey, ...]:
    return tuple(
        (u, v, a, b)
        for u in range(N)
        for v in range(u + 1, N)
        for a in range(D)
        for b in range(D)
    )


def supported_signature(
    coloring: tuple[int, ...],
    support: set[EdgeKey],
    pms,
    keys: tuple[EdgeKey, ...],
    lookup: dict[EdgeKey, int],
) -> Signature:
    terms = []
    for matching in pms:
        factors = tuple(
            sorted(lookup[edge_key(u, v, coloring[u], coloring[v])] for u, v in matching)
        )
        if all(keys[index] in support for index in factors):
            terms.append(factors)
    return tuple(sorted(terms))


def sieve(census: Path, orbit: int) -> dict[str, object]:
    payload = json.loads(census.read_text(encoding="utf-8"))
    row = next(item for item in payload["rows"] if item["orbit"] == orbit)
    support = {tuple(item) for item in row["support_keys"]}
    keys = all_keys()
    lookup = {key: index for index, key in enumerate(keys)}
    pms = matchings(tuple(range(N)))
    by_count: Counter[int] = Counter()
    targets: dict[Signature, list[tuple[int, ...]]] = defaultdict(list)
    zeros: dict[Signature, list[tuple[int, ...]]] = defaultdict(list)
    zero_binomials: dict[frozenset[Monomial], list[tuple[int, ...]]] = defaultdict(list)
    zero_trinomials: list[tuple[tuple[int, ...], Signature]] = []

    for coloring in itertools.product(range(D), repeat=N):
        signature = supported_signature(coloring, support, pms, keys, lookup)
        if len(set(coloring)) == 1:
            targets[signature].append(coloring)
        else:
            zeros[signature].append(coloring)
            by_count[len(signature)] += 1
            if len(signature) == 2:
                zero_binomials[frozenset(signature)].append(coloring)
            elif len(signature) == 3:
                zero_trinomials.append((coloring, signature))

    target_zero = []
    for signature, target_colorings in targets.items():
        for zero_coloring in zeros.get(signature, ()):
            target_zero.append(
                {
                    "target_coloring": target_colorings[0],
                    "zero_coloring": zero_coloring,
                    "terms": signature,
                }
            )

    binomial_trinomial = []
    for tri_coloring, signature in zero_trinomials:
        for pair in itertools.combinations(signature, 2):
            witnesses = zero_binomials.get(frozenset(pair))
            if witnesses:
                remaining = next(term for term in signature if term not in pair)
                binomial_trinomial.append(
                    {
                        "binomial_coloring": witnesses[0],
                        "trinomial_coloring": tri_coloring,
                        "shared_terms": pair,
                        "forced_zero_monomial": remaining,
                    }
                )

    return {
        "format": 1,
        "orbit": orbit,
        "support_size": len(support),
        "non_target_active_term_histogram": dict(sorted(by_count.items())),
        "target_zero_collisions": target_zero,
        "binomial_trinomial_collisions": binomial_trinomial,
        "exact_contradictions": len(target_zero) + len(binomial_trinomial),
        "interpretation": (
            "each recorded collision is an exact contradiction for this support; "
            "absence of collisions is not evidence that the support is realizable"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census", type=Path)
    parser.add_argument("--orbit", type=int, required=True, choices=range(31))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = sieve(args.census, args.orbit)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "orbit": result["orbit"],
                "support_size": result["support_size"],
                "exact_contradictions": result["exact_contradictions"],
                "histogram": result["non_target_active_term_histogram"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
