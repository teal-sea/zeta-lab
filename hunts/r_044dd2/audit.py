#!/usr/bin/env python3
"""Independent direct replay for one Krenn-Gu 8x3 support result."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

N = 8
D = 3


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


def key(u: int, v: int, a: int, b: int):
    return (u, v, a, b) if u < v else (v, u, b, a)


def active_count(support: set[tuple[int, int, int, int]], coloring, pms) -> int:
    return sum(
        all(key(u, v, coloring[u], coloring[v]) in support for u, v in pm)
        for pm in pms
    )


def star_ok(support, root: int, color: int) -> bool:
    return any(
        key(root, neighbor, color, color) in support
        and all(
            key(root, neighbor, color, other) not in support
            for other in range(D)
            if other != color
        )
        for neighbor in range(N)
        if neighbor != root
    )


def pair_ok(support, root: int, a: int, b: int) -> bool:
    pair = (a, b)
    pure = {}
    for output in pair:
        pure[output] = any(
            any(key(root, neighbor, source, output) in support for source in pair)
            and all(
                key(root, neighbor, source, other) not in support
                for source in pair
                for other in range(D)
                if other != output
            )
            for neighbor in range(N)
            if neighbor != root
        )
    preserves = all(
        key(root, neighbor, source, other) not in support
        for neighbor in range(N)
        if neighbor != root
        for source in pair
        for other in range(D)
        if other not in pair
    )
    return (pure[a] and pure[b]) or preserves


def column_ok(support, root: int, output: int) -> bool:
    return any(
        any(key(root, neighbor, source, output) in support for source in range(D))
        and all(
            key(root, neighbor, source, other) not in support
            for source in range(D)
            for other in range(D)
            if other != output
        )
        for neighbor in range(N)
        if neighbor != root
    )


def audit(path: Path) -> dict[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    support = {tuple(item) for item in payload["support_keys"]}
    pms = matchings(tuple(range(N)))
    equation_failures = []
    for coloring in itertools.product(range(D), repeat=N):
        count = active_count(support, coloring, pms)
        bad = count < 1 if len(set(coloring)) == 1 else count == 1
        if bad:
            equation_failures.append((coloring, count))
    star_failures = [
        (root, color)
        for root in range(N)
        for color in range(D)
        if not star_ok(support, root, color)
    ]
    pair_failures = [
        (root, a, b)
        for root in range(N)
        for a, b in itertools.combinations(range(D), 2)
        if not pair_ok(support, root, a, b)
    ]
    column_failures = [
        (root, color)
        for root in range(N)
        for color in range(D)
        if not column_ok(support, root, color)
    ]
    return {
        "support_size": len(support),
        "perfect_matchings": len(pms),
        "colorings": D**N,
        "equation_failures": len(equation_failures),
        "first_equation_failure": equation_failures[0] if equation_failures else None,
        "star_failures": star_failures,
        "pair_failures": pair_failures,
        "column_failures": column_failures,
        "verified_support_survivor": not (
            equation_failures or star_failures or pair_failures or column_failures
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    result = audit(args.result)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["verified_support_survivor"] else 1)


if __name__ == "__main__":
    main()
