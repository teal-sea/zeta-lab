"""Hunt #140 (`r_abf47b/`): the two statements its landing keeps, pinned.

1. The 57 H x S2 pair orbits refine the 31 S8 x S3 triple orbits (RESULTS.md
   section 2). `map_orbits.py` enumerates all 105^3 matching triples. This
   file takes a second route that never leaves the 11,025-point slice
   {M0} x PM x PM, and checks every orbit size against Hunt #71's census.
2. The Groebner input of RESULTS.md section 3 is homogeneous with no constant
   term, so no basis of it can be [1] (RESULTS.md "Audit correction"). A
   two-variable control runs both encodings on a system that is infeasible on
   the torus.

The slice route: S8 is transitive on perfect matchings, so every S8 x S3 orbit
of triples meets the slice. For a triple whose first matching is X, fix one
permutation r_X with r_X(X) = M0. Two slice points lie in one S8 x S3 orbit
exactly when H-moves (H = Stab(M0)) and lifts t -> r_X(pi t), pi in S3, join
them, because any g with g(X) = M0 is h r_X for some h in H. The same count
gives |orbit| = 105 |orbit meet slice|, since r_X carries the orbit's triples
that start with X onto its slice points.

Reads the tree and writes nothing into it.
"""

from __future__ import annotations

import importlib.util
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

import sympy

HERE = Path(__file__).resolve().parent
HUNTS = HERE.parent
CENSUS = HUNTS / "r_322dae" / "results.json"
SIEVE = HUNTS / "r_044dd2" / "polynomial_sieve.py"
SUPPORT7 = HUNTS / "r_044dd2" / "artifacts" / "orbit18-support-07.json"


def perfect_matchings(vertices: tuple[int, ...]) -> list[tuple[tuple[int, int], ...]]:
    if not vertices:
        return [()]
    first, out = vertices[0], []
    for i in range(1, len(vertices)):
        rest = vertices[1:i] + vertices[i + 1:]
        out.extend(((first, vertices[i]),) + tail for tail in perfect_matchings(rest))
    return out


def image(matching, perm) -> tuple[tuple[int, int], ...]:
    return tuple(sorted(tuple(sorted((perm[u], perm[v]))) for u, v in matching))


class Partition:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[a] = b


PMS = [tuple(sorted(m)) for m in perfect_matchings(tuple(range(8)))]
INDEX = {m: i for i, m in enumerate(PMS)}
N = len(PMS)
M0 = ((0, 1), (2, 3), (4, 5), (6, 7))

#: within-pair swaps and adjacent pair swaps of M0
H_GENERATORS = (
    (1, 0, 2, 3, 4, 5, 6, 7),
    (0, 1, 3, 2, 4, 5, 6, 7),
    (0, 1, 2, 3, 5, 4, 6, 7),
    (0, 1, 2, 3, 4, 5, 7, 6),
    (2, 3, 0, 1, 4, 5, 6, 7),
    (0, 1, 4, 5, 2, 3, 6, 7),
    (0, 1, 2, 3, 6, 7, 4, 5),
)


def to_slice(X: int) -> tuple[int, ...]:
    """r_X: a fixed permutation of the vertices sending matching X to M0."""
    perm = [0] * 8
    for k, (a, b) in enumerate(PMS[X]):
        perm[a], perm[b] = 2 * k, 2 * k + 1
    return tuple(perm)


def slice_partitions() -> tuple[Partition, Partition]:
    """(H x S2 orbits on pairs, S8 x S3 orbits met on the slice), both on a * N + b."""
    act = [[INDEX[image(m, g)] for m in PMS] for g in H_GENERATORS]
    lift = [[INDEX[image(m, to_slice(X))] for m in PMS] for X in range(N)]
    pairs, triples = Partition(N * N), Partition(N * N)
    for a in range(N):
        for b in range(N):
            here = a * N + b
            for table in act:
                there = table[a] * N + table[b]
                pairs.union(here, there)
                triples.union(here, there)
            pairs.union(here, b * N + a)
            triple = (0, a, b)
            for pi in itertools.permutations(range(3)):
                first, second, third = (triple[p] for p in pi)
                assert lift[first][first] == 0
                triples.union(here, lift[first][second] * N + lift[first][third])
    return pairs, triples


def test_the_generators_give_the_whole_stabilizer_of_m0() -> None:
    assert PMS[0] == M0 and N == 105
    group = {tuple(range(8))}
    frontier = list(group)
    while frontier:
        grown = []
        for g in frontier:
            for h in H_GENERATORS:
                c = tuple(h[g[i]] for i in range(8))
                if c not in group:
                    group.add(c)
                    grown.append(c)
        frontier = grown
    assert all(image(M0, g) == M0 for g in group)
    stabilizer = [p for p in itertools.permutations(range(8)) if image(M0, p) == M0]
    assert len(group) == len(stabilizer) == 40320 // N == 384
    assert all(image(PMS[X], to_slice(X)) == M0 for X in range(N))


def test_the_57_pair_orbits_refine_the_31_triple_orbits() -> None:
    pairs, triples = slice_partitions()
    pair_orbits: dict[int, set[int]] = {}
    for x in range(N * N):
        pair_orbits.setdefault(pairs.find(x), set()).add(triples.find(x))
    assert len(pair_orbits) == 57
    assert all(len(parents) == 1 for parents in pair_orbits.values())
    covered = Counter(next(iter(parents)) for parents in pair_orbits.values())
    assert len({triples.find(x) for x in range(N * N)}) == 31
    assert len(covered) == 31  # onto: no triple orbit is missed by the 57
    assert sorted(Counter(covered.values()).items()) == [(1, 8), (2, 20), (3, 3)]


def test_the_slice_classes_are_hunt_71s_census() -> None:
    census = json.loads(CENSUS.read_text(encoding="utf-8"))["census_8x3"]
    assert census["hs2_pair_orbits_count"] == 57
    assert census["num_orbits"] == census["burnside_orbit_count"] == 31
    _, triples = slice_partitions()
    slice_size = Counter(triples.find(x) for x in range(N * N))
    seen = set()
    for row in census["orbits"]:
        a, b, c = (
            INDEX[tuple(sorted(tuple(sorted(edge)) for edge in matching))]
            for matching in row["canonical_triple_matchings"]
        )
        r = to_slice(a)
        cls = triples.find(INDEX[image(PMS[b], r)] * N + INDEX[image(PMS[c], r)])
        seen.add(cls)
        assert row["orbit_size"] == N * slice_size[cls], row["orbit_id"]
    assert len(seen) == 31


def load_sieve():
    spec = importlib.util.spec_from_file_location("r_abf47b_polynomial_sieve", SIEVE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_the_groebner_input_is_homogeneous_with_no_constant_term() -> None:
    """What run_groebner.py handed sympy: 3 targets and 6,558 relations."""
    support, targets, relations, _ = load_sieve().build_system(SUPPORT7)
    assert len(support) == 138
    assert [len(terms) for _, terms in targets] == [15, 15, 20]
    assert {len(term) for _, terms in targets for term in terms} == {4}
    assert len(targets) + len(relations) == 6561
    degrees = Counter()
    for relation in relations:
        lengths = {len(term) for term in relation.terms}
        assert len(lengths) == 1, relation.coloring  # homogeneous
        degrees[lengths.pop()] += 1
    assert degrees == {3: 1458, 4: 5100}  # no degree-0 term anywhere


def test_the_zero_generator_encoding_cannot_see_an_infeasible_system() -> None:
    """Control: the relation x + y = 0 kills the target x + y on the torus.

    Entered as run_groebner.py enters it, target as a generator, the ideal is
    homogeneous and proper. Entered as a nonvanishing condition with the
    variables saturated (Rabinowitsch), the same system gives [1].
    """
    x, y, z = sympy.symbols("x y z")
    target, relation = x + y, x + y
    as_run = sympy.groebner([target, relation], x, y, order="grevlex")
    assert list(as_run.exprs) == [x + y]
    saturated = sympy.groebner(
        [relation, 1 - z * target * x * y], x, y, z, order="grevlex"
    )
    assert list(saturated.exprs) == [1]
