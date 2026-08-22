"""Hunt R-322DAE: Krenn-Gu 8x3 Orbit Census and Next Exact Frontier.

Reproduces the 6x3 census checksum (15 matchings, 3375 triples, 8 S6 x S3 orbits)
and parameterizes the full orbit-census layer for n=8 (105 matchings, 1157625 triples,
31 S8 x S3 orbits).
"""

from __future__ import annotations

import itertools
import json
import os
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np


def get_perfect_matchings(n: int) -> list[frozenset[frozenset[int]]]:
    """Generate all (n-1)!! perfect matchings of K_n in canonical sorted order."""
    def _match(vertices: list[int]) -> list[frozenset[frozenset[int]]]:
        if not vertices:
            return [frozenset()]
        v0 = vertices[0]
        rest = vertices[1:]
        res = []
        for i, v1 in enumerate(rest):
            pair = frozenset([v0, v1])
            remaining = rest[:i] + rest[i + 1:]
            for sub in _match(remaining):
                res.append(sub | frozenset([pair]))
        return res

    raw = _match(list(range(n)))
    # Sort deterministically
    return sorted(raw, key=lambda m: sorted([sorted(list(e)) for e in m]))


def matching_to_edges_list(m: frozenset[frozenset[int]]) -> list[list[int]]:
    """Convert matching to sorted list of 2-element lists."""
    return sorted([sorted(list(e)) for e in m])


def perm_power(p: tuple[int, ...], k: int) -> tuple[int, ...]:
    """Compute k-th power of permutation p."""
    res = list(range(len(p)))
    for _ in range(k):
        res = [p[x] for x in res]
    return tuple(res)


def compute_burnside_orbit_count(n: int, matchings: list[frozenset[frozenset[int]]]) -> float:
    """Compute exact number of orbits under Sn x S3 using Burnside Lemma."""
    sn = list(itertools.permutations(range(n)))
    s3_size = 6
    
    def apply_m(m: frozenset[frozenset[int]], p: tuple[int, ...]) -> frozenset[frozenset[int]]:
        return frozenset(frozenset([p[u] for u in e]) for e in m)
    
    def count_fixed(p: tuple[int, ...]) -> int:
        return sum(1 for m in matchings if apply_m(m, p) == m)

    total_fixed = 0
    for p in sn:
        f1 = count_fixed(p)
        f2 = count_fixed(perm_power(p, 2))
        f3 = count_fixed(perm_power(p, 3))
        # Conjugacy classes of S3: 1 identity (f1^3), 3 transpositions (f2*f1), 2 3-cycles (f3)
        fixed_triples = 1 * (f1 ** 3) + 3 * (f2 * f1) + 2 * f3
        total_fixed += fixed_triples

    return total_fixed / (len(sn) * s3_size)


def cycle_structure_2factor(
    m1_edges: list[list[int]], m2_edges: list[list[int]], n: int
) -> list[int]:
    """Compute sorted cycle lengths in the 2-factor formed by m1 union m2."""
    adj: dict[int, list[tuple[int, int]]] = {i: [] for i in range(n)}
    for u, v in m1_edges:
        adj[u].append((v, 1))
        adj[v].append((u, 1))
    for u, v in m2_edges:
        adj[u].append((v, 2))
        adj[v].append((u, 2))

    seen: set[int] = set()
    cycles: list[int] = []
    for i in range(n):
        if i not in seen:
            cur = i
            prev_color = 2
            cycle_len = 0
            while True:
                seen.add(cur)
                cycle_len += 1
                target_color = 1 if prev_color == 2 else 2
                nxt = None
                for neighbor, col in adj[cur]:
                    if col == target_color:
                        nxt = neighbor
                        break
                prev_color = target_color
                cur = nxt  # type: ignore[assignment]
                if cur == i:
                    break
            cycles.append(cycle_len)
    return sorted(cycles, reverse=True)


def compute_orbit_census(n: int) -> dict[str, Any]:
    """Compute complete orbit census of monochromatic matching triples under Sn x S3."""
    t0 = time.time()
    matchings = get_perfect_matchings(n)
    n_matchings = len(matchings)
    matching_to_idx = {m: i for i, m in enumerate(matchings)}

    sn = list(itertools.permutations(range(n)))
    s3 = list(itertools.permutations(range(3)))
    group_size = len(sn) * len(s3)

    # Precompute permutation table for Sn acting on matchings
    perm_table = np.zeros((len(sn), n_matchings), dtype=np.int32)
    for i_p, p in enumerate(sn):
        for i_m, m in enumerate(matchings):
            new_m = frozenset(frozenset([p[u] for u in e]) for e in m)
            perm_table[i_p, i_m] = matching_to_idx[new_m]

    n_triples = n_matchings ** 3
    visited = np.zeros(n_triples, dtype=bool)
    orbit_map = np.full(n_triples, -1, dtype=np.int32)

    burnside_orbits = compute_burnside_orbit_count(n, matchings)

    # Fixed matching stabilizer quotient
    # Stabilizer of matching 0 in Sn
    m0 = matchings[0]
    stab_m0_perms = [
        p for p in sn if frozenset(frozenset([p[u] for u in e]) for e in m0) == m0
    ]
    stab_m0_size = len(stab_m0_perms)
    perm_table_stab = np.zeros((stab_m0_size, n_matchings), dtype=np.int32)
    for i_p, p in enumerate(stab_m0_perms):
        for i_m, m in enumerate(matchings):
            new_m = frozenset(frozenset([p[u] for u in e]) for e in m)
            perm_table_stab[i_p, i_m] = matching_to_idx[new_m]

    # Orbits of pairs (M1, M2) under H = Stab(M0)
    visited_pairs_h = np.zeros((n_matchings, n_matchings), dtype=bool)
    h_pair_orbits_count = 0
    for m1 in range(n_matchings):
        for m2 in range(n_matchings):
            if visited_pairs_h[m1, m2]:
                continue
            c1 = perm_table_stab[:, m1]
            c2 = perm_table_stab[:, m2]
            visited_pairs_h[c1, c2] = True
            h_pair_orbits_count += 1

    # Orbits of pairs (M1, M2) under H x S2 (color transposition)
    visited_pairs_hs2 = np.zeros((n_matchings, n_matchings), dtype=bool)
    hs2_pair_orbits_count = 0
    for m1 in range(n_matchings):
        for m2 in range(n_matchings):
            if visited_pairs_hs2[m1, m2]:
                continue
            c1 = perm_table_stab[:, m1]
            c2 = perm_table_stab[:, m2]
            visited_pairs_hs2[c1, c2] = True
            visited_pairs_hs2[c2, c1] = True
            hs2_pair_orbits_count += 1

    orbits_data = []
    cur_idx = 0
    orbit_id = 0

    while cur_idx < n_triples:
        unvisited = np.where(~visited[cur_idx:])[0]
        if len(unvisited) == 0:
            break
        cur_idx += int(unvisited[0])

        m0_idx = cur_idx // (n_matchings * n_matchings)
        rem = cur_idx % (n_matchings * n_matchings)
        m1_idx = rem // n_matchings
        m2_idx = rem % n_matchings

        triple = (m0_idx, m1_idx, m2_idx)
        orbit_indices = []

        for p3 in s3:
            tm0 = triple[p3[0]]
            tm1 = triple[p3[1]]
            tm2 = triple[p3[2]]
            c0 = perm_table[:, tm0]
            c1 = perm_table[:, tm1]
            c2 = perm_table[:, tm2]
            idxs = c0 * (n_matchings * n_matchings) + c1 * n_matchings + c2
            orbit_indices.append(idxs)

        all_idxs = np.concatenate(orbit_indices)
        unique_idxs = np.unique(all_idxs)

        orbit_size = int(len(unique_idxs))
        stab_size = int(group_size // orbit_size)
        canonical_idx = int(np.min(unique_idxs))

        visited[unique_idxs] = True
        orbit_map[unique_idxs] = orbit_id

        cm0 = canonical_idx // (n_matchings * n_matchings)
        crem = canonical_idx % (n_matchings * n_matchings)
        cm1 = crem // n_matchings
        cm2 = crem % n_matchings

        mat0_edges = matching_to_edges_list(matchings[cm0])
        mat1_edges = matching_to_edges_list(matchings[cm1])
        mat2_edges = matching_to_edges_list(matchings[cm2])

        cs01 = cycle_structure_2factor(mat0_edges, mat1_edges, n)
        cs02 = cycle_structure_2factor(mat0_edges, mat2_edges, n)
        cs12 = cycle_structure_2factor(mat1_edges, mat2_edges, n)
        cycle_types = sorted([cs01, cs02, cs12])

        # Edge multiplicities in 3-regular multigraph
        edge_counts: dict[tuple[int, int], int] = {}
        for edges in [mat0_edges, mat1_edges, mat2_edges]:
            for u, v in edges:
                e_pair = (min(u, v), max(u, v))
                edge_counts[e_pair] = edge_counts.get(e_pair, 0) + 1

        mult_dist = {1: 0, 2: 0, 3: 0}
        for count in edge_counts.values():
            mult_dist[count] += 1

        # Connected components
        adj: dict[int, set[int]] = {v: set() for v in range(n)}
        for u, v in edge_counts:
            adj[u].add(v)
            adj[v].add(u)

        seen_v: set[int] = set()
        components: list[int] = []
        for v in range(n):
            if v not in seen_v:
                comp = set()
                q = [v]
                seen_v.add(v)
                while q:
                    curr = q.pop(0)
                    comp.add(curr)
                    for nxt in adj[curr]:
                        if nxt not in seen_v:
                            seen_v.add(nxt)
                            q.append(nxt)
                components.append(len(comp))
        components_sorted = sorted(components, reverse=True)

        distinct_matchings = len({cm0, cm1, cm2})

        orbits_data.append({
            "orbit_id": orbit_id,
            "canonical_index": canonical_idx,
            "canonical_triple_indices": [int(cm0), int(cm1), int(cm2)],
            "canonical_triple_matchings": [mat0_edges, mat1_edges, mat2_edges],
            "distinct_matchings": distinct_matchings,
            "orbit_size": orbit_size,
            "stabilizer_size": stab_size,
            "orbit_stabilizer_product": orbit_size * stab_size,
            "cycle_structures_2factor": cycle_types,
            "edge_multiplicities": {
                "triple_edges": mult_dist[3],
                "double_edges": mult_dist[2],
                "single_edges": mult_dist[1],
            },
            "connected_components": components_sorted,
        })
        orbit_id += 1

    total_time = time.time() - t0
    total_triples_covered = int(visited.sum())
    orbit_sizes_sum = sum(o["orbit_size"] for o in orbits_data)

    return {
        "n": n,
        "n_matchings": n_matchings,
        "n_triples": n_triples,
        "group_name": f"S{n} x S3",
        "group_size": group_size,
        "stabilizer_m0_name": f"S2 wr S{n // 2}",
        "stabilizer_m0_size": stab_m0_size,
        "h_pair_orbits_count": h_pair_orbits_count,
        "hs2_pair_orbits_count": hs2_pair_orbits_count,
        "burnside_orbit_count": int(burnside_orbits),
        "num_orbits": len(orbits_data),
        "total_triples_covered": total_triples_covered,
        "orbit_sizes_sum": orbit_sizes_sum,
        "coverage_is_exact_partition": (
            total_triples_covered == n_triples and orbit_sizes_sum == n_triples
        ),
        "orbits": orbits_data,
        "elapsed_seconds": total_time,
    }


def run_probe() -> dict[str, Any]:
    print("=" * 70)
    print("Hunt R-322DAE: Krenn-Gu Orbit Census (6x3 Checksum and 8x3 Frontier)")
    print("=" * 70)

    # 1. Verify 6x3
    print("\n--- 1. Reproducing 6x3 Census Checksum ---")
    res_6 = compute_orbit_census(6)
    print(f"n = 6: {res_6['n_matchings']} matchings, {res_6['n_triples']} triples")
    print(f"Group |S6 x S3| = {res_6['group_size']}")
    print(f"Burnside orbit count: {res_6['burnside_orbit_count']}")
    print(f"Constructed orbits: {res_6['num_orbits']}")
    print(f"Orbit sizes: {[o['orbit_size'] for o in res_6['orbits']]}")
    print(f"Stabilizer sizes: {[o['stabilizer_size'] for o in res_6['orbits']]}")
    print(f"Sum of orbit sizes: {res_6['orbit_sizes_sum']} (expected 3375)")
    print(f"Pair orbits under H = S2 wr S3: {res_6['h_pair_orbits_count']} (under H x S2: {res_6['hs2_pair_orbits_count']})")
    assert res_6["n_matchings"] == 15
    assert res_6["n_triples"] == 3375
    assert res_6["num_orbits"] == 8
    assert res_6["coverage_is_exact_partition"]
    assert sorted([o["orbit_size"] for o in res_6["orbits"]]) == [15, 90, 120, 270, 360, 360, 1080, 1080]

    # 2. Compute 8x3
    print("\n--- 2. Parameterizing 8x3 Orbit Census Frontier ---")
    res_8 = compute_orbit_census(8)
    print(f"n = 8: {res_8['n_matchings']} matchings, {res_8['n_triples']} triples")
    print(f"Group |S8 x S3| = {res_8['group_size']}")
    print(f"Burnside orbit count: {res_8['burnside_orbit_count']}")
    print(f"Constructed orbits: {res_8['num_orbits']}")
    print(f"Sum of orbit sizes: {res_8['orbit_sizes_sum']} (expected 1157625)")
    print(f"Pair orbits under H = S2 wr S4: {res_8['h_pair_orbits_count']} (under H x S2: {res_8['hs2_pair_orbits_count']})")
    print(f"Computation time: {res_8['elapsed_seconds']:.2f}s")
    assert res_8["n_matchings"] == 105
    assert res_8["n_triples"] == 1157625
    assert res_8["num_orbits"] == 31
    assert res_8["coverage_is_exact_partition"]

    print("\nDetailed 8x3 Orbit Summary:")
    print(f"{'Orbit':5s} | {'Canonical Triple':18s} | {'Dist':4s} | {'Size':8s} | {'Stab':6s} | {'Mult(3,2,1)':12s} | {'2-Factor Cycles'}")
    print("-" * 88)
    for o in res_8["orbits"]:
        mult_str = f"({o['edge_multiplicities']['triple_edges']},{o['edge_multiplicities']['double_edges']},{o['edge_multiplicities']['single_edges']})"
        print(f"{o['orbit_id']:5d} | {str(o['canonical_triple_indices']):18s} | {o['distinct_matchings']:4d} | {o['orbit_size']:8d} | {o['stabilizer_size']:6d} | {mult_str:12s} | {o['cycle_structures_2factor']}")

    combined_results = {
        "census_6x3": res_6,
        "census_8x3": res_8,
        "verified_checksum_6x3": True,
        "verified_partition_8x3": True,
    }

    # Write results.json
    out_dir = Path(__file__).resolve().parent
    results_path = out_dir / "results.json"
    with open(results_path, "w", encoding="utf-8") as f:
        json.dump(combined_results, f, indent=2)
    print(f"\nSaved findings to {results_path}")

    return combined_results


if __name__ == "__main__":
    run_probe()
