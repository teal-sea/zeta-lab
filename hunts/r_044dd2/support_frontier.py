#!/usr/bin/env python3
"""Lazy support-frontier optimizer for Krenn-Gu (n,d) = (8,3).

The optimizer is a scout, not an oracle.  ``audit.py`` independently replays
every returned support.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import time
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence

try:
    from ortools.sat.python import cp_model
except ImportError:  # pragma: no cover - the pure combinatorics stay importable
    cp_model = None

N = 8
D = 3
HERE = Path(__file__).resolve().parent
CENSUS = HERE.parent / "r_322dae" / "results.json"

EdgeKey = tuple[int, int, int, int]
Matching = tuple[tuple[int, int], ...]
Coloring = tuple[int, ...]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@lru_cache(maxsize=None)
def perfect_matchings(vertices: tuple[int, ...]) -> tuple[Matching, ...]:
    if not vertices:
        return ((),)
    first = vertices[0]
    out: list[Matching] = []
    for position in range(1, len(vertices)):
        partner = vertices[position]
        rest = vertices[1:position] + vertices[position + 1 :]
        for suffix in perfect_matchings(rest):
            out.append(((first, partner),) + suffix)
    return tuple(out)


def edge_key(u: int, v: int, color_u: int, color_v: int) -> EdgeKey:
    if u < v:
        return (u, v, color_u, color_v)
    return (v, u, color_v, color_u)


def variable_keys() -> tuple[EdgeKey, ...]:
    return tuple(
        (u, v, a, b)
        for u in range(N)
        for v in range(u + 1, N)
        for a in range(D)
        for b in range(D)
    )


def target_representatives() -> tuple[tuple[Matching, Matching, Matching], ...]:
    payload = json.loads(CENSUS.read_text(encoding="utf-8"))
    rows = payload["census_8x3"]["orbits"]
    return tuple(
        tuple(
            tuple(tuple(edge) for edge in matching)
            for matching in row["canonical_triple_matchings"]
        )
        for row in rows
    )


def branch_base_indices(orbit: int, lookup: dict[EdgeKey, int]) -> tuple[int, ...]:
    representatives = target_representatives()
    if not 0 <= orbit < len(representatives):
        raise ValueError(f"orbit must be in 0..{len(representatives) - 1}")
    return tuple(
        lookup[edge_key(u, v, color, color)]
        for color, matching in enumerate(representatives[orbit])
        for u, v in matching
    )


def term_edge_indices(
    coloring: Coloring,
    matchings: Sequence[Matching],
    lookup: dict[EdgeKey, int],
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(lookup[edge_key(u, v, coloring[u], coloring[v])] for u, v in matching)
        for matching in matchings
    )


def active_matching_indices(
    support: frozenset[int],
    coloring: Coloring,
    matchings: Sequence[Matching],
    lookup: dict[EdgeKey, int],
) -> tuple[int, ...]:
    return tuple(
        index
        for index, term in enumerate(term_edge_indices(coloring, matchings, lookup))
        if set(term) <= support
    )


class SupportModel:
    def __init__(self, orbit: int) -> None:
        if cp_model is None:
            raise RuntimeError(
                "OR-Tools is required: uv pip install --python .venv/bin/python "
                "ortools==9.15.6755"
            )
        self.orbit = orbit
        self.keys = variable_keys()
        self.lookup = {key: index for index, key in enumerate(self.keys)}
        self.matchings = perfect_matchings(tuple(range(N)))
        self.model = cp_model.CpModel()
        self.edges = [self.model.new_bool_var(f"edge_{i}") for i in range(len(self.keys))]
        self.encoded_colorings: set[Coloring] = set()
        self.terms_by_coloring: dict[Coloring, list] = {}
        for index in branch_base_indices(orbit, self.lookup):
            self.model.add(self.edges[index] == 1)
        self._add_star_anchor()
        self._add_pair_pencil()
        self._add_full_column()
        for color in range(D):
            self.add_coloring((color,) * N)
        self.model.minimize(sum(self.edges))

    def edge(self, root: int, neighbor: int, a: int, b: int):
        return self.edges[self.lookup[edge_key(root, neighbor, a, b)]]

    def _and(self, name: str, literals: Sequence):
        output = self.model.new_bool_var(name)
        self.model.add_bool_and(literals).only_enforce_if(output)
        self.model.add_bool_or([literal.Not() for literal in literals]).only_enforce_if(
            output.Not()
        )
        return output

    def _or(self, name: str, literals: Sequence):
        output = self.model.new_bool_var(name)
        self.model.add_bool_or(literals).only_enforce_if(output)
        self.model.add_bool_and([literal.Not() for literal in literals]).only_enforce_if(
            output.Not()
        )
        return output

    def _add_star_anchor(self) -> None:
        for root in range(N):
            for color in range(D):
                anchors = []
                for neighbor in range(N):
                    if neighbor == root:
                        continue
                    literals = [self.edge(root, neighbor, color, color)]
                    literals.extend(
                        self.edge(root, neighbor, color, other).Not()
                        for other in range(D)
                        if other != color
                    )
                    anchors.append(self._and(f"star_{root}_{color}_{neighbor}", literals))
                self.model.add_bool_or(anchors)

    def _add_pair_pencil(self) -> None:
        for root in range(N):
            for color_a, color_b in itertools.combinations(range(D), 2):
                pair = (color_a, color_b)
                pure_by_output: dict[int, list] = {color_a: [], color_b: []}
                for output in pair:
                    for neighbor in range(N):
                        if neighbor == root:
                            continue
                        has_target = self._or(
                            f"pair_has_{root}_{color_a}_{color_b}_{output}_{neighbor}",
                            [self.edge(root, neighbor, source, output) for source in pair],
                        )
                        contamination = [
                            self.edge(root, neighbor, source, other)
                            for source in pair
                            for other in range(D)
                            if other != output
                        ]
                        pure_by_output[output].append(
                            self._and(
                                f"pair_pure_{root}_{color_a}_{color_b}_{output}_{neighbor}",
                                [has_target, *(edge.Not() for edge in contamination)],
                            )
                        )
                has_a = self._or(
                    f"pair_output_{root}_{color_a}_{color_b}_{color_a}",
                    pure_by_output[color_a],
                )
                has_b = self._or(
                    f"pair_output_{root}_{color_a}_{color_b}_{color_b}",
                    pure_by_output[color_b],
                )
                both = self._and(f"pair_both_{root}_{color_a}_{color_b}", [has_a, has_b])
                outside = [
                    self.edge(root, neighbor, source, other)
                    for neighbor in range(N)
                    if neighbor != root
                    for source in pair
                    for other in range(D)
                    if other not in pair
                ]
                preserves = self._and(
                    f"pair_preserves_{root}_{color_a}_{color_b}",
                    [edge.Not() for edge in outside],
                )
                self.model.add_bool_or([both, preserves])

    def _add_full_column(self) -> None:
        for root in range(N):
            for output in range(D):
                anchors = []
                for neighbor in range(N):
                    if neighbor == root:
                        continue
                    has_column = self._or(
                        f"column_has_{root}_{output}_{neighbor}",
                        [self.edge(root, neighbor, source, output) for source in range(D)],
                    )
                    outside = [
                        self.edge(root, neighbor, source, other)
                        for source in range(D)
                        for other in range(D)
                        if other != output
                    ]
                    anchors.append(
                        self._and(
                            f"column_anchor_{root}_{output}_{neighbor}",
                            [has_column, *(edge.Not() for edge in outside)],
                        )
                    )
                self.model.add_bool_or(anchors)

    def add_coloring(self, coloring: Coloring) -> None:
        if coloring in self.encoded_colorings:
            return
        terms = []
        for matching_index, indices in enumerate(
            term_edge_indices(coloring, self.matchings, self.lookup)
        ):
            terms.append(
                self._and(
                    "term_" + "".join(map(str, coloring)) + f"_{matching_index}",
                    [self.edges[index] for index in indices],
                )
            )
        if len(set(coloring)) == 1:
            self.model.add(sum(terms) >= 1)
        else:
            self.model.add(sum(terms) != 1)
        self.encoded_colorings.add(coloring)
        self.terms_by_coloring[coloring] = terms

    def add_pattern_cut(self, patterns: Sequence[tuple[Coloring, Sequence[Sequence[int]]]]) -> None:
        """Forbid one exact collection of supported matching patterns."""
        literals = []
        for coloring, active_monomials in patterns:
            self.add_coloring(coloring)
            expected = {tuple(sorted(int(value) for value in term)) for term in active_monomials}
            actual = term_edge_indices(coloring, self.matchings, self.lookup)
            active_indices = {
                index for index, term in enumerate(actual) if tuple(sorted(term)) in expected
            }
            if len(active_indices) != len(expected):
                raise ValueError("pattern cut contains an unknown or duplicate monomial")
            terms = self.terms_by_coloring[coloring]
            literals.extend(
                term.Not() if index in active_indices else term
                for index, term in enumerate(terms)
            )
        self.model.add_bool_or(literals)

    def solve(self, seconds: float, workers: int, seed: int):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = seconds
        solver.parameters.num_search_workers = workers
        solver.parameters.random_seed = seed
        status = solver.solve(self.model)
        if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return solver, status, None
        support = frozenset(
            index for index, edge in enumerate(self.edges) if solver.value(edge)
        )
        return solver, status, support


def violated_colorings(
    support: frozenset[int],
    matchings: Sequence[Matching],
    lookup: dict[EdgeKey, int],
) -> list[Coloring]:
    violations = []
    for coloring in itertools.product(range(D), repeat=N):
        active = active_matching_indices(support, coloring, matchings, lookup)
        if len(set(coloring)) == 1:
            if not active:
                violations.append(coloring)
        elif len(active) == 1:
            violations.append(coloring)
    return violations


def run_orbit(
    orbit: int,
    *,
    seconds: float,
    workers: int,
    seed: int,
    max_rounds: int,
    cuts_per_round: int,
    optimize_rounds: int,
    pattern_cuts: Sequence[dict[str, object]] = (),
    pattern_cut_inputs: Sequence[dict[str, str]] = (),
) -> dict[str, object]:
    if cp_model is None:
        raise RuntimeError("OR-Tools is required to run the optimizer")
    started = time.time()
    frontier = SupportModel(orbit)
    for payload in pattern_cuts:
        certificate = payload.get("certificate")
        if not isinstance(certificate, dict):
            raise ValueError("pattern-cut file has no certificate")
        relations = certificate.get("relations")
        if not isinstance(relations, list) or not relations:
            raise ValueError("pattern-cut certificate has no relations")
        patterns = [
            (
                tuple(int(value) for value in item["binomial_coloring"]),
                [item["left_monomial"], item["right_monomial"]],
            )
            for item in relations
        ]
        patterns.append(
            (
                tuple(int(value) for value in certificate["trinomial_coloring"]),
                certificate["trinomial_terms"],
            )
        )
        frontier.add_pattern_cut(patterns)
    if optimize_rounds == 0:
        frontier.model.clear_objective()
    rounds = []
    support: frozenset[int] | None = None
    last_support: frozenset[int] | None = None
    final_status = "UNKNOWN"
    solver_terminal_status = "UNKNOWN"
    final_bound: float | None = None
    remaining: list[Coloring] = []
    for round_index in range(max_rounds):
        solver, status, support = frontier.solve(seconds, workers, seed + round_index)
        status_name = solver.status_name(status)
        solver_terminal_status = status_name
        final_status = status_name
        final_bound = float(solver.best_objective_bound)
        if support is None:
            rounds.append({"round": round_index, "status": status_name})
            if last_support is not None:
                support = last_support
                final_status = f"INCOMPLETE_AFTER_{status_name}"
            break
        last_support = support
        remaining = violated_colorings(support, frontier.matchings, frontier.lookup)
        rounds.append(
            {
                "round": round_index,
                "status": status_name,
                "support_size": len(support),
                "objective_bound": final_bound,
                "encoded_colorings": len(frontier.encoded_colorings),
                "violated_colorings": len(remaining),
            }
        )
        if not remaining:
            final_status = "VERIFIED_SUPPORT_SURVIVOR"
            break
        selected = remaining if cuts_per_round == 0 else remaining[:cuts_per_round]
        for coloring in selected:
            frontier.add_coloring(coloring)
        if round_index + 1 >= optimize_rounds:
            frontier.model.clear_objective()

    return {
        "format": 1,
        "n": N,
        "d": D,
        "orbit": orbit,
        "status": final_status,
        "solver_terminal_status": solver_terminal_status,
        "support_size": len(support) if support is not None else None,
        "objective_bound": final_bound,
        "support_keys": [frontier.keys[index] for index in sorted(support or ())],
        "remaining_violations": [list(coloring) for coloring in remaining],
        "rounds": rounds,
        "solver": "OR-Tools CP-SAT",
        "solver_version": getattr(cp_model, "__version__", "9.15.6755"),
        "seconds_per_round": seconds,
        "workers": workers,
        "seed": seed,
        "optimize_rounds": optimize_rounds,
        "pattern_cuts": len(pattern_cuts),
        "pattern_cut_inputs": list(pattern_cut_inputs),
        "elapsed_seconds": time.time() - started,
        "interpretation": "necessary support conditions only; not a complex solution",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orbit", type=int, required=True, choices=range(31))
    parser.add_argument("--seconds", type=float, default=30.0)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=20260822)
    parser.add_argument("--max-rounds", type=int, default=20)
    parser.add_argument(
        "--cuts-per-round",
        type=int,
        default=0,
        help="violations added per round; 0 adds all observed violations",
    )
    parser.add_argument(
        "--optimize-rounds",
        type=int,
        default=1,
        help="minimize support for this many initial rounds, then seek feasibility",
    )
    parser.add_argument(
        "--pattern-cut",
        action="append",
        type=Path,
        default=[],
        help="Laurent certificate JSON whose exact equation pattern is forbidden",
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    pattern_cuts = [
        json.loads(path.read_text(encoding="utf-8")) for path in args.pattern_cut
    ]
    repo_root = HERE.parents[1]
    pattern_cut_inputs = []
    for path in args.pattern_cut:
        resolved = path.resolve()
        try:
            display_path = str(resolved.relative_to(repo_root))
        except ValueError:
            display_path = str(resolved)
        pattern_cut_inputs.append(
            {"path": display_path, "sha256": file_sha256(resolved)}
        )
    result = run_orbit(
        args.orbit,
        seconds=args.seconds,
        workers=args.workers,
        seed=args.seed,
        max_rounds=args.max_rounds,
        cuts_per_round=args.cuts_per_round,
        optimize_rounds=args.optimize_rounds,
        pattern_cuts=pattern_cuts,
        pattern_cut_inputs=pattern_cut_inputs,
    )
    output = args.output or HERE / f"orbit_{args.orbit:02d}.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: result[key] for key in ("orbit", "status", "support_size", "elapsed_seconds")}, indent=2))


if __name__ == "__main__":
    main()
