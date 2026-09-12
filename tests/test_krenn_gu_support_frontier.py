from __future__ import annotations

import hashlib
import importlib.util
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "hunts" / "r_044dd2" / "support_frontier.py"
HUNT = ROOT / "hunts" / "r_044dd2"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def independent_edge_key(u: int, v: int, a: int, b: int):
    return (u, v, a, b) if u < v else (v, u, b, a)


def independent_transform_support(payload, pi, sigma):
    transformed = dict(payload)
    transformed["support_keys"] = sorted(
        independent_edge_key(pi[u], pi[v], sigma[a], sigma[b])
        for u, v, a, b in payload["support_keys"]
    )
    return transformed


def independent_signature(coloring, support, matchings):
    keys = tuple(
        (u, v, a, b)
        for u in range(8)
        for v in range(u + 1, 8)
        for a in range(3)
        for b in range(3)
    )
    lookup = {key: index for index, key in enumerate(keys)}
    terms = []
    for matching in matchings:
        factors = tuple(
            sorted(
                lookup[
                    independent_edge_key(
                        u, v, coloring[u], coloring[v]
                    )
                ]
                for u, v in matching
            )
        )
        if all(keys[index] in support for index in factors):
            terms.append(factors)
    return tuple(sorted(terms))


def certificate_patterns(payload):
    certificate = payload["certificate"]
    patterns = [
        (
            tuple(relation["binomial_coloring"]),
            tuple(
                sorted(
                    (
                        tuple(relation["left_monomial"]),
                        tuple(relation["right_monomial"]),
                    )
                )
            ),
        )
        for relation in certificate["relations"]
    ]
    patterns.append(
        (
            tuple(certificate["trinomial_coloring"]),
            tuple(
                sorted(tuple(term) for term in certificate["trinomial_terms"])
            ),
        )
    )
    return patterns


def load_script():
    spec = importlib.util.spec_from_file_location("krenn_support_frontier", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_named(name: str):
    path = HUNT / name
    spec = importlib.util.spec_from_file_location(f"krenn_{path.stem}", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_8x3_combinatorial_dimensions() -> None:
    module = load_script()
    assert len(module.perfect_matchings(tuple(range(8)))) == 105
    assert len(module.variable_keys()) == 252
    assert len(module.target_representatives()) == 31


def test_every_branch_base_has_four_matching_edges_per_colour() -> None:
    module = load_script()
    keys = module.variable_keys()
    lookup = {key: index for index, key in enumerate(keys)}
    matchings = module.perfect_matchings(tuple(range(8)))
    for orbit in range(31):
        base = frozenset(module.branch_base_indices(orbit, lookup))
        assert len(base) == 12
        for color in range(3):
            active = module.active_matching_indices(
                base, (color,) * 8, matchings, lookup
            )
            assert active


def test_edge_key_reverses_endpoint_colours() -> None:
    module = load_script()
    assert module.edge_key(6, 2, 1, 0) == (2, 6, 0, 1)


def test_committed_31_branch_census_replays(tmp_path: Path) -> None:
    audit = load_named("audit.py")
    census = json.loads((HUNT / "results.json").read_text(encoding="utf-8"))
    assert census["branches"] == 31
    assert census["verified_support_survivors"] == 31
    assert census["support_size_min"] == 76
    assert census["support_size_max"] == 132
    assert census["support_size_median"] == 118
    for row in census["rows"]:
        path = tmp_path / f"orbit-{row['orbit']}.json"
        path.write_text(json.dumps(row), encoding="utf-8")
        replay = audit.audit(path)
        assert replay["verified_support_survivor"], row["orbit"]


def test_three_laurent_certificates_replay() -> None:
    audit = load_named("audit_laurent.py")
    for index, expected_l1 in ((1, 1), (2, 3), (3, 1)):
        replay = audit.audit(
            HUNT / "artifacts" / f"orbit18-support-{index:02d}.json",
            HUNT / "artifacts" / f"orbit18-laurent-{index:02d}.json",
        )
        assert replay["verified"]
        assert replay["combination_l1"] == expected_l1


def test_followup_supports_replay_in_the_claimed_branch() -> None:
    audit = load_named("audit.py")
    for index in range(4, 8):
        replay = audit.audit(
            HUNT / "artifacts" / f"orbit18-support-{index:02d}.json"
        )
        assert replay["verified_support_survivor"], index
        assert replay["branch_base_failures"] == []


def test_fourth_laurent_certificate_replays() -> None:
    audit = load_named("audit_laurent.py")
    replay = audit.audit(
        HUNT / "artifacts" / "orbit18-support-05.json",
        HUNT / "artifacts" / "orbit18-laurent-05.json",
    )
    assert replay["verified"]
    assert replay["combination_l1"] == 1


def test_orbit18_stabilizer_is_exact_and_portable() -> None:
    stabilizer = load_named("stabilizer.py")
    expected_nonidentity = (
        (6, 7, 3, 2, 4, 5, 0, 1),
        (0, 2, 1),
    )
    elements = stabilizer.get_stabilizer(18)
    assert elements == ((tuple(range(8)), tuple(range(3))), expected_nonidentity)
    assert stabilizer.nonidentity_element(18) == expected_nonidentity
    assert stabilizer.CENSUS == HUNT.parent / "r_322dae" / "results.json"
    assert stabilizer.CENSUS.is_file()


def test_symmetric_certificates_replay_on_transformed_supports(
    tmp_path: Path,
) -> None:
    audit = load_named("audit_laurent.py")
    pi = (6, 7, 3, 2, 4, 5, 0, 1)
    sigma = (0, 2, 1)
    for index in (1, 2, 3, 5):
        source = HUNT / "artifacts" / f"orbit18-laurent-{index:02d}.json"
        symmetric = (
            HUNT / "artifacts" / f"orbit18-laurent-{index:02d}-sym.json"
        )
        support = json.loads(
            (
                HUNT / "artifacts" / f"orbit18-support-{index:02d}.json"
            ).read_text(encoding="utf-8")
        )
        transformed_path = tmp_path / f"support-{index:02d}-sym.json"
        transformed_path.write_text(
            json.dumps(independent_transform_support(support, pi, sigma)),
            encoding="utf-8",
        )
        replay = audit.audit(transformed_path, symmetric)
        metadata = json.loads(symmetric.read_text(encoding="utf-8"))[
            "symmetry_expansion"
        ]
        assert replay["verified"], index
        assert metadata["source"] == source.name
        assert metadata["source_sha256"] == file_sha256(source)


def test_support_artifacts_name_and_hash_every_loaded_cut() -> None:
    for index in range(1, 8):
        payload = json.loads(
            (
                HUNT / "artifacts" / f"orbit18-support-{index:02d}.json"
            ).read_text(encoding="utf-8")
        )
        inputs = payload["pattern_cut_inputs"]
        assert len(inputs) == payload["pattern_cuts"]
        for item in inputs:
            path = ROOT / item["path"]
            assert path.is_file()
            assert item["sha256"] == file_sha256(path)


def test_support7_is_a_concrete_blind_support_for_the_current_sieve() -> None:
    audit = load_named("audit.py")
    payload = json.loads(
        (HUNT / "artifacts" / "orbit18-support-07.json").read_text(
            encoding="utf-8"
        )
    )
    support = {tuple(item) for item in payload["support_keys"]}
    matchings = audit.matchings(tuple(range(8)))
    zero_binomial_colorings = [
        coloring
        for coloring in itertools.product(range(3), repeat=8)
        if len(set(coloring)) > 1
        and audit.active_count(support, coloring, matchings) == 2
    ]
    assert zero_binomial_colorings == []

    for item in payload["pattern_cut_inputs"]:
        certificate = json.loads((ROOT / item["path"]).read_text(encoding="utf-8"))
        assert any(
            independent_signature(coloring, support, matchings) != expected
            for coloring, expected in certificate_patterns(certificate)
        )
