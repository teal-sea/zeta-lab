from __future__ import annotations

import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "hunts" / "r_044dd2" / "support_frontier.py"
HUNT = ROOT / "hunts" / "r_044dd2"


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
