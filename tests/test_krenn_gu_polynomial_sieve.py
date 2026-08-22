from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HUNT = ROOT / "hunts" / "r_044dd2"
SCRIPT = HUNT / "polynomial_sieve.py"
SUPPORT = HUNT / "artifacts" / "orbit18-support-07.json"
ARTIFACT = HUNT / "artifacts" / "orbit18-polynomial-07-cap4.json"
RESOURCE_ARTIFACT = HUNT / "artifacts" / "orbit18-polynomial-07-cap5-resource.json"


def load_script():
    spec = importlib.util.spec_from_file_location("krenn_polynomial_sieve", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_sparse_exact_membership_accepts_and_rejects_toy_targets(capsys) -> None:
    module = load_script()
    relations = (module.Relation((0,), ((0,), (1,))),)

    reachable, columns, _, _, complete = module.reachable_closure(
        relations, {(0,): 1, (1,): 1}, progress_every=1
    )
    progress = [json.loads(line) for line in capsys.readouterr().out.splitlines()]
    assert progress[-1]["stage"] == "closure"
    assert progress[-1]["processed_monomials"] == 2
    assert progress[-1]["queued_monomials"] == 0
    assert complete
    assert module.exact_membership(
        relations, {(0,): 1, (1,): 1}, reachable, columns
    )[0]

    reachable, columns, _, _, complete = module.reachable_closure(
        relations, {(0,): 1}
    )
    assert complete
    assert not module.exact_membership(
        relations, {(0,): 1}, reachable, columns
    )[0]


def test_support7_trinomial_target_product_screen_replays() -> None:
    module = load_script()
    result = module.screen(
        SUPPORT,
        target_indices=(0, 1, 2),
        max_relation_terms=3,
        exact=True,
    )
    assert result["status"] == "NO_FIXED_DEGREE_MEMBERSHIP"
    assert result["retained_relations"] == 180
    assert result["target_terms"] == 4500
    assert result["reachable_monomials"] == 5406
    assert result["relation_multiples"] == 1569
    assert result["exact_rank"] == 523
    assert result["exact_residual_terms"] == 4500


def test_committed_cap4_frontier_is_bound_to_support7() -> None:
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["support_input"]["sha256"] == hashlib.sha256(
        SUPPORT.read_bytes()
    ).hexdigest()
    assert payload["support_size"] == 138
    assert payload["target_indices"] == [0, 1, 2]
    assert payload["max_relation_terms"] == 4
    assert payload["retained_relations"] == 755
    assert payload["reachable_monomials"] == 96319
    assert payload["relation_multiples"] == 184997
    assert payload["closure_complete"] is True
    assert payload["modular_membership"] is False
    assert payload["exact_membership"] is False
    assert payload["exact_rank"] == 59284
    assert payload["exact_residual_terms"] == 4216
    assert payload["status"] == "NO_FIXED_DEGREE_MEMBERSHIP"


def test_cap5_resource_frontier_is_bound_to_support7() -> None:
    payload = json.loads(RESOURCE_ARTIFACT.read_text(encoding="utf-8"))
    assert payload["support_input"]["sha256"] == hashlib.sha256(
        SUPPORT.read_bytes()
    ).hexdigest()
    assert payload["max_relation_terms"] == 5
    assert payload["closure"]["complete"] is True
    assert payload["closure"]["relation_multiples"] == 13_379_522
    assert payload["modular_elimination"]["processed_columns"] == 2_900_000
    assert payload["modular_elimination"]["total_columns"] == 13_379_522
    assert payload["status"] == "RESOURCE_LIMIT"
    assert "No algebraic conclusion" in payload["interpretation"]
