"""HuntSpec: the contract block a new hunt's MISSION.md carries.

Parser and validator live here on purpose — the primitive is on probation
(`hunts/HUNTSPEC.md`, probation terms) and earns a real module the first time
a kill condition fires mechanically. Three layers:

1. the parser handles exactly the strict flat subset the spec page promises
   (single-line scalars, lists of strings, nothing else);
2. the validator enforces the required keys, the non-empty rules, and the
   crude-but-running lexical rule that an oracle naming a model is refused;
3. the repository scan validates every ``MISSION.md`` that contains a block,
   and the template on the spec page itself — so the page cannot drift from
   the validator without a test failing.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
_HUNTS = _REPO_ROOT / "hunts"

_BLOCK = re.compile(r"```huntspec\n(.*?)```", re.DOTALL)

REQUIRED_SCALARS = ("question", "frontier")
REQUIRED_LISTS = (
    "dead_routes",
    "required_oracles",
    "kill_conditions",
    "agents_may",
    "agents_may_not",
)
OPTIONAL_SCALARS = ("id", "proposed_attack")

#: The crude lexical rule: an oracle entry naming a model is a declaration
#: that the charter's one rule is being broken, and it is refused at parse
#: time rather than discovered at post-mortem time.
_MODEL_WORDS = ("model", "llm", "gpt", "claude", "gemini", "agent")


class HuntSpecError(ValueError):
    pass


def parse_huntspec(text: str) -> dict:
    """Parse the strict flat subset: scalars and lists of strings only."""
    spec: dict[str, object] = {}
    current_list: list[str] | None = None
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip()
        if not line.strip() or line.strip().startswith("#"):
            continue
        if line.startswith("  - "):
            if current_list is None:
                raise HuntSpecError(f"line {lineno}: list item outside a list")
            item = line[4:].strip()
            if not item:
                raise HuntSpecError(f"line {lineno}: empty list item")
            current_list.append(item)
            continue
        if line.startswith((" ", "\t")):
            raise HuntSpecError(
                f"line {lineno}: nested or continued values are not in the "
                "subset; keep scalars on one line"
            )
        if ":" not in line:
            raise HuntSpecError(f"line {lineno}: expected 'key: value' or 'key:'")
        key, _, value = line.partition(":")
        key = key.strip()
        if key in spec:
            raise HuntSpecError(f"line {lineno}: key {key!r} repeated")
        value = value.strip()
        if value:
            spec[key] = value
            current_list = None
        else:
            current_list = []
            spec[key] = current_list
    return spec


def validate_huntspec(spec: dict) -> tuple[str, ...]:
    """Every rule the block breaks, one disputable sentence each."""
    problems: list[str] = []
    for key in REQUIRED_SCALARS:
        if key not in spec:
            problems.append(f"missing required key {key!r}")
        elif not isinstance(spec[key], str):
            problems.append(f"{key!r} must be a single-line scalar")
    for key in REQUIRED_LISTS:
        if key not in spec:
            problems.append(f"missing required key {key!r}")
        elif not isinstance(spec[key], list):
            problems.append(f"{key!r} must be a list")
        elif key != "dead_routes" and not spec[key]:
            problems.append(f"{key!r} must be non-empty")
    for key in spec:
        if key not in REQUIRED_SCALARS + REQUIRED_LISTS + OPTIONAL_SCALARS:
            problems.append(f"unknown key {key!r}")
    oracles = spec.get("required_oracles")
    if isinstance(oracles, list):
        for entry in oracles:
            lowered = entry.lower()
            for word in _MODEL_WORDS:
                if re.search(rf"\b{word}\b", lowered):
                    problems.append(
                        f"oracle {entry!r} names a model ({word!r}): a model "
                        "is not an oracle, and no agent runs without one"
                    )
    return tuple(problems)


def _blocks_in(text: str) -> list[str]:
    return _BLOCK.findall(text)


# --- run manifests: the primitive's other half, same subset, same home ----

_MANIFEST_BLOCK = re.compile(r"```runmanifest\n(.*?)```", re.DOTALL)

MANIFEST_SCALARS = ("id", "hunt", "started", "finished", "outcome")
MANIFEST_LISTS = ("ran", "artifacts")


def validate_runmanifest(spec: dict) -> tuple[str, ...]:
    problems: list[str] = []
    for key in MANIFEST_SCALARS:
        if key not in spec:
            problems.append(f"missing required key {key!r}")
        elif not isinstance(spec[key], str):
            problems.append(f"{key!r} must be a single-line scalar")
    for key in MANIFEST_LISTS:
        if key not in spec:
            problems.append(f"missing required key {key!r}")
        elif not isinstance(spec[key], list):
            problems.append(f"{key!r} must be a list")
    if isinstance(spec.get("ran"), list) and not spec["ran"]:
        problems.append("'ran' must be non-empty: a run that ran nothing is not a run")
    for key in spec:
        if key not in MANIFEST_SCALARS + MANIFEST_LISTS:
            problems.append(f"unknown key {key!r}")
    return tuple(problems)


# ---------------------------------------------------------------------------
# 1. the parser: exactly the promised subset
# ---------------------------------------------------------------------------

_GOOD = """\
id: sample
question: Does X improve the bound?
frontier: lower 0.1 upper 0.2
dead_routes:
  - the scalar route
required_oracles:
  - exact enumeration
kill_conditions:
  - deteriorates under refinement
agents_may:
  - search
agents_may_not:
  - declare novelty
"""


def test_the_good_block_parses_and_validates() -> None:
    spec = parse_huntspec(_GOOD)
    assert spec["question"] == "Does X improve the bound?"
    assert spec["dead_routes"] == ["the scalar route"]
    assert validate_huntspec(spec) == ()


def test_nested_values_are_refused() -> None:
    with pytest.raises(HuntSpecError, match="not in the subset"):
        parse_huntspec("frontier:\n  lower: 0.1\n")


def test_a_repeated_key_is_refused() -> None:
    with pytest.raises(HuntSpecError, match="repeated"):
        parse_huntspec("question: a\nquestion: b\n")


def test_a_stray_list_item_is_refused() -> None:
    with pytest.raises(HuntSpecError, match="outside a list"):
        parse_huntspec("  - floating\n")


# ---------------------------------------------------------------------------
# 2. the validator: required keys, non-empty rules, the oracle rule
# ---------------------------------------------------------------------------


def test_a_missing_kill_condition_list_is_reported() -> None:
    spec = parse_huntspec(_GOOD.replace("kill_conditions:\n  - deteriorates under refinement\n", ""))
    assert any("kill_conditions" in p for p in validate_huntspec(spec))


def test_an_empty_required_list_is_reported() -> None:
    spec = parse_huntspec(_GOOD)
    spec["kill_conditions"] = []
    assert any("non-empty" in p for p in validate_huntspec(spec))


def test_dead_routes_may_be_empty_but_must_exist() -> None:
    spec = parse_huntspec(_GOOD)
    spec["dead_routes"] = []
    assert validate_huntspec(spec) == ()
    del spec["dead_routes"]
    assert any("dead_routes" in p for p in validate_huntspec(spec))


def test_a_model_offered_as_an_oracle_is_refused() -> None:
    spec = parse_huntspec(_GOOD)
    spec["required_oracles"] = ["a frontier model votes on plausibility"]
    problems = validate_huntspec(spec)
    assert any("not an oracle" in p for p in problems)


def test_an_unknown_key_is_reported() -> None:
    spec = parse_huntspec(_GOOD + "vibe: good\n")
    assert any("unknown key 'vibe'" in p for p in validate_huntspec(spec))


# ---------------------------------------------------------------------------
# 3. the repository scan, and the spec page's own template
# ---------------------------------------------------------------------------


def test_the_spec_pages_template_is_valid() -> None:
    page = (_HUNTS / "HUNTSPEC.md").read_text(encoding="utf-8")
    blocks = _blocks_in(page)
    assert len(blocks) == 1, "hunts/HUNTSPEC.md must carry exactly one template block"
    spec = parse_huntspec(blocks[0])
    assert validate_huntspec(spec) == (), validate_huntspec(spec)


_MANIFEST_GOOD = """\
id: sample-run
hunt: sample
started: 2026-08-11T22:00-05:00
finished: 2026-08-12T05:40-05:00
ran:
  - a command
outcome: it measured a thing
artifacts:
"""


def test_the_good_manifest_validates() -> None:
    spec = parse_huntspec(_MANIFEST_GOOD)
    assert validate_runmanifest(spec) == ()
    assert spec["artifacts"] == []  # empty is allowed: nothing produced, said


def test_a_manifest_that_ran_nothing_is_refused() -> None:
    spec = parse_huntspec(_MANIFEST_GOOD)
    spec["ran"] = []
    assert any("not a run" in p for p in validate_runmanifest(spec))


def test_a_manifest_missing_its_outcome_is_reported() -> None:
    spec = parse_huntspec(_MANIFEST_GOOD.replace("outcome: it measured a thing\n", ""))
    assert any("outcome" in p for p in validate_runmanifest(spec))


def test_the_spec_pages_manifest_template_is_valid() -> None:
    page = (_HUNTS / "HUNTSPEC.md").read_text(encoding="utf-8")
    blocks = _MANIFEST_BLOCK.findall(page)
    assert len(blocks) == 1, "hunts/HUNTSPEC.md must carry exactly one manifest template"
    spec = parse_huntspec(blocks[0])
    assert validate_runmanifest(spec) == (), validate_runmanifest(spec)


def test_every_runmanifest_block_in_the_tree_validates() -> None:
    for path in sorted(_HUNTS.glob("*/*.md")):
        for block in _MANIFEST_BLOCK.findall(path.read_text(encoding="utf-8")):
            spec = parse_huntspec(block)
            problems = validate_runmanifest(spec)
            assert problems == (), f"{path}: {problems}"


def test_every_mission_huntspec_block_in_the_tree_validates() -> None:
    """Hunts live before 2026-08-11 carry no block and are out of scope;
    any block that exists must parse and validate."""
    checked = 0
    for mission in sorted(_HUNTS.glob("*/MISSION.md")):
        for block in _blocks_in(mission.read_text(encoding="utf-8")):
            spec = parse_huntspec(block)
            problems = validate_huntspec(spec)
            assert problems == (), f"{mission}: {problems}"
            checked += 1
    # No minimum: zero blocks is the pre-probation tree, and that is fine.
    assert checked >= 0
