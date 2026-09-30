"""Static port obligations. These checks do not replace a Lean build."""

import importlib.util
import json
import re
import subprocess
import sys
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
PACKAGES = [
    "lean", "lean/bridge", "lean/vendor/zeta23",
    "hunts/ainta_seven_point/lean", "hunts/ainta_seven_point/lean-four-point",
    "hunts/frontier_math/zeta23ext",
]


def test_heavy_certificate_build_has_bounded_concurrency():
    """No three cell modules or two chunk modules can build simultaneously."""
    root = ROOT / "hunts/ainta_seven_point/lean-four-point/FourPointCand"
    edges = {
        path.stem: set(re.findall(r"^public import FourPointCand\.(\w+)", path.read_text(), re.M))
        for path in root.glob("*.lean")
    }

    def ancestors(name, visiting=frozenset()):
        assert name not in visiting, "cyclic certificate imports"
        direct = edges.get(name, set())
        return direct | set().union(*(ancestors(dep, visiting | {name}) for dep in direct))

    closure = {name: ancestors(name) for name in edges}
    cells = [name for name in edges if re.fullmatch(r"Cells\d+", name)]
    chunks = [name for name in edges if re.fullmatch(r"Chunks\d+", name)]
    assert cells and chunks
    for triple in combinations(cells, 3):
        assert any(a in closure[b] or b in closure[a] for a, b in combinations(triple, 2))
    for a, b in combinations(chunks, 2):
        assert a in closure[b] or b in closure[a]
    for name in chunks:
        assert set(cells) | {"Cover"} <= closure[name]


def test_all_submitted_lean_files_have_module_headers_and_fit_the_line_cap():
    files = subprocess.check_output(
        ["git", "ls-files", "-z", "*.lean"], cwd=ROOT,
    ).decode().split("\0")
    files = [name for name in files if name]
    assert len(files) >= 643
    for name in files:
        path = ROOT / name
        assert not path.is_symlink(), name
        source = path.read_text()
        assert re.match(r"\A\s*(?:/-(?![!-]).*?-/\s*)*module(?:\s|$)", source, re.S), name
        assert len(source.rstrip("\n").split("\n")) <= 10000, name


def test_all_contained_packages_use_one_compiler_and_canonical_mathlib_pin():
    revisions = {}
    for name in PACKAGES:
        package = ROOT / name
        assert (package / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc2"
        manifest = json.loads((package / "lake-manifest.json").read_text())
        dependencies = manifest["packages"]
        assert len({item["name"] for item in dependencies}) == len(dependencies)
        mathlib = next(item for item in dependencies if item["name"] == "mathlib")
        assert mathlib["rev"] == MATHLIB
        assert mathlib["url"] == "https://github.com/leanprover-community/mathlib4"
        for item in dependencies:
            if item["type"] == "git":
                assert revisions.setdefault(item["name"], item["rev"]) == item["rev"]
            elif item["type"] == "path":
                dependency = (package / item["dir"]).resolve()
                assert dependency.is_relative_to(ROOT)
                assert (dependency / item["configFile"]).is_file()
            else:
                raise AssertionError(item)


def test_generator_preserves_the_proof_while_emitting_modules():
    directory = ROOT / "hunts/ainta_seven_point"
    spec = importlib.util.spec_from_file_location("four_point_gen", directory / "four_point_gen.py")
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(directory))
    try:
        spec.loader.exec_module(module)
    finally:
        sys.path.pop(0)
    source = "import FourPointCand.Base\n\nlemma example : True := by trivial\n"
    assert module.module_source(source) == (
        "module\n\npublic import FourPointCand.Base\n"
        "\n@[expose] public section\n\nlemma example : True := by trivial\n"
    )
    assert module.module_source is module.G.module_source


def test_analytic_bridge_port_evidence_records_success_and_standard_axioms():
    evidence = ROOT / "hunts/four_point_pressure/port-evidence/36505843011"
    assert (evidence / "revision.txt").read_text().strip() == "e9621a24948224acebca6e39980bdb0ea57db788"
    assert (evidence / "target.txt").read_text().strip() == "Port target: Zeta23Ext.Bridge.Main"
    assert (evidence / "outcome.txt").read_text().strip() == "Port build outcome: success"
    assert (evidence / "count.txt").read_text().strip() == "Module artifacts present: 157"
    assert "Lean (version 4.35.0-rc2," in (evidence / "lean-version.txt").read_text()
    log = (evidence / "build.log").read_text()
    assert "Build completed successfully" in log
    records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    assert any(name == "Zeta23Ext.Bridge.n_point_bound" for name, _ in records)
    for name, axioms in records:
        names = {item.strip().removeprefix("Classical.") for item in axioms.split(",")}
        assert names <= {"propext", "choice", "Quot.sound"}, name


def test_stronger_interface_preserves_the_source_statements_and_separates_challenge():
    package = ROOT / "hunts/ainta_seven_point/lean-four-point"
    challenge = (package / "StrongerChallenge.lean").read_text()
    solution = (package / "StrongerSolution.lean").read_text()
    source = (package / "FourPointCand/Main.lean").read_text()
    comparator = json.loads((package / "comparator.json").read_text())
    assert comparator["challenge_module"] == "StrongerChallenge"
    assert comparator["solution_module"] == "StrongerSolution"
    assert re.findall(r"^public import (\S+)", challenge, re.M) == ["Mathlib"]
    assert re.findall(r"^public import (\S+)", solution, re.M) == ["Mathlib", "FourPointCand.Main"]
    assert len(re.findall(r"^  sorry$", challenge, re.M)) == 2
    assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", solution)
    shared = lambda text: text.split("def IsNontrivialZero ", 1)[1].split("\ntheorem ", 1)[0]
    assert shared(challenge) == shared(solution)
    names = ["four_point_bound", "four_point_bound_ratio"]
    assert comparator["theorem_names"] == [f"Zeta23Ext.PalomarFourPoint.{name}" for name in names]
    assert set(comparator["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
    for name in names:
        pattern = rf"(?ms)^theorem {name} :(.*?) := by"
        statement = re.search(pattern, challenge)[1]
        assert re.search(pattern, solution)[1] == statement
        assert re.search(pattern, source)[1].replace("HD 1", "H") == statement
