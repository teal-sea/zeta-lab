"""Static port obligations. These checks do not replace a Lean build."""

import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
PACKAGES = [
    "lean", "lean/bridge", "lean/vendor/zeta23",
    "hunts/ainta_seven_point/lean", "hunts/ainta_seven_point/lean-four-point",
    "hunts/frontier_math/zeta23ext",
]


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
