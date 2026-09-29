"""Check the saved build record and its source binding, without replaying Lean."""

import hashlib
import json
import math
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "hunts/four_point_pressure/evidence"
LOG = EVIDENCE / "modal-ap-7zxzQj0YqTwlQUP6P06ecn-client-stdout-stderr-launch-20260928t220203.log"
LAYERS = (
    ["preflight", "Base"]
    + [f"Cells{i}" for i in range(26)]
    + ["Cells", "Cover"]
    + [f"Chunks{i}" for i in range(16)]
    + ["Boxes", "Main", "WholeLibrary"]
)
DECLARATIONS = {
    "F4_eq", "cover1", "four_point_cert", "Phi_four",
    "four_point_bound", "four_point_bound_ratio",
}


def verification():
    records = [
        json.loads(line.removeprefix("FPVERIFY_JSON "))
        for line in LOG.read_text().splitlines()
        if line.startswith("FPVERIFY_JSON ")
    ]
    assert len(records) == 1
    return records[0]


def test_raw_evidence_checksums():
    lines = (EVIDENCE / "SHA256SUMS").read_text().splitlines()
    assert len(lines) == 3
    names = set()
    for line in lines:
        digest, name = line.split("  ", 1)
        assert Path(name).name == name
        assert name not in names
        names.add(name)
        assert hashlib.sha256((EVIDENCE / name).read_bytes()).hexdigest() == digest
    assert names == {
        LOG.name, "zeta-fourpoint-serial-result-final3.md",
        "main-axioms-print-output.txt",
    }


def test_every_build_layer_has_a_successful_receipt():
    report = verification()
    assert report["ok"] is True
    assert report["problems"] == []
    assert list(report["receipts"]) == LAYERS
    paths = set()
    for index, name in enumerate(LAYERS):
        receipt = report["receipts"][name]
        assert receipt["index"] == index
        assert receipt["name"] == name
        assert receipt["ok"] is True
        if name == "preflight":
            assert receipt["hash_equal"] is True
            continue
        module = "FourPointCand" if name == "WholeLibrary" else f"FourPointCand.{name}"
        assert receipt["module"] == module
        assert receipt["sorry_warnings"] == 0
        builds = [step for step in receipt["steps"] if step["label"] == "build"]
        assert len(builds) == 1
        assert builds[0]["argv"] == ["lake", "build", module]
        for step in receipt["steps"]:
            assert step["rc"] == 0
            assert step["first_error"] is None
            assert step["sorry_warnings"] == 0
        assert len(receipt["olean"]) == 1
        artifact = receipt["olean"][0]
        assert artifact["bytes"] > 0
        assert re.fullmatch(r"[0-9a-f]{64}", artifact["sha256"])
        assert artifact["path"].endswith("/" + module.replace(".", "/") + ".olean")
        assert artifact["path"] not in paths
        paths.add(artifact["path"])
    assert len(paths) == 48
    assert set(report["oleans"]) == paths
    assert all(value is True for value in report["oleans"].values())
    assert report["unexpected_oleans"] == []
    assert all(hits == [] for hits in report["token_scan"].values())


def test_all_six_axiom_lines_match_the_raw_record():
    report = verification()
    lines = (EVIDENCE / "main-axioms-print-output.txt").read_text().splitlines()
    assert report["main_axiom_lines"] == lines
    assert report["receipts"]["Main"]["axiom_lines"] == lines
    assert len(lines) == 6
    found = set()
    for line in lines:
        match = re.fullmatch(
            r"info: FourPointCand/Main\.lean:\d+:0: "
            r"'Zeta23Ext\.Bridge\.FourPoint\.([A-Za-z0-9_]+)' "
            r"depends on axioms: \[propext, Classical\.choice, Quot\.sound\]",
            line,
        )
        assert match, line
        found.add(match[1])
    assert found == DECLARATIONS
    assert report["axiom_audit"]["ok"] is True


def test_recorded_source_manifests_match_preflight_and_final_verification():
    manifest = json.loads((EVIDENCE / "source-manifest.json").read_text())
    assert manifest["source_commit"] == "5522b96314f7f63198ae3ec4e71d954255f93d1a"
    report = verification()
    preflight = report["receipts"]["preflight"]
    for name, key, count in [("candidate", "fp", 51), ("bridge", "bridge", 84)]:
        group = manifest["groups"][name]
        assert len(group["files"]) == count == preflight[f"{key}_files"]
        records = sorted(f"{digest}  {path}\n" for path, digest in group["files"].items())
        digest = hashlib.sha256("".join(records).encode()).hexdigest()
        assert digest == group["tree_sha256"]
        assert digest == report[f"{key}_tree_sha256"] == preflight[f"{key}_tree_sha256"]


def test_candidate_proof_text_matches_the_historical_build_after_module_port():
    group = json.loads((EVIDENCE / "source-manifest.json").read_text())["groups"]["candidate"]
    package = ROOT / group["root"]
    sources = {
        path.relative_to(package).as_posix()
        for path in (package / "FourPointCand").rglob("*.lean")
    } | {"FourPointCand.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    assert sources == set(group["files"])
    for path, digest in group["files"].items():
        if not path.endswith(".lean"):
            continue
        source = (package / path).read_text()
        assert source.startswith("module\n\n")
        source = source.removeprefix("module\n\n")
        source = source.replace("\n@[expose] public section\n", "", 1)
        source = re.sub(r"(?m)^public import ", "import ", source)
        assert hashlib.sha256(source.encode()).hexdigest() == digest, path


def test_advertised_decimal_and_improvement():
    h = 1.5 - 1 / (math.sqrt(2) * math.tan(1 / math.sqrt(2)))
    candidate = (14400000 * h - 17240) / 14366681
    registered = (906250 * h - 1085) / 904171
    assert abs(candidate - 0.6728603588388667) < 1e-14
    assert abs(registered - 0.6728470197666888) < 1e-14
    assert candidate > registered
