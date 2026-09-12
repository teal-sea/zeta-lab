"""The adaptive-block freeze archive is present, hash-pinned, and its imports are honest.

Imported on 2026-09-06 under
``hunts/prime_pair_error/frontier/2026-09-06/adaptive_freeze_v1/`` from the downloaded
snapshot ``zeta_adaptive_freeze_v1.zip``, the checkpoint taken when the research was
paused. The archive bundles seventeen original research ZIPs, the snapshot's own
provenance files, a byte-identical extraction of the three newest packages (support
analysis, repair-cost rule, adaptive correction block), and its own verifier
``verify_freeze.py``. Nothing in it is a prime-counting record or an RH result, and the
last three packages carry no independent review.

Same discipline as ``tests/test_research_checkpoint_archive.py``, for the same reason: an
earlier preservation pass on this date documented an archive that never landed, and
nothing mechanical noticed. So this file does not trust either README. Every check below
fails rather than skips.

1. The ZIP is present, non-empty, and has the byte count and SHA-256 the download was
   delivered with. Those two are hard-coded here and cross-checked against the
   ``archive/SHA256SUMS`` sidecar and the hash the directory README states, so the three
   cannot drift apart silently.
2. The archive's own ``FILE_MANIFEST.json`` is non-empty, carries the right snapshot
   identity, and every file it lists is inside with the recorded hash and byte count, and
   nothing else is.
3. ``ARCHIVE_CONTENTS.json`` is the recursive inventory. It names exactly seventeen
   original archives, every nested member verifies by CRC and hash, and the four nested
   dependency links ``LOCAL_VALIDATION.json`` claims are byte-identical really are. The
   three originals already committed elsewhere in this tree are the same bytes as the
   committed files.
4. The archive's included verifier, run on a fresh extraction, reports PASS with the
   counts recorded for this snapshot. It is run against a scratch extraction, never
   against the repository tree, so a generated file in the working copy cannot make it
   fail and a missing file cannot make it pass.
5. The three working directories imported beside the archive contain exactly the archive's
   ``latest_extracted`` members, byte for byte, and those members are the same bytes as
   the members of the corresponding nested original ZIP. No file carries the reserved
   word, so no vocabulary edit is documented and the copies must be identical. A later
   review may add a review document and a ``review/`` subdirectory, the layout
   ``factorial_certificate_pilot/`` established; anything else is drift.
6. The nine provenance files beside the archive are byte-identical to the archive members
   they were copied from, and the ZIP itself is free of absolute paths, traversal,
   symlinks and encrypted members.

The negative controls at the end are the point of the file: they plant a missing, an
empty, a mutated, an extra and a symlinked file and assert that the checks above actually
turn red. A gate that cannot fail is not a gate.
"""

from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
import re
import shutil
import zipfile

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FRONTIER = os.path.join(REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06")
FREEZE = os.path.join(FRONTIER, "adaptive_freeze_v1")
ARCHIVE = os.path.join(FREEZE, "archive", "zeta_adaptive_freeze_v1.zip")
SUMS = os.path.join(FREEZE, "archive", "SHA256SUMS")
README = os.path.join(FREEZE, "README.md")
PROVENANCE = os.path.join(FREEZE, "provenance")
TOP = "zeta_adaptive_freeze_v1/"

SNAPSHOT_ID = "zeta-adaptive-freeze-v1"
EXPECTED_SHA256 = "a264da2d6da781a3133ab75557f22842fe2581e210c7a628c0fddeff0c653681"
EXPECTED_BYTES = 4_185_414

# What the snapshot's own verifier reports on a clean extraction.
EXPECTED_PAYLOAD_FILES = 85
EXPECTED_ORIGINAL_ARCHIVES = 17
EXPECTED_MEMBER_OCCURRENCES = 558
EXPECTED_EXTRACTED_FILES = 52

ORIGINAL_ARCHIVES = {
    "adaptive_correction_block.zip",
    "central_arithmetic_attack.zip",
    "certificate_refinement_rule.zip",
    "certificate_route_test.zip",
    "certificate_structural_step.zip",
    "factorial_certificate_pilot.zip",
    "joint_correction_candidate.zip",
    "joint_support_analysis.zip",
    "prime_mobius_review_bundle.zip",
    "prime_pair_multiscale.zip",
    "prime_pair_q3_followup.zip",
    "prime_pair_sharp_transfer.zip",
    "prime_reverse_engineering_bundle.zip",
    "repair_cost_rule.zip",
    "zero_energy_feasibility.zip",
    "zeta_frontier_handoff_2026-09-06.zip",
    "zeta_research_checkpoint_2026-09-06.zip",
}

#: Nested archives already committed on main before this import.
ALREADY_ON_MAIN = {
    "zeta_frontier_handoff_2026-09-06.zip": os.path.join(
        FRONTIER, "archive", "zeta_frontier_handoff_2026-09-06.zip"),
    "factorial_certificate_pilot.zip": os.path.join(
        FRONTIER, "factorial_certificate_pilot", "archive", "factorial_certificate_pilot.zip"),
    "zeta_research_checkpoint_2026-09-06.zip": os.path.join(
        FRONTIER, "checkpoint", "archive", "zeta_research_checkpoint_2026-09-06.zip"),
}

#: The snapshot's top-level files, copied beside the archive as provenance.
PROVENANCE_FILES = {
    "FREEZE.md", "CLAUDE_HANDOFF.md", "README.md", "FILE_MANIFEST.json",
    "ARCHIVE_CONTENTS.json", "IMPORT_MAP.json", "REPO_STATE.json",
    "LOCAL_VALIDATION.json", "verify_freeze.py",
}

PACKAGES = ("joint_support_analysis", "repair_cost_rule", "adaptive_correction_block")
#: File counts each package must import, from the snapshot's own manifest checks.
PACKAGE_FILE_COUNTS = {
    "joint_support_analysis": 22,
    "repair_cost_rule": 12,
    "adaptive_correction_block": 18,
}
#: The only names a later review may add beside the imported members.
REVIEW_ADDITIONS = {"REVIEW.md", "BLOCK_REVIEW.md", "review"}

_HEX64 = re.compile(r"`([0-9a-f]{64})`")


def _sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _readme_hash() -> str:
    text = open(README, encoding="utf-8").read()
    section = text.split("## The archive", 1)[1].split("## Layout", 1)[0]
    found = set(_HEX64.findall(section))
    assert len(found) == 1, f"README archive section must state exactly one SHA-256, found {sorted(found)}"
    return found.pop()


def _extract(tmp_path):
    """A clean extraction of the committed archive, used by several checks."""
    with zipfile.ZipFile(ARCHIVE) as z:
        z.extractall(tmp_path)
    return tmp_path / TOP.rstrip("/")


def _load_verifier(root):
    """Import the snapshot's verifier from *outside* the tree it is about to inspect.

    Importing it in place writes ``__pycache__/verify_freeze.cpython-*.pyc`` into the
    extraction, and the verifier's inventory check then reports that generated file as an
    unlisted extra. That is not a hypothetical: the first version of this file did import
    in place, and it turned the PASS case red and made two of the negative controls below
    pass for the wrong reason, since a polluted tree raises the same inventory error a
    missing file does. So the source is copied to the parent directory first, which leaves
    the snapshot root byte-for-byte as extracted.
    """
    loaded = root.parent / "_loaded_verify_freeze.py"
    shutil.copyfile(root / "verify_freeze.py", loaded)
    spec = importlib.util.spec_from_file_location("verify_freeze", loaded)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# ---------------------------------------------------------------------------
# 1. The archive is on disk and is the file every record names
# ---------------------------------------------------------------------------


def test_archive_is_present_and_hash_pinned():
    assert os.path.isfile(ARCHIVE), (
        f"{os.path.relpath(ARCHIVE, REPO_ROOT)} is missing; a documented archive that is "
        "not on disk is the 2026-09-06 frontier incident again"
    )
    assert os.path.getsize(ARCHIVE) == EXPECTED_BYTES, "byte count differs from the download"
    assert _sha256_file(ARCHIVE) == EXPECTED_SHA256, "SHA-256 differs from the download"


def test_sidecar_and_readme_state_the_same_hash():
    lines = open(SUMS, encoding="utf-8").read().strip().splitlines()
    assert len(lines) == 1, "SHA256SUMS must name exactly the one archive"
    digest, name = lines[0].split()
    assert name.lstrip("*") == os.path.basename(ARCHIVE)
    assert digest == EXPECTED_SHA256, "sidecar hash drifted from the pinned hash"
    assert _readme_hash() == EXPECTED_SHA256, "README hash drifted from the pinned hash"
    assert f"{EXPECTED_BYTES:,}" in open(README, encoding="utf-8").read(), (
        "README must state the archive's byte count"
    )


def test_archive_has_no_unsafe_members():
    with zipfile.ZipFile(ARCHIVE) as z:
        names = [i.filename for i in z.infolist()]
        assert len(names) == len(set(names)), "duplicate ZIP members"
        for info in z.infolist():
            name = info.filename
            assert not name.startswith("/") and not name.startswith("\\"), name
            assert ".." not in name.split("/"), name
            assert name.startswith(TOP), f"member outside the top directory: {name}"
            mode = (info.external_attr >> 16) & 0xFFFF
            assert not (mode and (mode & 0o170000) == 0o120000), f"symlink member: {name}"
            assert not info.flag_bits & 1, f"encrypted member: {name}"


# ---------------------------------------------------------------------------
# 2. The manifest is non-empty and exact
# ---------------------------------------------------------------------------


def test_file_manifest_is_nonempty_and_every_listed_file_is_inside():
    with zipfile.ZipFile(ARCHIVE) as z:
        assert z.testzip() is None, "CRC failure inside the archive"
        files = {i.filename for i in z.infolist() if not i.is_dir()}
        manifest = json.loads(z.read(TOP + "FILE_MANIFEST.json"))
        assert manifest.get("snapshot_id") == SNAPSHOT_ID, "wrong snapshot identity"
        records = manifest.get("files")
        assert isinstance(records, list) and records, "manifest lists no files"
        assert len(records) == EXPECTED_PAYLOAD_FILES
        listed = set()
        for r in records:
            assert r["path"] not in listed, f"duplicate manifest entry {r['path']}"
            listed.add(r["path"])
            member = TOP + r["path"]
            assert member in files, f"manifest lists {r['path']} but the archive lacks it"
            data = z.read(member)
            assert data, f"{r['path']} is empty"
            assert len(data) == r["bytes"], f"{r['path']}: {len(data)} bytes != {r['bytes']}"
            assert _sha256(data) == r["sha256"], f"{r['path']}: hash mismatch"
        assert files == {TOP + p for p in listed} | {TOP + "FILE_MANIFEST.json"}, (
            "archive carries files the manifest does not list, or lacks some it does"
        )


# ---------------------------------------------------------------------------
# 3. Seventeen originals, every nested member, and the pinned overlaps
# ---------------------------------------------------------------------------


def test_inventory_names_seventeen_originals_and_every_nested_member_verifies():
    with zipfile.ZipFile(ARCHIVE) as z:
        recorded = json.loads(z.read(TOP + "ARCHIVE_CONTENTS.json"))
        assert isinstance(recorded, list) and recorded, "recursive inventory is empty"
        assert len(recorded) == EXPECTED_MEMBER_OCCURRENCES
        by_locator = {row["locator"]: row for row in recorded}
        assert len(by_locator) == len(recorded), "duplicate locators in the inventory"

        archives = sorted(
            n for n in z.namelist()
            if n.startswith(TOP + "original_archives/") and n.endswith(".zip")
        )
        assert len(archives) == EXPECTED_ORIGINAL_ARCHIVES
        assert {os.path.basename(a) for a in archives} == ORIGINAL_ARCHIVES

        seen = 0

        def walk(data: bytes, label: str) -> None:
            nonlocal seen
            with zipfile.ZipFile(io.BytesIO(data)) as inner:
                assert inner.testzip() is None, label
                names = [i.filename for i in inner.infolist() if not i.is_dir()]
                assert len(names) == len(set(names)), label
                for name in names:
                    raw = inner.read(name)
                    locator = f"{label}!/{name}"
                    row = by_locator.get(locator)
                    assert row is not None, f"inventory omits {locator}"
                    assert len(raw) == row["bytes"], locator
                    assert _sha256(raw) == row["sha256"], locator
                    seen += 1
                    if name.lower().endswith(".zip"):
                        walk(raw, locator)

        for name in archives:
            walk(z.read(name), name[len(TOP):])
        assert seen == EXPECTED_MEMBER_OCCURRENCES, (
            f"walked {seen} member occurrences, inventory records {EXPECTED_MEMBER_OCCURRENCES}"
        )


def test_the_nested_dependency_chain_is_byte_identical():
    """The adaptive block's input is the repair-cost ZIP, and so on down the chain."""
    with zipfile.ZipFile(ARCHIVE) as z:
        claims = json.loads(z.read(TOP + "LOCAL_VALIDATION.json"))["nested_dependency_byte_matches"]
        assert len(claims) == 4, "expected four nested dependency links"
        for link in claims:
            with zipfile.ZipFile(io.BytesIO(z.read(TOP + "original_archives/" + link["archive"]))) as inner:
                member = inner.read(link["member"])
            standalone = z.read(TOP + "original_archives/" + link["matches_original"])
            assert member == standalone, (
                f"{link['member']} differs from the standalone {link['matches_original']}"
            )
            assert _sha256(member) == link["sha256"], link["member"]


def test_nested_archives_already_on_main_are_the_same_bytes():
    with zipfile.ZipFile(ARCHIVE) as z:
        for name, committed in ALREADY_ON_MAIN.items():
            assert os.path.isfile(committed), committed
            assert z.read(TOP + "original_archives/" + name) == open(committed, "rb").read(), (
                f"{name}: the nested copy differs from the file committed on main"
            )


# ---------------------------------------------------------------------------
# 4. The archive's own verifier passes on a fresh extraction
# ---------------------------------------------------------------------------


def test_the_included_verifier_passes_on_a_fresh_extraction(tmp_path):
    root = _extract(tmp_path)
    result = _load_verifier(root).verify(root)
    assert result["status"] == "PASS"
    assert result["snapshot_id"] == SNAPSHOT_ID
    assert result["payload_files"] == EXPECTED_PAYLOAD_FILES
    assert result["original_archives"] == EXPECTED_ORIGINAL_ARCHIVES
    assert result["recursive_archive_member_occurrences"] == EXPECTED_MEMBER_OCCURRENCES
    assert result["latest_extracted_files"] == EXPECTED_EXTRACTED_FILES


# ---------------------------------------------------------------------------
# 5. The imported working copies are exactly the archive's extractions
# ---------------------------------------------------------------------------


def test_imported_working_copies_equal_the_archive_members_exactly():
    with zipfile.ZipFile(ARCHIVE) as z:
        mapping = json.loads(z.read(TOP + "IMPORT_MAP.json"))
        assert len(mapping) == 3
        assert {os.path.basename(m["proposed_repo_path"]) for m in mapping} == set(PACKAGES)
        total = 0
        for item in mapping:
            pkg = os.path.basename(item["proposed_repo_path"])
            workdir = os.path.join(REPO_ROOT, item["proposed_repo_path"])
            assert os.path.isdir(workdir), f"{pkg} was not imported"

            prefix = TOP + item["extracted_path"] + "/"
            listed = {n[len(prefix):] for n in z.namelist()
                      if n.startswith(prefix) and not n.endswith("/")}
            assert listed, f"{pkg}: the archive carries no extraction"

            present = set()
            for dirpath, dirnames, filenames in os.walk(workdir):
                dirnames[:] = [d for d in dirnames if d != "__pycache__"]
                for fn in filenames:
                    full = os.path.join(dirpath, fn)
                    assert not os.path.islink(full), f"{pkg}: symlink in the import: {full}"
                    present.add(os.path.relpath(full, workdir).replace(os.sep, "/"))

            top_level = {p.split("/")[0] for p in present}
            extra = {p for p in present if p.split("/")[0] not in REVIEW_ADDITIONS} - listed
            missing = listed - present
            assert not extra, f"{pkg}: files beside the imported members: {sorted(extra)}"
            assert not missing, f"{pkg}: imported members missing: {sorted(missing)}"
            assert len(listed) == PACKAGE_FILE_COUNTS[pkg], (
                f"{pkg}: archive extraction has {len(listed)} files, expected "
                f"{PACKAGE_FILE_COUNTS[pkg]}"
            )
            assert not (top_level - {p.split("/")[0] for p in listed} - REVIEW_ADDITIONS)

            with zipfile.ZipFile(io.BytesIO(z.read(TOP + item["archive"]))) as original:
                for name in sorted(listed):
                    member = z.read(prefix + name)
                    copy = open(os.path.join(workdir, name), "rb").read()
                    assert copy, f"{pkg}/{name}: imported file is empty"
                    assert copy == member, f"{pkg}/{name}: working copy differs from the archive member"
                    assert member == original.read(item["member_prefix"] + name), (
                        f"{pkg}/{name}: archive extraction differs from the original nested ZIP"
                    )
                    total += 1
        assert total == EXPECTED_EXTRACTED_FILES


def _package_sums(pkg: str) -> dict:
    """The package's own manifest as ``{name: entry}``.

    The three packages were sealed by different runs and key the size differently:
    ``repair_cost_rule`` writes ``size`` where the other two write ``bytes``. Both are
    read; neither manifest is rewritten to agree with the other.
    """
    path = os.path.join(FRONTIER, pkg, "SHA256SUMS.json")
    return json.loads(open(path, encoding="utf-8").read())


def test_each_package_sha256sums_json_describes_its_own_files():
    for pkg in PACKAGES:
        workdir = os.path.join(FRONTIER, pkg)
        sums = _package_sums(pkg)
        assert sums, f"{pkg}: SHA256SUMS.json is empty"
        on_disk = set()
        for dirpath, dirnames, filenames in os.walk(workdir):
            dirnames[:] = [d for d in dirnames if d != "__pycache__"]
            for fn in filenames:
                on_disk.add(os.path.relpath(os.path.join(dirpath, fn), workdir).replace(os.sep, "/"))
        expected = on_disk - {"SHA256SUMS.json"} - REVIEW_ADDITIONS
        expected = {p for p in expected if p.split("/")[0] not in REVIEW_ADDITIONS}
        assert set(sums) == expected, (
            f"{pkg}: manifest and directory disagree: {sorted(set(sums) ^ expected)}"
        )
        for name, entry in sums.items():
            data = open(os.path.join(workdir, name), "rb").read()
            size = entry.get("bytes", entry.get("size"))
            assert size is not None, f"{pkg}/{name}: manifest entry records no size"
            assert len(data) == size, f"{pkg}/{name}: size mismatch"
            assert _sha256(data) == entry["sha256"], f"{pkg}/{name}: hash mismatch"


def test_no_imported_file_claims_the_reserved_word():
    """No vocabulary edit was needed, so the copies must be byte-identical originals."""
    for pkg in PACKAGES:
        for dirpath, dirnames, filenames in os.walk(os.path.join(FRONTIER, pkg)):
            dirnames[:] = [d for d in dirnames if d != "__pycache__"]
            for fn in filenames:
                if os.path.splitext(fn)[1].lower() not in {".py", ".md", ".json", ".txt", ".log"}:
                    continue
                data = open(os.path.join(dirpath, fn), "rb").read().lower()
                assert b"certified" not in data, f"{pkg}/{fn}: reserved word"


# ---------------------------------------------------------------------------
# 6. The provenance copies are the archive's own files
# ---------------------------------------------------------------------------


def test_provenance_copies_are_byte_identical_to_the_archive_members():
    assert os.path.isdir(PROVENANCE), "provenance/ is missing"
    present = set(os.listdir(PROVENANCE)) - {"__pycache__"}
    assert present == PROVENANCE_FILES, (
        f"provenance/ differs from the snapshot's top-level files: "
        f"{sorted(present ^ PROVENANCE_FILES)}"
    )
    with zipfile.ZipFile(ARCHIVE) as z:
        for name in sorted(PROVENANCE_FILES):
            copy = open(os.path.join(PROVENANCE, name), "rb").read()
            assert copy, f"provenance/{name} is empty"
            assert copy == z.read(TOP + name), (
                f"provenance/{name} differs from the archive member it was copied from"
            )


def test_the_record_states_the_import_and_keeps_the_review_status():
    readme = open(README, encoding="utf-8").read()
    frontier_readme = open(os.path.join(FRONTIER, "README.md"), encoding="utf-8").read()
    assert "adaptive_freeze_v1/archive/zeta_adaptive_freeze_v1.zip" in frontier_readme, (
        "the frontier README must record where the archive now lives"
    )
    assert EXPECTED_SHA256 in frontier_readme, "the frontier README must pin the hash"
    for text, label in ((readme, "adaptive_freeze_v1/README.md"), (frontier_readme, "frontier README")):
        lowered = text.lower()
        assert "unreviewed" in lowered or "not independently reviewed" in lowered, (
            f"{label} must record that the three latest stages are unreviewed"
        )
    for pr in ("#196", "#199", "#200"):
        assert pr in readme, f"the README must preserve the reference to PR {pr}"
    assert "9ec3b6b3b86c25e256ce605f5116fbda3cbc7689" in readme, (
        "the README must preserve the merge commit of the preceding checkpoint"
    )


# ---------------------------------------------------------------------------
# 7. Negative controls: the checks above must actually be able to fail
# ---------------------------------------------------------------------------


def _verify_raises(root, match: str):
    module = _load_verifier(root)
    with pytest.raises(ValueError, match=match):
        module.verify(root)


def test_verifier_rejects_a_missing_file(tmp_path):
    root = _extract(tmp_path)
    os.remove(root / "FREEZE.md")
    _verify_raises(root, "inventory mismatch")


def test_verifier_rejects_an_emptied_file(tmp_path):
    root = _extract(tmp_path)
    (root / "FREEZE.md").write_bytes(b"")
    _verify_raises(root, "Size/hash mismatch")


def test_verifier_rejects_an_altered_file(tmp_path):
    root = _extract(tmp_path)
    path = root / "FREEZE.md"
    data = bytearray(path.read_bytes())
    data[0] ^= 0x20  # same length, different bytes
    path.write_bytes(bytes(data))
    _verify_raises(root, "Size/hash mismatch")


def test_verifier_rejects_an_extra_file(tmp_path):
    root = _extract(tmp_path)
    (root / "UNLISTED.md").write_text("not in the manifest\n", encoding="utf-8")
    _verify_raises(root, "inventory mismatch")


def test_verifier_rejects_a_symlink(tmp_path):
    root = _extract(tmp_path)
    os.symlink(root / "FREEZE.md", root / "LINKED.md")
    _verify_raises(root, "Symlink in snapshot")


def test_verifier_rejects_a_truncated_original_archive(tmp_path):
    root = _extract(tmp_path)
    path = root / "original_archives" / "adaptive_correction_block.zip"
    path.write_bytes(path.read_bytes()[: 1 << 12])
    _verify_raises(root, "Size/hash mismatch")


def test_verifier_rejects_an_altered_extraction(tmp_path):
    """The imported-package check is what makes a silent edit to a working copy visible."""
    root = _extract(tmp_path)
    target = root / "latest_extracted" / "adaptive_correction_block" / "BLOCK_CORRECTIONS.md"
    data = bytearray(target.read_bytes())
    data[0] ^= 0x20
    target.write_bytes(bytes(data))
    _verify_raises(root, "Size/hash mismatch")


def test_verifier_rejects_an_empty_manifest(tmp_path):
    root = _extract(tmp_path)
    manifest = json.loads((root / "FILE_MANIFEST.json").read_text(encoding="utf-8"))
    manifest["files"] = []
    (root / "FILE_MANIFEST.json").write_text(json.dumps(manifest), encoding="utf-8")
    _verify_raises(root, "Empty or invalid file manifest")


def test_verifier_rejects_a_wrong_snapshot_identity(tmp_path):
    root = _extract(tmp_path)
    manifest = json.loads((root / "FILE_MANIFEST.json").read_text(encoding="utf-8"))
    manifest["snapshot_id"] = "something-else"
    (root / "FILE_MANIFEST.json").write_text(json.dumps(manifest), encoding="utf-8")
    _verify_raises(root, "Wrong snapshot identity")


def test_the_import_check_catches_a_mutated_working_copy(tmp_path):
    """The repository-side control for check 5, run on a copy so the tree is untouched."""
    workdir = tmp_path / "adaptive_correction_block"
    shutil.copytree(os.path.join(FRONTIER, "adaptive_correction_block"), workdir)
    target = workdir / "BLOCK_CORRECTIONS.md"
    data = bytearray(target.read_bytes())
    data[0] ^= 0x20
    target.write_bytes(bytes(data))
    with zipfile.ZipFile(ARCHIVE) as z:
        member = z.read(TOP + "latest_extracted/adaptive_correction_block/BLOCK_CORRECTIONS.md")
    assert target.read_bytes() != member, "the mutation must be visible to the byte comparison"
    assert open(os.path.join(FRONTIER, "adaptive_correction_block", "BLOCK_CORRECTIONS.md"), "rb").read() == member, (
        "the real working copy must still match the archive member"
    )
