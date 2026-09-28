"""The cumulative research checkpoint archive is present, hash-pinned, and its imports are honest.

Imported on 2026-09-06 under
``hunts/prime_pair_error/frontier/2026-09-06/checkpoint/archive/`` from the downloaded
cumulative checkpoint ``zeta_research_checkpoint_2026-09-06.zip``. The checkpoint bundles
twelve original research ZIPs, the loose companion files, a byte-identical extraction of
the three newest packages (structural step, refinement rule, route test), a manifest and
inventory, the narrative ``CHECKPOINT.md``, and its own verifier ``verify_snapshot.py``.
Nothing in it is a prime-counting record or an RH result.

Same discipline as ``tests/test_frontier_archive.py`` and ``tests/test_factorial_pilot_archive.py``,
for the same reason: the first preservation pass on this date documented an archive that
never landed, and nothing mechanical noticed. So this file does not trust the README. It
pins five things, and every one of them fails rather than skips.

1. The ZIP is present, non-empty, and has the SHA-256 the download was delivered with
   (hard-coded here, cross-checked against the ``archive/SHA256SUMS`` sidecar and the hash
   the checkpoint README states, so the three cannot drift apart silently).
2. The archive's own ``CHECKPOINT_MANIFEST.json`` is non-empty and every file it lists is
   inside with the recorded hash and byte count, and nothing else is.
3. ``ARCHIVE_INVENTORY.json`` names exactly the twelve original archives, each nested ZIP
   is inside with its recorded hash, and every member of every nested ZIP verifies. The
   two nested archives that were already committed on main are the same bytes as the
   committed files. The three newest packages have the hashes ``CHECKPOINT.md`` states.
4. The checkpoint's included verifier, run on a fresh extraction, reports PASS with the
   file, archive and member counts the checkpoint README states.
5. The three working directories imported beside the checkpoint contain exactly the
   archive's ``latest_extracted`` members, byte for byte, and those members are the same
   bytes as the members of the corresponding nested original ZIP. No vocabulary
   substitution was needed: none of the twenty-three files carries the reserved word, so
   there is no documented edit and the copies must be identical. A review may add
   ``BASELINE_REVIEW.md`` and a ``review/`` subdirectory beside the members (the layout
   ``factorial_certificate_pilot/`` established); anything else is a drift.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import zipfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FRONTIER = os.path.join(REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06")
CHECKPOINT = os.path.join(FRONTIER, "checkpoint")
ARCHIVE = os.path.join(CHECKPOINT, "archive", "zeta_research_checkpoint_2026-09-06.zip")
SUMS = os.path.join(CHECKPOINT, "archive", "SHA256SUMS")
README = os.path.join(CHECKPOINT, "README.md")
TOP = "zeta_research_checkpoint_2026-09-06/"

EXPECTED_SHA256 = "161575e3f8c88c263064099983cf586b89ad8abba2037c20766ce4eeaca257f9"
EXPECTED_BYTES = 1_524_467

# What the checkpoint README states the verifier reports.
EXPECTED_FILES = 56
EXPECTED_ORIGINAL_ARCHIVES = 12
EXPECTED_DIRECT_MEMBERS = 108

ORIGINAL_ARCHIVES = {
    "prime_reverse_engineering_bundle.zip",
    "prime_mobius_review_bundle.zip",
    "prime_pair_q3_followup.zip",
    "zero_energy_feasibility.zip",
    "prime_pair_sharp_transfer.zip",
    "prime_pair_multiscale.zip",
    "central_arithmetic_attack.zip",
    "zeta_frontier_handoff_2026-09-06.zip",
    "factorial_certificate_pilot.zip",
    "certificate_structural_step.zip",
    "certificate_refinement_rule.zip",
    "certificate_route_test.zip",
}

# CHECKPOINT.md section 2, the three newest original packages.
LATEST_ORIGINALS = {
    "certificate_structural_step.zip": (
        21_040, "4c230a967b3932dba18c6ee176611804a180bbae606e64cf73879f67dadc7d90"),
    "certificate_refinement_rule.zip": (
        26_100, "962dbe79c58b4ceb59300d9c0d2687e63693e3b58fe5b320fa0420f13ae42f9c"),
    "certificate_route_test.zip": (
        41_790, "992ca6730314390f0754db1fc7e96d361aa8e16691c5c6e83765e95dc32dec5a"),
}

# Nested archives that were already committed on main before this import.
ALREADY_ON_MAIN = {
    "zeta_frontier_handoff_2026-09-06.zip": os.path.join(
        FRONTIER, "archive", "zeta_frontier_handoff_2026-09-06.zip"),
    "factorial_certificate_pilot.zip": os.path.join(
        FRONTIER, "factorial_certificate_pilot", "archive", "factorial_certificate_pilot.zip"),
}

PACKAGES = ("certificate_structural_step", "certificate_refinement_rule", "certificate_route_test")
PACKAGE_MEMBERS = {
    "certificate_structural_step": {
        "STRUCTURAL_STEP.md", "SHA256SUMS.json", "check_and_compare.py", "checked_results.json",
        "probe.py", "requirements.txt", "results.json",
    },
    "certificate_refinement_rule": {
        "REFINEMENT.md", "SHA256SUMS.json", "exploration.json", "inputs.json", "refine.py",
        "requirements.txt", "results.json",
    },
    "certificate_route_test": {
        "ORIGINAL_REFINEMENT.md", "ROUTE_ASSESSMENT.md", "SHA256SUMS.json", "aggregate_repair.py",
        "aggregate_results.json", "inputs.json", "original_results.json", "refine.py",
        "requirements.txt",
    },
}
#: The only names a review may add beside the imported members.
REVIEW_ADDITIONS = {"BASELINE_REVIEW.md", "review"}

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
    section = text.split("## Complete original bytes", 1)[1].split("## Existing work preserved", 1)[0]
    found = set(_HEX64.findall(section))
    assert len(found) == 1, f"README storage section must state exactly one SHA-256, found {sorted(found)}"
    return found.pop()


# ---------------------------------------------------------------------------
# 1. The archive is on disk and is the file every record names
# ---------------------------------------------------------------------------


def test_archive_is_present_and_hash_pinned():
    assert os.path.isfile(ARCHIVE), (
        f"{os.path.relpath(ARCHIVE, REPO_ROOT)} is missing; a documented archive that is not "
        "on disk is the 2026-09-06 frontier incident again"
    )
    assert os.path.getsize(ARCHIVE) == EXPECTED_BYTES
    assert _sha256_file(ARCHIVE) == EXPECTED_SHA256


def test_sidecar_and_readme_state_the_same_hash():
    lines = open(SUMS, encoding="utf-8").read().strip().splitlines()
    assert len(lines) == 1, "SHA256SUMS must name exactly the one archive"
    digest, name = lines[0].split()
    assert name.lstrip("*") == os.path.basename(ARCHIVE)
    assert digest == EXPECTED_SHA256
    assert _readme_hash() == EXPECTED_SHA256


# ---------------------------------------------------------------------------
# 2. The manifest is non-empty and exact
# ---------------------------------------------------------------------------


def test_checkpoint_manifest_is_nonempty_and_every_listed_file_is_inside():
    with zipfile.ZipFile(ARCHIVE) as z:
        assert z.testzip() is None, "CRC failure inside the archive"
        files = {i.filename for i in z.infolist() if not i.is_dir()}
        assert all(n.startswith(TOP) for n in files), "member outside the top directory"
        manifest = json.loads(z.read(TOP + "CHECKPOINT_MANIFEST.json"))
        records = manifest.get("files")
        assert isinstance(records, list) and records, "manifest lists no files"
        assert len(records) == EXPECTED_FILES
        listed = set()
        for r in records:
            member = TOP + r["path"]
            assert r["path"] not in listed, f"duplicate manifest entry {r['path']}"
            listed.add(r["path"])
            assert member in files, f"manifest lists {r['path']} but the archive lacks it"
            data = z.read(member)
            assert len(data) == r["bytes"], f"{r['path']}: {len(data)} bytes != {r['bytes']}"
            assert _sha256(data) == r["sha256"], f"{r['path']}: hash mismatch"
        assert files == {TOP + p for p in listed} | {TOP + "CHECKPOINT_MANIFEST.json"}, (
            "archive carries files the manifest does not list, or lacks some it does"
        )


# ---------------------------------------------------------------------------
# 3. The twelve original archives, each nested member, and the pinned originals
# ---------------------------------------------------------------------------


def test_inventory_names_twelve_originals_and_every_nested_member_verifies():
    with zipfile.ZipFile(ARCHIVE) as z:
        inventory = json.loads(z.read(TOP + "ARCHIVE_INVENTORY.json"))
        archives = inventory.get("archives")
        assert isinstance(archives, list) and archives, "inventory lists no archives"
        assert len(archives) == EXPECTED_ORIGINAL_ARCHIVES
        assert {os.path.basename(a["path"]) for a in archives} == ORIGINAL_ARCHIVES
        total = 0
        for a in archives:
            data = z.read(TOP + a["path"])
            assert data, f"{a['path']} is empty"
            assert len(data) == a["bytes"], a["path"]
            assert _sha256(data) == a["sha256"], a["path"]
            required = a.get("members")
            assert required, f"{a['path']}: inventory lists no members"
            with zipfile.ZipFile(zipfile.io.BytesIO(data)) as inner:
                assert inner.testzip() is None, a["path"]
                names = [i.filename for i in inner.infolist() if not i.is_dir()]
                assert len(names) == len(set(names)), a["path"]
                assert set(names) == {m["path"] for m in required}, a["path"]
                for m in required:
                    b = inner.read(m["path"])
                    assert len(b) == m["bytes"], f"{a['path']}:{m['path']}"
                    assert _sha256(b) == m["sha256"], f"{a['path']}:{m['path']}"
                    total += 1
        assert total == inventory["member_count"] == EXPECTED_DIRECT_MEMBERS


def test_the_three_newest_originals_have_the_hashes_checkpoint_md_states():
    with zipfile.ZipFile(ARCHIVE) as z:
        for name, (nbytes, digest) in LATEST_ORIGINALS.items():
            data = z.read(TOP + "original_archives/" + name)
            assert len(data) == nbytes, name
            assert _sha256(data) == digest, name


def test_nested_archives_already_on_main_are_the_same_bytes():
    with zipfile.ZipFile(ARCHIVE) as z:
        for name, committed in ALREADY_ON_MAIN.items():
            assert os.path.isfile(committed), committed
            assert z.read(TOP + "original_archives/" + name) == open(committed, "rb").read(), (
                f"{name}: the nested copy differs from the file committed on main"
            )


# ---------------------------------------------------------------------------
# 4. The checkpoint's own verifier passes on a fresh extraction
# ---------------------------------------------------------------------------


def test_the_included_verifier_passes_on_a_fresh_extraction(tmp_path):
    with zipfile.ZipFile(ARCHIVE) as z:
        for info in z.infolist():
            assert not info.filename.startswith("/") and ".." not in info.filename.split("/")
        z.extractall(tmp_path)
    root = tmp_path / TOP.rstrip("/")
    spec = importlib.util.spec_from_file_location("verify_snapshot", root / "verify_snapshot.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    result = module.verify(root)
    assert result["status"] == "PASS"
    assert result["files"] == EXPECTED_FILES
    assert result["original_archives"] == EXPECTED_ORIGINAL_ARCHIVES
    assert result["direct_archive_members"] == EXPECTED_DIRECT_MEMBERS


# ---------------------------------------------------------------------------
# 5. The imported working directories are exactly the archive's extractions
# ---------------------------------------------------------------------------


def test_imported_working_copies_equal_the_archive_members_exactly():
    with zipfile.ZipFile(ARCHIVE) as z:
        for pkg in PACKAGES:
            workdir = os.path.join(FRONTIER, pkg)
            assert os.path.isdir(workdir), f"{pkg} was not imported"
            present = set(os.listdir(workdir)) - {"__pycache__"}
            extra = present - PACKAGE_MEMBERS[pkg] - REVIEW_ADDITIONS
            missing = PACKAGE_MEMBERS[pkg] - present
            assert not extra, f"{pkg}: files beside the imported members: {sorted(extra)}"
            assert not missing, f"{pkg}: imported members missing: {sorted(missing)}"
            prefix = TOP + "latest_extracted/" + pkg + "/"
            listed = {n[len(prefix):] for n in z.namelist() if n.startswith(prefix) and not n.endswith("/")}
            assert listed == PACKAGE_MEMBERS[pkg], f"{pkg}: archive extraction has a different member set"
            original = zipfile.ZipFile(zipfile.io.BytesIO(z.read(TOP + "original_archives/" + pkg + ".zip")))
            with original:
                for name in PACKAGE_MEMBERS[pkg]:
                    member = z.read(prefix + name)
                    copy = open(os.path.join(workdir, name), "rb").read()
                    assert copy == member, f"{pkg}/{name}: working copy differs from the archive member"
                    assert member == original.read(pkg + "/" + name), (
                        f"{pkg}/{name}: archive extraction differs from the original nested ZIP"
                    )
                    assert b"certified" not in copy.lower(), f"{pkg}/{name}: reserved word"


def _package_sums(pkg: str) -> dict:
    """The package's own manifest as {name: {bytes, sha256}}.

    The three packages were sealed by different runs and use two shapes: a dict keyed
    by file name (route test) and a ``{"files": [{"path", "bytes", "sha256"}, ...]}``
    list (structural step, refinement rule). Both are read; neither is rewritten.
    """
    raw = json.loads(open(os.path.join(FRONTIER, pkg, "SHA256SUMS.json"), encoding="utf-8").read())
    if isinstance(raw, dict) and isinstance(raw.get("files"), list):
        return {e["path"]: e for e in raw["files"]}
    return raw


def test_each_package_sha256sums_json_describes_its_own_files():
    for pkg in PACKAGES:
        workdir = os.path.join(FRONTIER, pkg)
        sums = _package_sums(pkg)
        assert sums, f"{pkg}: SHA256SUMS.json is empty"
        assert set(sums) == PACKAGE_MEMBERS[pkg] - {"SHA256SUMS.json"}, pkg
        for name, entry in sums.items():
            data = open(os.path.join(workdir, name), "rb").read()
            assert len(data) == entry["bytes"], f"{pkg}/{name}"
            assert _sha256(data) == entry["sha256"], f"{pkg}/{name}"


def test_source_notes_are_the_package_notes():
    pairs = {
        "STRUCTURAL_STEP.md": "certificate_structural_step",
        "REFINEMENT.md": "certificate_refinement_rule",
        "ROUTE_ASSESSMENT.md": "certificate_route_test",
    }
    for note, pkg in pairs.items():
        saved = open(os.path.join(CHECKPOINT, "source_notes", note), "rb").read()
        working = open(os.path.join(FRONTIER, pkg, note), "rb").read()
        assert saved == working, f"{note}: source note and imported package copy differ"


def test_the_record_keeps_the_failed_upload_and_states_the_import():
    readme = open(README, encoding="utf-8").read()
    checkpoint = open(os.path.join(CHECKPOINT, "CHECKPOINT.md"), encoding="utf-8").read()
    assert "failed base64 upload was real" in checkpoint, "the historical failure must stay documented"
    assert "## Repository import" in readme, "README must record where the archive now lives"
    assert "checkpoint/archive/zeta_research_checkpoint_2026-09-06.zip" in readme
    assert "## 8. Repository import" in checkpoint, "CHECKPOINT.md must carry the dated import addendum"
