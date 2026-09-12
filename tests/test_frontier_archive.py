"""The prime-pair frontier handoff archive is present and is the file its README names.

This file exists because of a real incident. On 2026-09-06 a preservation pass wrote
``hunts/prime_pair_error/frontier/2026-09-06/README.md`` describing an ``archive/``
directory of base64 chunks, a reconstruction command, and an expected SHA-256. The
directory was never created: the chunked upload through the GitHub text API did not
land, on ``main`` or on any branch, and nothing in the suite noticed. The documented
command produced a zero-byte file. Per ``PROVENANCE.md`` that archive was the only copy
of three precursor bundles, so the one artifact the pass existed to protect was the one
it did not.

The lesson is already written down in ``AGENTS.md`` about ``scripts/check_secrets.py``:
a guard that fails open is worse than none, because it also supplies confidence. So this
test does not trust the README. It reads the expected hash out of the README, hashes the
committed binary, and then opens the archive and checks every member its own
``SHA256SUMS.json`` lists, by hash and by size. If someone edits the README hash, moves
the file, or re-zips the contents, the suite goes red.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import zipfile

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FRONTIER = os.path.join(REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06")
README = os.path.join(FRONTIER, "README.md")
ARCHIVE = os.path.join(FRONTIER, "archive", "zeta_frontier_handoff_2026-09-06.zip")
SUMS = os.path.join(FRONTIER, "archive", "SHA256SUMS")
TOP = "zeta_frontier_handoff_2026-09-06/"

_HEX64 = re.compile(r"`([0-9a-f]{64})`")


def _readme_hash() -> str:
    text = open(README, encoding="utf-8").read()
    section = text.split("## Exact handoff archive", 1)[1].split("## Next phase", 1)[0]
    found = _HEX64.findall(section)
    assert len(found) == 1, f"README archive section must state exactly one SHA-256, found {found}"
    return found[0]


def _sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def test_archive_is_present_and_matches_readme_hash():
    assert os.path.isfile(ARCHIVE), (
        f"{os.path.relpath(ARCHIVE, REPO_ROOT)} is missing. The README documents an archive; "
        "a documented archive that is not on disk is the 2026-09-06 incident again."
    )
    assert os.path.getsize(ARCHIVE) > 0, "archive is zero bytes"
    assert _sha256(ARCHIVE) == _readme_hash()


def test_sha256sums_sidecar_matches_archive():
    line = open(SUMS, encoding="utf-8").read().strip().splitlines()
    assert len(line) == 1, "SHA256SUMS must name exactly the one archive"
    digest, name = line[0].split()
    assert name.lstrip("*") == os.path.basename(ARCHIVE)
    assert digest == _sha256(ARCHIVE)


def test_every_manifest_member_is_inside_with_recorded_hash_and_size():
    with zipfile.ZipFile(ARCHIVE) as z:
        names = set(z.namelist())
        assert TOP + "MANIFEST.md" in names
        sums = json.loads(z.read(TOP + "SHA256SUMS.json"))
        assert sums["files"], "inner SHA256SUMS.json lists no files"
        for entry in sums["files"]:
            member = TOP + entry["path"]
            assert member in names, f"manifest lists {entry['path']} but the archive lacks it"
            data = z.read(member)
            assert len(data) == entry["bytes"], f"{entry['path']}: size {len(data)} != {entry['bytes']}"
            assert hashlib.sha256(data).hexdigest() == entry["sha256"], f"{entry['path']}: hash mismatch"


def test_readme_no_longer_points_at_the_dead_reconstruction_route():
    text = open(README, encoding="utf-8").read()
    assert "part-*.b64" not in text.split("**Correction, 2026-09-06.**")[0], (
        "the README's live instructions must not tell a reader to concatenate b64 chunks "
        "that do not exist; the dead route may appear only inside the correction note"
    )
