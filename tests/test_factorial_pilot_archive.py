"""The factorial-certificate pilot archive is present, hash-pinned, and its copies are honest.

Preserved on 2026-09-06 under
``hunts/prime_pair_error/frontier/2026-09-06/factorial_certificate_pilot/`` from a downloaded
attachment (``factorial_certificate_pilot.zip``). The pilot is a Chebyshev-type factorial
upper certificate for psi(N); ``REVIEW.md`` there is the independent review. Nothing about
it is a prime-counting record or an RH result.

Same discipline as ``tests/test_frontier_archive.py`` and for the same reason: a documented
archive that is not on disk, or whose bytes drifted, must turn the suite red rather than be
discovered by the next reader. Three things are pinned.

1. The ZIP is present, non-empty, and has the SHA-256 the attachment was delivered with
   (hard-coded here, and cross-checked against the ``archive/SHA256SUMS`` sidecar so the two
   cannot drift apart silently).
2. Every member the archive's own ``SHA256SUMS.json`` lists is inside it with the recorded
   hash and byte count.
3. The extracted working copies next to ``archive/`` equal the archive's members byte for
   byte, with exactly one documented exception: ``pilot.py`` and ``results.json`` carry the
   reserved word (``AGENTS.md``: banned everywhere under ``hunts/``, disclaimers included), so
   the extracted copies have that one token replaced by ``established``, two occurrences in
   the script and one in the record. The test reconstructs the copy from the member by that
   substitution and demands equality, so the edit is the only difference there can be. The
   originals are the archive members and are not edited.

Also pinned, because it is cheap and it is what the review's "reproduces" verdict rests on:
every one of the 87 recorded seeds re-verifies with independent Fraction arithmetic, and
the three selected leading constants are the ones ``PILOT.md`` states.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import zipfile
from fractions import Fraction

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PILOT = os.path.join(
    REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06", "factorial_certificate_pilot"
)
ARCHIVE = os.path.join(PILOT, "archive", "factorial_certificate_pilot.zip")
SUMS = os.path.join(PILOT, "archive", "SHA256SUMS")
TOP = "factorial_certificate_pilot/"
EXPECTED_SHA256 = "215f0ab2de4957e5d98d42106f2a525286b9fa9e89fa5f4db167ceb82ed7ad0c"
EXPECTED_BYTES = 10876

# member -> number of reserved-word tokens the extracted copy has replaced
SUBSTITUTED = {"pilot.py": 2, "results.json": 1}
VERBATIM = ("PILOT.md", "requirements.txt", "SHA256SUMS.json")

# PILOT.md section 4, the three selected seeds
STATED_BEST = {(30, 6): 1.105550427521, (210, 6): 1.073965360073, (2310, 15): 1.069854452573}


def _sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def test_archive_is_present_and_hash_pinned():
    assert os.path.isfile(ARCHIVE), (
        f"{os.path.relpath(ARCHIVE, REPO_ROOT)} is missing; a documented archive that is not "
        "on disk is the 2026-09-06 frontier incident again"
    )
    assert os.path.getsize(ARCHIVE) == EXPECTED_BYTES
    assert _sha256(ARCHIVE) == EXPECTED_SHA256


def test_sha256sums_sidecar_matches_archive():
    lines = open(SUMS, encoding="utf-8").read().strip().splitlines()
    assert len(lines) == 1, "SHA256SUMS must name exactly the one archive"
    digest, name = lines[0].split()
    assert name.lstrip("*") == os.path.basename(ARCHIVE)
    assert digest == EXPECTED_SHA256


def test_every_manifest_member_is_inside_with_recorded_hash_and_size():
    with zipfile.ZipFile(ARCHIVE) as z:
        names = set(z.namelist())
        sums = json.loads(z.read(TOP + "SHA256SUMS.json"))
        assert set(sums) == {"PILOT.md", "pilot.py", "requirements.txt", "results.json"}
        for path, entry in sums.items():
            member = TOP + path
            assert member in names, f"manifest lists {path} but the archive lacks it"
            data = z.read(member)
            assert len(data) == entry["bytes"], f"{path}: {len(data)} bytes != {entry['bytes']}"
            assert hashlib.sha256(data).hexdigest() == entry["sha256"], f"{path}: hash mismatch"
        assert names == {TOP + p for p in list(sums) + ["SHA256SUMS.json"]}, "unexpected members"


def test_extracted_copies_equal_members_modulo_the_documented_edit():
    with zipfile.ZipFile(ARCHIVE) as z:
        for name in VERBATIM:
            assert z.read(TOP + name) == open(os.path.join(PILOT, name), "rb").read(), name
        for name, count in SUBSTITUTED.items():
            member = z.read(TOP + name)
            assert member.count(b"certified") == count, f"{name}: archive member changed shape"
            expected = member.replace(b"certified", b"established")
            copy = open(os.path.join(PILOT, name), "rb").read()
            assert copy == expected, (
                f"{name}: extracted copy differs from the archive member by more than the "
                "one documented token substitution"
            )
            assert b"certified" not in copy


@pytest.fixture(scope="module")
def record():
    return json.loads(open(os.path.join(PILOT, "results.json"), encoding="utf-8").read())


def test_all_87_recorded_seeds_reverify_exactly(record):
    cases = record["cases"]
    assert len(cases) == 87
    assert [(c["period"], c["radix"]) for c in cases] == [
        (L, M) for L in (30, 210, 2310) for M in range(2, 31)
    ]
    for c in cases:
        L, M = c["period"], c["radix"]
        seed = {int(j): Fraction(a) for j, a in c["coefficients"].items()}
        assert all(L % j == 0 for j in seed), (L, M)
        assert sum((a / j for j, a in seed.items()), Fraction(0)) == 0, (L, M)
        for r in range(L):
            g = sum((a * (r // j) for j, a in seed.items()), Fraction(0))
            assert g >= (1 if 1 <= r < M else 0), (L, M, r, g)
        C = -sum(float(a) * math.log(j) / j for j, a in seed.items()) / (1 - 1 / M)
        assert abs(C - c["leading_constant_float"]) < 1e-9, (L, M)
        assert C > 1, (L, M)


def test_the_three_selected_constants_are_the_ones_pilot_md_states(record):
    best = {(b["period"], b["radix"]): b["leading_constant_float"] for b in record["best_in_numerical_search"]}
    assert best.keys() == STATED_BEST.keys()
    for key, stated in STATED_BEST.items():
        assert abs(best[key] - stated) < 1e-9, key


def test_review_labels_the_material_as_a_pilot():
    text = open(os.path.join(PILOT, "REVIEW.md"), encoding="utf-8").read().lower()
    assert "pilot" in text
    assert "not a new prime-counting record" in text
    assert "nothing here bears on rh" in text
