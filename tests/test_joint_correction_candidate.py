"""The joint signed-correction candidate is preserved unchanged, and its review's numbers hold.

``hunts/prime_pair_error/frontier/2026-09-06/joint_correction_candidate/`` preserves a
downloaded attachment (``joint_correction_candidate.zip``): the first coordinated
signed-correction candidate against the reviewed combined-weight baseline in
``../certificate_route_test/``. ``JOINT_REVIEW.md`` is the independent review; its checker,
``review/joint_check.py``, shares no code with the candidate or the baseline package.

Same discipline as ``tests/test_factorial_pilot_archive.py``: a documented archive that is
not on disk, or whose bytes drifted, turns the suite red. Three things.

1. The ZIP is present, non-empty, and has the SHA-256 the download was delivered with
   (hard-coded here and cross-checked against ``archive/SHA256SUMS``). Its three members
   are the three files beside the archive, byte for byte. No vocabulary substitution was
   needed, so the copies must be identical.
2. The review's checker run says every check passed and reports the quantities the review
   states, and the recorded candidate re-verifies from scratch with the checker's own
   functions: amplitudes on the 1/108 grid summing to 701/108, the finite seed balanced
   with mass 56345/108, lifted prefix at least one on every cell of [1, R), and the leading
   constant strictly below the baseline's by exact rational enclosure.
3. The review labels the material honestly.

The full checker (about 40 s) is not rerun here; this is the fast tier.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import zipfile
from fractions import Fraction

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FRONTIER = os.path.join(REPO_ROOT, "hunts", "prime_pair_error", "frontier", "2026-09-06")
PKG = os.path.join(FRONTIER, "joint_correction_candidate")
BASE = os.path.join(FRONTIER, "certificate_route_test")
ARCHIVE = os.path.join(PKG, "archive", "joint_correction_candidate.zip")
SUMS = os.path.join(PKG, "archive", "SHA256SUMS")
TOP = "joint_correction_candidate/"
EXPECTED_SHA256 = "828a4d85d471b51331b5f0a32c30818ccff4de95e9e4c91dbb836536376e8260"
EXPECTED_BYTES = 13_746
MEMBERS = {
    "JOINT_CORRECTION.md": ("e573762c46d817f2e6e7693c79cf5f0b7eb459c05b1f3102167b657231d45247", 7_334),
    "joint_correction.py": ("92dd9b882f7edba1f8f99e46e3469fc1791e3cc7c2eb5c7b6931809f27ff1eaf", 9_640),
    "joint_results.json": ("e951a89fdd8fe4311cc5e0e5a8ad303945f10982844e37669fde3ae48f933e89", 22_880),
}

STATED_C_PREFIX = "1.047623931379267860580006972148025253682"
STATED_MASS = Fraction(56345, 108)
STATED_H = Fraction(701, 36)
STATED_REPAIRS = 172
STATED_NEGATIVE_CELLS = 640
STATED_STARTS = [17, 18, 19, 23, 24, 25, 29, 31, 32]


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _checker():
    spec = importlib.util.spec_from_file_location("joint_check", os.path.join(PKG, "review", "joint_check.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_archive_is_present_and_hash_pinned():
    assert os.path.isfile(ARCHIVE), (
        f"{os.path.relpath(ARCHIVE, REPO_ROOT)} is missing; a documented archive that is not on disk "
        "is the 2026-09-06 frontier incident again"
    )
    assert os.path.getsize(ARCHIVE) == EXPECTED_BYTES
    assert _sha256(open(ARCHIVE, "rb").read()) == EXPECTED_SHA256
    lines = open(SUMS, encoding="utf-8").read().strip().splitlines()
    assert len(lines) == 1
    digest, name = lines[0].split()
    assert name.lstrip("*") == os.path.basename(ARCHIVE) and digest == EXPECTED_SHA256


def test_members_equal_the_files_beside_the_archive():
    with zipfile.ZipFile(ARCHIVE) as z:
        names = {i.filename for i in z.infolist() if not i.is_dir()}
        assert names == {TOP + m for m in MEMBERS}, "unexpected member set"
        for name, (digest, nbytes) in MEMBERS.items():
            member = z.read(TOP + name)
            assert len(member) == nbytes and _sha256(member) == digest, name
            copy = open(os.path.join(PKG, name), "rb").read()
            assert copy == member, f"{name}: extracted copy differs from the archive member"
            assert b"certified" not in copy.lower(), name


def test_the_recorded_checker_run_passed_and_states_the_reviewed_quantities():
    run = json.loads(open(os.path.join(PKG, "review", "joint_check.json"), encoding="utf-8").read())
    assert run["all_ok"] is True
    assert all(v.get("ok", True) for v in run["checks"].values())
    got = run["reproduced"]
    assert got["C_new"].startswith(STATED_C_PREFIX)
    assert Fraction(got["finite_coefficient_mass"]) == STATED_MASS
    assert Fraction(got["tail_coefficient"]) == STATED_H
    assert got["repairs"] == STATED_REPAIRS
    assert got["negative_seed_cells_below_R"] == STATED_NEGATIVE_CELLS


def test_the_recorded_candidate_reverifies_from_scratch():
    jc = _checker()
    cand = json.loads(open(os.path.join(PKG, "joint_results.json"), encoding="utf-8").read())
    inp = json.loads(open(os.path.join(BASE, "inputs.json"), encoding="utf-8").read())
    agg = json.loads(open(os.path.join(BASE, "aggregate_results.json"), encoding="utf-8").read())
    y = {int(q): Fraction(a) for q, a in cand["selected_masked_corrections"].items()}
    lam = {int(n): Fraction(a) for n, a in cand["repair_coefficients"].items()}
    assert sorted(y) == STATED_STARTS
    assert all(108 % a.denominator == 0 and a > 0 for a in list(y.values()) + list(lam.values()))
    assert sum(y.values()) == Fraction(701, 108) and 3 * sum(y.values()) == STATED_H
    assert len(lam) == STATED_REPAIRS

    star = jc.coeffs(inp["repair_coefficients"])
    D = jc.coeffs(cand["new_coefficients"])
    baseline = jc.coeffs(agg["new_coefficients"])
    assert jc.balanced(D) and jc.mass(D) == STATED_MASS
    lifted = jc.lifted_table(D, jc.R, 108)
    assert min(lifted[1:]) >= 108, "a cell of [1, R) has lifted weight below one"
    seed = jc.floor_sum_table(D, jc.R, 108)
    assert sum(1 for x in seed[1:] if x < 0) == STATED_NEGATIVE_CELLS

    new = jc.C_bounds_exact(D, STATED_H, star)
    old = jc.C_bounds_exact(baseline, Fraction(agg["tail_multiplier"]), star)
    assert new[1] < old[0], "the exact enclosures must separate C_new below C_old"
    assert new[0] > 1, "the leading constant is above one; nothing here is an RH-scale bound"
    assert jc.kappa_bounds_exact(D)[0] > 0, "kappa(D) > 0 is what lets the budget drop its geometric tails"


def test_the_review_labels_the_material_honestly():
    text = open(os.path.join(PKG, "JOINT_REVIEW.md"), encoding="utf-8").read()
    assert "**SURVIVES.**" in text
    assert "nothing here is a prime-counting record" in text.lower()
    assert "bears on rh" in text.lower()
    assert "external verification is pending" in text.lower()
    assert "certified" not in text.lower()
