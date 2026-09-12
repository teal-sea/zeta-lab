"""Replay every Palomar submission outcome against the correspondence check.

A guard written after a failure is worth what it would have caught. So this
file does not test the checker against invented inputs: it replays the four
real submission events, two registered and two refused, and requires the
checker to sort them the way Palomar did.

  registered  pub1        comparator.json      + formalization.yaml
  registered  dh v2       comparator-dh.json   + palomar-dh/formalization.yaml
  REFUSED     dh v1       the same pair at the commit before PR #79, whose
                          record asserted the whole tree was sorry-free
  REFUSED     bridge v2   comparator-v2.json submitted with the pinned V1
                          record, the 2026-08-25 filing error

A checker that passes all four is not proof of much; a checker that fails any
of them is known to be useless, which is the cheaper thing to know. The
refused cases are the load-bearing half: if either starts passing, this file
fails loudly rather than a submission cycle being spent to rediscover it.
"""
from __future__ import annotations

import pathlib
import subprocess
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import palomar_correspondence as pc  # noqa: E402

# The commit whose record was refused, and the fix that followed it.
DH_V1_FIX_PR = "097215a8413641fd3b3de137386316bf294328de"
DH_YAML = "lean/palomar-dh/formalization.yaml"


def _fails(comparator: str, metadata: str) -> list[str]:
    return pc.check(str(ROOT), comparator, metadata)[2]


# --- the two that registered ------------------------------------------------

@pytest.mark.parametrize("comparator,metadata", [
    ("lean/comparator.json", "lean/formalization.yaml"),
    ("lean/comparator-dh.json", "lean/palomar-dh/formalization.yaml"),
    ("lean/bridge/comparator-v2.json", "lean/bridge/palomar-v2/formalization.yaml"),
])
def test_accepted_surfaces_pass(comparator, metadata):
    """The two registered records, and the V2 record as intended to be filed."""
    assert _fails(comparator, metadata) == []


# --- the two that were refused ----------------------------------------------

def test_v2_filed_against_the_v1_record_is_refused():
    """The 2026-08-25 refusal: right mathematics, wrong record.

    The form defaulted to lean/bridge/formalization.yaml. Mechanical
    verification passed on both kernels and the editorial review still refused
    it, because the V1 record describes four conditional seven-point
    declarations and the comparator selected seven V2 ones.
    """
    fails = _fails("lean/bridge/comparator-v2.json", "lean/bridge/formalization.yaml")
    assert fails, "the misfiling that cost a cycle must not pass"
    assert any("pairing" in f for f in fails)
    # And independently of the hand-maintained registry: the two artifacts
    # disagree on their face. The V1 record names Zeta23Ext.Palomar.*, the V2
    # comparator selects Zeta23Ext.PalomarV2.*, and the sets do not intersect.
    assert any("alignment" in f for f in fails), (
        "alignment must fire too; a stale palomar-pairs.json must not be the "
        "only thing standing between us and this refusal")


def test_alignment_survives_a_wrong_registry_row(tmp_path):
    """Defence in depth: corrupt the registry, alignment still refuses.

    palomar-pairs.json is hand-maintained, which is the same kind of artifact
    that produced both refusals in the first place. This pins that the guard
    does not collapse to it.
    """
    import json as _json

    stage = tmp_path / "repo"
    for f in ("lean/bridge/comparator-v2.json", "lean/bridge/formalization.yaml"):
        (stage / f).parent.mkdir(parents=True, exist_ok=True)
        (stage / f).write_text((ROOT / f).read_text(encoding="utf-8"), encoding="utf-8")

    bad = _json.loads((ROOT / "lean/palomar-pairs.json").read_text(encoding="utf-8"))
    for row in bad["pairs"]:                       # the wrong pairing, blessed
        if row["label"] == "bridge-v2":
            row["metadata"] = "lean/bridge/formalization.yaml"
    bad["refused_metadata"] = []
    (stage / "lean/palomar-pairs.json").write_text(_json.dumps(bad), encoding="utf-8")

    fails = pc.check(str(stage), "lean/bridge/comparator-v2.json",
                     "lean/bridge/formalization.yaml")[2]
    assert any("alignment" in f for f in fails)
    assert not any("pairing" in f for f in fails), "registry was deliberately made to agree"


def test_the_compatibility_copy_is_refused_by_name():
    """lean/bridge/formalization-v2.yaml reads correct and is not the path.

    It is the plausible wrong answer sitting next to the right one, which is
    the shape of trap that costs cycles. Refused explicitly rather than left
    to judgement.
    """
    fails = _fails("lean/bridge/comparator-v2.json", "lean/bridge/formalization-v2.yaml")
    assert any("refused by name" in f for f in fails)


def test_dh_v1_unqualified_sorry_free_claim_is_refused(tmp_path):
    """The 2026-08-21 refusal, replayed from the actual pre-fix file.

    Recovered from git rather than retyped, so this tests the text Palomar
    actually read. Skips rather than passing vacuously if the history is not
    present -- a shallow clone must not silently turn this into a green run.
    """
    shallow = subprocess.run(
        ["git", "rev-parse", "--is-shallow-repository"],
        cwd=ROOT, capture_output=True, text=True)
    if shallow.stdout.strip() == "true":
        pytest.skip("shallow clone: the pre-fix commit is not in this history")

    got = subprocess.run(
        ["git", "show", f"{DH_V1_FIX_PR}^1:{DH_YAML}"],
        cwd=ROOT, capture_output=True, text=True)
    if got.returncode != 0:
        pytest.skip(f"pre-fix {DH_YAML} not reachable from this checkout")

    # Reconstruct the refused submission: the pre-fix record, its comparator.
    stage = tmp_path / "repo"
    (stage / "lean" / "palomar-dh").mkdir(parents=True)
    (stage / DH_YAML).write_text(got.stdout, encoding="utf-8")
    for f in ("lean/comparator-dh.json", "lean/palomar-pairs.json"):
        (stage / f).write_text((ROOT / f).read_text(encoding="utf-8"), encoding="utf-8")

    fails = pc.check(str(stage), "lean/comparator-dh.json", DH_YAML)[2]
    assert any("sorry" in f for f in fails), (
        "the record that claimed the whole tree was sorry-free must be refused")


# --- the property that removes the hand selection ---------------------------

def test_resolve_derives_the_path_rather_than_the_operator_picking_it():
    assert pc.resolve("lean/bridge/comparator-v2.json", str(ROOT)) == \
        "lean/bridge/palomar-v2/formalization.yaml"
    assert pc.resolve("lean/comparator.json", str(ROOT)) == "lean/formalization.yaml"


def test_an_unregistered_comparator_raises_rather_than_guessing():
    with pytest.raises(KeyError):
        pc.resolve("lean/comparator-nonexistent.json", str(ROOT))


def test_the_precheck_runs_clean_on_every_registered_surface():
    """One argument per surface, zero FAIL. The end-to-end shape of a filing.

    Slow-ish (four subprocess runs) but this is the command an operator
    actually types before a submission, so it is the one worth pinning.
    """
    for row in pc.load_pairs(str(ROOT))["pairs"]:
        got = subprocess.run(
            [sys.executable, "scripts/palomar_precheck.py", ".", row["comparator"]],
            cwd=ROOT, capture_output=True, text=True)
        assert got.returncode == 0, (
            f"{row['label']}: {[l for l in got.stdout.splitlines() if 'FAIL' in l]}")
        assert row["metadata"] in got.stdout


def test_project_dir_is_derived_not_typed():
    """Passing `lean` where the bridge wants `lean/bridge` reports a missing
    Challenge module, which reads like a defect in the submission rather than
    a mistyped argument. Deriving it removes the confusion."""
    assert pc.resolve_project("lean/bridge/comparator-v2.json", str(ROOT)) == "lean/bridge"
    assert pc.resolve_project("lean/comparator.json", str(ROOT)) == "lean"


def test_every_pair_in_the_registry_points_at_files_that_exist():
    for row in pc.load_pairs(str(ROOT))["pairs"]:
        assert (ROOT / row["comparator"]).is_file(), row["comparator"]
        assert (ROOT / row["metadata"]).is_file(), row["metadata"]
    for row in pc.load_pairs(str(ROOT))["refused_metadata"]:
        assert (ROOT / row["path"]).is_file(), (
            f"{row['path']} is refused by name but absent; either the trap is "
            f"gone and the row should go, or the path is wrong")
