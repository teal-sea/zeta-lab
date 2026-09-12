"""The Hardy Z dossier, measured, every claim it makes, re-derived here.

A dossier that asserted support without a test would be the exact decoration
``dossier/status.py`` refuses to allow. So each obligation naming an artifact
in this file has a test of that name, and the artifact strings are themselves
checked against what exists.

The interesting test is
:func:`test_Z_changes_sign_but_the_rejected_alternative_does_not`: it runs the
*rejected* definition alongside the accepted one and shows that the rejected
one passes every obligation except the discriminating one. That is the
experiment's thesis in executable form, formally defensible, semantically
wrong, and caught by exactly one check.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest
from mpmath import mp

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(_REPO_ROOT))

from dossier import dossier_reasons, render_text  # noqa: E402
from dossier.status import (  # noqa: E402
    AXES,
    CertifiedStatus,
    FormalStatus,
    LiteratureStatus,
    NumericStatus,
)
from dossier.subjects.hardy_z import (  # noqa: E402
    DEFINITION_AGREEMENT_DEFECT,
    SAMPLE_TS,
    Z_via_completed,
    build,
)
from zeta import Z  # noqa: E402

DPS = 30
TOL = mp.mpf("1e-28")


@pytest.fixture(scope="module")
def hardy_z():
    return build()


# ---------------------------------------------------------------------------
# The dossier itself
# ---------------------------------------------------------------------------


def test_the_dossier_is_valid(hardy_z) -> None:
    assert dossier_reasons(hardy_z) == ()


def test_it_has_a_discriminating_obligation(hardy_z) -> None:
    names = {o.name for o in hardy_z.discriminating_obligations}
    assert "changes_sign" in names


def test_the_report_renders_all_four_axes(hardy_z) -> None:
    text = render_text(hardy_z)
    for axis in AXES:
        assert axis in text


def test_the_report_never_says_verified(hardy_z) -> None:
    """No aggregate leaks into the prose either."""
    text = render_text(hardy_z).lower()
    for banned in ("fully verified", "is verified", "verification: complete", "100%"):
        assert banned not in text


def test_no_axis_claims_support_without_an_artifact_that_exists(hardy_z) -> None:
    """An artifact backing an *assertion* must exist in this tree.

    Only assertions carry the burden. A ``not-attempted`` axis may point at
    something aspirational or, as here, at a file that is not tracked yet,
    the formal axis names a Lean draft that exists on one machine and is not
    committed. Requiring that to exist would make a fresh clone fail a test
    about a claim the dossier is not making.
    """
    records = [(a, hardy_z.support.record(a)) for a in AXES]
    records += [(a, o.support.record(a)) for o in hardy_z.obligations for a in AXES]
    for axis, record in records:
        if not record.artifact or not record.asserts_support(axis):
            continue
        path = record.artifact.split("::")[0]
        assert (_REPO_ROOT / path).exists(), f"artifact {record.artifact!r} does not exist"


def test_the_named_tests_in_artifacts_exist_in_this_module(hardy_z) -> None:
    """An artifact naming a test in this file must name one that is here."""
    this_file = Path(__file__).name
    source = Path(__file__).read_text(encoding="utf-8")
    records = [hardy_z.support.record(a) for a in AXES]
    records += [o.support.record(a) for o in hardy_z.obligations for a in AXES]
    for record in records:
        if "::" not in record.artifact:
            continue
        path, test_name = record.artifact.split("::", 1)
        if Path(path).name != this_file:
            continue
        assert f"def {test_name}(" in source, f"{record.artifact} names a test that is not here"


# ---------------------------------------------------------------------------
# The obligations, measured
# ---------------------------------------------------------------------------


def test_Z_is_real_on_the_sample() -> None:
    with mp.workdps(DPS):
        for t in SAMPLE_TS:
            assert abs(mp.im(mp.mpc(Z_via_completed(t, dps=DPS)))) < TOL, t


def test_the_two_definitions_agree() -> None:
    """exp(i*theta)*zeta versus the completed-zeta route, which uses no branch."""
    with mp.workdps(DPS):
        worst = max(abs(Z_via_completed(t, dps=DPS) - Z(t, dps=DPS)) for t in SAMPLE_TS)
    assert worst < TOL, worst
    # The pinned figure in the dossier is an order of magnitude, not a bound.
    assert float(worst) < 10 * float(mp.mpf(DEFINITION_AGREEMENT_DEFECT))


def test_magnitude_matches_zeta() -> None:
    with mp.workdps(DPS):
        for t in SAMPLE_TS:
            lhs = abs(Z(t, dps=DPS))
            rhs = abs(mp.zeta(mp.mpc(mp.mpf(1) / 2, t)))
            assert abs(lhs - rhs) < TOL, t


def test_Z_is_even() -> None:
    with mp.workdps(DPS):
        for t in SAMPLE_TS:
            assert abs(Z(-t, dps=DPS) - Z(t, dps=DPS)) < TOL, t


def test_Z_changes_sign_but_the_rejected_alternative_does_not() -> None:
    """The thesis, executable.

    ``|zeta(1/2+it)|``, the rejected alternative, is real, is even, and
    vanishes at exactly the same points. It fails one obligation, and that one
    failure is the whole reason it is the wrong object.
    """
    with mp.workdps(DPS):
        accepted = [Z(t, dps=DPS) for t in (0.0, 100.0)]
        rejected = [abs(mp.zeta(mp.mpc(mp.mpf(1) / 2, t))) for t in (0.0, 100.0)]

        # The accepted definition takes both signs.
        assert accepted[0] < 0 < accepted[1]

        # The rejected one is real (passes), even (passes), has the same zeros
        # (passes), and never negative, so it can never bracket a zero.
        assert all(value >= 0 for value in rejected)
        assert not any(a * b < 0 for a, b in zip(rejected, rejected[1:]))


def test_Z_at_zero_is_zeta_at_one_half() -> None:
    """Pins the sign convention: theta(0) = 0, so no absolute value crept in."""
    with mp.workdps(DPS):
        assert abs(Z(0, dps=DPS) - mp.zeta(mp.mpf(1) / 2)) < TOL
        assert Z(0, dps=DPS) < 0


def test_Z_vanishes_at_the_first_two_ordinates() -> None:
    with mp.workdps(DPS):
        for gamma in (14.134725141734694, 21.022039638771555):
            assert abs(Z(gamma, dps=DPS)) < mp.mpf("1e-14"), gamma


# ---------------------------------------------------------------------------
# The honest-status tests: what the dossier does NOT claim
# ---------------------------------------------------------------------------


def test_nothing_is_claimed_certified(hardy_z) -> None:
    """'Certified' is reserved; this dossier has run no enclosure."""
    assert hardy_z.support.certified.status == CertifiedStatus.NOT_ATTEMPTED
    for obligation in hardy_z.obligations:
        assert obligation.support.certified.status != CertifiedStatus.CERTIFIED


def test_proved_cites_a_watched_dated_kernel_run_the_tree_corroborates(hardy_z) -> None:
    """'Proved' must cite a dated observation, and the tree must corroborate it.

    This test replaced ``test_nothing_is_claimed_proved`` on 2026-08-07, when a
    kernel run was finally watched (lake build, 8706 jobs) and the axis moved
    ``stated-unchecked`` → ``proved``. The upgrade rule it enforces: a PROVED
    formal record must (a) carry a date, (b) name a lemma that exists in the
    cited file, (c) cite a file with no ``sorry`` that the root build actually
    wires in, and (d), when git is available, cite an observation no older
    than the file's last change, so editing HardyZ.lean re-opens the question.
    Machine-checked *consistency*, human-recorded *observations*: the status
    field never flips itself.
    """
    import re
    import shutil
    import subprocess

    source = (_REPO_ROOT / "lean/ZetaLean/HardyZ.lean").read_text(encoding="utf-8")
    root = (_REPO_ROOT / "lean/ZetaLean.lean").read_text(encoding="utf-8")

    rec = hardy_z.support.formal
    assert rec.status == FormalStatus.PROVED
    records = [rec] + [
        o.support.formal
        for o in hardy_z.obligations
        if o.support.formal.status == FormalStatus.PROVED
    ]
    assert len(records) >= 4, "the three lemma-backed obligations plus the subject record"
    for r in records:
        dates = re.findall(r"\d{4}-\d{2}-\d{2}", r.detail)
        assert dates, f"a PROVED record must date its observation: {r.detail[:60]}"
        assert "import ZetaLean.HardyZ" in root, (
            "PROVED cites a build of a file the root build does not include"
        )
        assert "sorry" not in source
        if r is not rec:  # obligation records lead with their lemma's name
            lemma = r.detail.split(":", 1)[0].strip()
            assert f"lemma {lemma}" in source, lemma
        # (d) the observation must postdate the last edit of what it certifies
        if shutil.which("git") and (_REPO_ROOT / ".git").exists():
            # A depth-1 clone has one commit in it, so `log -1 -- <path>`
            # answers with the checkout rather than with the file's history.
            # That is not a stricter check, it is a different and meaningless
            # one: it passed only while CI ran on the same calendar day as the
            # last re-observation, then failed at midnight and read as "the
            # record is stale" when nothing had changed. Refuse to answer
            # instead, the same way `rigor.proven_sign` returns 0 for "not
            # decided" rather than guessing a sign.
            shallow = subprocess.run(
                ["git", "rev-parse", "--is-shallow-repository"],
                cwd=_REPO_ROOT, capture_output=True, text=True,
            ).stdout.strip()
            if shallow == "true":
                pytest.skip(
                    "shallow checkout: the last change to HardyZ.lean cannot "
                    "be read from a truncated history, so the staleness check "
                    "is not run. Clone with fetch-depth: 0 to restore it."
                )
            last = subprocess.run(
                ["git", "log", "-1", "--format=%ad", "--date=short", "--",
                 "lean/ZetaLean/HardyZ.lean"],
                cwd=_REPO_ROOT, capture_output=True, text=True,
            ).stdout.strip()
            if last:
                assert max(dates) >= last, (
                    "HardyZ.lean changed after the recorded kernel observation: "
                    "re-observe (re-run lake build) and update the record"
                )


def test_the_r_vs_c_open_question_is_resolved_and_the_tree_agrees(hardy_z) -> None:
    """The other half of the staleness lesson: an answered question needs
    somewhere to record the answer, or it goes stale exactly like a status
    field does.

    The R-vs-C open question asked to be settled by ``hardyZ_is_real`` being
    proved in Lean; that happened (see the formal-axis tests above), so it is
    resolved here rather than left to silently drift, and the resolution text
    is checked against the tree so it cannot drift into fiction either.
    """
    q = next(
        o for o in hardy_z.open_questions if o.question.startswith("Should the Lean definition")
    )
    assert q.resolution.strip(), "the R-vs-C question is settled and must say so"

    source = (_REPO_ROOT / "lean/ZetaLean/HardyZ.lean").read_text(encoding="utf-8")
    for lemma in (
        "hardyZReal",
        "hardyZReal_eq_hardyZ",
        "abs_hardyZReal_eq_abs_zeta",
        "hardyZReal_even",
        "hardyZReal_zero_iff",
        "continuous_hardyZReal",
    ):
        assert lemma in q.resolution, f"resolution doesn't mention {lemma}"
        assert lemma in source, f"resolution cites {lemma}, which isn't in the Lean file"
    assert "sorry" not in source
    # the original C-valued API must still be there: this is meant to be
    # additive, not a replacement, per the resolution's own claim
    assert "noncomputable def hardyZ (t : ℝ) : ℂ" in source


def test_stated_unchecked_may_not_cite_a_file_the_root_build_compiles(hardy_z) -> None:
    """The staleness tripwire, the mechanism whose absence caused an incident.

    History: this dossier spent 2026-08-07 10:49 → ~18:10 as stated-unchecked,
    *correctly*: HardyZ.lean sat outside the root import, exactly where a
    complete-looking proof can hide a non-compiling one. Commit 150ac05 then
    wired the root import and its green build compiled the file for the first
    time, and the record stayed stale for ~3 hours because no mechanism coupled
    build evidence to recorded status.

    The coupling, in this repository's own terms: the root build is the
    certificate (docs/doors/certify.md), so a file wired into ZetaLean.lean has
    been kernel-checked by whoever last built, and a formal record that stays
    "stated-unchecked because not compiled" while its artifact is wired is
    contradicted by the tree it cites. The moment such a wiring lands, this
    fails and demands a recorded observation (or a demotion with reasons).

    This reads text files only, so no missing toolchain can switch it off,
    per the ROADMAP rule that a control the environment can disable is not a
    control.
    """
    root = (_REPO_ROOT / "lean/ZetaLean.lean").read_text(encoding="utf-8")
    wired = "import ZetaLean.HardyZ" in root
    records = [hardy_z.support.formal] + [o.support.formal for o in hardy_z.obligations]
    for r in records:
        if (
            r.status == FormalStatus.STATED_UNCHECKED
            and (r.artifact or "").endswith("HardyZ.lean")
        ):
            assert not wired, (
                "a formal record still reads stated-unchecked, but the root "
                "build wires lean/ZetaLean/HardyZ.lean, the tree contradicts "
                "the record; watch a build and update the dossier"
            )


def test_the_lean_file_really_has_those_lemmas_and_no_sorry(hardy_z) -> None:
    """The dossier names Lean lemmas; check they exist and the file is clean.

    This is what stops the formal axis from drifting into fiction. It does not
    upgrade the status, only a kernel can do that.
    """
    source = (_REPO_ROOT / "lean/ZetaLean/HardyZ.lean").read_text(encoding="utf-8")
    for lemma in (
        "hardyZ_is_real",
        "abs_hardyZ_eq_abs_zeta",
        "hardyZ_even",
        "hardyZ_zero_iff",
        "continuous_hardyZ",
    ):
        assert f"lemma {lemma}" in source, lemma
    assert "sorry" not in source


def test_the_discriminating_obligation_is_the_one_lean_does_not_cover(hardy_z) -> None:
    """The finding, pinned.

    Four obligations have a Lean statement behind them. The single
    *discriminating* one, that Z changes sign, the only property separating Z
    from |zeta(1/2+it)|, has none. A formalisation can be complete about
    everything except the thing that made the object worth defining, and that
    is precisely what an intent-carrying record is for noticing.

    If this test ever fails because ``changes_sign`` acquired a formal status,
    that is good news: delete the test and record the lemma.
    """
    covered = {
        o.name
        for o in hardy_z.obligations
        if o.support.formal.status != FormalStatus.NOT_ATTEMPTED
    }
    uncovered = {
        o.name
        for o in hardy_z.obligations
        if o.support.formal.status == FormalStatus.NOT_ATTEMPTED
    }
    assert covered, "expected some obligations to have a Lean statement"
    discriminating = {o.name for o in hardy_z.discriminating_obligations}
    assert "changes_sign" in uncovered
    assert "changes_sign" in discriminating
    source = (_REPO_ROOT / "lean/ZetaLean/HardyZ.lean").read_text(encoding="utf-8").lower()
    assert "sign" not in source, "Lean gained a sign lemma, update the dossier"


def test_the_numeric_axis_is_not_read_as_proof(hardy_z) -> None:
    """The strongest numeric value available is still only 'agrees'."""
    assert hardy_z.support.numeric.status == NumericStatus.AGREES_TO_TOLERANCE
    assert "proved" not in str(hardy_z.support.numeric.status)


def test_the_literature_axis_says_standard_not_novel(hardy_z) -> None:
    assert hardy_z.support.literature.status == LiteratureStatus.STANDARD


def test_the_open_questions_each_say_what_would_settle_them(hardy_z) -> None:
    assert hardy_z.open_questions
    for question in hardy_z.open_questions:
        assert question.what_would_settle_it.strip()
