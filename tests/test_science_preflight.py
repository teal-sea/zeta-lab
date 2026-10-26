"""The preflight's history check must warn, and must never fail open.

``scripts/science_preflight.py`` is the first thing an outside session runs,
and its verdict is what that session then believes about the tree. The git
history check landed with a fail-open path: when git could not answer, which
is the case on a snapshot mounted without ``.git``, it printed one line,
returned no warning, and the verdict read "Ready. Every claim this repository
knows how to make is available." A guard that fails open is worse than none,
because it also supplies confidence (``tests/test_check_secrets.py`` pins the
same lesson for the secret guard).

These tests run the check against small throwaway repositories rather than
this checkout, whose depth depends on how it was cloned. Every way of not
knowing the history must give a warning, a real shallow clone must give one,
and a complete history must give none, so that the warnings are shown to be
able to stay quiet as well as to fire.

The verdict had the same hole one section earlier: a degraded ball-arithmetic
backend accepted with ``--allow-fallback`` left no trace in it. That warning is
pinned here too, against the control that a run with no warning at all still
ends on the full readiness line.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from scripts import science_preflight as preflight

pytestmark = pytest.mark.skipif(shutil.which("git") is None, reason="needs git")

EVERY_CLAIM = "Every claim this repository knows how to make is available"
UNREADABLE = "git history not readable here"


@pytest.fixture(autouse=True)
def _plain_git_environment(monkeypatch):
    """No inherited GIT_DIR and friends: each test names its own tree."""
    for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_CEILING_DIRECTORIES"):
        monkeypatch.delenv(name, raising=False)


def _git(*args: str, cwd: Path) -> None:
    subprocess.run(
        ["git", "-c", "user.name=preflight", "-c", "user.email=preflight@example.invalid",
         "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", *args],
        cwd=cwd, check=True, capture_output=True, text=True,
    )


@pytest.fixture
def complete_repo(tmp_path: Path) -> Path:
    """A three-commit repository holding its whole history."""
    repo = tmp_path / "complete"
    repo.mkdir()
    _git("init", "-q", cwd=repo)
    for i in range(3):
        (repo / "f.txt").write_text(f"{i}\n", encoding="utf-8")
        _git("add", "f.txt", cwd=repo)
        _git("commit", "-q", "-m", f"commit {i}", cwd=repo)
    return repo


def _history(monkeypatch, root: Path) -> list[str]:
    monkeypatch.setattr(preflight, "REPO_ROOT", str(root))
    return preflight._check_history()


def test_a_complete_history_gives_no_warning(monkeypatch, capsys, complete_repo):
    assert _history(monkeypatch, complete_repo) == []
    assert "complete: 3 commits" in capsys.readouterr().out


def test_a_shallow_clone_warns(monkeypatch, capsys, complete_repo, tmp_path):
    shallow = tmp_path / "shallow"
    _git("clone", "-q", "--depth", "1", complete_repo.as_uri(), str(shallow), cwd=tmp_path)
    warnings = _history(monkeypatch, shallow)
    assert len(warnings) == 1 and warnings[0].startswith("shallow clone")
    assert "SHALLOW CLONE: 1 commits" in capsys.readouterr().out


def test_a_tree_git_cannot_read_warns_rather_than_passing(monkeypatch, capsys, tmp_path):
    """The fail-open path that landed with the check, pinned.

    A snapshot with no ``.git``. ``GIT_CEILING_DIRECTORIES`` keeps git from
    walking up into whatever repository the temporary directory sits in.
    """
    snapshot = tmp_path / "snapshot"
    snapshot.mkdir()
    monkeypatch.setenv("GIT_CEILING_DIRECTORIES", str(tmp_path))
    warnings = _history(monkeypatch, snapshot)
    assert len(warnings) == 1 and warnings[0].startswith(UNREADABLE)
    assert "NOT READABLE" in capsys.readouterr().out


def test_no_git_at_all_warns_rather_than_passing(monkeypatch, complete_repo, tmp_path):
    monkeypatch.setenv("PATH", str(tmp_path / "no-such-directory"))
    warnings = _history(monkeypatch, complete_repo)
    assert len(warnings) == 1 and warnings[0].startswith(UNREADABLE)


def test_a_tree_inside_another_repository_warns(monkeypatch, complete_repo):
    """A snapshot unpacked inside some other repository.

    git walks up and answers for the enclosing repository, whose history is not
    this tree's. Counting it would be the same silent error as counting a
    shallow one.
    """
    inner = complete_repo / "snapshot"
    inner.mkdir()
    warnings = _history(monkeypatch, inner)
    assert len(warnings) == 1 and warnings[0].startswith(UNREADABLE)


def test_a_git_too_old_to_answer_warns(monkeypatch, complete_repo):
    """Before 2.15, rev-parse echoes the flag it does not know instead of answering."""
    real = preflight._git

    def old_git(*args: str) -> str:
        if args == ("rev-parse", "--is-shallow-repository"):
            return "--is-shallow-repository"
        return real(*args)

    monkeypatch.setattr(preflight, "_git", old_git)
    warnings = _history(monkeypatch, complete_repo)
    assert len(warnings) == 1 and warnings[0].startswith(UNREADABLE)


def _verdict(monkeypatch, capsys, history=(), backend=()) -> tuple[int, str]:
    """Run ``main`` with the checks stubbed to report only the given warnings."""
    monkeypatch.setattr(preflight, "_check_interpreter", lambda: [])
    monkeypatch.setattr(preflight, "_check_backend", lambda allow_fallback: ([], list(backend)))
    monkeypatch.setattr(preflight, "_check_history", lambda: list(history))
    monkeypatch.setattr(preflight.sys, "argv", ["science_preflight.py"])
    code = preflight.main()
    return code, capsys.readouterr().out.split("\nverdict\n", 1)[1]


def test_a_history_warning_narrows_the_verdict(monkeypatch, capsys):
    code, verdict = _verdict(monkeypatch, capsys, history=[f"{UNREADABLE}: stub"])
    assert code == 0
    assert f"WARNING: {UNREADABLE}" in verdict
    assert EVERY_CLAIM not in verdict


def test_with_nothing_wrong_the_verdict_says_so(monkeypatch, capsys):
    """The control: the narrowed verdict is not simply printed every time."""
    code, verdict = _verdict(monkeypatch, capsys)
    assert code == 0
    assert "WARNING" not in verdict
    assert EVERY_CLAIM in verdict


def test_an_accepted_fallback_is_a_warning_not_nothing(monkeypatch):
    """``--allow-fallback`` continues past a degraded backend; it must not vanish.

    Before 2026-10-21 the accepted fallback left no trace in the verdict, which
    then said every claim was available on a run that had just given up the
    two-backend cross-check.
    """
    from zeta import rigor

    monkeypatch.setattr(rigor, "BACKEND", "mpmath.iv")
    monkeypatch.setattr(rigor, "available_backends", lambda: ("mpmath.iv",))
    problems, warnings = preflight._check_backend(allow_fallback=False)
    assert len(problems) == 1 and warnings == []
    problems, warnings = preflight._check_backend(allow_fallback=True)
    assert problems == [] and len(warnings) == 1


def test_an_accepted_fallback_narrows_the_verdict(monkeypatch, capsys):
    code, verdict = _verdict(monkeypatch, capsys, backend=["ball-arithmetic backend: stub"])
    assert code == 0
    assert "WARNING: ball-arithmetic backend" in verdict
    assert EVERY_CLAIM not in verdict
