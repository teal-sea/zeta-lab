"""Repository hygiene: no machine-local path may enter the tree.

`tests/test_discovery_funnel.py` already forbids a machine-local path in a
*recorded ledger path*. That rule was correct and too narrow: twenty tracked
files carried a home-directory path anyway, in a public repository, because
nothing checked anywhere else.

This is the same rule at tree scope, with one deliberate exception recorded
below rather than hidden in the pattern.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[1]

# The shape of a home directory on macOS, Linux, or Windows. Deliberately loose:
# it is the *detector*, and it is asserted against directly below.
_MACHINE_LOCAL = re.compile(r"/Users/[^/\s\"']+|/home/[^/\s\"']+|[A-Za-z]:\\Users\\")

# The shape of a home directory belonging to a *real account*. The username must
# look like an identifier, which is what separates a leaked path from the two
# things that legitimately contain this substring: another guard's own regex
# source (`/Users/|`, `/Users/[^/...`) and documentation ellipses (`/Users/…`).
_REAL_HOME = re.compile(
    r"(?:/Users/|/home/|[A-Za-z]:\\Users\\)(?P<user>[A-Za-z0-9._-]{1,32})(?![A-Za-z0-9._-])"
)

# Fixture names. A planted path is how a detector proves it can fire, so these
# are evidence the rule works rather than violations of it.
_PLACEHOLDER_USERS = frozenset(
    {"someone", "somebody", "user", "username", "you", "me", "name", "example", "USER", "runner"}
)

_TEXT_SUFFIXES = {".py", ".md", ".txt", ".lean", ".toml", ".jsonl", ".yaml", ".yml", ".sh"}

_SKIP_DIRS = {".git", ".venv", "data", "figures", "__pycache__", ".pytest_cache", ".lake"}

# The one exception, and it is not a lapse.
#
# `harness/blind_authoring_2026_08_09/SHA256SUMS.txt` pins these ten modules as
# they were when they were scored, and `docs/23` §7 states that no
# blind-authored battery is edited for any reason. De-identifying them would
# break a live digest, and re-taking the digest afterwards would prove strictly
# less than the original pin does. The stale absolute path is the cheaper cost,
# so it is carried on purpose.
_PINNED_BLIND_MODULES = frozenset(
    f"harness/blind_authoring_2026_08_09/party{i:02d}/department.py" for i in range(1, 11)
)


def _tracked_text_files() -> list[Path]:
    tracked = subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=_REPO_ROOT
    ).decode("utf-8").split("\0")
    out: list[Path] = []
    for relative in tracked:
        if not relative:
            continue
        path = _REPO_ROOT / relative
        if not path.is_file() or path.suffix not in _TEXT_SUFFIXES:
            continue
        if any(part in _SKIP_DIRS for part in Path(relative).parts):
            continue
        out.append(path)
    return out


def _leaks(text: str) -> list[tuple[int, str]]:
    found = []
    for match in _REAL_HOME.finditer(text):
        if match.group("user") in _PLACEHOLDER_USERS:
            continue
        found.append((text.count("\n", 0, match.start()) + 1, match.group(0)))
    return found


def test_no_machine_local_path_outside_the_pinned_blind_modules() -> None:
    offenders = []
    for path in _tracked_text_files():
        rel = path.relative_to(_REPO_ROOT).as_posix()
        if rel in _PINNED_BLIND_MODULES:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        offenders += [f"{rel}:{line}: {hit}" for line, hit in _leaks(text)]
    assert not offenders, "machine-local paths in tracked files:\n" + "\n".join(offenders)


def test_the_exception_is_real_and_still_pinned() -> None:
    """The exemption must not outlive the reason for it.

    If a pinned module stops existing, or the digest file stops covering
    exactly these ten, the exemption is dead and should be deleted rather than
    left to quietly widen the rule.
    """
    for rel in sorted(_PINNED_BLIND_MODULES):
        assert (_REPO_ROOT / rel).is_file(), f"exempted file no longer exists: {rel}"

    sums = _REPO_ROOT / "harness/blind_authoring_2026_08_09/SHA256SUMS.txt"
    assert sums.is_file(), "the exemption's justification (the digest pin) is missing"
    pinned_in_file = {
        f"harness/blind_authoring_2026_08_09/{line.split()[1]}"
        for line in sums.read_text().splitlines()
        if line.strip()
    }
    assert pinned_in_file == set(_PINNED_BLIND_MODULES), (
        "the exemption list and SHA256SUMS.txt disagree about what is pinned"
    )


def test_the_exempted_files_are_the_reason_the_exemption_exists() -> None:
    """At least one pinned module must actually still carry a leaked path.

    Otherwise the exemption is buying nothing and should go.
    """
    assert any(
        _leaks((_REPO_ROOT / rel).read_text(encoding="utf-8")) for rel in _PINNED_BLIND_MODULES
    ), "no pinned module carries a machine-local path — delete the exemption"


def _home(user: str, style: str = "mac") -> str:
    """Build a home path at runtime.

    Assembled from parts on purpose: a literal one in this file would be a real
    leak by this module's own rule, and a guard that has to exempt itself is a
    guard with a hole in it.
    """
    if style == "mac":
        return "/Users" + "/" + user
    if style == "linux":
        return "/home" + "/" + user
    return "C:" + "\\Users" + "\\" + user


def test_the_detector_would_notice_a_planted_path(tmp_path: Path) -> None:
    """A guard that cannot fail is indistinguishable from a correct one."""
    planted = tmp_path / "planted.py"
    planted.write_text(f'sys.path.insert(0, "{_home("ahiddenname")}/Project")\n')
    assert _leaks(planted.read_text())

    clean = tmp_path / "clean.py"
    clean.write_text("sys.path.insert(0, str(Path(__file__).resolve().parents[3]))\n")
    assert not _leaks(clean.read_text())


def test_a_placeholder_is_not_a_leak_but_still_matches_the_shape() -> None:
    """The two layers do different jobs, and the difference is load-bearing."""
    fixture = '"/Users/someone/Project"'
    assert _MACHINE_LOCAL.search(fixture), "the shape detector must still fire"
    assert not _leaks(fixture), "a fixture username is not a leaked account"


def test_another_guards_regex_source_is_not_read_as_a_leak() -> None:
    """This is what made the first version of this test fail against the tree."""
    for regex_source in (r"/Users/[^/\s\"']+", r"(?:/Users/|/home/)", "`/Users/…`"):
        assert not _leaks(regex_source), regex_source


@pytest.mark.parametrize("style", ["mac", "linux", "windows"])
def test_the_pattern_covers_all_three_platforms(style: str) -> None:
    sample = _home("ahiddenname", style)
    assert _MACHINE_LOCAL.search(sample), sample
    assert _leaks(sample), sample
