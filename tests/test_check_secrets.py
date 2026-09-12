"""The secret guard must fire, and must never fail open.

Context, because the file exists for a specific incident. On 2026-08-20 a live
OpenRouter API key was committed in plain text to a local branch of this
repository, in two files across two commits. It was caught by a human asking an
unrelated question, not by anything mechanical, and nothing in the tree would
have stopped the push.

The guard written in response had a worse bug than the one it prevents: its
object lister returned an empty list when git errored, so a malformed revision
range made the scan report *clean* and the pre-push hook allowed the push. A
guard that fails open is worse than no guard, because it also supplies
confidence. ``test_a_broken_range_fails_loudly_rather_than_clean`` is the pin
for that.

Every key-shaped string below is assembled at runtime rather than written as a
literal, so this file does not itself contain anything a scanner should flag.
"""

from __future__ import annotations

import subprocess

import pytest

from scripts.check_secrets import PATTERNS, scan


def _fake(prefix: str, n: int = 40) -> str:
    """A syntactically valid, entirely fictional credential."""
    return prefix + "A1b2C3d4E5f6G7h8" * (n // 16 + 1)


@pytest.mark.parametrize(
    "label,sample",
    [
        ("OpenRouter key", _fake("sk-or-" + "v1-")),
        ("Anthropic key", _fake("sk-ant-" + "api")),
        ("OpenAI key", _fake("sk-" + "proj-")),
        ("Perplexity key", _fake("pp" + "lx-", 48)),
        ("Google API key", _fake("AI" + "za", 40)),
        ("GitHub token", _fake("gh" + "p_", 40)),
    ],
)
def test_each_pattern_matches_its_credential_shape(label, sample):
    """A pattern that matches nothing protects nothing."""
    assert PATTERNS[label].search(sample.encode()), f"{label} did not match its own shape"


def test_patterns_do_not_fire_on_ordinary_text():
    """Specificity, same as everywhere else in this tree.

    A guard that flags every hex string gets disabled within a week, which is
    the failure mode that matters for a hook people can bypass with
    ``--no-verify``.
    """
    benign = (
        b"the commit is 9d3ab7bc0f1e2d3a4b5c6d7e8f90a1b2c3d4e5f6\n"
        b"digest 816672b4c412313e4ae4c7cbcda2cfb165206eb5fa20ca6aad81bb1e4896434d\n"
        b"export PATH=/usr/local/bin:$PATH\n"
        b"api_key = os.environ['SOME_KEY']\n"
        b"sk-or-v1-short\n"
    )
    for label, pattern in PATTERNS.items():
        assert not pattern.search(benign), f"{label} fired on ordinary text"


def test_a_broken_range_fails_loudly_rather_than_clean():
    """The bug that made the guard useless, pinned.

    ``scan`` must raise when git cannot resolve the revision range. If it ever
    returns ``[]`` here again, the pre-push hook silently permits everything.
    """
    with pytest.raises(RuntimeError):
        scan(["definitely-not-a-ref-9f8e7d..HEAD"])


def test_the_current_tree_is_clean():
    """This repository is public. It must carry no credential at any commit."""
    assert scan(["HEAD"]) == []


def test_the_hook_is_installed_and_executable():
    """A hook that is not installed is a document, not a guard."""
    hooks = subprocess.run(
        ["git", "rev-parse", "--git-path", "hooks"],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    import os

    hook = os.path.join(hooks, "pre-push")
    if not os.path.exists(hook):
        pytest.skip("pre-push hook not installed; run scripts/install_hooks.sh")
    assert os.access(hook, os.X_OK), f"{hook} is not executable"
