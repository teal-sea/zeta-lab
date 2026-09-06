"""Doc numbers are unique, and every reference to one resolves.

This file exists because of a real incident. On 2026-08-10 a session working
against a read-only snapshot of the tree added a second document numbered 21,
``21-the-local-positivity-attempt.md`` alongside the existing
``21-forward-deployed-verification.md``: and nothing in the suite noticed. The
tree carried two documents numbered 21 until a human spotted it.

(Doc filenames are written here without their ``docs/`` prefix on purpose:
with it, the examples below would match this file's own regexes.)

``AGENTS.md`` already states the rule the collision broke, "keep
cross-references consistent with actual filenames … a bare ``docs/08`` always
means ``08-why-it-is-hard.md``", and the repo has been here before: the
detector-strength findings once shared a number with ``08`` and had to be moved
to ``22``. A prose rule that has already been violated twice is a rule that
wants a test.

Three checks, cheapest first:

* numbers are unique, so a bare ``docs/NN`` is unambiguous by construction;
* every ``docs/NN-full-name.md`` reference points at a file that exists, so a
  rename cannot silently break a citation;
* every bare ``docs/NN`` reference names a document that exists.
"""

from __future__ import annotations

import os
import re

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = os.path.join(REPO_ROOT, "docs")

# Directories that hold generated output, vendored code or caches. Scanning
# them would report other people's text as this repository's defects.
_SKIP_DIRS = {
    ".git",
    ".venv",
    ".lake",
    ".pytest_cache",
    "__pycache__",
    "node_modules",
    "data",
    "figures",
    "conjectures",
    "automation",
    # agent worktrees and vendored outside checkouts live under these; each is
    # a whole other working tree whose docs/ numbering is its own business
    ".claude",
    "external",
}


def _is_other_checkout(path: str) -> bool:
    """A directory containing a `.git` entry is another working tree.

    Nested worktrees (``git worktree add`` writes a `.git` *file*) and vendored
    clones must not be scanned: their cross-references resolve against their
    own tree, not this one, and scanning them once double-reported a live
    worktree's docs as this repository's defects.
    """
    return os.path.exists(os.path.join(path, ".git"))

# Text we own and cite from. CONTEXT.md is generated, and is included on
# purpose: a stale generated index pointing at a renamed doc is still a defect.
_SCAN_SUFFIXES = {".md", ".py", ".txt", ".lean", ".sh"}

_NUMBERED_DOC = re.compile(r"^(\d{2})-[\w.-]+\.md$")
# A full filename reference: the docs prefix, then NN-some-name.md.
_FILENAME_REF = re.compile(r"docs/(\d{2}-[\w.-]+\.md)")
# A bare number, but not a filename reference and not the 4-digit 1000.yaml.
_BARE_REF = re.compile(r"docs/(\d{2})(?![\d\-\w])")


def _numbered_docs() -> dict[str, list[str]]:
    """Leading number -> the doc filenames carrying it."""
    by_number: dict[str, list[str]] = {}
    for name in sorted(os.listdir(DOCS)):
        m = _NUMBERED_DOC.match(name)
        if m:
            by_number.setdefault(m.group(1), []).append(name)
    return by_number


def _scanned_files() -> list[str]:
    found = []
    for dirpath, dirnames, filenames in os.walk(REPO_ROOT):
        dirnames[:] = [
            d
            for d in dirnames
            if d not in _SKIP_DIRS and not _is_other_checkout(os.path.join(dirpath, d))
        ]
        for name in filenames:
            if os.path.splitext(name)[1] in _SCAN_SUFFIXES:
                found.append(os.path.join(dirpath, name))
    return found


def test_no_two_docs_share_a_number() -> None:
    """The check the 2026-08-10 collision would have failed."""
    by_number = _numbered_docs()
    collisions = {n: names for n, names in by_number.items() if len(names) > 1}
    assert not collisions, (
        "two or more documents share a leading number, so every bare "
        f"`docs/NN` reference to them is ambiguous: {collisions}"
    )


def test_the_course_has_no_gap_that_hides_a_lost_document() -> None:
    """Numbers run 00..N with no hole.

    A hole is not automatically wrong, a doc can be withdrawn, but it is
    always worth a deliberate decision rather than an accident, and every hole
    to date has been one of the two collisions being resolved.
    """
    numbers = sorted(int(n) for n in _numbered_docs())
    assert numbers, "docs/ has no numbered documents"
    expected = list(range(numbers[0], numbers[-1] + 1))
    assert numbers == expected, (
        f"gap in the doc course: have {numbers}, expected {expected}. If a "
        "document was withdrawn on purpose, record it in ROADMAP.md and "
        "relax this test deliberately."
    )


def test_every_full_filename_reference_to_a_doc_resolves() -> None:
    """`docs/05-de-bruijn-newman.md` must name a file that exists."""
    existing = set(os.listdir(DOCS))
    dangling: dict[str, set[str]] = {}
    for path in _scanned_files():
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        for ref in set(_FILENAME_REF.findall(text)):
            if ref not in existing:
                rel = os.path.relpath(path, REPO_ROOT)
                dangling.setdefault(rel, set()).add(ref)
    assert not dangling, f"references to docs that do not exist: {dangling}"


def test_every_doc_heading_carries_its_own_number() -> None:
    """A document's H1 must agree with its filename.

    Added 2026-09-05, after `30-prime-zeta-rightmost-zeros.md` was found opening
    with `# 28: The rightmost zeros of the prime zeta function`. Nothing above
    could see it: the filenames were unique, the course had no gap, and every
    citation resolved. Only the text a reader actually sees was wrong, and it
    named a document that exists and is about something else, which is worse
    than naming nothing. Four other documents carried no number at all, so a
    reader arriving from a citation could not confirm they had landed right.

    The form is `# NN. Title`. The separator is fixed rather than tolerant on
    purpose: a rule that accepts four spellings is a rule nobody can apply from
    memory, and the repository has two collisions on record from exactly that.
    """
    wrong: dict[str, str] = {}
    for number, (name,) in sorted(_numbered_docs().items()):
        with open(os.path.join(DOCS, name), encoding="utf-8") as fh:
            heading = next((ln for ln in fh if ln.startswith("# ")), "")
        if not heading:
            wrong[name] = "no H1 heading at all"
        elif not heading.startswith(f"# {number}. "):
            wrong[name] = heading.strip()
    assert not wrong, (
        "these documents' headings disagree with their filenames; a heading is "
        f"what a reader sees, so it is the citation that matters most: {wrong}"
    )


def test_the_docs_index_lists_every_document() -> None:
    """`docs/README.md` is the index, and an index that omits is worse than none.

    An index nobody has to update is the only kind that stays true, and this
    one is hand-written, so it gets a test instead. A document absent from the
    index is unreachable for a reader who starts where the front page sends
    them, which is the failure that put 88 hunt documents and the whole working
    paper off the public site while they sat in a public tree.
    """
    index_path = os.path.join(DOCS, "README.md")
    assert os.path.isfile(index_path), "docs/README.md, the document index, is missing"
    with open(index_path, encoding="utf-8") as fh:
        index = fh.read()
    missing = [
        name for (name,) in (v for _, v in sorted(_numbered_docs().items()))
        if name not in index
    ]
    assert not missing, f"documents absent from docs/README.md: {missing}"


def test_every_bare_number_reference_names_a_document_that_exists() -> None:
    """`docs/08` must resolve, and uniqueness above makes it resolve to one."""
    known = set(_numbered_docs())
    dangling: dict[str, set[str]] = {}
    for path in _scanned_files():
        with open(path, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        for num in set(_BARE_REF.findall(text)):
            if num not in known:
                rel = os.path.relpath(path, REPO_ROOT)
                dangling.setdefault(rel, set()).add(f"docs/{num}")
    assert not dangling, f"bare references to docs that do not exist: {dangling}"
