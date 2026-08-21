"""Every Python file `docs/` points a reader at must exist.

`docs/` is the reading course: a document that says "in
`discovery/01_f1_geometry.py`, we built the scaffolding" is an instruction,
and a reader who follows it lands on nothing.  That exact sentence stood in
`docs/15-the-f1-discovery-engine.md` from the rename of `discovery/` to
`ontology/` until 2026-08-21, together with two more references to the dead
directory, and nothing in the suite noticed: `scripts/make_context.py
--check` indexes what exists rather than what is cited, and the site
generator publishes prose without resolving it.

Scope, deliberately narrow so the guard has no allowlist to rot:

* **`.py` citations only.**  Markdown, Lean and JSON paths in `docs/` are
  frequently relative to a package root (`ZetaLean/DHAnalytic.lean` under
  `lean/`, `zeta23ext/...` under `hunts/frontier_math/`) or belong to another
  repository entirely, so requiring them to resolve from the repo root would
  encode a convention the tree does not keep.
* **`docs/` only.**  A hunt write-up legitimately names files that never
  existed: `hunts/r_c35cd1/RESULTS.md` discusses planted paths like
  `tests/mutant_helper.py` as *examples of what a guard fails to see*, and a
  scan that failed on those would be measuring the wrong thing.

The guard is therefore one rule with zero exceptions rather than a wide rule
with a list of them.
"""

from __future__ import annotations

import pathlib
import re

REPO = pathlib.Path(__file__).resolve().parent.parent
DOCS = REPO / "docs"

#: A backticked path with a directory component and a `.py` suffix.  The
#: directory component is what makes it a repo-root-relative citation rather
#: than a bare module name mentioned in passing.
_CITATION = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*/[A-Za-z0-9_./-]*\.py)`")


def _citations() -> list[tuple[pathlib.Path, str]]:
    found = []
    for document in sorted(DOCS.rglob("*.md")):
        text = document.read_text(encoding="utf-8")
        for match in _CITATION.finditer(text):
            found.append((document, match.group(1)))
    return found


def test_the_scan_finds_something_to_check() -> None:
    """A guard that matches nothing passes for the wrong reason."""
    citations = _citations()
    assert len(citations) > 50, f"only {len(citations)} citations found; the regex has drifted"


def test_every_cited_python_file_exists() -> None:
    missing = sorted(
        {f"{document.relative_to(REPO)} -> {cited}"
         for document, cited in _citations()
         if not (REPO / cited).exists()}
    )
    assert not missing, "docs/ cites Python files that do not exist:\n  " + "\n  ".join(missing)
