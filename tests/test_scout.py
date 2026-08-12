"""The literature scout: passages, never verdicts.

Pins the three load-bearing properties: the report states exactly what was
and was not searched (absent corpora are loud, truncation is loud); a hit
never becomes ``FOUND`` (no code path in the module can emit one); and the
label survives ``funnel_label`` in both outcomes, so the funnel can never
hear novelty from a scout run.
"""

from __future__ import annotations

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from ontology.knownness import LiteratureStatus, funnel_label  # noqa: E402
from ontology.scout import (  # noqa: E402
    MAX_HITS_PER_CORPUS,
    CorpusSpec,
    LocalCorpusBackend,
    ScoutError,
    search_corpora,
)


@pytest.fixture()
def corpus(tmp_path: Path) -> CorpusSpec:
    root = tmp_path / "papers"
    root.mkdir()
    (root / "match.md").write_text(
        "A survey of pair correlation bounds.\n"
        "The montgomery pair correlation approach gives the constant.\n",
        encoding="utf-8",
    )
    (root / "other.md").write_text("nothing relevant here\n", encoding="utf-8")
    (root / "binary.bin").write_bytes(b"\x00montgomery\x00")
    return CorpusSpec(name="test corpus", path=root)


# ---------------------------------------------------------------------------
# 1. the report says what the search was
# ---------------------------------------------------------------------------


def test_a_hit_is_reported_with_its_passage(corpus: CorpusSpec) -> None:
    report = search_corpora(["montgomery", "pair correlation"], corpora=(corpus,))
    assert report.sources_searched == {"test corpus": 2}  # .bin not read
    assert report.sources_missing == ()
    assert len(report.hits) >= 1
    assert report.hits[0].path == "match.md"
    passages = " ".join(h.passage.casefold() for h in report.hits)
    assert "montgomery" in passages and "pair correlation" in passages
    assert "leads, not findings" in report.describe()


def test_no_hits_is_a_bounded_sentence(corpus: CorpusSpec) -> None:
    report = search_corpora(["nonexistent phrase xyzzy"], corpora=(corpus,))
    assert report.hits == ()
    text = report.describe()
    assert "no matching result located" in text
    assert "not about the literature" in text


def test_an_absent_corpus_is_loud(tmp_path: Path, corpus: CorpusSpec) -> None:
    ghost = CorpusSpec(name="ghost corpus", path=tmp_path / "not-there")
    report = search_corpora(["montgomery"], corpora=(corpus, ghost))
    assert report.sources_missing == ("ghost corpus",)
    assert "absent on this machine: ghost corpus" in report.describe()


def test_truncation_is_loud(tmp_path: Path) -> None:
    root = tmp_path / "many"
    root.mkdir()
    for i in range(MAX_HITS_PER_CORPUS + 5):
        (root / f"f{i:03d}.md").write_text("the term appears\n", encoding="utf-8")
    report = search_corpora(["term"], corpora=(CorpusSpec(name="many", path=root),))
    assert report.truncated == {"many": MAX_HITS_PER_CORPUS + 5}
    assert f"showing {MAX_HITS_PER_CORPUS} of" in report.describe()


def test_an_empty_query_is_refused(corpus: CorpusSpec) -> None:
    with pytest.raises(ScoutError, match="at least one non-empty term"):
        search_corpora(["  ", ""], corpora=(corpus,))


def test_matching_is_file_level_and_over_all_terms(corpus: CorpusSpec) -> None:
    # "montgomery" appears in match.md but "xyzzy" nowhere: AND fails.
    report = search_corpora(["montgomery", "xyzzy"], corpora=(corpus,))
    assert report.hits == ()


# ---------------------------------------------------------------------------
# 2. the gate adapter: conservative in the only safe direction
# ---------------------------------------------------------------------------


def _candidate(**claim) -> SimpleNamespace:
    return SimpleNamespace(claim=claim, label="")


def test_a_hit_does_not_become_found(corpus: CorpusSpec) -> None:
    backend = LocalCorpusBackend(corpora=(corpus,))
    result = backend.lookup(_candidate(subject="montgomery"))
    assert result.status is LiteratureStatus.NOT_FOUND
    assert result.sources_queried == ("test corpus",)
    assert "candidate passage" in result.detail
    assert result.establishes_novelty is False


def test_no_hit_is_not_found_with_sources_named(corpus: CorpusSpec) -> None:
    backend = LocalCorpusBackend(corpora=(corpus,))
    result = backend.lookup(_candidate(subject="xyzzy nonesuch"))
    assert result.status is LiteratureStatus.NOT_FOUND
    assert result.sources_queried == ("test corpus",)
    assert "no matching result located" in result.detail


def test_a_textless_candidate_means_no_lookup_ran(corpus: CorpusSpec) -> None:
    backend = LocalCorpusBackend(corpora=(corpus,))
    result = backend.lookup(SimpleNamespace(claim={"n": 7}, label=""))
    assert result.status is LiteratureStatus.UNKNOWN
    assert "no lookup ran" in result.detail


def test_all_corpora_absent_means_unknown(tmp_path: Path) -> None:
    ghost = CorpusSpec(name="ghost", path=tmp_path / "nope")
    backend = LocalCorpusBackend(corpora=(ghost,))
    result = backend.lookup(_candidate(subject="anything"))
    assert result.status is LiteratureStatus.UNKNOWN
    assert "nothing was searched" in result.detail


def test_the_module_has_no_route_to_found() -> None:
    import ast
    import inspect

    import ontology.scout as scout

    tree = ast.parse(inspect.getsource(scout))
    found_refs = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr == "FOUND"
    ]
    assert found_refs == [], (
        "ontology.scout references LiteratureStatus.FOUND: the scout must "
        "never assert prior art itself — a human registers a confirmed match"
    )


def test_both_outcomes_survive_the_funnel_label_gate(corpus: CorpusSpec) -> None:
    backend = LocalCorpusBackend(corpora=(corpus,))
    for subject in ("montgomery", "xyzzy nonesuch"):
        result = backend.lookup(_candidate(subject=subject))
        assert funnel_label(result.label) == result.label
