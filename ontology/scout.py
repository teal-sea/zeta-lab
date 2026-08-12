"""``ontology.scout`` — the literature scout: passages, never verdicts.

The adopted contract (`ROADMAP.md`, "The outside memos, triaged", deferred
list — contract adopted in advance of the build): the scout's output is
*databases searched, sources inspected, candidate matches, unresolved
ambiguity, and "no matching result located"* — never the word the funnel is
forbidden to hear. Failure to find prior art is not proof of novelty, and a
lexical hit is not proof of prior art; both directions stay open until a
human adjudicates, and this module is built so neither can be collapsed by
code.

What it searches is whatever corpora the machine actually has. The tracked
tree carries ``references/``; a machine that has run the ecosystem fetch
(``external/README.md``) also carries DeepMind's formal-conjectures
collection and the AlphaProof Nexus proof corpus — kernel-checked prior art
of exactly the kind worth colliding with. A corpus that is absent is
reported in ``sources_missing``, loudly: a scout that silently searched less
than it names would be the W2 failure mode wearing a new hat.

How the result feeds the gate: :class:`LocalCorpusBackend` adapts a scout
run to :class:`ontology.knownness.LiteratureBackend`. The mapping is
deliberately conservative in the only safe direction —

* **no hits** → ``NOT_FOUND`` with the sources named (a true statement:
  these corpora were searched and nothing matched; the label remains
  ``not-recognised-offline`` and no funnel may read it as more);
* **hits** → still ``NOT_FOUND``, with every candidate passage carried in
  ``detail``. A grep hit does not establish that the observation *is* the
  literature's — claiming ``FOUND`` would manufacture a terminal ``known``
  verdict out of a substring. The passages are for a human, whose confirmed
  match enters the :class:`~ontology.knownness.KnownFactRegistry`, which is
  the one honest route from "looks like prior art" to "is prior art".

Like :mod:`ontology.knownness`, this module is domain-neutral: standard
library only, plus the backend interface it adapts to. It knows *where
corpora live*, not what the laboratory studies; the caller brings the query
terms.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import Final

from ontology.knownness import (
    NOT_RECOGNISED_OFFLINE,
    LiteratureBackend,
    LiteratureResult,
    LiteratureStatus,
)

__all__ = [
    "CorpusSpec",
    "DEFAULT_CORPORA",
    "LocalCorpusBackend",
    "ScoutError",
    "ScoutReport",
    "SourceHit",
    "search_corpora",
]


class ScoutError(ValueError):
    """A scout invocation that cannot mean anything."""


_REPO_ROOT: Final[Path] = Path(__file__).resolve().parent.parent

_TEXT_SUFFIXES: Final[frozenset[str]] = frozenset(
    {".md", ".txt", ".lean", ".py", ".json", ".yaml", ".yml", ".tex"}
)

#: Per-corpus cap on reported hits. The cap is not silent: a truncated corpus
#: says so in the report, with the total count.
MAX_HITS_PER_CORPUS: Final[int] = 20


@dataclass(frozen=True)
class CorpusSpec:
    """One searchable corpus: a name a report can cite, and where it lives."""

    name: str
    path: Path
    note: str = ""


#: What a fully-fetched machine can search. Order is citation order.
DEFAULT_CORPORA: Final[tuple[CorpusSpec, ...]] = (
    CorpusSpec(
        name="references (tracked)",
        path=_REPO_ROOT / "references",
        note="the repository's own curated reference list",
    ),
    CorpusSpec(
        name="formal-conjectures (DeepMind)",
        path=_REPO_ROOT / "external" / "formal-conjectures",
        note="open conjectures stated in Lean; machine state, see external/README.md",
    ),
    CorpusSpec(
        name="alphaproof-nexus-results (DeepMind)",
        path=_REPO_ROOT / "external" / "alphaproof-nexus-results",
        note="kernel-checked Lean proofs and prose proofs; machine state",
    ),
    CorpusSpec(
        name="alphaevolve problems (DeepMind)",
        path=_REPO_ROOT / "external" / "alphaevolve_repository_of_problems",
        note="the AlphaEvolve problem suite; machine state",
    ),
)


@dataclass(frozen=True)
class SourceHit:
    """One candidate passage. A passage is a lead, not a finding."""

    corpus: str
    path: str
    line_no: int
    passage: str


@dataclass(frozen=True)
class ScoutReport:
    """What was searched, what was absent, and every passage located.

    ``sources_searched`` maps corpus name to the number of files actually
    read; ``sources_missing`` names the corpora this machine does not have.
    ``truncated`` names corpora whose hits exceeded the cap, with totals, so
    a bounded report never reads as an exhaustive one. There is no novelty
    field, no significance field, and no boolean that summarises the search:
    ``hits`` is evidence to adjudicate, and an empty ``hits`` is the sentence
    "no matching result located in the corpora searched" — nothing more.
    """

    terms: tuple[str, ...]
    sources_searched: dict[str, int] = field(default_factory=dict)
    sources_missing: tuple[str, ...] = ()
    hits: tuple[SourceHit, ...] = ()
    truncated: dict[str, int] = field(default_factory=dict)

    def describe(self) -> str:
        searched = (
            ", ".join(f"{name} ({n} files)" for name, n in self.sources_searched.items())
            or "nothing"
        )
        lines = [f"searched: {searched}"]
        if self.sources_missing:
            lines.append(f"absent on this machine: {', '.join(self.sources_missing)}")
        if self.hits:
            lines.append(f"{len(self.hits)} candidate passage(s) — leads, not findings:")
            lines.extend(
                f"  {h.corpus}: {h.path}:{h.line_no}: {h.passage}" for h in self.hits
            )
        else:
            lines.append(
                "no matching result located in the corpora searched — which is "
                "a statement about these corpora, not about the literature"
            )
        for name, total in self.truncated.items():
            lines.append(
                f"  ({name}: showing {MAX_HITS_PER_CORPUS} of {total} matching files)"
            )
        return "\n".join(lines)


def _clean_terms(terms) -> tuple[str, ...]:
    cleaned = tuple(
        t.strip().casefold() for t in terms if isinstance(t, str) and t.strip()
    )
    if not cleaned:
        raise ScoutError(
            "the scout needs at least one non-empty term: an empty query "
            "matching everything would report the corpus, not the candidate"
        )
    return cleaned


def search_corpora(
    terms,
    corpora: tuple[CorpusSpec, ...] = DEFAULT_CORPORA,
) -> ScoutReport:
    """Search every available corpus for files containing *all* terms.

    Matching is case-insensitive substring containment, file-level AND over
    the terms — crude on purpose: the scout's job is recall of leads for a
    human, and the report says exactly what the search was so "not located"
    is bounded by it. Passages quoted are the first lines containing any
    term, up to three per file.
    """

    cleaned = _clean_terms(terms)
    searched: dict[str, int] = {}
    missing: list[str] = []
    hits: list[SourceHit] = []
    truncated: dict[str, int] = {}
    for corpus in corpora:
        if not corpus.path.is_dir():
            missing.append(corpus.name)
            continue
        files_read = 0
        matching_files = 0
        for dirpath, dirnames, filenames in os.walk(corpus.path):
            dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            for filename in sorted(filenames):
                path = Path(dirpath) / filename
                if path.suffix.lower() not in _TEXT_SUFFIXES:
                    continue
                try:
                    text = path.read_text(encoding="utf-8", errors="ignore")
                except OSError:  # pragma: no cover - unreadable file
                    continue
                files_read += 1
                lowered = text.casefold()
                if not all(term in lowered for term in cleaned):
                    continue
                matching_files += 1
                if matching_files > MAX_HITS_PER_CORPUS:
                    continue
                rel = str(path.relative_to(corpus.path))
                quoted = 0
                for line_no, line in enumerate(text.splitlines(), 1):
                    if quoted >= 3:
                        break
                    line_l = line.casefold()
                    if any(term in line_l for term in cleaned):
                        hits.append(
                            SourceHit(
                                corpus=corpus.name,
                                path=rel,
                                line_no=line_no,
                                passage=line.strip()[:200],
                            )
                        )
                        quoted += 1
        searched[corpus.name] = files_read
        if matching_files > MAX_HITS_PER_CORPUS:
            truncated[corpus.name] = matching_files
    return ScoutReport(
        terms=cleaned,
        sources_searched=searched,
        sources_missing=tuple(missing),
        hits=tuple(hits),
        truncated=truncated,
    )


class LocalCorpusBackend(LiteratureBackend):
    """The scout as a :func:`ontology.knownness.check_literature` backend.

    Both outcomes map to ``NOT_FOUND`` — see the module docstring for why a
    lexical hit must not become ``FOUND``. The passages ride in ``detail``;
    the one honest route from a hit to a ``known`` verdict is a human
    confirming the match and registering it as a cited fact.
    """

    name = "local-corpus-scout"
    online = False

    def __init__(self, corpora: tuple[CorpusSpec, ...] = DEFAULT_CORPORA) -> None:
        self.corpora = corpora

    @staticmethod
    def _terms_from(candidate) -> tuple[str, ...]:
        terms = [
            value
            for value in getattr(candidate, "claim", {}).values()
            if isinstance(value, str) and value.strip()
        ]
        label = getattr(candidate, "label", "")
        if isinstance(label, str) and label.strip():
            terms.append(label)
        return tuple(terms)

    def lookup(self, candidate) -> LiteratureResult:
        terms = self._terms_from(candidate)
        if not terms:
            return LiteratureResult(
                status=LiteratureStatus.UNKNOWN,
                label=NOT_RECOGNISED_OFFLINE,
                backend=self.name,
                online=False,
                detail=(
                    "the candidate's claim carries no searchable text, so no "
                    "lookup ran"
                ),
            )
        report = search_corpora(terms, corpora=self.corpora)
        if not report.sources_searched:
            return LiteratureResult(
                status=LiteratureStatus.UNKNOWN,
                label=NOT_RECOGNISED_OFFLINE,
                backend=self.name,
                online=False,
                detail=(
                    "no corpus is present on this machine (see "
                    "external/README.md); nothing was searched"
                ),
            )
        return LiteratureResult(
            status=LiteratureStatus.NOT_FOUND,
            label=NOT_RECOGNISED_OFFLINE,
            backend=self.name,
            online=False,
            sources_queried=tuple(report.sources_searched),
            detail=report.describe(),
        )
