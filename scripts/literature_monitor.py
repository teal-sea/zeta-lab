#!/usr/bin/env python3
"""A standing literature watch on the lab's own subject. arXiv to GitHub issues.

Why this exists
---------------
``meta/literature-monitor.md`` records the incident: Biao Wang posted
arXiv:2609.07918 on 2026-09-07, the short-interval version of the theorem every
Palomar entry in this laboratory is built on, and the lab learned of it five
days later from a stranger's email. Nothing in this tree watched the
literature. ``ontology/scout_online.py`` can ask arXiv about a candidate it is
handed; nothing asked arXiv what had landed.

What it does
------------
One scheduled job (``.github/workflows/literature-monitor.yml``). For each
query in :data:`QUERIES` it asks the arXiv API for the most recent submissions,
newest first, pages back until it has covered the lookback window, and keeps
the entries whose submission date falls inside it. It then

* opens one GitHub issue per paper that is not cited anywhere in the tree and
  not mentioned in any existing issue (dedup state is the issue list, not a
  committed file: it survives a clean checkout and needs no write-back), and
* opens one issue per *new version* of a paper the tree already cites, because
  a v2 of a load-bearing source is as interesting as a new paper.

The issue body carries identifier, title, authors, submission date, abstract,
the queries that matched, and a link. No assessment. The monitor reports that a
paper exists; a session decides whether it matters.

It fails closed
---------------
``scripts/check_secrets.py`` once failed open and ``CLAUDE.md`` records the
cost. This script has the same failure shape, because an empty result is the
normal state on a quiet day and also what a broken query, a changed schema, a
network failure and an expired token look like. So:

* an HTTP error, a parse failure, or a zero-entry response to a query that
  the recorded baseline (``tests/fixtures/literature_monitor/baseline.json``)
  says has never returned zero, fails the run with the query named;
* a failed dedup lookup fails the run rather than opening duplicates or
  silently opening nothing;
* every query is reported as either ``queried`` (with counts) or
  ``DID NOT QUERY`` (with the error), never as a bare "no new papers".

Usage
-----
    python scripts/literature_monitor.py --dry-run                # print, open nothing
    python scripts/literature_monitor.py --since 2026-09-01 --until 2026-09-12 --dry-run
    python scripts/literature_monitor.py --fixture tests/fixtures/literature_monitor --dry-run
    python scripts/literature_monitor.py --record tests/fixtures/literature_monitor --since ... --until ...

Standard library only. Follows the fetch pattern of
``ontology.scout_online.ArxivBackend`` (urllib, injectable fetch, an honest
"did not reach" path) without importing it: ``ontology/`` is domain-agnostic
and this script is nothing but subject matter.

Author queries are deliberately absent from :data:`QUERIES`. See the note at
:data:`AUTHOR_WATCH_UNVERIFIED` for why.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import Callable

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ARXIV_API = "https://export.arxiv.org/api/query"
GITHUB_API = "https://api.github.com"
USER_AGENT = "zeta-lab-literature-monitor/0.1 (research tool; spaced queries)"

#: arXiv's stated courtesy limit is one request every three seconds. Every
#: network request in this script goes through :func:`_spaced`, which enforces
#: at least this gap between consecutive calls.
SPACING_SECONDS = 3.0

#: How many entries one page asks for and how many pages one query may walk
#: before the run refuses to claim it covered the window.
PAGE_SIZE = 100
MAX_PAGES = 10

#: How far back a scheduled run looks. Seven days, so that a Friday submission
#: announced on Monday is seen even if one weekday run is lost, and so that a
#: dedup miss is bounded rather than repeated forever.
DEFAULT_LOOKBACK_DAYS = 7

#: The primary category filter. math.NT is where the race is; the brief lists
#: math.CA, math.SP and cs.LO as lower-weight candidates for the analysis and
#: formalization sides. They are included as a disjunction, at the same weight,
#: because the monitor has no weights: it reports, a session decides.
CATEGORIES = ("math.NT", "math.CA", "math.SP", "cs.LO")
CATEGORY_CLAUSE = "(" + " OR ".join(f"cat:{c}" for c in CATEGORIES) + ")"

#: The label the monitor puts on every issue it opens.
ISSUE_LABEL = "literature"

#: The recorded baseline: query name to the number of entries its first page
#: returned when the fixtures were recorded. A query listed here with a
#: positive count that now returns zero entries is treated as broken, not quiet.
BASELINE_PATH = os.path.join(ROOT, "tests", "fixtures", "literature_monitor", "baseline.json")

#: Directories never searched for citations. The fixture directory is skipped
#: because it contains the very ids the scan returns, and treating those as
#: citations would make every fixture paper look already known.
SKIP_DIRS = frozenset(
    {".git", ".venv", "venv", "__pycache__", ".lake", ".pytest_cache", "node_modules",
     ".claude", "figures", "data"}
)
SKIP_PATH_PREFIXES = (os.path.join("tests", "fixtures", "literature_monitor"),)
TEXT_SUFFIXES = (".md", ".py", ".lean", ".txt", ".json", ".yml", ".yaml", ".tex",
                 ".bib", ".rst", ".html", ".toml", ".cfg", ".jsonl")

ARXIV_ID_RE = re.compile(r"(?<![0-9])(\d{4}\.\d{4,5})(v\d+)?(?![0-9])")
ARXIV_CITATION_RE = re.compile(r"arXiv:\s?(\d{4}\.\d{4,5})(v\d+)?", re.IGNORECASE)


@dataclass(frozen=True)
class Query:
    """One narrow arXiv query. ``name`` is what reports and fixtures key on."""

    name: str
    search: str

    def full(self) -> str:
        return f"{self.search} AND {CATEGORY_CLAUSE}"


#: The union of narrow queries. Single queries have blind spots that the
#: calibration in meta/literature-monitor.md section 2 measured before any code
#: was written: ``all:"simple zeros"`` misses Wang (who writes "simple critical
#: zeros") and ``all:"simple critical zeros"`` misses Lamzouri. Both are here,
#: and tests/test_literature_monitor.py pins that removing either fails.
QUERIES: tuple[Query, ...] = (
    Query("pair-correlation", 'all:"pair correlation"'),
    Query("simple-zeros", 'all:"simple zeros"'),
    Query("simple-critical-zeros", 'all:"simple critical zeros"'),
    Query("critical-line", 'abs:"critical line"'),
    Query("zeros-of-the-riemann-zeta", 'all:"zeros of the Riemann zeta"'),
    Query("de-bruijn-newman", 'all:"de Bruijn-Newman"'),
    Query("davenport-heilbronn", 'all:"Davenport-Heilbronn"'),
    Query("li-criterion", 'all:"Li\'s criterion"'),
    Query("mollifier", "all:mollifier"),
    Query("form-factor", 'all:"form factor" AND all:zeta'),
    Query("short-intervals-zeta", 'all:"short intervals" AND all:zeta'),
)

#: Author watches the brief asks for, NOT enabled. The brief records that
#: ``au:Wang_B`` with a category filter returned nothing, and the arXiv API was
#: rate-limiting (HTTP 429) throughout the build session, so no author syntax
#: could be verified against a known paper. An unverified author query is worse
#: than none: it would report a clean run while watching nobody. When the API
#: is reachable, run ``--verify-authors`` and move each entry that returns its
#: known paper into :data:`QUERIES` as ``Query("au-<name>", "au:...")``.
AUTHOR_WATCH_UNVERIFIED: tuple[tuple[str, str, str], ...] = (
    # (candidate search, a paper that author is known to have posted, author)
    ("au:Lamzouri", "2609.02882", "Lamzouri"),
    ('au:"Wang, Biao"', "2609.07918", "Biao Wang"),
    ("au:Baluyot", "", "Baluyot"),
    ("au:Goldston", "", "Goldston"),
    ("au:Suriajaya", "", "Suriajaya"),
    ("au:Turnage-Butterbaugh", "", "Turnage-Butterbaugh"),
    ("au:Chirre", "", "Chirre"),
    ("au:Goncalves", "", "Goncalves"),
    ('au:"de Laat"', "", "de Laat"),
    ("au:Bui", "", "Bui"),
    ("au:Conrey", "", "Conrey"),
    ("au:Pratt", "", "Pratt"),
    ("au:Farmer", "", "Farmer"),
    ("au:Gonek", "", "Gonek"),
    ("au:Lee", "", "Lee"),
)


@dataclass
class Paper:
    """One arXiv entry, as parsed. ``version`` is the integer after ``v``."""

    ident: str
    version: int
    title: str
    authors: tuple[str, ...]
    published: str  # ISO date of v1 submission
    updated: str  # ISO date of the latest version
    summary: str
    primary_category: str
    matched: list[str] = field(default_factory=list)

    @property
    def link(self) -> str:
        return f"https://arxiv.org/abs/{self.ident}v{self.version}"

    @property
    def versioned(self) -> str:
        return f"{self.ident}v{self.version}"


class MonitorError(Exception):
    """A failure the run must surface as non-zero exit, with the query named."""


# ---------------------------------------------------------------------------
# fetching: live, recorded, and replayed
# ---------------------------------------------------------------------------

Fetch = Callable[[str], str]

_last_request_at = [0.0]


def _spaced() -> None:
    """Enforce the courtesy gap between consecutive network requests."""
    gap = SPACING_SECONDS - (time.monotonic() - _last_request_at[0])
    if gap > 0:
        time.sleep(gap)
    _last_request_at[0] = time.monotonic()


def _live_fetch(url: str, timeout: float = 60.0, retries: int = 4) -> str:
    """GET ``url`` with the courtesy gap, retrying 429/503 with backoff.

    Any failure after the retries raises; the caller turns that into a named
    ``DID NOT QUERY`` line. Nothing here returns an empty string on error.
    """
    last: Exception | None = None
    for attempt in range(retries + 1):
        _spaced()
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                return response.read().decode("utf-8", errors="replace")
        except urllib.error.HTTPError as exc:
            last = exc
            if exc.code not in (429, 503) or attempt == retries:
                raise
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            last = exc
            if attempt == retries:
                raise
        time.sleep(SPACING_SECONDS * (2 ** attempt))
    assert last is not None  # unreachable: the loop returns or raises
    raise last


def _request_key(params: dict[str, str]) -> str:
    """Deterministic key for a request, used to name recorded responses."""
    canonical = urllib.parse.urlencode(sorted(params.items()))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


class FixtureFetch:
    """Replay recorded responses. A request with no recording is a failure,
    not an empty result: a fixture run must never look like a quiet day."""

    def __init__(self, directory: str) -> None:
        self.directory = directory
        manifest = os.path.join(directory, "manifest.json")
        if not os.path.exists(manifest):
            raise MonitorError(f"fixture directory {directory} has no manifest.json")
        with open(manifest, encoding="utf-8") as fh:
            self.manifest: dict[str, dict] = json.load(fh)

    def __call__(self, params: dict[str, str]) -> str:
        key = _request_key(params)
        record = self.manifest.get(key)
        if record is None:
            raise MonitorError(
                f"no recorded response for request {params!r} (key {key})"
            )
        status = int(record.get("status", 200))
        if status != 200:
            raise urllib.error.HTTPError(
                ARXIV_API, status, f"recorded HTTP {status}", hdrs=None, fp=None  # type: ignore[arg-type]
            )
        with open(os.path.join(self.directory, record["file"]), encoding="utf-8") as fh:
            return fh.read()


class RecordingFetch:
    """Live fetch that also writes every response into a fixture directory."""

    def __init__(self, directory: str) -> None:
        self.directory = directory
        os.makedirs(directory, exist_ok=True)
        self.manifest_path = os.path.join(directory, "manifest.json")
        self.manifest: dict[str, dict] = {}
        if os.path.exists(self.manifest_path):
            with open(self.manifest_path, encoding="utf-8") as fh:
                self.manifest = json.load(fh)

    def __call__(self, params: dict[str, str]) -> str:
        key = _request_key(params)
        if key in self.manifest and os.path.exists(
            os.path.join(self.directory, self.manifest[key]["file"])
        ):
            with open(os.path.join(self.directory, self.manifest[key]["file"]), encoding="utf-8") as fh:
                return fh.read()
        body = _live_fetch(ARXIV_API + "?" + urllib.parse.urlencode(params))
        name = _fixture_name(params, key)
        with open(os.path.join(self.directory, name), "w", encoding="utf-8") as fh:
            fh.write(body)
        self.manifest[key] = {"file": name, "status": 200, "params": params}
        with open(self.manifest_path, "w", encoding="utf-8") as fh:
            json.dump(self.manifest, fh, indent=2, sort_keys=True)
            fh.write("\n")
        return body


def _fixture_name(params: dict[str, str], key: str) -> str:
    if "id_list" in params:
        return f"ids-{key}.xml"
    slug = re.sub(r"[^a-z0-9]+", "-", params.get("search_query", "q").lower()).strip("-")[:60]
    return f"q-{slug}-start{params.get('start', '0')}-{key}.xml"


def _live(params: dict[str, str]) -> str:
    return _live_fetch(ARXIV_API + "?" + urllib.parse.urlencode(params))


ParamFetch = Callable[[dict[str, str]], str]


# ---------------------------------------------------------------------------
# parsing
# ---------------------------------------------------------------------------

_NS = {
    "atom": "http://www.w3.org/2005/Atom",
    "opensearch": "http://a9.com/-/spec/opensearch/1.1/",
    "arxiv": "http://arxiv.org/schemas/atom",
}


def _text(node: ET.Element | None) -> str:
    return " ".join((node.text or "").split()) if node is not None else ""


def parse_feed(atom: str, context: str) -> tuple[int | None, list[Paper]]:
    """Parse one Atom page. Raises :class:`MonitorError` naming ``context`` on
    anything that is not a well-formed arXiv feed."""
    try:
        root = ET.fromstring(atom)
    except ET.ParseError as exc:
        raise MonitorError(f"{context}: response is not well-formed XML: {exc}") from exc
    if root.tag != f"{{{_NS['atom']}}}feed":
        raise MonitorError(f"{context}: response root is {root.tag!r}, not an Atom feed")
    total_node = root.find("opensearch:totalResults", _NS)
    total = int(total_node.text) if total_node is not None and (total_node.text or "").strip().isdigit() else None
    papers: list[Paper] = []
    for entry in root.findall("atom:entry", _NS):
        raw_id = _text(entry.find("atom:id", _NS))
        match = ARXIV_ID_RE.search(raw_id)
        if match is None:
            # arXiv answers a malformed query with a single entry whose id is
            # an api URL and whose title is "Error". That is an error, not a paper.
            title = _text(entry.find("atom:title", _NS))
            raise MonitorError(f"{context}: entry without an arXiv id (title {title!r}, id {raw_id!r})")
        ident, suffix = match.group(1), match.group(2)
        version = int(suffix[1:]) if suffix else 1
        primary = entry.find("arxiv:primary_category", _NS)
        papers.append(
            Paper(
                ident=ident,
                version=version,
                title=_text(entry.find("atom:title", _NS)),
                authors=tuple(_text(a.find("atom:name", _NS)) for a in entry.findall("atom:author", _NS)),
                published=_text(entry.find("atom:published", _NS))[:10],
                updated=_text(entry.find("atom:updated", _NS))[:10],
                summary=_text(entry.find("atom:summary", _NS)),
                primary_category=primary.get("term", "") if primary is not None else "",
            )
        )
    return total, papers


# ---------------------------------------------------------------------------
# the scan
# ---------------------------------------------------------------------------


@dataclass
class QueryReport:
    name: str
    queried: bool
    error: str = ""
    pages: int = 0
    entries: int = 0  # entries returned across pages
    in_window: int = 0


def _query_params(query: Query, start: int) -> dict[str, str]:
    return {
        "search_query": query.full(),
        "start": str(start),
        "max_results": str(PAGE_SIZE),
        "sortBy": "submittedDate",
        "sortOrder": "descending",
    }


def run_query(
    query: Query,
    fetch: ParamFetch,
    since: str,
    until: str,
    baseline: dict[str, int],
) -> tuple[QueryReport, list[Paper]]:
    """Walk one query newest-first until the window is covered.

    Returns the report and the papers whose ``published`` date lies in
    ``[since, until]``. Raises nothing: every failure lands in the report with
    ``queried=False`` and the reason, so the caller can name the query.
    """
    report = QueryReport(name=query.name, queried=False)
    kept: list[Paper] = []
    try:
        start = 0
        covered = False
        while report.pages < MAX_PAGES:
            atom = fetch(_query_params(query, start))
            total, papers = parse_feed(atom, f"query {query.name!r} start={start}")
            report.pages += 1
            report.entries += len(papers)
            if not papers:
                if start == 0 and baseline.get(query.name, 1) > 0:
                    raise MonitorError(
                        f"query {query.name!r} returned zero entries; the recorded "
                        f"baseline says it has never returned zero (total reported: {total})"
                    )
                covered = True
                break
            for paper in papers:
                if since <= paper.published <= until:
                    paper.matched.append(query.name)
                    kept.append(paper)
            oldest = min(p.published for p in papers)
            if oldest < since or len(papers) < PAGE_SIZE:
                covered = True
                break
            start += PAGE_SIZE
        if not covered:
            raise MonitorError(
                f"query {query.name!r}: {report.pages} pages of {PAGE_SIZE} did not reach "
                f"back to {since}; the window is not covered and the run will not pretend it is"
            )
        report.queried = True
        report.in_window = len(kept)
    except urllib.error.HTTPError as exc:
        report.error = f"HTTP {exc.code} from arXiv"
    except MonitorError as exc:
        report.error = str(exc)
    except Exception as exc:  # noqa: BLE001, every failure is named, none is swallowed
        report.error = f"{exc.__class__.__name__}: {exc}"
    return report, kept


def scan(
    fetch: ParamFetch,
    since: str,
    until: str,
    queries: tuple[Query, ...] = QUERIES,
    baseline: dict[str, int] | None = None,
) -> tuple[list[QueryReport], dict[str, Paper]]:
    """Run every query; merge hits by identifier, recording which queries matched."""
    baseline = baseline if baseline is not None else load_baseline()
    reports: list[QueryReport] = []
    hits: dict[str, Paper] = {}
    for query in queries:
        report, papers = run_query(query, fetch, since, until, baseline)
        reports.append(report)
        for paper in papers:
            known = hits.get(paper.ident)
            if known is None:
                hits[paper.ident] = paper
            else:
                known.matched.extend(m for m in paper.matched if m not in known.matched)
    return reports, hits


def load_baseline(path: str = BASELINE_PATH) -> dict[str, int]:
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    return {str(k): int(v) for k, v in data.items()}


# ---------------------------------------------------------------------------
# what the tree already cites, and version tracking
# ---------------------------------------------------------------------------


def cited_in_tree(root: str = ROOT) -> dict[str, int]:
    """Every ``arXiv:NNNN.NNNNN[vN]`` citation in the tree, to the highest
    version suffix cited (0 when only bare citations exist)."""
    cited: dict[str, int] = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        rel = os.path.relpath(dirpath, root)
        if any(rel == p or rel.startswith(p + os.sep) for p in SKIP_PATH_PREFIXES):
            dirnames[:] = []
            continue
        for filename in filenames:
            if not filename.endswith(TEXT_SUFFIXES):
                continue
            path = os.path.join(dirpath, filename)
            try:
                with open(path, encoding="utf-8", errors="replace") as fh:
                    text = fh.read()
            except OSError:
                continue
            for match in ARXIV_CITATION_RE.finditer(text):
                ident, suffix = match.group(1), match.group(2)
                version = int(suffix[1:]) if suffix else 0
                cited[ident] = max(cited.get(ident, 0), version)
    return cited


@dataclass
class VersionReport:
    queried: bool
    error: str = ""
    checked: int = 0


def check_versions(
    cited: dict[str, int],
    fetch: ParamFetch,
    since: str,
    until: str,
    batch: int = 50,
) -> tuple[VersionReport, list[tuple[Paper, int]]]:
    """Ask arXiv for the latest version of every cited paper.

    A cited paper earns a version issue when either the tree names a version
    lower than the latest, or the tree cites it bare and a version above v1
    landed inside the window. Returns ``(report, [(paper, cited_version)])``.
    """
    report = VersionReport(queried=False)
    updates: list[tuple[Paper, int]] = []
    idents = sorted(cited)
    try:
        for i in range(0, len(idents), batch):
            chunk = idents[i : i + batch]
            params = {"id_list": ",".join(chunk), "max_results": str(len(chunk))}
            total, papers = parse_feed(fetch(params), f"id_list batch starting {chunk[0]}")
            if not papers:
                raise MonitorError(
                    f"id_list batch starting {chunk[0]} returned zero entries for "
                    f"{len(chunk)} known identifiers"
                )
            report.checked += len(papers)
            for paper in papers:
                cited_version = cited.get(paper.ident, 0)
                if cited_version and paper.version > cited_version:
                    updates.append((paper, cited_version))
                elif not cited_version and paper.version > 1 and since <= paper.updated <= until:
                    updates.append((paper, cited_version))
        report.queried = True
    except urllib.error.HTTPError as exc:
        report.error = f"HTTP {exc.code} from arXiv"
    except MonitorError as exc:
        report.error = str(exc)
    except Exception as exc:  # noqa: BLE001
        report.error = f"{exc.__class__.__name__}: {exc}"
    return report, updates


# ---------------------------------------------------------------------------
# dedup against the issue list, and issue creation
# ---------------------------------------------------------------------------


def _github(method: str, path: str, payload: dict | None = None) -> object:
    """One authenticated GitHub API call. The token is read here, at call
    time, and never stored on the object or written anywhere."""
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise MonitorError("GITHUB_TOKEN is not set; cannot reach the issue list")
    body = json.dumps(payload).encode("utf-8") if payload is not None else None
    request = urllib.request.Request(
        GITHUB_API + path,
        data=body,
        method=method,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": USER_AGENT,
            "Content-Type": "application/json",
        },
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.loads(response.read().decode("utf-8"))


def fetch_existing_issues(repo: str) -> list[dict]:
    """Every issue in ``repo`` (open and closed, pull requests excluded),
    reduced to ``{"number", "title", "body"}``."""
    issues: list[dict] = []
    page = 1
    while True:
        chunk = _github("GET", f"/repos/{repo}/issues?state=all&per_page=100&page={page}")
        if not isinstance(chunk, list):
            raise MonitorError(f"issue list for {repo} page {page}: unexpected payload shape")
        for item in chunk:
            if "pull_request" in item:
                continue
            issues.append({"number": item.get("number"), "title": item.get("title") or "",
                           "body": item.get("body") or ""})
        if len(chunk) < 100:
            return issues
        page += 1
        if page > 100:
            raise MonitorError(f"issue list for {repo}: more than 100 pages, refusing to dedup against a partial list")


def ids_mentioned(issues: list[dict]) -> tuple[set[str], set[str]]:
    """``(bare ids, versioned ids)`` mentioned anywhere in the issue titles and bodies."""
    bare: set[str] = set()
    versioned: set[str] = set()
    for issue in issues:
        text = f"{issue.get('title', '')}\n{issue.get('body', '')}"
        for match in ARXIV_ID_RE.finditer(text):
            bare.add(match.group(1))
            if match.group(2):
                versioned.add(match.group(1) + match.group(2))
    return bare, versioned


def new_paper_issue(paper: Paper) -> tuple[str, str]:
    title = f"arXiv:{paper.ident}: {paper.title}"[:250]
    body = "\n".join(
        [
            f"**arXiv:{paper.versioned}**",
            "",
            f"**Title:** {paper.title}",
            f"**Authors:** {', '.join(paper.authors)}",
            f"**Submitted:** {paper.published}" + (f" (latest version {paper.updated})" if paper.updated != paper.published else ""),
            f"**Primary category:** {paper.primary_category}",
            f"**Matched queries:** {', '.join(paper.matched)}",
            f"**Link:** {paper.link}",
            "",
            "**Abstract**",
            "",
            paper.summary,
            "",
            "Opened by `scripts/literature_monitor.py`. This is a report that a paper exists, "
            "not an assessment of it; see `meta/literature-monitor.md`.",
        ]
    )
    return title, body


def version_issue(paper: Paper, cited_version: int) -> tuple[str, str]:
    cited_text = f"v{cited_version}" if cited_version else "without a version suffix"
    title = f"arXiv:{paper.ident} has a new version v{paper.version} (tree cites {cited_text})"[:250]
    body = "\n".join(
        [
            f"**arXiv:{paper.versioned}**",
            "",
            f"**Title:** {paper.title}",
            f"**Authors:** {', '.join(paper.authors)}",
            f"**First submitted:** {paper.published}",
            f"**This version:** v{paper.version}, {paper.updated}",
            f"**Cited in this tree as:** {cited_text}",
            f"**Link:** {paper.link}",
            "",
            "**Abstract (current version)**",
            "",
            paper.summary,
            "",
            "Opened by `scripts/literature_monitor.py`. A replaced version of a paper this tree "
            "cites; what changed is unchecked. See `meta/literature-monitor.md`.",
        ]
    )
    return title, body


def open_issue(repo: str, title: str, body: str) -> int:
    payload = {"title": title, "body": body, "labels": [ISSUE_LABEL]}
    try:
        created = _github("POST", f"/repos/{repo}/issues", payload)
    except urllib.error.HTTPError as exc:
        if exc.code != 422:
            raise
        # The label may not exist and the token may not be allowed to create
        # it. An unlabeled issue is still the record; a missing issue is not.
        created = _github("POST", f"/repos/{repo}/issues", {"title": title, "body": body})
    if not isinstance(created, dict) or "number" not in created:
        raise MonitorError("issue creation returned no issue number")
    return int(created["number"])


# ---------------------------------------------------------------------------
# the run
# ---------------------------------------------------------------------------


@dataclass
class Action:
    kind: str  # "new-paper" or "new-version"
    key: str  # the identifier the dedup is keyed on
    title: str
    body: str


def plan_actions(
    hits: dict[str, Paper],
    updates: list[tuple[Paper, int]],
    cited: dict[str, int],
    existing_bare: set[str],
    existing_versioned: set[str],
) -> tuple[list[Action], list[str]]:
    """Decide what to open. Returns ``(actions, skipped)``, where each skipped
    line says why a hit was not turned into an issue."""
    actions: list[Action] = []
    skipped: list[str] = []
    for ident in sorted(hits):
        paper = hits[ident]
        if ident in cited:
            skipped.append(f"{ident}: already cited in the tree")
            continue
        if ident in existing_bare:
            skipped.append(f"{ident}: already mentioned in an existing issue")
            continue
        title, body = new_paper_issue(paper)
        actions.append(Action("new-paper", ident, title, body))
    for paper, cited_version in updates:
        if paper.versioned in existing_versioned:
            skipped.append(f"{paper.versioned}: version already reported in an existing issue")
            continue
        title, body = version_issue(paper, cited_version)
        actions.append(Action("new-version", paper.versioned, title, body))
    return actions, skipped


def _print_reports(reports: list[QueryReport], version_report: VersionReport | None, out) -> int:
    failures = 0
    for r in reports:
        if r.queried:
            print(f"queried        {r.name:<28} {r.entries:>4} entries over {r.pages} page(s), "
                  f"{r.in_window} in window", file=out)
        else:
            failures += 1
            print(f"DID NOT QUERY  {r.name:<28} {r.error}", file=out)
    if version_report is not None:
        if version_report.queried:
            print(f"queried        {'version-check':<28} {version_report.checked:>4} cited identifiers checked", file=out)
        else:
            failures += 1
            print(f"DID NOT QUERY  {'version-check':<28} {version_report.error}", file=out)
    return failures


def _verify_authors(fetch: ParamFetch, out) -> int:
    """Try each unverified author query against its known paper; report."""
    bad = 0
    for search, known, author in AUTHOR_WATCH_UNVERIFIED:
        params = {
            "search_query": f"{search} AND {CATEGORY_CLAUSE}",
            "start": "0", "max_results": "50",
            "sortBy": "submittedDate", "sortOrder": "descending",
        }
        try:
            _, papers = parse_feed(fetch(params), f"author {author!r}")
        except Exception as exc:  # noqa: BLE001
            print(f"DID NOT QUERY  {author:<24} {search:<22} {exc}", file=out)
            bad += 1
            continue
        found = {p.ident for p in papers}
        if known:
            verdict = "returns known paper" if known in found else f"MISSES known paper {known}"
            bad += known not in found
        else:
            verdict = "no known paper to check against"
        print(f"queried        {author:<24} {search:<22} {len(papers)} entries; {verdict}", file=out)
    return bad


def main(argv: list[str] | None = None, out=None) -> int:
    out = out or sys.stdout
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--dry-run", action="store_true", help="print what would be opened; open nothing")
    parser.add_argument("--since", help="start of the window, YYYY-MM-DD (default: today minus %d days)" % DEFAULT_LOOKBACK_DAYS)
    parser.add_argument("--until", help="end of the window, YYYY-MM-DD, inclusive (default: today)")
    parser.add_argument("--fixture", metavar="DIR", help="replay recorded API responses from DIR instead of the network")
    parser.add_argument("--record", metavar="DIR", help="query live and save every response into DIR (implies --dry-run)")
    parser.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", ""), help="owner/name (default: $GITHUB_REPOSITORY)")
    parser.add_argument("--existing-issues", metavar="FILE", help="JSON list of {number,title,body} to dedup against instead of the GitHub API")
    parser.add_argument("--tree-root", default=ROOT, help="tree to grep for citations (default: this checkout)")
    parser.add_argument("--no-version-check", action="store_true", help="skip the cited-paper version check")
    parser.add_argument("--verify-authors", action="store_true", help="probe the unverified author queries and exit")
    args = parser.parse_args(argv)

    today = dt.date.today()
    until = args.until or today.isoformat()
    since = args.since or (today - dt.timedelta(days=DEFAULT_LOOKBACK_DAYS)).isoformat()
    for label, value in (("--since", since), ("--until", until)):
        try:
            dt.date.fromisoformat(value)
        except ValueError:
            print(f"{label} must be YYYY-MM-DD, got {value!r}", file=out)
            return 2

    fetch: ParamFetch
    if args.fixture and args.record:
        print("--fixture and --record are exclusive", file=out)
        return 2
    try:
        if args.fixture:
            fetch = FixtureFetch(args.fixture)
        elif args.record:
            fetch = RecordingFetch(args.record)
            args.dry_run = True
        else:
            fetch = _live
    except MonitorError as exc:
        print(f"DID NOT QUERY  {exc}", file=out)
        return 1

    if args.verify_authors:
        bad = _verify_authors(fetch, out)
        print(f"author verification: {bad} of {len(AUTHOR_WATCH_UNVERIFIED)} failed or unreachable", file=out)
        return 1 if bad else 0

    print(f"window {since} to {until}; {len(QUERIES)} queries; categories {', '.join(CATEGORIES)}", file=out)
    reports, hits = scan(fetch, since, until, queries=QUERIES)
    cited = cited_in_tree(args.tree_root)
    version_report: VersionReport | None = None
    updates: list[tuple[Paper, int]] = []
    if not args.no_version_check:
        version_report, updates = check_versions(cited, fetch, since, until)
    failures = _print_reports(reports, version_report, out)

    if args.record:
        baseline = {r.name: r.entries for r in reports if r.queried}
        with open(os.path.join(args.record, "baseline.json"), "w", encoding="utf-8") as fh:
            json.dump(baseline, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(f"recorded {len(baseline)} baselines into {args.record}", file=out)

    # Dedup. A failed lookup is a failed run: opening duplicates and opening
    # nothing are both wrong, and neither may look like a clean day.
    existing_bare: set[str] = set()
    existing_versioned: set[str] = set()
    dedup_note = ""
    if args.existing_issues:
        with open(args.existing_issues, encoding="utf-8") as fh:
            existing_bare, existing_versioned = ids_mentioned(json.load(fh))
        dedup_note = f"dedup against {args.existing_issues}"
    elif args.dry_run and not (args.repo and os.environ.get("GITHUB_TOKEN")):
        # A dry run opens nothing, so skipping dedup is safe; say so rather than
        # let the list below read as what a real run would open.
        dedup_note = "dedup NOT performed: dry run without both --repo and GITHUB_TOKEN; the list below is before issue dedup"
    else:
        if not args.repo:
            print("DID NOT DEDUP  no --repo and no $GITHUB_REPOSITORY", file=out)
            return 1
        try:
            existing_bare, existing_versioned = ids_mentioned(fetch_existing_issues(args.repo))
            dedup_note = f"dedup against the issue list of {args.repo}"
        except Exception as exc:  # noqa: BLE001
            print(f"DID NOT DEDUP  {args.repo}: {exc.__class__.__name__}: {exc}", file=out)
            return 1

    actions, skipped = plan_actions(hits, updates, cited, existing_bare, existing_versioned)
    print("", file=out)
    print(f"{len(hits)} hit(s) in window; {len(cited)} identifiers cited in the tree; {dedup_note}", file=out)
    for line in skipped:
        print(f"skip           {line}", file=out)
    for action in actions:
        print(f"{'WOULD OPEN' if args.dry_run else 'OPEN':<14} {action.kind:<12} {action.title}", file=out)

    if not args.dry_run:
        for action in actions:
            try:
                number = open_issue(args.repo, action.title, action.body)
            except Exception as exc:  # noqa: BLE001
                print(f"FAILED TO OPEN {action.kind:<12} {action.key}: {exc.__class__.__name__}: {exc}", file=out)
                failures += 1
                continue
            print(f"opened         #{number:<11} {action.key}", file=out)

    print("", file=out)
    queried = sum(1 for r in reports if r.queried)
    print(f"summary: {queried}/{len(reports)} queries answered; {len(actions)} issue(s) "
          f"{'would be ' if args.dry_run else ''}opened; {failures} failure(s)", file=out)
    if failures:
        print("RUN FAILED: at least one query did not complete. Do not read this as a quiet day.", file=out)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
