"""Chain lane of hunt #147 (`dbn_pt_height`): the files are checked, not trusted.

What is pinned here.

1. **Every quotation is re-read.**  Each quotation in `chain.json` is an exact
   substring (after collapsing whitespace; HTML and JSON after removing tags
   and decoding entities) of a source whose SHA-256, URL and retrieval time
   are in `sources.json`.  When the download cache exists (it does on the box
   this hunt ran on), every quotation is re-read from the cached bytes at its
   locator: a TeX line, a file at a git commit, a blog comment anchor whose
   author, date and parent are read from the page, a GitHub comment id with
   its author and time, or a bundle member found by basename and SHA-256.
   When the cache is absent the re-reading tests skip and say so; the shape,
   arithmetic and prose checks still run.
2. **Every stated identity is re-derived**, in exact rationals or in interval
   arithmetic, by two backends that must agree (mpmath `iv` and python-flint
   Arb, 256 bits), never read back from the JSON.
3. **The notes are tied to the evidence.**  Every number token in the notes
   must occur in a quotation or in a structured field of `chain.json` (SHA-256
   digests, commit ids and URLs are excluded from that registry, so a digest
   cannot vouch for a number by accident).  Every date, every named
   attribution and every count in `CHAIN.md`, `REDUCTION.md` and the case-log
   entry sits inside a registered fact (`chain.json`, `facts`) whose check
   reads the evidence: a comment's author and date, a commit's date, a count
   of commits, issues or quotations.  The headline verdict in `CHAIN.md` must
   be the one recorded in `chain.json`.  What this does not do: a one- or
   two-digit number in running prose that no fact covers is checked only by
   the registry, where small numbers occur by chance.
4. **History and bundle claims are re-derived** from the cached clone and the
   cached archive: which files the project repository ever held, which bundle
   members name the banked window bound, and which runs the bundle's logs
   belong to.

The lexical rules of this tree are also enforced on the chain lane's own
files, more strictly than the hunt-wide gate: no em dash and no occurrence of
the reserved stem at all.
"""

from __future__ import annotations

import datetime as dt
import gzip
import hashlib
import html
import json
import os
import re
import subprocess
import sys
from contextlib import contextmanager
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import pytest
from mpmath import iv, mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
if str(REPO) not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, str(REPO))

CHAIN = json.loads((HERE / "chain.json").read_text(encoding="utf-8"))
SOURCES = json.loads((HERE / "sources.json").read_text(encoding="utf-8"))
SRC = SOURCES["sources"]
CACHE = Path(os.environ.get("DBN_CACHE_ROOT", os.path.expanduser("~/.cache/zeta-lab/dbn")))
QUOTES = {q["id"]: q for q in CHAIN["quotes"]}
FACTS = CHAIN["facts"]
PEOPLE = CHAIN["people"]

OWN_FILES = ["MISSION.md", "CHAIN.md", "REDUCTION.md", "chain.json", "sources.json", "test_chain.py"]
STEM = "cert" + "if"
EM_DASH = "\u2014"
MONTHS = ["January", "February", "March", "April", "May", "June", "July", "August",
          "September", "October", "November", "December"]

needs_cache = pytest.mark.skipif(not CACHE.is_dir(), reason="download cache not present on this machine")


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def strip_tags(s: str, alt: bool = False) -> str:
    s = re.sub(r"<script.*?</script>", " ", s, flags=re.S)
    s = re.sub(r"<style.*?</style>", " ", s, flags=re.S)
    if alt:  # restore the LaTeX that the blog renders as images
        s = re.sub(r'<img\b[^>]*?\balt="([^"]*)"[^>]*>', lambda m: " " + m.group(1) + " ", s)
    return norm(html.unescape(re.sub(r"<[^>]+>", " ", s)))


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# the notes: which text each check reads
# ---------------------------------------------------------------------------


def note_text(name: str) -> str:
    """The text a fact or the registry check reads.

    `RUNS.md` is shared with the evaluator lane: only the chain lane's section
    is read, with its run-manifest block removed.  `hunts/README.md` is read
    from the Hunt #147 heading to the next case-log heading.
    """
    if name == "RUNS.md":
        text = (HERE / "RUNS.md").read_text(encoding="utf-8")
        text = text[text.index("## Chain lane"):]
        return re.sub(r"```runmanifest\n.*?```", " ", text, flags=re.S)
    if name == "hunts/README.md":
        text = (REPO / "hunts" / "README.md").read_text(encoding="utf-8")
        start = text.index("### Hunt #147:")
        end = text.find("\n### ", start + 10)
        return text[start:end if end > 0 else len(text)]
    return (HERE / name).read_text(encoding="utf-8")


NOTES_WITH_FACTS = ["CHAIN.md", "REDUCTION.md", "hunts/README.md"]
NOTES_REGISTERED = NOTES_WITH_FACTS + ["MISSION.md", "RUNS.md"]


# ---------------------------------------------------------------------------
# shape and lexical rules
# ---------------------------------------------------------------------------


def test_own_files_exist_and_obey_the_lexical_rules() -> None:
    texts = {name: (HERE / name).read_text(encoding="utf-8") for name in OWN_FILES}
    texts["RUNS.md (chain section)"] = note_text("RUNS.md")
    texts["hunts/README.md (Hunt #147)"] = note_text("hunts/README.md")
    for name, text in texts.items():
        assert STEM not in text.lower(), f"{name} carries the reserved stem"
        assert EM_DASH not in text, f"{name} carries an em dash"


def test_sources_have_url_time_and_digest() -> None:
    for key, s in SRC.items():
        assert s.get("note"), key
        if s["kind"] in {"file", "derived"}:
            assert re.fullmatch(r"[0-9a-f]{64}", s["sha256"]), key
            assert isinstance(s["bytes"], int) and s["bytes"] > 0, key
            assert re.fullmatch(r"2026-10-21T\d\d:\d\d:\d\dZ", s["retrieved_utc"]), key
            assert s["url"], key
        elif s["kind"] == "git":
            assert re.fullmatch(r"[0-9a-f]{40}", s["head"]), key
        elif s["kind"] == "export":
            assert re.fullmatch(r"[0-9a-f]{40}", s["commit"]), key


def _cited_in_json() -> set[str]:
    cited: set[str] = set()

    def walk(node, key=None) -> None:
        if isinstance(node, dict):
            for k, v in node.items():
                walk(v, k)
        elif isinstance(node, list):
            if key in {"quotes", "gap_quotes", "mitigation"} or (key and key.startswith("ev_")):
                for v in node:
                    assert isinstance(v, str), v
                    cited.add(v)
            else:
                for v in node:
                    walk(v, key)

    for key, node in CHAIN.items():
        if key == "quotes":
            continue
        if key in {"verdict_row2", "label_swap"}:
            for v in node.values():
                if isinstance(v, list):
                    cited.update(v)
        elif key == "outside_review":
            cited.update(node)
        else:
            walk(node, key)
    for f in FACTS:
        if "quote" in f:
            cited.add(f["quote"])
    return cited


def _unticked(name: str) -> str:
    """The note without backticked spans (where `[Q:ID]` is explained, not used)."""
    return re.sub(r"`[^`\n]*`", " ", note_text(name))


def test_every_cited_quote_exists() -> None:
    cited = _cited_in_json()
    for name in NOTES_REGISTERED:
        cited |= set(re.findall(r"\[Q:([A-Z0-9]+)\]", _unticked(name)))
    missing = sorted(c for c in cited if c not in QUOTES)
    assert not missing, f"cited quotations that do not exist: {missing}"
    assert len(QUOTES) == len(CHAIN["quotes"]), "duplicate quotation id"


# Facts whose phrase points at a quotation printed elsewhere instead of tagging it.
TAG_ELSEWHERE = {
    "C15": "the quotation follows as a block quote, which carries [Q:I1]",
    "C21": "refers back to that block quote",
    "C34": "refers back to that block quote",
}


def _tag_misplacements(text_of) -> list[str]:
    bad = []
    for f in FACTS:
        if "quote" not in f or f["file"] == "hunts/README.md" or f["id"] in TAG_ELSEWHERE:
            continue  # the case-log entry carries no citation tags by convention
        paras = [p for p in re.split(r"\n\s*\n", text_of(f["file"])) if norm(f["phrase"]) in norm(p)]
        if not any(f"[Q:{f['quote']}]" in p for p in paras):
            bad.append(f"{f['id']}: [Q:{f['quote']}] is not in the paragraph of {f['phrase']!r}")
    return bad


def test_a_fact_bound_to_a_quotation_sits_beside_its_tag() -> None:
    """A tag swapped for another existing tag passes the existence check; this
    check ties each quotation-bound fact to its own tag (added 2026-10-26, after
    the planted-fault re-run let a swapped [Q:B1] through)."""
    assert _tag_misplacements(note_text) == []
    assert set(TAG_ELSEWHERE) <= {f["id"] for f in FACTS}


def test_a_swapped_citation_tag_is_refused() -> None:
    text = note_text("CHAIN.md")
    assert "[Q:B1]" in text
    planted = text.replace("[Q:B1]", "[Q:B2]", 1)  # the tag after the 5 July 2024 comment
    assert _tag_misplacements(lambda n: planted if n == "CHAIN.md" else note_text(n))


def test_citation_tags_are_well_formed() -> None:
    """A tag the existence check cannot parse would escape it: refuse any other shape."""
    for name in NOTES_REGISTERED:
        for tag in re.findall(r"\[Q:([^\]]*)\]", _unticked(name)):
            assert re.fullmatch(r"[A-Z][A-Z0-9]*\d[A-Z0-9]*", tag), f"{name}: malformed citation [Q:{tag}]"


# ---------------------------------------------------------------------------
# the number registry: every number in the notes occurs in the evidence
# ---------------------------------------------------------------------------

_SCI = re.compile(r"(\d+(?:\.\d+)?)\s*(?:\\times|\\cdot|\u00d7|x)\s*10\s*\^\s*\{?\s*(-?\d+)\s*\}?")
_TOKEN = re.compile(r"(?<![\d.])\d+(?:\.\d+)?(?:e-?\d+)?(?:/\d+(?:\.\d+)?)?")
_EXCLUDED_KEYS = {"sha256", "head", "commit", "url", "members_root", "cache_path"}


def _registry_strings() -> list[str]:
    out: list[str] = []

    def walk(node, key=None) -> None:
        if key in _EXCLUDED_KEYS:
            return
        if isinstance(node, dict):
            for k, v in node.items():
                walk(v, k)
        elif isinstance(node, list):
            for v in node:
                walk(v, key)
        elif isinstance(node, (int, float)) and not isinstance(node, bool):
            out.append(str(node))
        elif isinstance(node, str):
            if _is_hex_id(node) or node.startswith(("http://", "https://")):
                return
            out.append(re.sub(r"\b[0-9a-f]{16,}\b", lambda m: " " if _is_hex_id(m.group(0)) else m.group(0), node))

    walk(CHAIN)
    walk(SOURCES)
    return out


def _is_hex_id(s: str) -> bool:
    """A commit id or digest: hex, at least seven characters, and at least one letter."""
    return bool(re.fullmatch(r"[0-9a-f]{7,64}", s) and re.search(r"[a-f]", s))


def _tokens(text: str) -> set[str]:
    text = re.sub(r"(?<=\d)(?:\\,|\{,\}|,)(?=\d{3}(?!\d))", "", text)  # digit-group separators
    found = {f"{m.group(1)}e{m.group(2)}" for m in _SCI.finditer(text)}
    return found | set(_TOKEN.findall(text))


@lru_cache(maxsize=1)
def registry() -> frozenset[str]:
    return frozenset(_tokens("\n".join(_registry_strings())))


def _prose(name: str) -> str:
    """The note with citation tags, URLs and backticked identifiers removed."""
    text = note_text(name)
    text = re.sub(r"\[Q:[^\]]*\]", " ", text)
    text = re.sub(r"https?://\S+", " ", text)
    return re.sub(r"`[^`\n]*`", " ", text)


def test_backticked_commit_ids_are_real() -> None:
    """Every backticked hex id in the notes is the prefix of a full commit id recorded in the JSON."""
    blob = (HERE / "chain.json").read_text(encoding="utf-8") + (HERE / "sources.json").read_text(encoding="utf-8")
    known = set(re.findall(r"\b[0-9a-f]{40}\b", blob))
    for name in NOTES_REGISTERED:
        for span in re.findall(r"`([0-9a-f]{7,40})`", note_text(name)):
            if _is_hex_id(span):
                assert any(k.startswith(span) for k in known), f"{name}: unknown commit id {span}"


def test_every_number_in_the_notes_is_registered() -> None:
    reg = registry()
    for name in NOTES_REGISTERED:
        loose = sorted((t for t in _tokens(_prose(name)) if t not in reg), key=lambda t: (len(t), t))
        assert not loose, f"{name}: numbers with no entry in the quotations or chain.json: {loose}"


def test_the_registry_excludes_digests() -> None:
    """The control: a number that occurs only inside a SHA-256 digest is not registered."""
    reg = registry()
    digest_only = set()
    for s in SRC.values():
        if s.get("sha256"):
            digest_only |= set(re.findall(r"\d{5,}", s["sha256"]))
    others = "\n".join(_registry_strings())
    probes = sorted(d for d in digest_only if d not in others)
    assert probes, "no digest-only digit run to probe with"
    assert not [p for p in probes if p in reg]


# ---------------------------------------------------------------------------
# facts: dates, names and counts in the notes, checked against the evidence
# ---------------------------------------------------------------------------

_ISO = re.compile(r"\b((?:19|20)\d\d)-(\d\d)-(\d\d)\b")
_DMY = re.compile(r"\b(\d{1,2}) (%s),? ((?:19|20)\d\d)\b" % "|".join(MONTHS))


def _dates_in(text: str) -> list[tuple[int, int, dt.date]]:
    out = []
    for m in _ISO.finditer(text):
        out.append((m.start(), m.end(), dt.date(int(m.group(1)), int(m.group(2)), int(m.group(3)))))
    for m in _DMY.finditer(text):
        out.append((m.start(), m.end(), dt.date(int(m.group(3)), MONTHS.index(m.group(2)) + 1, int(m.group(1)))))
    return out


def _parse_date(s: str) -> dt.date:
    found = _dates_in(s)
    assert len(found) == 1, f"not one date in {s!r}"
    return found[0][2]


def _repo(key: str) -> Path:
    return CACHE / SRC[key]["cache_path"]


def _git(key: str, *args: str) -> str:
    return subprocess.run(["git", "-C", str(_repo(key)), *args], capture_output=True, text=True, check=True).stdout


def _locator_meta(q: dict) -> dict:
    """Author, date and parent of a quotation, read from its source (not from the locator)."""
    loc, kind = q["locator"], q["kind"]
    if kind in {"json_comment", "json_comment_list", "json_issue_body"}:
        return {"author": loc["author"], "date": dt.date.fromisoformat(loc["created_at"][:10])}
    if kind == "html_comment":
        meta = _comment_meta(q["source"])[loc["anchor"]]
        return {"author": meta["author"], "date": _parse_date(meta["date"]), "parent": meta["parent"]}
    if kind == "gitfile":
        day = _git(q["source"], "log", "-1", "--format=%ad", "--date=short", loc["commit"]).strip()
        return {"date": dt.date.fromisoformat(day)}
    raise AssertionError(f"{q['id']}: kind {kind} carries no author or date")


def test_facts_are_well_formed_and_their_phrases_are_in_the_notes() -> None:
    ids = [f["id"] for f in FACTS]
    assert len(ids) == len(set(ids)), "duplicate fact id"
    for f in FACTS:
        assert f["file"] in NOTES_WITH_FACTS + ["MISSION.md", "RUNS.md"], f["id"]
        assert norm(f["phrase"]) in norm(note_text(f["file"])), f"{f['id']}: phrase not in {f['file']}: {f['phrase']!r}"
        if "date" in f:
            assert _parse_date(f["phrase"]) == dt.date.fromisoformat(f["date"]), f"{f['id']}: phrase date"
        if "name" in f:
            assert f["name"] in f["phrase"], f"{f['id']}: the phrase does not carry the name it pins"


def _check_fact(f: dict) -> None:
    kind = f["kind"]
    if kind == "quote_meta":
        q = QUOTES[f["quote"]]
        meta = _locator_meta(q)
        for key in ("name", "author_is"):
            if key in f:
                assert meta["author"] in PEOPLE[f[key]], f"{f['id']}: author {meta['author']!r} is not {f[key]}"
        for key in ("date", "on"):
            if key in f:
                assert meta["date"] == dt.date.fromisoformat(f[key]), f"{f['id']}: date {meta['date']}"
        if "parent" in f:
            assert meta["parent"] == f["parent"], f"{f['id']}: parent {meta['parent']}"
        if "parent_name" in f:
            parent = _comment_meta(q["source"])[meta["parent"]]
            assert parent["author"] in PEOPLE[f["parent_name"]], f"{f['id']}: parent author {parent['author']!r}"
    elif kind == "json_date":
        obj = json.loads(_file(f["source"]).read_text(encoding="utf-8"))
        assert str(_dotted(obj, f["field"]))[:10] == f["date"], f"{f['id']}: {f['field']}"
    elif kind == "no_reply":
        meta = _comment_meta(f["source"])
        assert f["anchor"] in meta
        assert not [a for a, m in meta.items() if m["parent"] == f["anchor"]], f"{f['id']}: a reply exists"
    elif kind == "quote_text":
        assert norm(f["phrase"]) in norm(QUOTES[f["quote"]]["text"]), f"{f['id']}: not verbatim in {f['quote']}"
    elif kind == "commit_date":
        day = _git(f["source"], "log", "-1", "--format=%ad", "--date=short", f["commit"]).strip()
        assert day == f["date"], f"{f['id']}: commit date {day}"
        assert f["commit"][:7] in f["phrase"]
    elif kind == "git_count":
        for ref, want in f["counts"].items():
            got = int(_git(f["source"], "rev-list", "--count", *(["--all"] if ref == "all" else [ref])).strip())
            assert got == want, f"{f['id']}: {ref} has {got} commits"
            assert str(want) in f["phrase"]
    elif kind == "issue_count":
        rows = [r for key in f["sources"] for r in json.loads(_file(key).read_text(encoding="utf-8"))]
        assert len(rows) == f["value"] and len({r["number"] for r in rows}) == f["value"], f["id"]
        assert str(f["value"]) in f["phrase"]
    elif kind == "quote_count":
        assert len(QUOTES) == f["value"] and str(f["value"]) in f["phrase"], f"{f['id']}: {len(QUOTES)} quotations"
    elif kind == "self_date":
        assert CHAIN["written"] in f["phrase"]
    elif kind == "arith":
        assert F(f["t0"]) + F(f["y0"]) ** 2 / 2 == F(f["Lambda"]), f"{f['id']}: t0 + y0^2/2"
        for key in ("t0", "y0", "Lambda"):
            assert re.search(r"(?<![\d.])%s(?![\d])" % re.escape(f[key]), f["phrase"]), f"{f['id']}: {key}"
    elif kind == "outsider":
        _check_outsider(f)
    elif kind == "sweep_2018":
        _check_sweep(f)
    else:  # pragma: no cover - a new kind must be taught here first
        raise AssertionError(f"unknown fact kind {kind}")


@pytest.mark.parametrize("fid", [f["id"] for f in FACTS])
def test_fact_holds_in_the_evidence(fid: str) -> None:
    f = next(f for f in FACTS if f["id"] == fid)
    if f["kind"] not in {"quote_text", "quote_count", "self_date", "arith"} and not CACHE.is_dir():
        pytest.skip("download cache not present on this machine")
    _check_fact(f)


def _covered(text: str, phrases: list[str]) -> list[tuple[int, int]]:
    spans = []
    for p in phrases:
        start = 0
        while (i := text.find(p, start)) >= 0:
            spans.append((i, i + len(p)))
            start = i + 1
    return spans


@pytest.mark.parametrize("name", NOTES_WITH_FACTS)
def test_every_date_and_named_person_in_the_notes_sits_inside_a_fact(name: str) -> None:
    text = norm(note_text(name))
    phrases = [norm(f["phrase"]) for f in FACTS if f["file"] == name]
    spans = _covered(text, phrases)
    loose = [text[a:b] for a, b, _ in _dates_in(text) if not any(s <= a and b <= e for s, e in spans)]
    assert not loose, f"{name}: dates outside every fact: {loose}"
    named = [norm(f["phrase"]) for f in FACTS if f["file"] == name and "name" in f]
    name_spans = _covered(text, named)
    for person in PEOPLE:
        for m in re.finditer(r"\b%s\b" % re.escape(person), text):
            assert any(s <= m.start() and m.end() <= e for s, e in name_spans), (
                f"{name}: {person!r} at {text[max(0, m.start() - 40):m.end() + 40]!r} is outside every named fact")


_QUOTED = re.compile(r'"([^"\n]{2,400}?)"')
_TAGS = re.compile(r"(?:\[Q:[A-Z0-9]+\]\s*)+")


@pytest.mark.parametrize("name", NOTES_WITH_FACTS)
def test_inline_quotations_are_verbatim(name: str) -> None:
    """A phrase in double quotes must occur in one of the quotations cited by the next group of
    citation tags within 250 characters; a quoted phrase with no tag that close is a name, not a citation."""
    text = norm(_unticked_keep_tags(name))
    bad, checked = [], 0
    for m in _QUOTED.finditer(text):
        tags = _TAGS.search(text, m.end(), m.end() + 250)
        if not tags:
            continue
        checked += 1
        span = norm(m.group(1))
        ids = re.findall(r"\[Q:([A-Z0-9]+)\]", tags.group(0))
        if not any(span in norm(QUOTES[i]["text"]) for i in ids if i in QUOTES):
            bad.append((span, ids))
    assert not bad, f"{name}: inline quotations not verbatim in the cited quotations: {bad}"
    if name != "hunts/README.md":
        assert checked >= 10


def _unticked_keep_tags(name: str) -> str:
    return re.sub(r"`[^`\n]*`", " ", note_text(name))


def test_the_headline_verdict_is_the_recorded_one() -> None:
    text = note_text("CHAIN.md")
    block = text[text.index("## Verdict"):]
    first_bold = re.search(r"\*\*(.+?)\*\*", block, flags=re.S).group(1)
    assert norm(first_bold) == CHAIN["verdict_row2"]["headline"]


def _table_rows(text: str, heading: str) -> list[list[str]]:
    block = text[text.index(heading):]
    block = block[:block.find("\n## ", 4) if block.find("\n## ", 4) > 0 else len(block)]
    rows = [[c.strip() for c in line.strip().strip("|").split("|")] for line in block.split("\n") if line.startswith("|")]
    return [r for r in rows[2:]]


def test_the_dependency_table_is_the_recorded_one() -> None:
    """REDUCTION.md part C must say what chain.json's dependencies say, row by row."""
    rows = {re.sub(r"\*", "", r[0]): r for r in _table_rows(note_text("REDUCTION.md"), "## C. Which rows depend on which")}
    deps = {d["row"]: d for d in CHAIN["dependencies"]}
    assert set(rows) == set(deps)

    def says(cell: str) -> bool:
        cell = re.sub(r"\*", "", cell).lower()
        assert cell.startswith(("yes", "no", "it is the reduction")), cell
        return not cell.startswith("no")

    for row, d in deps.items():
        assert says(rows[row][2]) == d["uses_1875_reduction"], row
        assert says(rows[row][3]) == d["inherits_row2_gap"], row


def test_a_planted_change_to_the_notes_is_refused() -> None:
    """The control for the prose checks: edits of the kind an adversary planted must turn red."""
    text = note_text("CHAIN.md")
    reg = registry()
    assert "19/100" not in reg and "19/200" in reg
    phrases = [norm(f["phrase"]) for f in FACTS if f["file"] == "CHAIN.md"]
    for old, new in [("2019-04-15", "2019-04-16"), ("5 July 2024", "7 July 2024"), ("778", "779")]:
        assert old in text
        hit = [p for p in phrases if old in p]
        assert hit, f"no fact covers {old}"
        assert all(norm(text.replace(old, new)).find(p) < 0 for p in hit)


# ---------------------------------------------------------------------------
# 1. quotations re-read from the hashed cache
# ---------------------------------------------------------------------------


def _file(key: str) -> Path:
    s = SRC[key]
    p = CACHE / s["cache_path"]
    assert p.is_file(), f"{key}: cached file missing"
    assert sha256(p) == s["sha256"], f"{key}: cached bytes differ from the recorded SHA-256"
    return p


def _lines(text: str, span) -> str:
    lines = text.split("\n")
    a, b = span
    return norm("\n".join(lines[a - 1:b]))


def _bundle_root(key: str) -> Path:
    return CACHE / SRC[key].get("members_root", SRC[key]["cache_path"])


def _bundle_member(key: str, basename: str, digest: str) -> Path:
    hits = []
    for d, _, files in os.walk(_bundle_root(key)):
        if basename in files:
            p = Path(d) / basename
            if sha256(p) == digest:
                hits.append(p)
    assert len(hits) == 1, f"{key}: {basename} with the recorded digest found {len(hits)} times"
    return hits[0]


def _git_show(key: str, commit: str, path: str) -> str:
    return _git(key, "show", f"{commit}:{path}")


def _dotted(obj, dotted: str):
    for part in dotted.split("."):
        obj = obj[part]
    return obj


_COMMENT = re.compile(r'<div class="comment ([^"]*?)depth-(\d+)[^"]*" id="(comment-\d+)">')


@lru_cache(maxsize=None)
def _comment_meta(key: str) -> dict:
    """Author, date, parent and text of every comment on a blog page, by anchor."""
    raw = _file(key).read_text(encoding="utf-8", errors="replace")
    ms = list(_COMMENT.finditer(raw))
    out, stack = {}, {}
    for k, m in enumerate(ms):
        depth, anchor = int(m.group(2)), m.group(3)
        seg = raw[m.start():ms[k + 1].start() if k + 1 < len(ms) else len(raw)]
        date = re.search(r'title="Permalink to this comment">([^<]*)</a>', seg).group(1).split(" at ")[0]
        author = strip_tags(re.search(r'<strong class="fn">(.*?)</strong>', seg, re.S).group(1))
        stack[depth] = anchor
        out[anchor] = {"author": author, "date": date, "parent": stack.get(depth - 1) if depth > 1 else None,
                       "seg": seg}
    return out


def _check(q: dict) -> None:
    kind, key, want, loc = q["kind"], q["source"], norm(q["text"]), q["locator"]
    if kind == "line":
        text = _file(key).read_text(encoding="utf-8")
        assert want in _lines(text, loc["lines"])
    elif kind == "repo":
        text = (REPO / loc["path"]).read_text(encoding="utf-8")
        assert want in _lines(text, loc["lines"])
    elif kind == "gitfile":
        assert want in _lines(_git_show(key, loc["commit"], loc["path"]), loc["lines"])
    elif kind == "bundle":
        p = _bundle_member(key, loc["basename"], loc["sha256"])
        assert want in _lines(p.read_text(encoding="utf-8"), loc["lines"])
    elif kind == "html_page":
        raw = _file(key).read_text(encoding="utf-8", errors="replace")
        if "lines" in loc:
            raw = "\n".join(raw.split("\n")[loc["lines"][0] - 1:loc["lines"][1]])
        assert want in strip_tags(raw, alt=loc.get("alt", False))
    elif kind == "html_comment":
        meta = _comment_meta(key)[loc["anchor"]]
        assert meta["author"] == loc["author"], f"author {meta['author']!r}"
        assert _parse_date(meta["date"]) == _parse_date(loc["date"]), f"date {meta['date']!r}"
        assert meta["parent"] == loc.get("parent"), f"parent {meta['parent']!r}"
        assert want in strip_tags(meta["seg"], alt=loc.get("alt", False))
    elif kind == "json_comment":
        rows = json.loads(_file(key).read_text(encoding="utf-8"))
        row = [r for r in rows if r["id"] == loc["comment_id"]]
        assert len(row) == 1 and row[0]["user"]["login"] == loc["author"]
        assert row[0]["created_at"] == loc["created_at"]
        assert want in norm(row[0]["body"])
    elif kind == "json_issue_body":
        rows = json.loads(_file(key).read_text(encoding="utf-8"))
        row = [r for r in rows if r["number"] == loc["issue"]]
        assert len(row) == 1 and row[0]["user"]["login"] == loc["author"]
        assert row[0]["created_at"] == loc["created_at"]
        assert want in norm(row[0]["body"])
    elif kind == "json_field":
        obj = json.loads(_file(key).read_text(encoding="utf-8"))
        assert want in strip_tags(_dotted(obj, loc["field"]))
    elif kind == "json_comment_list":
        row = json.loads(_file(key).read_text(encoding="utf-8"))[loc["index"]]
        assert row["user"]["login"] == loc["author"] and row["created_at"] == loc["created_at"]
        assert want in norm(row["body"])
    else:  # pragma: no cover - a new kind must be taught here first
        raise AssertionError(f"unknown quotation kind {kind}")


@needs_cache
@pytest.mark.parametrize("qid", sorted(QUOTES))
def test_quotation_is_in_its_hashed_source(qid: str) -> None:
    _check(QUOTES[qid])


@needs_cache
def test_every_cached_file_still_has_its_recorded_digest() -> None:
    for key, s in SRC.items():
        if s["kind"] in {"file", "derived"}:
            _file(key)
        elif s["kind"] == "git":
            assert _git(key, "rev-parse", "HEAD").strip() == s["head"], key


@needs_cache
def test_a_planted_misquote_is_refused() -> None:
    """The control: one changed token in a real quotation, or a wrong author, date or parent, must fail."""
    for qid, old, new in [("P12", "(iii)", "(ii)"), ("P9", "630783", "630784"), ("I1", "N_0", "N_1")]:
        q = dict(QUOTES[qid])
        q["text"] = q["text"].replace(old, new)
        with pytest.raises(AssertionError):
            _check(q)
    for field, value in [("author", "Terence Tao"), ("date", "6 July, 2024"), ("parent", "comment-685279")]:
        q = json.loads(json.dumps(QUOTES["B5"]))
        q["locator"][field] = value
        with pytest.raises(AssertionError):
            _check(q)


# ---------------------------------------------------------------------------
# facts that read more than one line: the outside reader and the 2018 sweeps
# ---------------------------------------------------------------------------


def _check_outsider(f: dict) -> None:
    """The commenter's name occurs nowhere in the project's issue records, and none of the blog
    comments under that name predates 2024; the first one is on the recorded date."""
    names = set(PEOPLE[f["who"]])
    stem = f["who"].lower()
    for key in f["json_sources"]:
        assert stem not in _file(key).read_text(encoding="utf-8").lower(), f"{f['id']}: {key}"
    mine = []
    for key in f["blog_sources"]:
        for anchor, meta in _comment_meta(key).items():
            if meta["author"] in names:
                mine.append(_parse_date(meta["date"]))
    assert mine and min(mine).year >= 2024, f"{f['id']}: an earlier comment exists"
    if "date" in f:
        assert min(mine) == dt.date.fromisoformat(f["date"]), f"{f['id']}: first comment {min(mine)}"


def _sweep_rows(commit: str, path: str) -> list[tuple[int, float, float]]:
    rows = []
    for line in _git_show("DBN_REPO", commit, path).split("\n"):
        parts = [p.strip() for p in line.split(",")]
        if len(parts) >= 3 and parts[0].isdigit():
            rows.append((int(parts[0]), float(parts[1]), float(parts[2])))
    return rows


def _check_sweep(f: dict) -> None:
    route = next(r for r in CHAIN["routes_2018"] if r["id"] == f["route"])
    rows = _sweep_rows(route["sweep_commit"], route["sweep_path"])
    lo = min(rows, key=lambda r: r[1])
    got = {"N_first": rows[0][0], "N_last": rows[-1][0], "min_bound": lo[1], "min_at_N": lo[0],
           "max_error": max(r[2] for r in rows), "rows": len(rows)}
    for k, v in got.items():
        assert v == route["sweep"][k], f"{f['id']}: {k} = {v}"
    assert all(r[2] < r[1] for r in rows), "an error bound exceeds its lower bound"


# ---------------------------------------------------------------------------
# repository history
# ---------------------------------------------------------------------------


@needs_cache
def test_the_recorded_dois_are_the_records_own() -> None:
    for key, doi in CHAIN["dois"].items():
        assert json.loads(_file(key).read_text(encoding="utf-8"))["doi"] == doi, key


@needs_cache
def test_the_expect_sentence_entered_the_writeup_at_4a460d9() -> None:
    """CHAIN.md section 2: absent from further.tex at 7eff611, present at 4a460d9."""
    before = _git_show("DBN_REPO", "7eff6114efd97ed8de58d31503a6e4b464d61c18", "Writeup/further.tex")
    after = _git_show("DBN_REPO", "4a460d9b85198c78e6314f30718314160e2b1473", "Writeup/further.tex")
    assert "expect to be able" not in before and "expect to be able" in after


@needs_cache
def test_no_sweep_at_row2_parameters_in_any_commit() -> None:
    """Every file the eulerbounds path ever held is at y = 0.2; the only N0 = 630783 sweep is t = 0.17."""
    out = _git("DBN_REPO", "log", "--all", "--format=", "--name-only", "--", "output/eulerbounds")
    names = sorted({n for n in out.split("\n") if n.strip() and not n.endswith("README.md")})
    assert len(names) >= 12
    assert all("y_0.2" in n for n in names), names
    assert not [n for n in names if "16733" in n or "0.186" in n]
    at_n0 = [n for n in names if "630783" in n]
    assert at_n0 == ["output/eulerbounds/lemmasawtooth_bounds_t_0.17_y_0.2_N_630783_15mil_moll_2,3,5.txt"]


@needs_cache
def test_the_row2_y0_string_never_entered_a_sweep_file() -> None:
    """A history search for 0.16733 touches only the writeup, row 2's barrier output, and y = 0.2 sweeps."""
    out = _git("DBN_REPO", "log", "--all", "-S0.16733", "--format=", "--name-only")
    paths = sorted({p for p in out.split("\n") if p.strip()})
    barrier = "output/windingnumbers/windnum_nolemma_x5000000194858_y_0.16733_1_t_0_0.186.txt"
    assert barrier in paths
    for p in paths:
        assert p.startswith("Writeup/") or p == barrier or (p.startswith("output/eulerbounds/") and "y_0.2" in p), p


@needs_cache
def test_every_file_naming_the_2018_points_is_listed() -> None:
    """CHAIN.md section 2a: the history holds, for the two 2018 points, barrier summaries,
    stored sums and one sweep each, and no other file (in particular no tail file)."""
    out = _git("DBN_REPO", "log", "--all", "--format=", "--name-only")
    paths = sorted({p for p in out.split("\n") if p.strip()})
    for route in CHAIN["routes_2018"]:
        hits = sorted(p for p in paths if re.search(route["path_regex"], p))
        assert hits == sorted(route["files_in_history"]), (route["id"], hits)
        assert route["barrier_path"] in hits and route["sweep_path"] in hits
        assert not [p for p in hits if "tail" in p.lower() or "triangle" in p.lower()]


# ---------------------------------------------------------------------------
# the 0.1875 bundle and the 0.16 bundle
# ---------------------------------------------------------------------------


def _bundle_files(key: str):
    for d, _, files in os.walk(_bundle_root(key)):
        for name in files:
            yield Path(d) / name


@needs_cache
def test_the_banked_window_bound_has_no_run_in_the_bundle() -> None:
    """REDUCTION.md A4.  The members naming lwin2, and those naming its cap 2745000, are exactly
    the recorded lists, and none is C or GP source; every compressed log in the bundle belongs to a
    run at t = 0.1770, t = 0.1775 or the box between them; and the only t-box invocations anywhere
    in the bundle are at those values.  So the parametric producer ships, but no lwin2 run does."""
    a4 = next(r for r in CHAIN["reduction_1875"] if r["id"] == "A4")
    seen_lwin2, seen_cap, triples = set(), set(), set()
    logs = {}
    for p in _bundle_files("ZEN_ZIP"):
        if p.stat().st_size > 50_000_000:
            continue
        data = p.read_bytes()
        if b"lwin2" in data:
            seen_lwin2.add(p.name)
        if b"2745000" in data:
            seen_cap.add(p.name)
        if p.suffix == ".gz":
            with gzip.open(p, "rt", errors="replace") as fh:
                logs[p] = fh.readline().strip()
        else:
            for m in re.finditer(rb"\b(1[67]\d[05]) +(1[67]\d[05]) +10000\b", data):
                triples.add((m.group(1).decode(), m.group(2).decode()))
    assert seen_lwin2 == set(a4["lwin2_naming_members"])
    assert seen_cap == set(a4["cap_naming_members"])
    assert not [n for n in seen_lwin2 | seen_cap if n.endswith((".c", ".gp"))]
    assert triples == {("1770", "1770"), ("1770", "1775"), ("1775", "1775")}, triples
    prov = a4["compressed_logs"]
    assert sorted(p.name for p in logs) == sorted(prov), "the set of compressed logs changed"
    for p, first in logs.items():
        rule = prov[p.name]
        if rule == "tbox_header":
            assert first == "TBOX 1770/10000 1775/10000", (p.name, first)
        elif rule == "file_name":
            assert re.search(r"t1770|t1775|row1775", p.name), p.name
        elif rule == "driver":
            assert first == "ALLDONE", p.name
        else:  # the run script that wrote it sits in the same package and is a re-read quotation
            q = QUOTES[rule["quote"]]
            script = _bundle_member(q["source"], q["locator"]["basename"], q["locator"]["sha256"])
            assert rule["dir"] in {p.parent.name, p.parent.parent.name}, (p.name, rule)
            assert script.parent.name == rule["dir"], (p.name, script)
    assert len(logs) == a4["compressed_log_count"]


@needs_cache
def test_the_record_pdf_is_the_bundle_paper_its_readme_describes() -> None:
    """REDUCTION.md part 0: the record's PDF is byte-identical to the bundle's paper, which the bundle's
    paper README (quotation Z31, in the same directory) describes as the 0.1965 paper."""
    readme = _bundle_member("ZEN_ZIP", "README.md", QUOTES["Z31"]["locator"]["sha256"])
    paper = readme.parent / "main.pdf"
    assert paper.is_file() and sha256(paper) == SRC["ZEN_PDF"]["sha256"]
    assert sha256(_file("ZEN_PDF")) == sha256(paper)


@needs_cache
def test_the_frozen_anchor_copy_differs_from_the_zenodo_writeup_in_one_word() -> None:
    """REDUCTION.md B0: same length, one differing line (74), and the difference is one word."""
    zen = _bundle_member("ZEN_ZIP", "ASSEMBLY_1875.md", QUOTES["Z23"]["locator"]["sha256"])
    frozen = _bundle_member("FORK_0160", "anchor.txt", QUOTES["F18"]["locator"]["sha256"])
    a = zen.read_text(encoding="utf-8").split("\n")
    b = frozen.read_text(encoding="utf-8").split("\n")
    assert len(a) == len(b)
    diff = [i + 1 for i, (x, y) in enumerate(zip(a, b)) if x != y]
    assert diff == [74]
    wa, wb = a[73].split(), b[73].split()
    assert len(wa) == len(wb) and [(x, y) for x, y in zip(wa, wb) if x != y] == [("campaign-targeted", "operator-targeted")]


# ---------------------------------------------------------------------------
# 2. identities, re-derived by two interval backends
# ---------------------------------------------------------------------------


@contextmanager
def ivprec(bits: int):
    """mpmath's interval context has no workprec; set and restore by hand."""
    old = iv.prec
    iv.prec = bits
    try:
        yield
    finally:
        iv.prec = old


T_PT = 3000175332800
X2 = 5000000194858
XS = 6000000185827
X18 = 1000000046880


def _row2() -> tuple[F, F]:
    r = CHAIN["row2"]
    return F(r["t0"]), F(r["y0"])


def test_row2_parameters_match_the_quoted_table_row() -> None:
    row = QUOTES["P9"]["text"]
    assert "194858" in row and "0.186" in row and "0.16733" in row and "630783" in row and "0.0376" in row
    assert CHAIN["row2"]["X"] == str(X2) and CHAIN["row2"]["N0"] == 630783


def test_row2_lambda() -> None:
    t0, y0 = _row2()
    lam = t0 + y0 ** 2 / 2
    assert lam == F(3999993289, 20000000000)
    assert str(float(lam)) == "0.19999966445"
    assert lam <= F(1, 5)


def test_row2_height() -> None:
    half = F(X2, 2)
    assert half == 2500000097429
    assert T_PT - half == 500175235371
    assert half < F(251, 100) * 10 ** 12 <= T_PT  # PT's printed sufficient threshold, 2.51e12


def _N_bounds_iv(x_lo: int, t_hi: F) -> tuple:
    with ivprec(256):
        lo = iv.mpf(x_lo) / (4 * iv.pi)
        hi = iv.mpf(x_lo + 1) / (4 * iv.pi) + iv.mpf(t_hi.numerator) / iv.mpf(t_hi.denominator) / 16
        return lo.a, hi.b


def _N_is_constant(x_lo: int, t_hi: F, n: int) -> bool:
    """floor(sqrt(x/(4 pi) + t/16)) == n on [x_lo, x_lo + 1] x [0, t_hi]; the argument increases in x and t.

    Decided twice, by mpmath iv and by python-flint Arb at 256 bits; the two must agree."""
    from flint import arb, ctx

    lo, hi = _N_bounds_iv(x_lo, t_hi)
    with ivprec(256):
        by_iv = (iv.mpf(n) ** 2).b < lo and hi < (iv.mpf(n + 1) ** 2).a
    old = ctx.prec
    ctx.prec = 256
    try:
        alo = arb(x_lo) / (4 * arb.pi())
        ahi = arb(x_lo + 1) / (4 * arb.pi()) + arb(t_hi.numerator) / arb(t_hi.denominator) / 16
        by_arb = bool(arb(n) ** 2 < alo) and bool(ahi < arb(n + 1) ** 2)
    finally:
        ctx.prec = old
    assert by_iv == by_arb, f"backends disagree at {x_lo}, {t_hi}, {n}"
    return by_iv


def test_row2_N_constant_on_the_barrier_slab() -> None:
    t0, _ = _row2()
    assert _N_is_constant(X2, t0, 630783)
    assert not _N_is_constant(X2, t0, 630782)


def test_site_1875_identities() -> None:
    assert F(1680, 10 ** 4) + F(39, 1000) / 2 == F(3, 16)
    assert F(XS, 2) == F(6000000185827, 2)
    assert T_PT - F(XS, 2) == F(350479773, 2)
    assert F(33, 200) ** 2 == F(1089, 40000)
    assert F(39, 1000) - F(33, 200) ** 2 == F(471, 40000)
    assert _N_is_constant(XS, F(1809, 10000), 690988)


def test_collision_band_walls() -> None:
    from flint import arb, ctx

    a, b = F(4, 25), F(3, 16)
    C, H, J, W = 690988, 2299999, 2300000, 66476100549959
    with ivprec(256):
        def wall(n, t):
            return 4 * iv.pi * (iv.mpf(n) ** 2 - iv.mpf(t.numerator) / iv.mpf(t.denominator) / 16)

        assert wall(C, a).b < XS < wall(C + 1, b).a
        assert wall(H, a).b < W < wall(J, b).a and wall(J, b).b < W + 1  # so W = floor(s_J(b))
    old = ctx.prec
    ctx.prec = 256
    try:
        def awall(n, t):
            return 4 * arb.pi() * (arb(n) ** 2 - arb(t.numerator) / arb(t.denominator) / 16)

        assert awall(C, a) < XS < awall(C + 1, b)
        assert awall(H, a) < W < awall(J, b) < W + 1
    finally:
        ctx.prec = old


def test_the_2018_points() -> None:
    """CHAIN.md section 2a: 0.17 + 0.2^2/2 = 0.19 at row 2's X; 0.18 + 0.2^2/2 = 1/5 at X = 10^12 + 46880;
    both heights lie below Platt-Trudgian's; N is constant on both barrier slabs."""
    assert F(17, 100) + F(1, 5) ** 2 / 2 == F(19, 100)
    assert F(18, 100) + F(1, 5) ** 2 / 2 == F(1, 5)
    assert F(X18, 2) == 500000023440 and T_PT - F(X18, 2) == 2500175309360
    assert _N_is_constant(X2, F(17, 100), 630783)
    assert _N_is_constant(X18, F(18, 100), 282094)
    assert not _N_is_constant(X18, F(18, 100), 282093)
    routes = {r["id"]: r for r in CHAIN["routes_2018"]}
    assert routes["r019"]["X"] == str(X2) and routes["r020"]["X"] == str(X18)


def test_rounded_values_in_the_notes() -> None:
    """Every rounded or truncated value the notes print is the rounding (half up) or truncation of the
    exact value it stands for, which is itself in a quotation or in chain.json."""
    from decimal import ROUND_DOWN, ROUND_HALF_UP, Decimal

    assert CHAIN["roundings"]
    for r in CHAIN["roundings"]:
        v, of = Decimal(r["value"]), Decimal(r["of"])
        mode = ROUND_DOWN if r.get("mode") == "truncate" else ROUND_HALF_UP
        assert of.quantize(Decimal(1).scaleb(v.as_tuple().exponent), rounding=mode) == v, r
        if r.get("quote"):
            assert r["of"] in QUOTES[r["quote"]]["text"], r


def test_collision_bands() -> None:
    assert F(4, 25) == F("0.16") and F(319, 2000) == F("0.1595")
    assert 0 < F(319, 2000) < F(4, 25) < F(3, 16)


# ---------------------------------------------------------------------------
# the structural Davenport-Heilbronn gate
# ---------------------------------------------------------------------------


def test_dh_zero_is_the_laboratory_pin() -> None:
    from zeta import epstein

    gate = CHAIN["dh_gate"]
    assert gate["zero_re"] == epstein.OFFLINE_ZERO_RE
    assert gate["zero_im"] == epstein.OFFLINE_ZERO_IM
    with mp.workdps(40):
        rho = mp.mpc(mp.mpf(gate["zero_re"]), mp.mpf(gate["zero_im"]))
        assert abs(epstein.dh_f(rho, dps=40)) < mp.mpf("1e-20")
        assert mp.re(rho) - mp.mpf(1) / 2 > mp.mpf("0.3")


def test_dh_fails_the_verification_height_input() -> None:
    gate = CHAIN["dh_gate"]
    sigma, gamma = F(gate["zero_re"]), F(gate["zero_im"])
    t0, y0 = _row2()
    # row 2: Theorem 1.2 (i) excludes zeros with (1 + y0)/2 <= sigma <= 1 and 0 <= T <= X/2
    assert (1 + y0) / 2 < sigma <= 1 and 0 < gamma <= F(X2, 2)
    # the 0.1875 site, y0 = sqrt(39/1000): (1 + y0)/2 < sigma iff y0 < 2 sigma - 1
    assert F(39, 1000) < (2 * sigma - 1) ** 2 and 0 < gamma <= F(XS, 2)
    # wide frame s = 1/2 + i z / 2: z = 2 gamma - i (2 sigma - 1)
    assert F(gate["wide_frame_z_re"]) == 2 * gamma
    assert F(gate["wide_frame_z_im_abs"]) == 2 * sigma - 1
    assert 0 < 2 * gamma <= XS and 2 * sigma - 1 > 0
    assert gate["fails_input"] == "verification height" and gate["passes_gate"] is True
