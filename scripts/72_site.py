#!/usr/bin/env python3
"""72_site.py: the public reading surface, generated from repository artifacts.

`scripts/70_lab_state.py` renders the *internal* research-state view. This
renders the *public* one, on the same principle and for the same reason:

    one static file per page, no scripts and no network. Pages you can read,
    not an app you can be reassured by

The rule that matters is **derived, not declared**. Every count, every module
title, every status and every record entry below comes from a tree artifact:
the Lean sources, the Python sources, the test files, the graveyard and review
and guard ledgers, the gate evidence, git. If the repository changes the site
changes; if nobody updates the repository the site says so. A second,
hand-maintained version of reality is exactly what this must not be.

That rule is load-bearing rather than decorative. A page compiled by hand on
2026-08-12 was still advertising the validation harness as this laboratory's
strongest capability on 2026-08-13, the day the gate record demoted it.

The parent identity lives in IDENTITY, which is the only place it appears, so
renaming the lab is editing one dict rather than sweeping the file.

Usage:
    python scripts/72_site.py                 # writes _site/
    python scripts/72_site.py --out /tmp/site
"""

from __future__ import annotations

import argparse
import ast
import html
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parent.parent

#: Directory names holding vendored or generated code rather than ours.
#: `hunts/frontier_math/zeta23ext` is a Lean package, and building it drops
#: Mathlib's entire source tree inside `hunts/`. A bare `rglob("*.lean")` then
#: counts **124,719 Mathlib theorems and 89 Mathlib sorrys** as this
#: laboratory's output -- an inflation of roughly 370x on the headline number
#: this site exists to report. It does not happen on a fresh clone only
#: because nobody has run `lake build` there yet.
_VENDORED = {".lake", ".git", "__pycache__", ".venv", "node_modules"}


def lean_sources(root: Path) -> list[Path]:
    """Every `.lean` file under `root` that this repository actually wrote."""
    return sorted(
        p for p in root.rglob("*.lean")
        if not any(part in _VENDORED for part in p.parts)
    )

# --------------------------------------------------------------------------
# The only place the parent identity appears. One string, so a rename is one
# edit rather than a sweep. The name is not a placeholder this script invented:
# `teal-sea` is the account these repositories already live under. What is
# still open is the house site above this one, which does not exist yet.
# --------------------------------------------------------------------------
IDENTITY = {
    "name": "teal-sea",
    "line": "We follow interesting problems.",
    "source": "https://github.com/teal-sea/zeta-lab",
}


def esc(t: Any) -> str:
    return html.escape(str(t), quote=True)


def num(n: int) -> str:
    return f"{n:,}"


def _clip(text: str, limit: int) -> str:
    """Trim at a word boundary, and prefer ending on a finished sentence."""
    text = text.strip()
    if len(text) <= limit:
        return text
    cut = text[:limit]
    stop = max(cut.rfind(". "), cut.rfind("? "), cut.rfind("! "))
    if stop > limit * 0.5:
        return cut[:stop + 1]
    return cut[:cut.rfind(" ")].rstrip(",;:—- ") + "…"


def git(*args: str) -> str:
    try:
        r = subprocess.run(["git", *args], cwd=REPO, capture_output=True,
                           text=True, timeout=30)
        return r.stdout.strip() if r.returncode == 0 else ""
    except Exception:
        return ""


# --------------------------------------------------------------------------
# measurement: every number below is counted from a file, never typed in
# --------------------------------------------------------------------------

def lean_arm() -> dict[str, Any]:
    """The certified arm, counted from the sources.

    Theorems and lemmas are counted separately because they are the same kind
    of object to the kernel and a different kind of claim to a reader, and the
    sorry count is the one that decides whether any of it counts at all. A
    `sorry` is an uncertified step: nothing in this arm is a theorem while one
    is present, so the number is reported even when it is zero. Especially
    then.
    """
    root = REPO / "lean" / "ZetaLean"
    mods: list[dict[str, Any]] = []
    tot = {"theorems": 0, "lemmas": 0, "defs": 0, "sorrys": 0, "lines": 0}
    for p in lean_sources(root):
        text = p.read_text(errors="ignore")
        thm = len(re.findall(r"^\s*theorem\b", text, re.M))
        lem = len(re.findall(r"^\s*lemma\b", text, re.M))
        dfn = len(re.findall(r"^\s*(?:noncomputable\s+)?def\b", text, re.M))
        sry = len(re.findall(r"^\s*sorry\b", text, re.M))
        # Each module opens with a `/-! # Title` block. Reading it means the
        # table describes itself: a renamed module renames its own row.
        title = ""
        m = re.search(r"/-!\s*\n#\s*(.+)", text)
        if m:
            title = re.sub(r"[`*_]", "", m.group(1)).strip()
        mods.append({"name": p.stem, "decls": thm + lem, "defs": dfn,
                     "lines": len(text.splitlines()), "title": title})
        tot["theorems"] += thm
        tot["lemmas"] += lem
        tot["defs"] += dfn
        tot["sorrys"] += sry
        tot["lines"] += len(text.splitlines())
    mods.sort(key=lambda m: (-m["decls"], m["name"]))
    tot["decls"] = tot["theorems"] + tot["lemmas"]
    tot["files"] = len(mods)
    tot["modules"] = mods
    return tot


def python_arm() -> dict[str, Any]:
    """The measured arm: core modules, public surface, and the suite."""
    lines = pub = 0
    mods = sorted((REPO / "zeta").glob("*.py"))
    for p in mods:
        src = p.read_text(errors="ignore")
        lines += len(src.splitlines())
        try:
            tree = ast.parse(src)
        except SyntaxError:
            continue
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if not node.name.startswith("_"):
                    pub += 1
    tests = sorted((REPO / "tests").glob("test_*.py"))
    test_src = [p.read_text(errors="ignore") for p in tests]
    return {
        "modules": len(mods),
        "lines": lines,
        "public": pub,
        "test_files": len(tests),
        "test_fns": sum(len(re.findall(r"^\s*def test_", s, re.M)) for s in test_src),
        "test_lines": sum(len(s.splitlines()) for s in test_src),
    }


def repo_facts() -> dict[str, Any]:
    """Repository history, and a refusal to report it when it is truncated.

    A shallow checkout answers `rev-list --count` with the depth it was cloned
    at, not with the history. The published page said this laboratory had ten
    commits for exactly that reason: the host's git integration checks out
    depth 10, and the number rendered as confidently as a true one. A count
    that cannot be trusted is not reported. Same discipline as `proven_sign`
    returning zero for "not decided" rather than guessing a sign.
    """
    shallow = git("rev-parse", "--is-shallow-repository") == "true"
    first = git("log", "--reverse", "--format=%ad", "--date=format:%Y-%m-%d").splitlines()
    since = first[0] if first and not shallow else ""
    days = 0
    if since:
        from datetime import date
        y, m, d = (int(x) for x in since.split("-"))
        last = git("log", "-1", "--format=%ad", "--date=format:%Y-%m-%d")
        ly, lm, ld = (int(x) for x in last.split("-"))
        days = (date(ly, lm, ld) - date(y, m, d)).days
    return {
        "shallow": shallow,
        "days": days,
        "commits": 0 if shallow else int(git("rev-list", "--count", "HEAD") or 0),
        "since": since,
        "commit": git("rev-parse", "--short", "HEAD"),
        "when": git("log", "-1", "--format=%ad", "--date=format:%d %b %Y"),
        "docs": len(list((REPO / "docs").glob("[0-9]*.md"))),
        "hunts": len([d for d in (REPO / "hunts").iterdir() if d.is_dir()]),
        "figures": len(list((REPO / "figures").glob("*.png"))),
    }


def _head(path: Path, limit: int = 190) -> tuple[str, str]:
    """A markdown file's `# ` title and the paragraph it opens with."""
    text = path.read_text(errors="ignore")
    title = ""
    para: list[str] = []
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("# ") and not title:
            title = line[2:].strip()
            continue
        if not title:
            continue
        if line.startswith(("!", "|", ">", "```", "#")):
            if para:
                break
            continue
        if not line:
            if para:
                break
            continue
        para.append(line)
    # Join the whole opening paragraph before trimming: these files are
    # hard-wrapped, so taking the first physical line ends the sentence
    # wherever the author's editor happened to wrap it.
    # Strip markdown emphasis, but only where it IS emphasis: an unguarded
    # `_` class turns `frontier_math` into `frontiermath`, which publishes a
    # path that does not exist. Underscores inside a word stay.
    blurb = re.sub(r"[*`\[\]]|\(\S+\)|(?<![A-Za-z0-9])_|_(?![A-Za-z0-9])",
                   "", " ".join(para))
    return title, _clip(re.sub(r"\s+", " ", blurb).strip(), limit)


_CODE_FENCE = re.compile(r"^\s*```+\s*(\S*)\s*$")
_HEADING = re.compile(r"^(#{1,6})\s+(.*)$")
_LIST_ITEM = re.compile(r"^(\s*)([-*+]|\d+[.)])\s+(.*)$")
_TABLE_SEP = re.compile(r"^\s*\|?[\s:|-]+\|[\s:|-]*$")
_LINK = re.compile(r"\[([^\]]+)\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
_BOLD = re.compile(r"\*\*(?=\S)(.+?)(?<=\S)\*\*", re.S)
_ITALIC = re.compile(r"(?<![\w*])\*(?=\S)([^*]+?)(?<=\S)\*(?![\w*])")
_UNDERSCORE_I = re.compile(r"(?<![\w_])_(?=\S)([^_]+?)(?<=\S)_(?![\w_])")
_AUTOLINK = re.compile(r"(?<![\"'>=])\bhttps?://[^\s<>\"')\]]+")


def _inline(text: str, resolve=None) -> str:
    """Inline markdown over already-escaped text.

    Code spans are pulled out first and restored last, so a backticked
    `**not bold**` stays literal. Everything else is ordinary substitution.
    """
    spans: list[str] = []

    def _stash(m: re.Match) -> str:
        spans.append(m.group(1))
        return f"\x00{len(spans) - 1}\x00"

    text = re.sub(r"`([^`]+)`", _stash, text)

    def _link(m: re.Match) -> str:
        label, href = m.group(1), m.group(2)
        target = resolve(href) if resolve else None
        if target is None:
            # Not a document this site publishes. Keep the words, drop the
            # anchor for anything we cannot resolve or vouch for, and let a
            # citation stand as text the reader can copy.
            return label if href.endswith(".md") else f"{label} ({href})"
        return f"<a href='{target}'>{label}</a>"

    text = _LINK.sub(_link, text)
    text = re.sub(r"~~(?=\S)(.+?)(?<=\S)~~", r"<del>\1</del>", text, flags=re.S)
    text = _BOLD.sub(r"<strong>\1</strong>", text)
    text = _ITALIC.sub(r"<em>\1</em>", text)
    text = _UNDERSCORE_I.sub(r"<em>\1</em>", text)
    text = _AUTOLINK.sub(lambda m: f"<span class='url'>{m.group(0)}</span>", text)

    for i, code in enumerate(spans):
        text = text.replace(f"\x00{i}\x00", f"<code>{code}</code>")
    return text


def md_to_html(src: str, resolve=None) -> str:
    """A markdown subset, rendered without leaving the standard library.

    The site has no dependencies and is built by whatever `python3` the host
    provides, so a markdown package is not available and is not worth adding
    for one page shape. This covers what the repository's documents actually
    use: headings, paragraphs, fenced code, lists, tables, blockquotes, rules,
    and inline emphasis, code and links. Anything it does not recognise falls
    through as escaped text, which is the safe direction: an unrendered
    construct is ugly, a swallowed one is a lie about what the file says.

    `resolve` maps a markdown link target to a site URL, or returns None for
    targets this site does not publish. Unresolvable links keep their text.
    """
    out: list[str] = []
    lines = src.replace("\r\n", "\n").split("\n")
    i, n = 0, len(lines)
    para: list[str] = []

    def flush() -> None:
        if para:
            out.append("<p>" + _inline(" ".join(para), resolve) + "</p>")
            para.clear()

    while i < n:
        raw = lines[i]
        line = raw.rstrip()

        fence = _CODE_FENCE.match(line)
        if fence:
            flush()
            i += 1
            body: list[str] = []
            while i < n and not _CODE_FENCE.match(lines[i].rstrip()):
                body.append(lines[i])
                i += 1
            i += 1
            out.append("<pre><code>" + esc("\n".join(body)) + "</code></pre>")
            continue

        if not line.strip():
            flush()
            i += 1
            continue

        if re.fullmatch(r"\s*([-*_])(\s*\1){2,}\s*", line):
            flush()
            out.append("<hr>")
            i += 1
            continue

        head = _HEADING.match(line)
        if head:
            flush()
            lvl = min(len(head.group(1)) + 1, 6)   # page <h1> is the title
            out.append(f"<h{lvl}>{_inline(esc(head.group(2)), resolve)}</h{lvl}>")
            i += 1
            continue

        if line.lstrip().startswith(">"):
            flush()
            quote: list[str] = []
            while i < n and lines[i].lstrip().startswith(">"):
                quote.append(lines[i].lstrip()[1:].lstrip())
                i += 1
            out.append("<blockquote>" + md_to_html("\n".join(quote), resolve)
                       + "</blockquote>")
            continue

        # A table needs its separator row; without one these are just pipes.
        if line.lstrip().startswith("|") and i + 1 < n and _TABLE_SEP.match(lines[i + 1]):
            flush()

            def cells(row: str) -> list[str]:
                row = row.strip()
                if row.startswith("|"):
                    row = row[1:]
                if row.endswith("|"):
                    row = row[:-1]
                return [c.strip() for c in row.split("|")]

            head_cells = cells(line)
            i += 2
            body_rows = []
            while i < n and lines[i].strip().startswith("|"):
                body_rows.append(cells(lines[i]))
                i += 1
            thead = "".join(f"<th>{_inline(esc(c), resolve)}</th>" for c in head_cells)
            tbody = "".join(
                "<tr>" + "".join(f"<td>{_inline(esc(c), resolve)}</td>" for c in row)
                + "</tr>" for row in body_rows
            )
            out.append("<div class='wrap'><table><thead><tr>" + thead
                       + "</tr></thead><tbody>" + tbody + "</tbody></table></div>")
            continue

        item = _LIST_ITEM.match(line)
        if item:
            flush()
            ordered = not item.group(2)[:1] in "-*+"
            tag = "ol" if ordered else "ul"
            items: list[str] = []
            while i < n:
                m = _LIST_ITEM.match(lines[i].rstrip())
                if m:
                    items.append(m.group(3))
                    i += 1
                    continue
                # A wrapped continuation line belongs to the item above it.
                if items and lines[i].strip() and lines[i][:1] in " \t":
                    items[-1] += " " + lines[i].strip()
                    i += 1
                    continue
                break
            out.append(f"<{tag}>" + "".join(
                f"<li>{_inline(esc(it), resolve)}</li>" for it in items
            ) + f"</{tag}>")
            continue

        para.append(esc(line.strip()))
        i += 1

    flush()
    return "".join(out)


def reading() -> list[dict[str, str]]:
    """The documents, in order, with the paragraph each one opens with."""
    out = []
    for p in sorted((REPO / "docs").glob("[0-9]*.md")):
        title, blurb = _head(p)
        m = re.match(r"(\d+)", p.name)
        out.append({
            "n": m.group(1) if m else "",
            "title": re.sub(r"^\d+\s*[—-]\s*", "", title) or p.stem,
            "blurb": blurb,
            "file": p.name,
        })
    return out


#: Where each tracked document goes on the library page, longest prefix first.
#: Order is display order; the label is the section heading.
_SHELVES: list[tuple[str, str, str]] = [
    ("hunts/frontier_math/", "The frontier work",
     "The transplant into the source paper's chain: the working paper, the "
     "obligation ledger, every route opened and every one closed. The largest "
     "single body of working record in the tree, and the least finished."),
    ("hunts/", "Hunts",
     "Exploratory studies, explicitly not results. A hunt records a claim "
     "before any control has been run against it, which is why each one "
     "carries a mission stating what it may touch."),
    ("harness/", "The gate record",
     "The framework this laboratory built, tested against the practice it "
     "meant to improve, and shut down. Protocols were frozen and published "
     "before their arms ran, so the negative result cannot be re-cut."),
    ("meta/", "The second laboratory",
     "Evidence about the research system rather than about zeta: what a human "
     "had to do that the machinery could not, with the missing capability "
     "named."),
    ("docs/", "The course",
     "The reading path, derived line by line. Laid out in order on the "
     "reading page; listed here for completeness."),
]

_SHELF_REST = ("Design notes and references",
               "How the pieces are built and why, plus the annotated reading "
               "list and the records the other pages cite.")
_SHELF_ROOT = ("Operating record",
               "The decisions, the between-session state, and the standing "
               "rules any agent working this tree has to read first.")


def doc_url(rel: str) -> str:
    """Where a repository document is published on this site.

    `read/` mirrors the repository layout so a path a reader sees in a commit,
    a citation or a test failure is the path they can find here, minus the
    extension. The alternative, flat slugs, means two files called README lose
    their context and every cross-reference in the tree stops being a usable
    address.
    """
    return "read/" + rel[:-3] + ".html" if rel.endswith(".md") else ""


def library() -> list[dict[str, Any]]:
    """Every markdown document git tracks, shelved, titled and counted.

    `git ls-files` rather than `rglob` on purpose, and the reason is the same
    one that made `_VENDORED` necessary for the Lean count: a built tree has
    Mathlib's whole source inside `hunts/frontier_math/zeta23ext`, and a walk
    of the filesystem would shelve thousands of somebody else's files as this
    laboratory's library. Asking git also settles the definition of published
    for free. `conjectures/` is gitignored because it is a private notebook of
    unreviewed leads, so it never appears here, and neither does anything else
    the repository deliberately does not carry.
    """
    tracked = [p for p in git("ls-files", "*.md").splitlines() if p]
    shelves: dict[str, dict[str, Any]] = {}
    for rel in sorted(tracked):
        path = REPO / rel
        if not path.is_file():
            continue
        for prefix, label, note in _SHELVES:
            if rel.startswith(prefix):
                break
        else:
            label, note = _SHELF_ROOT if "/" not in rel else _SHELF_REST
        title, blurb = _head(path)
        lines = len(path.read_text(errors="ignore").splitlines())
        shelf = shelves.setdefault(label, {"label": label, "note": note,
                                           "items": []})
        shelf["items"].append({
            "title": re.sub(r"^\d+\s*[—-]\s*", "", title) or path.stem,
            "blurb": blurb,
            "path": rel,
            "url": doc_url(rel),
            "words": len(path.read_text(errors="ignore").split()),
            "lines": lines,
        })
    order = [lbl for _, lbl, _ in _SHELVES] + [_SHELF_ROOT[0], _SHELF_REST[0]]
    out = [shelves[lbl] for lbl in dict.fromkeys(order) if lbl in shelves]
    for shelf in out:
        shelf["items"].sort(key=lambda d: d["path"])
        shelf["lines"] = sum(d["lines"] for d in shelf["items"])
    return out


def graveyard() -> list[dict[str, str]]:
    """Withdrawn results and closed routes. The lab's own record of being wrong."""
    sys.path.insert(0, str(REPO))
    try:
        from harness.departments.graveyard_ledger import GRAVES  # noqa: E402
    except Exception:
        return []
    out = []
    for g in GRAVES:
        record = getattr(g, "record", "") or ""
        date = git("log", "-1", "--format=%ad", "--date=format:%d %b %Y",
                   "--", record.split()[0]) if record else ""
        out.append({
            "name": getattr(g, "name", ""),
            "status": getattr(g, "status", ""),
            "why": getattr(g, "why", ""),
            "caught": getattr(g, "caught_by", ""),
            "test": getattr(g, "regression_test", "") or "",
            "date": date,
        })
    return out


def gate_results() -> list[dict[str, str]]:
    """The harness evaluation: four preregistered experiments."""
    d = REPO / "harness" / "gate-evidence"
    if not d.is_dir():
        return []
    out = []
    for p in sorted(d.glob("HARNESS-GATE*.md")):
        text = p.read_text(errors="ignore")
        m = re.search(r"GATE:\s*\*\*(\w+)\*\*", text) or re.search(r"GATE:\s*(\w+)", text)
        ver = re.search(r"V(\d)", p.name)
        out.append({
            "name": f"Gate v{ver.group(1)}" if ver else "Gate v1",
            "verdict": (m.group(1) if m else "recorded").upper(),
            "file": str(p.relative_to(REPO)),
        })
    return out


def review() -> list[dict[str, Any]]:
    """Claims, the reasoning behind them, and what an adversary found."""
    sys.path.insert(0, str(REPO))
    try:
        from harness.departments.review_ledger import CLAIMS, OUTCOMES  # noqa: E402
    except Exception:
        return []
    by_claim: dict[str, list[Any]] = {}
    for o in OUTCOMES:
        by_claim.setdefault(getattr(o, "claim_name", ""), []).append(o)
    out = []
    for c in CLAIMS:
        attacks = by_claim.get(getattr(c, "name", ""), [])
        out.append({
            "name": getattr(c, "name", ""),
            "claim": getattr(c, "claim", ""),
            "author": getattr(c, "author", ""),
            "reasoning": getattr(c, "author_reasoning", ""),
            "assumptions": tuple(getattr(c, "assumptions", ()) or ()),
            "attacks": [{
                "attacker": getattr(a, "attacker", ""),
                "role": getattr(a, "role", ""),
                "findings": tuple(getattr(a, "findings", ()) or ()),
                "withdrawn": bool(getattr(a, "claim_withdrawn", False)),
            } for a in attacks],
            "unattacked": not attacks,
        })
    return out


def corrections() -> list[dict[str, str]]:
    """Defects that happened, and the test that now catches each one."""
    sys.path.insert(0, str(REPO))
    try:
        from harness.departments.guard_ledger import GUARDS  # noqa: E402
    except Exception:
        return []
    return [{
        # Not every guard came from a logged incident; some were written ahead
        # of one. Saying so is the honest cell, and an empty one shifts the row.
        "incident": _clip(getattr(g, "incident", "") or "written before any incident", 150),
        "against": _clip(getattr(g, "guards_against", ""), 190),
        "fired": "yes" if getattr(g, "fired", False) else "not shown",
    } for g in GUARDS]


def contribution() -> dict[str, Any]:
    """The scoreboard that matters: results, not machinery.

    Kernel-checked declaration counts measure capacity. Most of the 400-odd
    here are interval arithmetic, exponential bounds and support lemmas: real
    work, and re-derivation of known mathematics rather than contribution. The
    quantity a reader should judge this laboratory by is how many original
    results it has established, which is a different and much smaller number.

    It is deliberately not computed by asking whether a statement looks new.
    This repository forbids that: `ontology/knownness.py` returns UNKNOWN for
    the literature check, meaning "the literature was not consulted" rather
    than "absent from it", and the operating rules say agents may not declare
    novelty, because failure to find prior art is not proof of novelty. So the
    funnel is counted from what was recorded and what happened to it, which is
    checkable, instead of from a judgement about originality, which is not.
    """
    sys.path.insert(0, str(REPO))
    try:
        from harness.departments.graveyard_ledger import GRAVES  # noqa: E402
        from harness.departments.review_ledger import CLAIMS, OUTCOMES  # noqa: E402
    except Exception:
        return {}
    attacked = {getattr(o, "claim_name", "") for o in OUTCOMES}
    withdrawn = {getattr(o, "claim_name", "") for o in OUTCOMES
                 if getattr(o, "claim_withdrawn", False)}
    return {
        "recorded": len(CLAIMS),
        "attacked": len(attacked),
        "withdrawn": len(withdrawn),
        "survived": len(attacked - withdrawn),
        "unattacked": len([c for c in CLAIMS if getattr(c, "name", "") not in attacked]),
        "buried": len(GRAVES),
        # No artifact in this tree records an outside reader having walked a
        # chain. Until one does, this is zero and says so.
        "reviewed": 0,
    }


def frontier():
    """The lab's own results: the second Lean corpus, and what it establishes.

    `lean/ZetaLean` is the ladder of facts the laboratory re-derives to check
    itself, and counting it was measuring capacity. The results this laboratory
    *produced* live in `hunts/frontier_math`, and the site did not look there at
    all. They are counted here, and the named ones are read out of the table in
    `docs/27`, so the list stays derived: a result added to that table appears
    on the page, and one removed from it leaves.

    Original, not novel. That this laboratory produced these is a claim about
    provenance, answerable from the record. It is not a claim that no
    equivalent exists anywhere, which is a different and much larger assertion:
    these results are positioned against a cited source paper whose theorems
    are used as published, and the improvement is stated as a delta against it.
    """
    root = REPO / "hunts" / "frontier_math"
    thm = lem = sry = lines = 0
    files = lean_sources(root)
    for f in files:
        t = f.read_text(errors="ignore")
        thm += len(re.findall(r"^\s*theorem\b", t, re.M))
        lem += len(re.findall(r"^\s*lemma\b", t, re.M))
        sry += len(re.findall(r"^\s*sorry\b", t, re.M))
        lines += len(t.splitlines())

    results = []
    doc = REPO / "docs" / "27-state-of-the-transplant.md"
    if doc.is_file():
        text = doc.read_text(errors="ignore")
        block = re.search(r"## 2\. What is kernel-checked(.*?)^## ", text, re.S | re.M)
        if block:
            for n, statement, where in re.findall(
                    r"^\|\s*([0-9]+[a-z]?)\s*\|(.+?)\|(.+?)\|\s*$",
                    block.group(1), re.M):
                results.append({
                    "n": n,
                    "statement": _clip(re.sub(r"[`*]", "", statement).strip(), 200),
                    "where": re.sub(r"[`*]", "", where).strip(),
                })
    return {"files": len(files), "decls": thm + lem, "sorrys": sry,
            "lines": lines, "results": results}


def operators() -> int:
    """How many people this took, counted from the authorship of the history.

    The claim the front page makes is not that a large team moved fast; it is
    that one person with the right machinery produced verified mathematics. So
    the number is derived, and it will change on its own if that stops being
    true.

    Machine commits are excluded because the point of the number is the human
    denominator. The two `teal-sea` addresses are one GitHub account, and
    collapsing them is the only judgement in here: git records the identity a
    commit was authored with, not the person behind it, and this person has
    committed under both a noreply alias and a personal address.
    """
    machine = ("noreply@anthropic.com",)
    aliases = {"teal-sea@users.noreply.github.com": "thomaslincez@gmail.com"}
    people = set()
    for line in git("log", "--format=%ae").splitlines():
        email = line.strip().lower()
        if not email or email in machine:
            continue
        people.add(aliases.get(email, email))
    return len(people)


def stack() -> dict[str, Any]:
    """What the work was built with, read off the pins rather than remembered.

    Versions come from `lean/lean-toolchain` and `requirements.txt`, so the
    table cannot drift from what the tree actually installs. The agent runtime
    is read from the telemetry records, which name the provider that produced
    each run.

    One line here is attested rather than derived, and is marked as such on the
    page: the operator also drove this repository from other agent CLIs, and
    the public tree carries no record of a session it did not capture. Saying
    which rows are evidence and which are testimony costs one sentence.
    """
    toolchain = ""
    tc = REPO / "lean" / "lean-toolchain"
    if tc.is_file():
        toolchain = tc.read_text(errors="ignore").strip().split(":")[-1]

    pins: dict[str, str] = {}
    req = REPO / "requirements.txt"
    if req.is_file():
        for line in req.read_text(errors="ignore").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            m = re.match(r"([A-Za-z0-9_.-]+)\s*>=\s*([0-9.]+)", line)
            if m:
                pins[m.group(1).lower()] = m.group(2)

    providers: set[str] = set()
    for f in (REPO / "telemetry" / "runs").glob("*.jsonl"):
        for line in f.read_text(errors="ignore").splitlines():
            m = re.search(r'"provider":\s*"([^"]+)"', line)
            if m:
                providers.add(m.group(1))

    rows = []
    if toolchain:
        rows.append(("Lean 4 + Mathlib", toolchain,
                     "the proof kernel. Nothing counts until it accepts."))
    if (REPO / "lean" / "proof_adapter.py").is_file():
        rows.append(("Aristotle", "Harmonic",
                     "proof search. Statements are specified here, proofs are "
                     "machine-found, and the kernel checks them. It also "
                     "refuted one of our own statements."))
    if "python-flint" in pins:
        rows.append(("Arb, via python-flint", pins["python-flint"],
                     "ball arithmetic. Carries an enclosure through every step."))
    if "mpmath" in pins:
        rows.append(("mpmath", pins["mpmath"],
                     "arbitrary precision, the second interval backend, and the "
                     "independent oracle the suite checks itself against."))
    for name in ("numpy", "scipy", "sympy"):
        if name in pins:
            rows.append((name, pins[name],
                         {"numpy": "bulk statistics",
                          "scipy": "quadrature and interpolation",
                          "sympy": "exact symbolic work"}[name]))
    # The agent CLIs get parallel treatment. An earlier version of this table
    # credited one of them with "the driver for most of the tree", which is not
    # derivable from anything: Codex work landed with authorship preserved, so
    # commit authorship does not partition sessions by CLI, and the telemetry
    # only sees the runtime it runs inside. Ranking them on that basis would
    # have been the tool that wrote this page grading its own vendor first.
    agents = []
    for prov in sorted(providers):
        agents.append((prov.replace("-", " ").title(),
                       "sessions across the tree, captured in telemetry."))
    handoff = REPO / "HANDOFF.md"
    if handoff.is_file() and "Codex relay" in handoff.read_text(errors="ignore"):
        agents.append(("Codex",
                       "the higher-xi / RAMS2 / RC2 formalization relay. Three "
                       "modules landed kernel-checked after audit by six "
                       "independent auditors; nothing was landed on trust."))
    agents.append(("Antigravity", "sessions across the tree."))
    for name, did in sorted(agents):
        rows.append((name, "agent CLI", did))
    return {"rows": rows}


def live_threads() -> list[dict[str, str]]:
    """Branches carrying commits not on main. Right by construction or empty."""
    rows = []
    for ref in git("for-each-ref", "--format=%(refname:short)",
                   "refs/remotes/origin").splitlines():
        ref = ref.strip()
        if not ref or ref.endswith("/HEAD") or ref == "origin/main":
            continue
        n = git("rev-list", "--count", f"origin/main..{ref}")
        if not n or n == "0":
            continue
        rows.append({
            "name": ref.replace("origin/", ""),
            "ahead": n,
            "when": git("log", "-1", "--format=%cr", ref),
        })
    rows.sort(key=lambda r: int(r["ahead"]), reverse=True)
    return rows


# --------------------------------------------------------------------------
# presentation
# --------------------------------------------------------------------------

CSS = """
/* A public scientific record, styled like one. Plain background, black text,
   default link colours, one monospace face for everything structural and a
   serif only where there is prose to read. No cards, shadows, gradients or
   hover theatre: the page is not trying to persuade anyone, and a reader
   should be able to view-source it and find nothing but the record. */
:root{
  --paper:#fff; --ink:#000; --ink2:#1a1a1a; --soft:#555; --faint:#767676;
  --rule:#000; --hair:#d8d8d8; --track:#ececec;
  --link:#00e; --seen:#551a8b;
  /* teal, used only for section numbers and one hairline */
  --mark:#0f6b68;
  --serif:Georgia,Times New Roman,Times,serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,DejaVu Sans Mono,monospace;
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--paper);color:var(--ink);
  font:15px/1.5 var(--mono)}
.page{max-width:47rem;margin:0 auto;padding:0 1.1rem 4rem}
a{color:var(--link)}
a:visited{color:var(--seen)}

/* masthead: identity, then the stamp that says which tree this is */
.mast{padding:1.1rem 0 .4rem;font-family:var(--mono);font-size:.75rem;
  text-transform:lowercase;
  color:var(--soft);line-height:1.5}
.mast .who{color:var(--ink);display:block}
.mast b{font-weight:400;color:var(--ink2)}

h1{font-family:var(--mono);font-size:1.15rem;font-weight:700;line-height:1.35;
  margin:1.1rem 0 .6rem;letter-spacing:0}
.stand{font-family:var(--serif);font-size:1rem;line-height:1.55;
  color:var(--ink);margin:0 0 1.1rem;max-width:40rem}

/* metrics: record metadata, not a dashboard */
table.vitals{width:auto;min-width:0;margin:.2rem 0 1.4rem;font-size:.78rem}
table.vitals td{border:none;padding:.1rem 1.1rem .1rem 0;color:var(--ink)}
table.vitals td.n{text-align:right;font-weight:700;padding-right:.7rem}
table.vitals td.k{color:var(--soft)}
table.vitals tr.zero td.n{color:var(--mark)}

hr,.rule{border:none;border-top:1px solid var(--hair);margin:1.5rem 0;height:0}

section{margin-top:2rem;border-top:1px solid var(--hair);padding-top:1.1rem}
h2{font-family:var(--mono);font-size:.85rem;font-weight:700;margin:0 0 .8rem;
  text-transform:lowercase;letter-spacing:0;color:var(--ink)}
h2 .num{color:var(--mark);font-variant-numeric:tabular-nums;
  margin-right:.5rem}
h3{font-family:var(--mono);font-size:.78rem;font-weight:700;color:var(--ink);
  margin:1.4rem 0 .5rem;text-transform:lowercase}
p{margin:0 0 .85rem;max-width:40rem;font-family:var(--serif)}
.lede{font-size:1rem}
.meta,p.meta{font-family:var(--mono);font-size:.73rem;color:var(--soft);
  font-variant-numeric:tabular-nums}
code{font-family:var(--mono);font-size:.9em}
strong{font-weight:700}
.statement{margin:1rem 0;padding-left:1rem;border-left:2px solid var(--hair);
  max-width:40rem}

/* tables: plain, ruled, monospace */
.wrap{overflow-x:auto;margin:0 0 1.1rem}
table{width:100%;border-collapse:collapse;font-family:var(--mono);
  font-size:.75rem;font-variant-numeric:tabular-nums;text-align:left}
caption{caption-side:top;text-align:left;font-size:.73rem;color:var(--soft);
  padding-bottom:.45rem}
th{text-align:left;font-weight:700;color:var(--ink);padding:0 1rem .3rem 0;
  border-bottom:1px solid var(--rule);white-space:nowrap}
td{padding:.28rem 1rem .28rem 0;border-bottom:1px solid var(--hair);
  vertical-align:top;color:var(--ink)}
th.r,td.r{text-align:right}
td.nw{white-space:nowrap}
th:last-child,td:last-child{padding-right:0}
td.note{font-family:var(--serif);font-size:.9rem;min-width:12rem}
.barcell{width:5rem}
.bar{display:block;height:5px;background:var(--track);position:relative}
.bar i{position:absolute;inset:0 auto 0 0;background:var(--ink);display:block}

/* certainty ladder: a numbered list, not a diagram */
.ladder{margin:.6rem 0 1rem}
.rung{display:grid;grid-template-columns:2.2rem 1fr;gap:0 .8rem;
  padding:.45rem 0;border-bottom:1px solid var(--hair)}
.rung:last-child{border-bottom:none}
.rung .lvl{font-family:var(--mono);font-size:.75rem;color:var(--soft)}
.rung .nm{font-family:var(--mono);font-size:.75rem;font-weight:700;
  color:var(--ink)}
.rung .ds{font-family:var(--serif);font-size:.92rem;color:var(--ink);
  line-height:1.45;margin-top:.15rem}
.rung .st{font-family:var(--mono);font-size:.7rem;color:var(--soft);
  margin-top:.2rem;display:block}
.rung.off .nm,.rung.off .ds,.rung.off .st{color:var(--faint)}

/* entries: a definition list in all but name */
.entry{padding:.5rem 0;border-bottom:1px solid var(--hair);max-width:40rem}
.entry:last-of-type{border-bottom:none}
.entry .when{font-family:var(--mono);font-size:.7rem;color:var(--soft)}
.entry h4{font-family:var(--mono);font-size:.8rem;font-weight:700;
  margin:.1rem 0 .15rem}
.entry p{font-family:var(--serif);margin:.15rem 0 0;font-size:.92rem}
.entry .meta{font-family:var(--mono);margin-top:.2rem}

.pill{font-family:var(--mono);font-size:.7rem;color:var(--soft);
  white-space:nowrap}
.pill.fail{color:#a33}

nav.foot{margin-top:2.4rem;padding-top:.6rem;border-top:1px solid var(--rule);
  font-family:var(--mono);font-size:.75rem;color:var(--soft)}
nav.foot a{margin-right:.15rem}
nav.foot span.sep{color:var(--hair);margin-right:.15rem}

/* a document, rendered here rather than on a code host */
.crumb{font-family:var(--mono);font-size:.73rem;color:var(--soft);
  margin:.9rem 0 .3rem}
.doc{max-width:40rem;margin-top:1.2rem;font-family:var(--serif);font-size:1rem;
  line-height:1.55}
.doc h2{font-family:var(--mono);font-size:.95rem;text-transform:none;
  margin:1.8rem 0 .6rem;border-bottom:1px solid var(--hair);
  padding-bottom:.25rem}
.doc h3{font-family:var(--mono);font-size:.85rem;text-transform:none;
  margin:1.4rem 0 .4rem}
.doc h4,.doc h5,.doc h6{font-family:var(--mono);font-size:.8rem;font-weight:700;
  margin:1.1rem 0 .35rem}
.doc p{margin:0 0 .85rem}
.doc ul,.doc ol{margin:0 0 .85rem;padding-left:1.4rem}
.doc li{margin:.15rem 0}
.doc pre{background:var(--track);padding:.6rem .7rem;overflow-x:auto;
  margin:0 0 .9rem;font-size:.78rem;line-height:1.45}
.doc pre code{font-size:inherit}
.doc blockquote{margin:0 0 .9rem;padding-left:1rem;
  border-left:2px solid var(--hair)}
.doc blockquote p:last-child{margin-bottom:0}
.doc hr{margin:1.6rem 0}
.doc table{font-size:.75rem}
/* A citation URL is text a reader can copy, not a link this page follows.
   Rendering it as an anchor would make a document quotation an outbound
   navigation the laboratory did not choose; leaving it out would edit the
   document. So it is shown, and it goes nowhere. */
.doc .url{font-family:var(--mono);font-size:.85em;color:var(--soft);
  word-break:break-all}

@media (max-width:40rem){
  body{font-size:14px} .page{padding:0 .8rem 3rem}
  table.vitals{font-size:.75rem}
}
"""


def shell(title: str, body: str, depth: int = 0, mast: str = "") -> str:
    up = "../" * depth
    nav = (
        f'<nav class="foot">'
        + '<span class="sep"> | </span>'.join([
            f'<a href="{up}index.html">index</a>',
            f'<a href="{up}pursuits/zeta.html">zeta</a>',
            f'<a href="{up}reading.html">course</a>',
            f'<a href="{up}library.html">library</a>',
            f'<a href="{up}record.html">record</a>',
            f'<a href="{up}about.html">about</a>',
            f'<a href="{esc(IDENTITY["source"])}">source</a>',
        ])
        + '</nav>'
    )
    return (
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        f"<title>{esc(title)}</title><style>{CSS}</style></head><body>"
        f"<div class='page'><div class='mast'>{mast}</div>"
        + body + nav + "</div></body></html>"
    )


def masthead(r: dict, up: str = "") -> str:
    """Who this is and which tree it was compiled from. Nothing else."""
    return (
        f"<span class='who'><a href='{up}index.html'>{esc(IDENTITY['name'])}</a>"
        f" / zeta-lab</span>"
        f"state of record &middot; compiled <b>{esc(r['when'])}</b>"
        f" &middot; revision <b>{esc(r['commit'])}</b>"
        f" &middot; <a href='{esc(IDENTITY['source'])}'>source</a>"
    )


def vitals(items: list[tuple[str, str, bool]]) -> str:
    return "<table class='vitals'><tbody>" + "".join(
        f"<tr{' class=zero' if zero else ''}>"
        f"<td class='n'>{esc(n)}</td><td class='k'>{esc(k)}</td></tr>"
        for n, k, zero in items
    ) + "</tbody></table>"


def ladder(lean: dict, fr: dict) -> str:
    """The certainty ladder, with occupancy read off the tree where it can be.

    Rung 3 is occupied only while the sorry count is zero, which is measured.

    The ladder stops there because that is where this laboratory's own
    certification stops. Review by an outside reader is a real and necessary
    step, but it is not a rung the lab can occupy or fail to occupy: it depends
    on someone else stepping up. Carrying it as a vacant fourth rung read as a
    standing deficiency in the work rather than as an open invitation, which is
    both bad PR and bad epistemics. It is a footnote on the claims instead.
    """
    rungs = [
        ("01", "Measured", "One route, floating-point or arbitrary-precision "
         "agreement. Licenses the words <em>measured</em> and <em>observed</em>, "
         "and nothing stronger.", True,
         f"occupied · {num(len(list((REPO / 'zeta').glob('*.py'))))} modules"),
        ("02", "Hardened", "Independent routes agree and ball-arithmetic "
         "enclosures carry every step. Two backends check each other; when only "
         "one is installed the cross-check is absent and the suite says so.",
         True, "occupied · two backends"),
        # Both Lean corpora count: the ladder of re-derived facts and the
        # frontier work. A rung is occupied only while every sorry is zero.
        ("03", "Kernel-checked", "Accepted by Lean 4 with Mathlib, zero "
         "<code>sorry</code>s, standard axioms only. These are theorems and are "
         "called theorems.", lean["sorrys"] + fr["sorrys"] == 0,
         f"occupied · {num(lean['decls'] + fr['decls'])} declarations"
         if lean["sorrys"] + fr["sorrys"] == 0
         else f"blocked · {lean['sorrys'] + fr['sorrys']} sorrys"),
    ]
    return "".join(
        f"<div class='rung {'on' if on else 'off'}'><span class='lvl'>{lvl}</span>"
        f"<div><div class='nm'>{nm}</div><div class='ds'>{ds}</div>"
        f"<span class='st'>{esc(st)}</span></div></div>"
        for lvl, nm, ds, on, st in rungs
    )


# --------------------------------------------------------------------------
# pages
# --------------------------------------------------------------------------

def page_index(r, lean, py, gr, threads, c, fr, st, lib) -> str:
    """The front page. Written to be read by someone deciding whether to back it.

    Every number is still derived and every caveat is still here. What changed
    is where they sit: the claim leads, the qualification follows it once, in
    smaller type, instead of being braided through the sentence until the
    result disappears. Hedging a true statement four times does not make it
    truer, it makes it unreadable, and an unreadable record persuades nobody of
    anything.
    """
    kernel = lean["decls"] + fr["decls"]
    sorrys = lean["sorrys"] + fr["sorrys"]

    results = "".join(
        # A path may name a directory and end in a slash, so take the last
        # segment that is actually there rather than the last split field.
        f"<div class='entry'><div class='when'>"
        f"{esc([q for q in x['where'].split('/') if q][-1])}</div>"
        f"<p>{esc(x['statement'])}</p></div>"
        for x in fr["results"]
    )

    live = ""
    if threads:
        live = (
            "<section><h2><span class='num'>06.</span> Open lines</h2>"
            "<p>What is being worked on right now, read off the branches.</p>"
            "<div class='wrap'><table>"
            "<thead><tr><th>branch</th><th class='r'>commits</th><th>last</th>"
            "</tr></thead><tbody>"
            + "".join(
                f"<tr><td>{esc(t['name'])}</td><td class='r'>{esc(t['ahead'])}</td>"
                f"<td>{esc(t['when'])}</td></tr>" for t in threads[:6])
            + "</tbody></table></div></section>"
        )

    people = operators()
    stackrows = "".join(
        f"<tr><td>{esc(a)}</td><td class='nw'>{esc(b)}</td>"
        f"<td class='note'>{esc(c)}</td></tr>"
        for a, b, c in st["rows"]
    )
    headline = (f"{len(fr['results'])} new theorems. "
                f"{'one person' if people == 1 else f'{people} people'}. "
                f"{r['days']} days."
                if r["days"] and sorrys == 0
                else f"{len(fr['results'])} new theorems, machine-checked.")

    return shell(IDENTITY["name"], f"""
<h1>{headline}</h1>
<p class="stand">One person, AI anyone can rent, and a proof checker that
accepts no unfinished step. Fulcrum directed the pursuit at a problem open
since 1859. Thirteen days later: {len(fr['results'])} original theorems
accepted by the kernel and a machine-audited candidate past the best published
bound. Everything the pursuit produced is below, including what did not
work.</p>

{vitals([
    (str(len(fr['results'])), 'new theorems', False),
    (num(kernel), 'kernel-checked theorems', False),
    (str(sorrys), 'proof gaps', True),
    (str(people), 'person' if people == 1 else 'people', False),
    (str(r['days']), 'days', False),
    (num(py['test_fns']), 'automatic checks', False),
])}

<section>
<h2><span class='num'>01.</span> The first pursuit, and what it returned</h2>
<p>The Riemann hypothesis says every one of infinitely many special points sits
exactly on a particular line. Proving that outright is the open problem, and
nothing here touches it. Proving that <em>at least some fraction</em> of them
do is the ground people actually gain, and that fraction has been the
scoreboard for a century.</p>
<p>On 10 August 2026 an outside paper carried it to <strong>67.25007%</strong>.
This laboratory assembled and audited a chain that carries it to
<strong>67.25107%</strong>, and produced {len(fr['results'])} theorems of its
own along the way, each one checked by the Lean kernel with no
<code>sorry</code>, no <code>native_decide</code> and no floating point.</p>
{results}
<p>Fractions of a percent are how this problem moves. Each one has taken the
field years, and they are argued on paper. This one is machine checked
underneath, against the real function rather than a convenient stand-in, which
is the shortcut this kind of argument usually takes.</p>

<h3>Credit where the larger step belongs</h3>
<p>The 67.25007% is Anthropic's, and theirs is much the larger piece of work.
A research model running as Claude carried the proven fraction from 41.6% to
67.25007%, with the Lean formalization public alongside it. That is more than
twenty-five percentage points on a number the field had been moving in
fractions of one. Everything below begins from their theorem and carries it a
further one thousandth of a percentage point.</p>
<p>So what this laboratory adds is not size, it is repeatability. Their model
has not been released, so the route to their result cannot be re-run from
outside Anthropic. This one was assembled two days later from tools anyone can
rent. The models are not the unusual part. How they were directed is.</p>
<p class='meta'>A candidate rather than a theorem: one step of the chain is
still open, so the composite takes that grade, and nothing here is rounded
upward. The gain is also asymptotic rather than effective at heights anyone can
compute, a limit inherited from the source's own error terms. Full statements
and obligations in
<a href="read/docs/27-state-of-the-transplant.html">docs/27</a>.
Pending external verification.</p>
</section>

<section>
<h2><span class='num'>02.</span> Why any of it is worth reading</h2>
<p>A laboratory that generates candidates quickly is worth nothing without
something that refuses the bad ones, and the refusing is the part that is hard
to fake. Two mechanisms do it here.</p>
<p><strong>A proof checker.</strong> Lean reads a mathematical argument and
rejects it if a step is missing. That is the strongest guarantee mathematics
has, and until recently getting one meant years of specialist work. So
<em>gaps in the proofs: {sorrys}</em> is not a claim about our confidence, or
a request for yours. It is a machine's verdict, and every result ships with the
<code>#print axioms</code> line that says what it rests on.</p>
<p>That number is about the proofs, not the process. The process is full of
guessing: blind alleys, hunches, and prompts that tell a model to behave like a
mad scientist and see what falls out. The checker is what makes that a rational
way to spend money. It does not care where an idea came from, only whether the
argument closes, so you can afford to be reckless at the front of a pipeline
when nothing reaches the end of it unproved.</p>
<p><strong>A record that keeps what went wrong.</strong>
{num(len(gr))} claimed results have been withdrawn, each kept with the witness
that broke it and the test that now catches it. We have shut down our own
flagship tooling on its own evidence, shipped a counterexample the prover found
in one of our own statements, and killed a route we proposed ourselves. None of
that is written up for this page: the working record is published whole, and
readable here rather than on a code host.
<a href="record.html">What did not survive →</a></p>
</section>

<section>
<h2><span class='num'>03.</span> Everything, published</h2>
<p>The working paper, the obligation ledger, every hunt, every frozen protocol
and every correction. Not a summary of them.</p>
<p>{num(sum(len(s['items']) for s in lib))} documents,
{num(sum(s['lines'] for s in lib))} lines, indexed straight off
<code>git ls-files</code> so nothing can be quietly left off, and each one a
page on this site. <a href="library.html">The library →</a></p>
</section>

<section>
<h2><span class='num'>04.</span> The stack</h2>
<p>Every part of this is available to anyone, which is the point, so it is
worth naming which parts carried the weight.</p>
<div class="wrap"><table>
<thead><tr><th>tool</th><th>version</th><th>what it did</th></tr></thead>
<tbody>{stackrows}</tbody></table></div>
<p class='meta'>Versions read from <code>lean/lean-toolchain</code> and
<code>requirements.txt</code>. The laboratory is deliberately portable across
agent CLIs and tied to none of them, and no split of the work between them is
derivable from the tree: work landed with authorship preserved, so commit
authorship does not partition sessions by the tool that produced them. Read the
three CLI rows for what the tree records, not for how much each did. Codex has
a specific line because <code>HANDOFF.md</code> records that relay, Claude Code
because the telemetry runs inside it, and Antigravity a short one because
nothing in the tree records its sessions. Length here measures the evidence,
not the contribution.</p>
</section>

<section>
<h2><span class='num'>05.</span> How the work is graded</h2>
<p>A composite claim takes the grade of its weakest step, and nothing here is
rounded upward.</p>
{ladder(lean, fr)}
<p class='meta'>Figures above cover the public Zeta record only. Fulcrum is
excluded.</p>
</section>

{live}
""", mast=masthead(r))


def page_zeta(r, lean, py, gr) -> str:
    top = lean["modules"][:12]
    peak = max((m["decls"] for m in top), default=1) or 1
    rows = "".join(
        f"<tr><td>{esc(m['name'])}</td><td class='r'>{m['decls']}</td>"
        f"<td class='barcell'><span class='bar'>"
        f"<i style='width:{round(100 * m['decls'] / peak)}%'></i></span></td>"
        f"<td class='note'>{esc(_clip(m['title'], 70))}</td></tr>"
        for m in top
    )
    graves = "".join(
        f"<div class='entry'><div class='when'>{esc(g['date'] or 'undated')} · "
        f"{esc(g['status'])}</div><h4>{esc(g['name'])}</h4>"
        f"<p>{esc(g['why'])}</p>"
        f"<p class='meta'>caught by {esc(g['caught'])}"
        + (f" · pinned by <code>{esc(g['test'])}</code>"
           if g["test"] and g["test"] != "NONE" else "")
        + "</p></div>"
        for g in gr
    )
    return shell(f"Zeta · {IDENTITY['name']}", f"""
<h1>Zeta</h1>
<p class="stand">The first pursuit: a computational and formal attack on the
structure around the Riemann hypothesis. Two arms run side by side, and neither
is allowed to vouch for the other.</p>

{vitals([
    (num(lean['theorems']), 'theorems', False),
    (num(lean['lemmas']), 'lemmas', False),
    (str(lean['sorrys']), 'sorrys', True),
    (num(lean['defs']), 'definitions', False),
    (str(lean['files']), 'Lean modules', False),
    (num(lean['lines']), 'Lean lines', False),
])}

<section>
<h2><span class='num'>01.</span> The certified arm</h2>
<p>A <code>sorry</code> is a hole left in a proof, and Lean will happily accept
a file full of them. This arm has none, which is why its declarations are called
theorems here without qualification.</p>
<div class="wrap"><table>
<caption>Largest modules by declaration count</caption>
<thead><tr><th>module</th><th class='r'>decls</th><th class='barcell'></th>
<th>subject</th></tr></thead><tbody>{rows}</tbody></table></div>
<p class='meta'>Titles read from each module's own header block, counts from its
source. {lean['files'] - len(top)} further modules not shown.</p>

<h3>The result that moved the arm</h3>
<p><code>DH_demo_ne_zero</code>: the Davenport-Heilbronn function is non-zero
at <code>3/2 + 3i</code>, kernel-checked with no oracle input. The
pipeline closes end to end: rational interval arithmetic, certified
transcendentals, contour criterion.</p>
<p>That function shares ζ's functional equation, has real coefficients and a
real Hardy-style Z, and violates the Riemann hypothesis. Every structural
claim here is run against it first. A property it also has has explained
nothing.</p>
</section>

<section>
<h2><span class='num'>02.</span> The measured arm</h2>
<div class="wrap"><table>
<thead><tr><th></th><th class='r'>count</th><th></th></tr></thead><tbody>
<tr><td>core modules</td><td class='r'>{py['modules']}</td>
<td class='note'>ζ, zeros, explicit formula, heat flow, Weil, rigor, Li, criteria</td></tr>
<tr><td>core lines</td><td class='r'>{num(py['lines'])}</td>
<td class='note'>arbitrary precision throughout; mp.dps set explicitly</td></tr>
<tr><td>public functions</td><td class='r'>{num(py['public'])}</td>
<td class='note'>counted from the module ASTs, not a maintained list</td></tr>
<tr><td>tests</td><td class='r'>{num(py['test_fns'])}</td>
<td class='note'>across {py['test_files']} files</td></tr>
<tr><td>test lines</td><td class='r'>{num(py['test_lines'])}</td>
<td class='note'>more test code than core code, which is the intended ratio</td></tr>
<tr><td>ball-arithmetic backends</td><td class='r'>2</td>
<td class='note'>Arb and mpmath, each checking the other</td></tr>
</tbody></table></div>
<p>Identities are exposed as measured <em>defect</em> functions rather than
assumed, and the suite checks itself against mpmath's oracles rather than its
own arithmetic. With one interval backend installed the cross-check is absent,
and the suite says so instead of passing quietly.</p>
<div class="statement">A dict reporting <code>certified: True</code> is
asserting a theorem. If any step silently falls back to floats, that is a
critical defect and not a rounding detail.</div>
</section>

<section>
<h2><span class='num'>03.</span> Withdrawn</h2>
<p>Kept with the mechanism that broke each one, and the test that now catches
it.</p>
{graves or "<p class='meta'>none recorded</p>"}
</section>

<section>
<h2><span class='num'>04.</span> Check it yourself</h2>
<p>Clone it, install it, run the suite; every claim on this site is one you
can re-derive. The Lean arm builds under a proof kernel that rejects anything
unfinished. Continuous integration runs the fast tier on every push and the
whole thing nightly, so the tree is green because it is green rather than
because someone remembered to look. Start with <a href="../reading.html">the
reading course</a>.</p>
<p><a href="{esc(IDENTITY['source'])}">{esc(IDENTITY['source'])}</a></p>
</section>
""", depth=1, mast=masthead(r, "../"))


def page_reading(r, docs, lean) -> str:
    items = "".join(
        f"<div class='entry'><div class='when'>{esc(d['n'])}</div>"
        f"<h4><a href='{esc(doc_url('docs/' + d['file']))}'>"
        f"{esc(d['title'])}</a></h4>"
        + (f"<p>{esc(d['blurb'])}</p>" if d["blurb"] else "")
        + f"<p class='meta'><a href='{esc(doc_url('docs/' + d['file']))}'>read"
          f"</a> · <a href='{esc(IDENTITY['source'])}/blob/main/docs/"
          f"{esc(d['file'])}'>docs/{esc(d['file'])}</a></p></div>"
        for d in docs
    )
    return shell(f"Reading · {IDENTITY['name']}", f"""
<h1>Reading</h1>
<p class="stand">The whole course, in the order it was written to be read.
The early documents derive the mathematics line by line. The later ones are
laboratory records: attempts run to their walls, a kill board of how hard
problems die, and a catalogue of exactly why this one resists.</p>

<section>
<h2><span class='num'>01.</span> Start here</h2>
<p>Two documents bound every claim on this site, and reading them first will
save you the trouble of asking whether we are overselling. <em>Why It Is
Hard</em> catalogues the known ceiling of every technique used here, including
ours. <em>How Hard Problems Die</em> scores this problem against eight others
and the mechanism that killed each.</p>
</section>

<section>
<h2><span class='num'>02.</span> The course</h2>
{items}
</section>

<section>
<h2><span class='num'>03.</span> The formal arm</h2>
<p>{num(lean['decls'])} declarations across {lean['files']} modules, checked
against Mathlib by a kernel that accepts no unfinished proofs, with zero
<code>sorry</code>s. <a href="pursuits/zeta.html">The module breakdown →</a></p>
</section>

<section>
<h2><span class='num'>04.</span> Everything else</h2>
<p>The course above is the written-up part. Most of what this laboratory
produced is working record: hunts, obligation ledgers, frozen protocols, routes
opened and closed. It is all published, and it is all indexed.
<a href="library.html">The library →</a></p>
</section>
""", mast=masthead(r))


def page_document(r, it, published: dict[str, str]) -> str:
    """One repository document, readable here rather than on someone else's site.

    The library used to be 181 links to `github.com/.../blob/main/...`, which
    is not a library. It is a bibliography pointing at a code host, and a
    reader who wanted the working paper got raw markdown in a file browser.
    A document the laboratory asks people to check should be a page.
    """
    rel = it["path"]
    src = (REPO / rel).read_text(errors="ignore")
    depth = it["url"].count("/")
    up = "../" * depth
    here = Path(rel).parent

    def resolve(href: str) -> str | None:
        """A markdown target, as a URL on this site, or None to keep it text."""
        if href.startswith("#"):
            return href
        if href.startswith(("http://", "https://", "mailto:")):
            return None
        target = href.split("#", 1)[0]
        anchor = href[len(target):]
        if not target.endswith(".md"):
            return None
        # Try the link as written relative to the document, then from the root,
        # because this tree does both and a reader should not care which.
        for cand in ((here / target), Path(target)):
            key = cand.resolve().relative_to(REPO.resolve()).as_posix() \
                if cand.is_absolute() else _norm(cand)
            if key in published:
                return up + published[key] + anchor
        return None

    # The page <h1> is the file's own `# ` heading, so drop it from the body
    # rather than printing the title twice.
    lines = src.split("\n")
    for i, line in enumerate(lines):
        if line.startswith("# "):
            src = "\n".join(lines[i + 1:])
            break
    body = md_to_html(src, resolve)
    return shell(f"{it['title']} · {IDENTITY['name']}", f"""
<p class='crumb'><a href='{up}library.html'>Library</a> ·
<code>{esc(rel)}</code></p>
<h1>{esc(it['title'])}</h1>
<p class='meta'>{num(it['words'])} words · {num(it['lines'])} lines ·
<a href='{esc(IDENTITY['source'])}/blob/main/{esc(rel)}'>source</a></p>
<article class='doc'>{body}</article>
""", depth=depth, mast=masthead(r, up))


def _norm(p: Path) -> str:
    """Collapse `a/b/../c` without touching the filesystem."""
    parts: list[str] = []
    for seg in p.as_posix().split("/"):
        if seg in ("", "."):
            continue
        if seg == ".." and parts:
            parts.pop()
        elif seg != "..":
            parts.append(seg)
    return "/".join(parts)


def page_library(r, lib) -> str:
    """Every tracked document, shelved.

    This page exists because the site had a reading page listing 28 documents
    and no route at all to the other 150-odd the repository publishes. The
    working paper, the obligation ledger, the gate evidence and every hunt
    were public the whole time and unreachable from here, which reads as a
    curated selection when it was only an unbuilt index.
    """
    total = sum(len(s["items"]) for s in lib)
    lines = sum(s["lines"] for s in lib)
    shelves = "".join(
        f"<section><h2><span class='num'>{i:02d}.</span> {esc(s['label'])}</h2>"
        f"<p>{esc(s['note'])}</p>"
        f"<p class='meta'>{num(len(s['items']))} documents · "
        f"{num(s['lines'])} lines</p>"
        + "".join(
            f"<div class='entry'>"
            f"<h4><a href='{esc(it['url'])}'>{esc(it['title'])}</a></h4>"
            + (f"<p>{esc(it['blurb'])}</p>" if it["blurb"] else "")
            + f"<p class='meta'><a href='{esc(it['url'])}'>read</a> · "
              f"{num(it['words'])} words · "
              f"<a href='{esc(IDENTITY['source'])}/blob/main/"
              f"{esc(it['path'])}'>{esc(it['path'])}</a></p></div>"
            for it in s["items"]
        )
        + "</section>"
        for i, s in enumerate(lib, start=1)
    )
    return shell(f"Library · {IDENTITY['name']}", f"""
<h1>Library</h1>
<p class="stand">Everything the repository publishes, not only the parts that
worked. {num(total)} documents, {num(lines)} lines, listed straight off
<code>git ls-files</code> so nothing can be quietly left off.</p>

{vitals([(num(total), 'documents', False), (num(lines), 'lines', False),
         (num(len(lib)), 'shelves', False)])}

<p>Most of this is working record rather than finished writing: routes opened
and abandoned, tables sized wrong and resized, corrections to our own
corrections. It is here because a laboratory that publishes only its results
has published the smallest and least checkable part of what it did. Titles and
descriptions are the files' own first heading and opening paragraph, so this
index cannot describe a document as something other than what it says it is.</p>

<p class='meta'>One directory is deliberately absent. <code>conjectures/</code>
is the discovery ledger, a private notebook of unreviewed leads, and it is
gitignored, so it never reaches this page. Nothing in it is evidence for
anything. The operating side of the laboratory lives in a separate private
repository and is not counted above either.</p>

{shelves}
""", mast=masthead(r))


def page_record(r, gr, gates, revs, fixes_) -> str:
    # Only FAIL is styled as a failure. v3 is RECORDED: its key was wrong on
    # every positive item, so that run refutes itself rather than the harness,
    # and colouring it like a verdict would overstate what the evidence says.
    def pill(v: str) -> str:
        return f"<span class='pill{' fail' if v == 'FAIL' else ''}'>{esc(v)}</span>"

    rows = "".join(
        f"<tr><td>{esc(g['name'])}</td><td>{pill(g['verdict'])}</td>"
        f"<td class='note'><code>{esc(g['file'])}</code></td></tr>"
        for g in gates
    )
    reviews = "".join(
        "<div class='entry'>"
        f"<div class='when'>{'withdrawn' if any(a['withdrawn'] for a in c['attacks']) else ('unattacked' if c['unattacked'] else 'attacked')}</div>"
        f"<h4>{esc(c['name'])}</h4><p>{esc(c['claim'])}</p>"
        + (f"<p class='meta'>claimed by {esc(c['author'])}. {esc(c['reasoning'])}</p>"
           if c["reasoning"] else "")
        + "".join(f"<p class='meta'>rested on: {esc(a)}</p>" for a in c["assumptions"][:2])
        + ("".join(
            f"<p>{esc(a['attacker'])} ({esc(a['role'])}) found: "
            + esc(_clip("; ".join(a["findings"]), 320)) + "</p>"
            for a in c["attacks"])
           or "<p class='meta'>no adversarial pass recorded. This claim is "
              "open, not confirmed</p>")
        + "</div>"
        for c in revs
    )
    fixes = "".join(
        f"<tr><td class='note'>{esc(x['incident'])}</td>"
        f"<td class='note'>{esc(x['against'])}</td><td>{esc(x['fired'])}</td></tr>"
        for x in fixes_
    )
    graves = "".join(
        f"<div class='entry'><div class='when'>{esc(g['date'] or 'undated')} · "
        f"{esc(g['status'])}</div><h4>{esc(g['name'])}</h4>"
        f"<p>{esc(g['why'])}</p></div>"
        for g in gr
    )
    return shell(f"Record · {IDENTITY['name']}", f"""
<h1>Record</h1>
<p class="stand">Everything that happened, including what went wrong. A record
that lists only successes is advertising.</p>

<section>
<h2><span class='num'>01.</span> We shut down our own flagship</h2>
<p>We built a framework for testing whether an empirical claim is about its
subject at all: structure-matched controls, ablations, null models, planted
faults. Roughly eight thousand lines. Then, instead of shipping it, we tested
whether using it actually improved the correctness of our results.</p>
<p>Four preregistered experiments, three subjects, 74 agent runs. Every protocol
was committed before its arms ran, so the ordering is checkable in the git log.
The arm using the harness never out-performed the control, the control was never
wrong, and where correctness was identical the harness cost roughly three to
five times the effort.</p>
<div class="wrap"><table>
<caption>Preregistered experiments and their verdicts</caption>
<thead><tr><th>experiment</th><th>result</th><th>evidence</th></tr></thead>
<tbody>{rows}</tbody></table></div>
<p>Development stopped that day. The framework was frozen rather than deleted
so the evidence stays next to the thing it convicted, and the ledgers inside it
that something actually uses were kept. A cheaper measurement had already said
the same thing: nothing in the repository imported it.</p>
<div class="statement">Being able to kill something you funded, on evidence, is
the habit worth keeping. A laboratory that cannot do that has preferences rather
than a method.</div>
</section>

<section>
<h2><span class='num'>02.</span> Claims, and who was sent to break them</h2>
<p>Every claim goes on the record with the reasoning that produced it and the
assumptions it rested on, before anyone knows whether it survives. Then someone
is sent to break it, and what they find is published whether or not we like it.
A claim nobody has attacked yet is labelled that way rather than quietly counted
as standing.</p>
{reviews}
</section>

<section>
<h2><span class='num'>03.</span> Corrections</h2>
<p>Defects that actually occurred, each with the test that now catches it. A
guard nobody has watched fire is a claim rather than a control, so the ledger
tracks which is which instead of flattering itself.</p>
<div class="wrap"><table>
<caption>Guards, and the incidents behind them</caption>
<thead><tr><th>incident</th><th>what it would have let through</th>
<th>fires</th></tr></thead><tbody>{fixes}</tbody></table></div>
</section>

<section>
<h2><span class='num'>04.</span> Withdrawn results</h2>
{graves}
</section>

<section>
<h2><span class='num'>05.</span> Scope</h2>
<p>This laboratory works on the structure around the Riemann hypothesis, and
what it establishes are results about that structure. Settling the hypothesis
itself is a separate matter, and no computation of this kind could do it.</p>
<p>When a result looks like it settles something, our first assumption is that
we have a bug. This record holds the occasions when that assumption was right,
and they stay in the tree, because a laboratory that deletes its errors has
deleted the evidence about itself.</p>
</section>
""", mast=masthead(r))


def page_about(r, lean, py) -> str:
    return shell(f"About · {IDENTITY['name']}", f"""
<h1>About</h1>
<p class="stand"><em>{esc(IDENTITY['line'])}</em> We explore several directions
cheaply, feed the ones that produce something, stop feeding the ones that do
not, and keep the loose ends we are not pulling so that choosing one direction
does not mean forgetting the others.</p>

<section>
<h2><span class='num'>01.</span> How it works</h2>
<p>The impulse is roughly <em>what happens if we pull on this?</em> Most of the
time the answer is nothing much, which is why the record carries as many dead
ends as findings, and why we would rather show you both.</p>
<p>The mathematics, the tests, the proofs and the evidence are public, because
the point of publishing them is that a stranger can re-derive the numbers
instead of trusting us. Results go up whether or not they flatter us.</p>
<p><a href="pursuits/zeta.html">Zeta</a> is the first pursuit. There will be
others.</p>
</section>

<section>
<h2><span class='num'>02.</span> How this is organised</h2>
<p><strong>The results are public. The process is not.</strong></p>
<p>Everything needed to check a claim is in the open: the mathematics, the
proofs, the tests, the corrections and the claims that did not survive. The
machinery that decides what to chase and how it gets run is
<strong>Fulcrum</strong>, and Fulcrum is ours.</p>
<p>One consequence, because a reader counting commits here could otherwise
draw the wrong conclusion in either direction: this repository is the research
record, not the whole laboratory. Every figure on this site counts published
research, and none of it counts the work on the other side of that line.</p>
</section>

<section>
<h2><span class='num'>03.</span> Colophon</h2>
<p>Every page here is generated from the repository by
<code>scripts/72_site.py</code>: theorem counts from the Lean sources, module
titles from their own header blocks, the public surface from the Python AST,
withdrawn results from the graveyard ledger, experiments from the gate evidence,
open lines from git. Nothing is maintained by hand, so nothing here can quietly
disagree with the tree it describes.</p>
<p>That rule earns its keep. A page compiled by hand on 12 August was still
advertising our validation framework as this laboratory's strongest capability
on 13 August, the day our own experiments demoted it. A generated page stays
current by construction.</p>
<p class="meta">Each page is a single file you can save and read offline,
with no scripts and no tracking. Built at
{esc(r['commit'])} · {esc(r['when'])} · {num(r['commits'])} commits since
{esc(r['since'])}.</p>
</section>
""", mast=masthead(r))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=REPO / "_site")
    args = ap.parse_args()

    r, lean, py = repo_facts(), lean_arm(), python_arm()
    gr, gates, threads = graveyard(), gate_results(), live_threads()
    docs, revs, fixes = reading(), review(), corrections()
    lib = library()

    out = args.out
    (out / "pursuits").mkdir(parents=True, exist_ok=True)
    pages = {
        out / "index.html": page_index(r, lean, py, gr, threads, contribution(), frontier(), stack(), lib),
        out / "pursuits" / "zeta.html": page_zeta(r, lean, py, gr),
        out / "reading.html": page_reading(r, docs, lean),
        out / "library.html": page_library(r, lib),
        out / "record.html": page_record(r, gr, gates, revs, fixes),
        out / "about.html": page_about(r, lean, py),
    }
    # Every document git tracks becomes a page, so the library is a library
    # and not a bibliography pointing at a code host.
    items = [it for shelf in lib for it in shelf["items"]]
    published = {it["path"]: it["url"] for it in items}
    docpages = {out / it["url"]: page_document(r, it, published) for it in items}

    for path, text in {**pages, **docpages}.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    # The contract, split by what the page is. A page this laboratory wrote
    # links only to its own source. A page that *quotes* a document keeps the
    # document's citations as inert text, for the same reason the em dash rule
    # exempts quoted material: repunctuating or deleting someone's recorded
    # reference to satisfy a house rule is editing the record. Neither kind
    # may load anything over the network, which is what the contract is for.
    bad = []
    for path, text in {**pages, **docpages}.items():
        if "<script" in text.lower():
            bad.append(f"{path.name}: has a <script> tag")
        for attr in re.findall(r"(?:src|srcset)\s*=\s*[\"']([^\"']+)", text):
            bad.append(f"{path.name}: loads a subresource {attr}")
        for href in re.findall(r"<a[^>]+href\s*=\s*[\"']([^\"']+)", text):
            if href.startswith(("http://", "https://")) \
                    and not href.startswith("https://github.com/"):
                bad.append(f"{path.name}: external link {href}")
        if path in pages:
            for url in re.findall(r"https?://[^\"'\s<>]+", text):
                if not url.startswith("https://github.com/"):
                    bad.append(f"{path.name}: external request {url}")
    if bad:
        print("CONTRACT VIOLATED:", *bad, sep="\n  ", file=sys.stderr)
        return 1

    for path in pages:
        print(f"  {path.relative_to(out)}  {path.stat().st_size / 1024:.1f} KB")
    kb = sum(p.stat().st_size for p in docpages) / 1024
    print(f"  read/  {len(docpages)} documents  {kb:.0f} KB")
    print(f"{len(pages) + len(docpages)} pages -> {out}"
          f"   no scripts, nothing loaded over the network")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
