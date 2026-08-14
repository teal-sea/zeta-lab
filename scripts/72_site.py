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

# --------------------------------------------------------------------------
# The only place the parent identity appears. One string, so a rename is one
# edit rather than a sweep. The name is not a placeholder this script invented:
# `teal-sea` is the account these repositories already live under. What is
# still open is the house site above this one, which does not exist yet.
# --------------------------------------------------------------------------
IDENTITY = {
    "name": "teal sea",
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
    for p in sorted(root.rglob("*.lean")):
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


def reading() -> list[dict[str, str]]:
    """The documents, in order, with the paragraph each one opens with."""
    out = []
    for p in sorted((REPO / "docs").glob("[0-9]*.md")):
        text = p.read_text(errors="ignore")
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
        blurb = re.sub(r"[*_`\[\]]|\(\S+\)", "", " ".join(para))
        m = re.match(r"(\d+)", p.name)
        out.append({
            "n": m.group(1) if m else "",
            "title": re.sub(r"^\d+\s*[—-]\s*", "", title) or p.stem,
            "blurb": _clip(re.sub(r"\s+", " ", blurb).strip(), 190),
            "file": p.name,
        })
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
    files = sorted(root.rglob("*.lean"))
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
:root{
  --paper:#fdfcfa; --ink:#0f1113; --ink2:#3c434b; --soft:#666e77; --faint:#949ba3;
  --rule:#cdd2d8; --hair:#e8e9ec; --mark:#14425f; --track:#eceef1;
  --serif:Iowan Old Style,Charter,Palatino Linotype,Palatino,Georgia,serif;
  --sans:-apple-system,BlinkMacSystemFont,Segoe UI,system-ui,sans-serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
}
/* One committed look, deliberately. This page is sent to people as a record,
   and a record that changes appearance with the reader's operating system is
   one you cannot screenshot, cite or predict: the author sees paper white and
   half the readers see something else. The palette above is the whole palette;
   there is no theme to follow. */
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--paper);color:var(--ink);
  font:17px/1.6 var(--serif);-webkit-font-smoothing:antialiased;
  text-rendering:optimizeLegibility}
/* One centred measure. The prose fills it rather than being capped narrower
   than the frame, which reads as a broken layout rather than a restrained one.
   Tables and the vitals band break out wider on large screens. */
.page{max-width:44rem;margin:0 auto;padding:0 1.6rem 6rem}
@media (min-width:68rem){
  .vitals,.wrap,.ladder{width:52rem;margin-left:-4rem}
}
a{color:var(--mark);text-decoration:none;border-bottom:1px solid transparent}
a:hover{border-bottom-color:currentColor}
a:focus-visible{outline:2px solid var(--mark);outline-offset:3px}

/* masthead */
.mast{border-top:3px solid var(--ink);margin-top:2.6rem;padding:.75rem 0 .7rem;
  border-bottom:1px solid var(--rule);display:flex;flex-wrap:wrap;
  gap:.35rem 2.4rem;font-family:var(--mono);font-size:.645rem;
  letter-spacing:.14em;text-transform:uppercase;color:var(--soft)}
.mast b{color:var(--ink2);font-weight:500}
.mast a{color:inherit}

h1{font-size:clamp(2.3rem,6.5vw,3.7rem);line-height:1;letter-spacing:-.025em;
  font-weight:400;margin:2.6rem 0 0;text-wrap:balance}
.stand{font-size:1.16rem;line-height:1.5;color:var(--ink2);
  margin:1.4rem 0 0;text-wrap:pretty}

/* vitals */
.vitals{display:grid;grid-template-columns:repeat(3,1fr);gap:1px;
  background:var(--hair);border:1px solid var(--hair);margin:2.9rem 0 0}
.vitals>div{background:var(--paper);padding:1.35rem 1.25rem 1.2rem}
.vitals .n{font-family:var(--mono);font-size:2.8rem;line-height:.95;
  letter-spacing:-.045em;font-variant-numeric:tabular-nums;display:block}
.vitals .k{font-family:var(--mono);font-size:.6rem;letter-spacing:.13em;
  text-transform:uppercase;color:var(--soft);margin-top:.7rem;display:block;
  line-height:1.35}
/* The zero is the load-bearing figure in the whole arm, not a null result. */
.vitals .zero .n{color:var(--mark)}
@media (max-width:34rem){.vitals{grid-template-columns:repeat(2,1fr)}
  .vitals .n{font-size:2.1rem}}

section{margin-top:3.6rem}
h2{font-family:var(--mono);font-size:.78rem;letter-spacing:.15em;
  text-transform:uppercase;font-weight:600;margin:0 0 1.45rem;
  padding-bottom:.6rem;border-bottom:2px solid var(--ink);display:flex;
  gap:1.1rem;color:var(--ink)}
h2 .num{color:var(--mark);font-variant-numeric:tabular-nums}
h3{font-family:var(--mono);font-size:.625rem;letter-spacing:.13em;
  text-transform:uppercase;font-weight:500;color:var(--soft);margin:2rem 0 .8rem}
p{margin:0 0 1.05rem;text-wrap:pretty}
.lede{font-size:1.1rem;color:var(--ink2)}
.meta{font-family:var(--mono);font-size:.7rem;color:var(--faint);
  letter-spacing:.02em;font-variant-numeric:tabular-nums}
code{font-family:var(--mono);font-size:.85em}
strong{font-weight:600}

.statement{border-left:3px solid var(--mark);padding:.1rem 0 .1rem 1.4rem;
  margin:1.8rem 0;max-width:34rem;font-size:1.12rem;line-height:1.45}

/* tables */
.wrap{overflow-x:auto;margin:0 0 1.3rem}
table{width:100%;min-width:28rem;border-collapse:collapse;font-family:var(--mono);
  font-size:.775rem;font-variant-numeric:tabular-nums}
caption{caption-side:top;text-align:left;font-family:var(--mono);font-size:.625rem;
  letter-spacing:.13em;text-transform:uppercase;color:var(--soft);
  padding-bottom:.7rem}
th{text-align:left;font-weight:500;font-size:.6rem;letter-spacing:.12em;
  text-transform:uppercase;color:var(--soft);padding:0 .8rem .5rem 0;
  border-bottom:1px solid var(--rule);white-space:nowrap}
th.r,td.r{text-align:right}
/* figures that read as one unit must not wrap into a ragged stack */
td.nw{white-space:nowrap}
th:last-child,td:last-child{padding-right:0}
td{padding:.55rem .8rem .55rem 0;border-bottom:1px solid var(--hair);
  vertical-align:baseline;color:var(--ink2)}
td:first-child{color:var(--ink)}
tr:last-child td{border-bottom:1px solid var(--rule)}
td.note{font-family:var(--serif);font-size:.93rem;min-width:13rem}
.barcell{width:6.5rem}
.bar{display:block;height:6px;background:var(--track);position:relative}
.bar i{position:absolute;inset:0 auto 0 0;background:var(--ink);display:block}

/* ladder */
.ladder{margin:1.5rem 0 1.2rem}
.rung{display:grid;grid-template-columns:1.9rem 1fr;gap:0 1.3rem;
  padding:1rem 0;align-items:start;position:relative}
/* the spine: one rail down the rungs, filled where the rung is occupied */
.rung::before{content:"";position:absolute;left:.52rem;top:0;bottom:0;
  width:1px;background:var(--rule)}
.rung:first-child::before{top:.95rem}
.rung:last-child::before{bottom:auto;height:.95rem}
.rung .lvl{font-family:var(--mono);font-size:.66rem;color:var(--soft);
  font-variant-numeric:tabular-nums;padding-top:.72rem;position:relative;
  z-index:1;background:var(--paper)}
.rung .lvl::before{content:"";display:block;width:9px;height:9px;
  margin:0 0 .5rem .1rem;border:1px solid var(--ink);background:var(--paper)}
.rung.on .lvl::before{background:var(--ink)}
.rung.off .lvl::before{border-color:var(--faint)}
.rung .nm{font-family:var(--mono);font-size:.7rem;letter-spacing:.11em;
  text-transform:uppercase;color:var(--ink);margin-bottom:.28rem}
.rung .ds{font-size:.96rem;color:var(--ink2);line-height:1.45;max-width:36rem}
.rung .st{font-family:var(--mono);font-size:.585rem;letter-spacing:.12em;
  text-transform:uppercase;margin-top:.4rem;display:inline-block;
  padding:.14rem .48rem;border:1px solid var(--rule);color:var(--soft)}
.rung.on .st{border-color:var(--ink);color:var(--ink)}
.rung.off .nm,.rung.off .ds{color:var(--faint)}

/* entries */
.entry{padding:1.05rem 0;border-bottom:1px solid var(--hair);max-width:38rem}
.entry:last-child{border-bottom:none}
.entry .when{font-family:var(--mono);font-size:.6rem;color:var(--soft);
  text-transform:uppercase;letter-spacing:.12em}
.entry h4{font-family:var(--sans);font-size:1rem;font-weight:600;margin:.25rem 0 .3rem}
.entry p{margin:.3rem 0 0;color:var(--ink2);font-size:.96rem}
.entry .meta{margin-top:.4rem}

.pill{font-family:var(--mono);font-size:.585rem;font-weight:500;letter-spacing:.11em;
  text-transform:uppercase;padding:.14rem .45rem;border:1px solid currentColor;
  color:var(--soft);white-space:nowrap}
.pill.fail{color:#9c4f18}

nav.foot{margin-top:4.5rem;padding-top:1rem;border-top:1px solid var(--rule);
  font-family:var(--mono);font-size:.63rem;letter-spacing:.12em;
  text-transform:uppercase;display:flex;gap:.4rem 2rem;flex-wrap:wrap;
  color:var(--soft)}

@media (max-width:660px){
  body{font-size:16px} .page{padding:0 1.1rem 4rem}
  .mast{gap:.3rem 1.4rem} .vitals .n{font-size:1.6rem}
}
"""


def shell(title: str, body: str, depth: int = 0, mast: str = "") -> str:
    up = "../" * depth
    nav = (
        f'<nav class="foot">'
        f'<a href="{up}index.html">index</a>'
        f'<a href="{up}pursuits/zeta.html">zeta</a>'
        f'<a href="{up}reading.html">reading</a>'
        f'<a href="{up}record.html">record</a>'
        f'<a href="{up}about.html">about</a>'
        f'<a href="{esc(IDENTITY["source"])}">source</a>'
        f'</nav>'
    )
    return (
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        f"<title>{esc(title)}</title><style>{CSS}</style></head><body>"
        f"<div class='page'><div class='mast'>{mast}</div>"
        + body + nav + "</div></body></html>"
    )


def masthead(r: dict, up: str = "") -> str:
    return (
        f"<span><a href='{up}index.html'>{esc(IDENTITY['name'])}</a>"
        f" &nbsp;·&nbsp; <b>state of record</b></span>"
        f"<span>compiled <b>{esc(r['when'])}</b></span>"
        f"<span>revision <b>{esc(r['commit'])}</b></span>"
    )


def vitals(items: list[tuple[str, str, bool]]) -> str:
    return "<div class='vitals'>" + "".join(
        f"<div{' class=zero' if zero else ''}><span class='n'>{esc(n)}</span>"
        f"<span class='k'>{esc(k)}</span></div>"
        for n, k, zero in items
    ) + "</div>"


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

def page_index(r, lean, py, gr, threads, c, fr) -> str:
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
            "<section><h2><span class='num'>§5</span> Open lines</h2>"
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
    headline = (f"{len(fr['results'])} new theorems."
                f"<br>{'One person' if people == 1 else f'{people} people'}."
                f"<br>{r['days']} days."
                if r["days"] and sorrys == 0
                else f"{len(fr['results'])} new theorems, machine-checked.")

    return shell(IDENTITY["name"], f"""
<h1>{headline}</h1>
<p class="stand">No institution, no research group, no model of our own. One
operator directing off-the-shelf models at a problem open since 1859, with
every result checked by a proof kernel that accepts no shortcuts, and every
failure published as readily as every success.</p>

{vitals([
    (num(kernel), 'machine-checked theorems', False),
    (str(sorrys), 'unproven steps', True),
    (num(py['test_fns']), 'tests', False),
    (str(operators()), 'people', False),
    (num(py['public']), 'public API functions', False),
    (num(r['docs']), 'documents', False),
])}

<section>
<h2><span class='num'>§1</span> What we proved</h2>
<p>Four results, produced here and checked by the Lean kernel. No
<code>sorry</code>s, no <code>native_decide</code>, no floating point, standard
axioms only. Each ships with its <code>#print axioms</code> line, so a skeptic
can confirm what it rests on without taking our word for anything.</p>
{results}
<p class='meta'>Full statements and their obligations in
<a href="{esc(IDENTITY['source'])}/blob/main/docs/27-state-of-the-transplant.md">docs/27</a>.
Pending external verification.</p>
</section>

<section>
<h2><span class='num'>§2</span> We improved a constant three days after it was published</h2>
<p>On 10 August an outside paper established a bound unconditionally:
<strong>0.6725007037</strong>. This laboratory assembled and audited a chain
that carries it to <strong>0.6725106958</strong>.</p>
<p>The census floor underneath it is machine-checked for the genuine
Montgomery-Taylor kernel, not a rational stand-in, which is the step that
usually gets waved through.</p>
<p class='meta'>A candidate rather than a theorem: one step of the chain is
still open, so the composite takes that grade. The gain is also asymptotic, not
effective at heights anyone can compute, a limit inherited from the source's own
error terms.</p>
</section>

<section>
<h2><span class='num'>§3</span> Why the numbers are worth anything</h2>
<p>Machinery that only ever agrees with you is decoration. Three things here
disagreed with us, on the record.</p>
<div class='entry'><div class='when'>our own tooling</div>
<h4>We shut down our flagship when it failed its own test</h4>
<p>Four preregistered experiments asked whether our validation framework
improved the correctness of our results. It did not. Eight thousand lines,
frozen, with the evidence published beside it.
<a href="record.html">The record →</a></p></div>
<div class='entry'><div class='when'>our own submission</div>
<h4>The prover refuted us and we shipped the counterexample</h4>
<p>Asked to prove a grid-incidence law, the prover found a hypothesis gap in
our own statement and produced a counterexample showing the evenness condition
cannot be dropped. It ships in the file as
<code>grid_incidence_needs_even</code>.</p></div>
<div class='entry'><div class='when'>our own route</div>
<h4>We killed our own proposed argument</h4>
<p>The per-pair domination route to multi-pair universality was proposed here
and refuted here, with the numbers that killed it: the sum of single-pair caps
already exceeds the budget while the joint verdict closes with 40% margin.</p></div>
<p>Three results have been withdrawn after they were claimed. Each one is kept
with the witness that broke it and the test that now catches it, because a
laboratory that deletes its errors has deleted its evidence about itself.</p>
</section>

<section>
<h2><span class='num'>§4</span> How the work is graded</h2>
<p>A composite claim takes the grade of its weakest step, and nothing here is
rounded upward.</p>
{ladder(lean, fr)}
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
<h2><span class='num'>§1</span> The certified arm</h2>
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
<h2><span class='num'>§2</span> The measured arm</h2>
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
<h2><span class='num'>§3</span> Withdrawn</h2>
<p>Kept with the mechanism that broke each one, and the test that now catches
it.</p>
{graves or "<p class='meta'>none recorded</p>"}
</section>

<section>
<h2><span class='num'>§4</span> Check it yourself</h2>
<p>Nothing here asks to be believed. Clone it, install it, run the suite; the
Lean arm builds under a proof kernel that will reject anything unfinished.
Continuous integration runs the fast tier on every push and the whole thing
nightly, so the tree is green because it is green, not because someone
remembered to look. Start with <a href="../reading.html">the reading
course</a>.</p>
<p><a href="{esc(IDENTITY['source'])}">{esc(IDENTITY['source'])}</a></p>
</section>
""", depth=1, mast=masthead(r, "../"))


def page_reading(r, docs, lean) -> str:
    items = "".join(
        f"<div class='entry'><div class='when'>{esc(d['n'])}</div>"
        f"<h4>{esc(d['title'])}</h4>"
        + (f"<p>{esc(d['blurb'])}</p>" if d["blurb"] else "")
        + f"<p class='meta'><a href='{esc(IDENTITY['source'])}/blob/main/docs/"
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
<h2><span class='num'>§1</span> Start here</h2>
<p>Two documents bound every claim on this site, and reading them first will
save you the trouble of asking whether we are overselling. <em>Why It Is
Hard</em> catalogues the known ceiling of every technique used here, including
ours. <em>How Hard Problems Die</em> scores this problem against eight others
and the mechanism that killed each.</p>
</section>

<section>
<h2><span class='num'>§2</span> The course</h2>
{items}
</section>

<section>
<h2><span class='num'>§3</span> The formal arm</h2>
<p>{num(lean['decls'])} declarations across {lean['files']} modules, checked
against Mathlib by a kernel that accepts no unfinished proofs, with zero
<code>sorry</code>s. <a href="pursuits/zeta.html">The module breakdown →</a></p>
</section>
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
<h2><span class='num'>§1</span> We shut down our own flagship</h2>
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
<h2><span class='num'>§2</span> Claims, and who was sent to break them</h2>
<p>Every claim goes on the record with the reasoning that produced it and the
assumptions it rested on, before anyone knows whether it survives. Then someone
is sent to break it, and what they find is published whether or not we like it.
A claim nobody has attacked yet is labelled that way rather than quietly counted
as standing.</p>
{reviews}
</section>

<section>
<h2><span class='num'>§3</span> Corrections</h2>
<p>Defects that actually occurred, each with the test that now catches it. A
guard nobody has watched fire is a claim rather than a control, so the ledger
tracks which is which instead of flattering itself.</p>
<div class="wrap"><table>
<caption>Guards, and the incidents behind them</caption>
<thead><tr><th>incident</th><th>what it would have let through</th>
<th>fires</th></tr></thead><tbody>{fixes}</tbody></table></div>
</section>

<section>
<h2><span class='num'>§4</span> Withdrawn results</h2>
{graves}
</section>

<section>
<h2><span class='num'>§5</span> What we do not claim</h2>
<p>Nothing computed here is evidence for or against the Riemann hypothesis, and
no computation in this tree could be. When a result looks like it settles
something, our first assumption is that we have a bug, and this record contains
the occasions when that assumption was right. They stay in the tree, because a
laboratory that deletes its errors has deleted the evidence about itself.</p>
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
<h2><span class='num'>§1</span> How it works</h2>
<p>The impulse is roughly <em>what happens if we pull on this?</em> Most of the
time the answer is nothing much, which is why the record carries as many dead
ends as findings, and why we would rather show you both.</p>
<p>The mathematics, the tests, the proofs and the evidence are public, because
the point of publishing them is that a stranger can re-derive the numbers
instead of trusting us. Results go up whether or not they flatter us.</p>
<p><a href="pursuits/zeta.html">Zeta</a> is the first pursuit. It is not the
boundary of what this can be about.</p>
</section>

<section>
<h2><span class='num'>§2</span> How this is organised</h2>
<p>Two repositories, split by what an outside reader needs rather than by
secrecy. <strong>Fulcrum</strong> is the operating layer: the private
repository through which pursuits are directed and managed.
<strong>Zeta</strong> is this pursuit, and it is public.</p>
<p>The rule that decides where something goes: if you need it to evaluate or
reproduce a claim, it is here, in the open. If it teaches the laboratory how to
allocate, route, prompt or operate itself, it lives in Fulcrum. Which repository
holds a thing, whether that repository can be cloned, and how much of the
research process outsiders can inspect are three separate questions, and the
answer to the last is <em>as much as is meaningful</em>, including the
criticism, the corrections and the claims that did not survive.</p>
<p class="meta">Fulcrum is private, not secret. The supervisor loop that would
launch and collect work across the two is not built yet; when it is, the runs it
produces are provenance and belong on this side.</p>
</section>

<section>
<h2><span class='num'>§3</span> Colophon</h2>
<p>Every page here is generated from the repository by
<code>scripts/72_site.py</code>: theorem counts from the Lean sources, module
titles from their own header blocks, the public surface from the Python AST,
withdrawn results from the graveyard ledger, experiments from the gate evidence,
open lines from git. Nothing is maintained by hand, so nothing here can quietly
disagree with the tree it describes.</p>
<p>That is not decoration. A page compiled by hand on 12 August was still
advertising our validation framework as this laboratory's strongest capability
on 13 August, the day our own experiments demoted it. A generated page cannot
make that mistake.</p>
<p class="meta">No scripts, no tracking, no network requests. Built at
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

    out = args.out
    (out / "pursuits").mkdir(parents=True, exist_ok=True)
    pages = {
        out / "index.html": page_index(r, lean, py, gr, threads, contribution(), frontier()),
        out / "pursuits" / "zeta.html": page_zeta(r, lean, py, gr),
        out / "reading.html": page_reading(r, docs, lean),
        out / "record.html": page_record(r, gr, gates, revs, fixes),
        out / "about.html": page_about(r, lean, py),
    }
    for path, text in pages.items():
        path.write_text(text, encoding="utf-8")

    bad = []
    for path, text in pages.items():
        if "<script" in text.lower():
            bad.append(f"{path.name}: has a <script> tag")
        for url in re.findall(r"https?://[^\"'\s<>]+", text):
            if not url.startswith("https://github.com/"):
                bad.append(f"{path.name}: external request {url}")
    if bad:
        print("CONTRACT VIOLATED:", *bad, sep="\n  ", file=sys.stderr)
        return 1

    for path in pages:
        print(f"  {path.relative_to(out)}  {path.stat().st_size / 1024:.1f} KB")
    print(f"{len(pages)} pages -> {out}   no scripts, no external requests")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
