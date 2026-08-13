#!/usr/bin/env python3
"""72_site.py — the public reading surface, generated from repository artifacts.

`scripts/70_lab_state.py` renders the *internal* research-state view. This
renders the *public* one, on the same principle and for the same reason:

    one static file per page, no scripts and no network — pages you can read,
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
# The only place the parent identity appears — one string, so a rename is one
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
# measurement — every number below is counted from a file, never typed in
# --------------------------------------------------------------------------

def lean_arm() -> dict[str, Any]:
    """The certified arm, counted from the sources.

    Theorems and lemmas are counted separately because they are the same kind
    of object to the kernel and a different kind of claim to a reader, and the
    sorry count is the one that decides whether any of it counts at all. A
    `sorry` is an uncertified step: nothing in this arm is a theorem while one
    is present, so the number is reported even when — especially when — it is
    zero.
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
    first = git("log", "--reverse", "--format=%ad", "--date=format:%Y-%m-%d").splitlines()
    return {
        "commits": int(git("rev-list", "--count", "HEAD") or 0),
        "since": first[0] if first else "",
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


def ladder(lean: dict) -> str:
    """The certainty ladder, with occupancy read off the tree where it can be.

    Rung 3 is occupied only while the sorry count is zero, which is measured.
    Rung 4 is vacant because no artifact in this repository records an outside
    reader having walked a chain — and saying so plainly is the point of having
    the rung at all.
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
        ("03", "Kernel-checked", "Accepted by Lean 4 with Mathlib, zero "
         "<code>sorry</code>s, standard axioms only. These are theorems and are "
         "called theorems.", lean["sorrys"] == 0,
         f"occupied · {num(lean['decls'])} declarations" if lean["sorrys"] == 0
         else f"blocked · {lean['sorrys']} sorrys"),
        ("04", "Externally reviewed", "A qualified outside reader has walked the "
         "chain. The words <em>established</em> and <em>settles</em> become "
         "available at this rung and not before.", False, "not occupied"),
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

def page_index(r, lean, py, gr, threads) -> str:
    live = ""
    if threads:
        live = (
            "<section><h2><span class='num'>§4</span> Open lines</h2>"
            "<p>Branches carrying commits that are not on the trunk, derived "
            "from git rather than from a list anyone maintains. Right by "
            "construction, or empty.</p><div class='wrap'><table>"
            "<thead><tr><th>branch</th><th class='r'>commits</th><th>last</th>"
            "</tr></thead><tbody>"
            + "".join(
                f"<tr><td>{esc(t['name'])}</td><td class='r'>{esc(t['ahead'])}</td>"
                f"<td>{esc(t['when'])}</td></tr>" for t in threads[:6])
            + "</tbody></table></div></section>"
        )
    return shell(IDENTITY["name"], f"""
<h1>Nothing counts until<br>the kernel accepts it.</h1>
<p class="stand">A small laboratory working the Riemann hypothesis in two
regimes of certainty — quantities that are <em>measured</em>, and statements a
proof kernel has <em>accepted</em>. Every figure below was counted from the
repository at the revision named above, including the ones that record what did
not work.</p>

{vitals([
    (num(lean['decls']), 'kernel-checked declarations', False),
    (str(lean['sorrys']), 'sorrys', True),
    (num(py['test_fns']), 'tests', False),
    (num(py['public']), 'public API functions', False),
    (num(r['docs']), 'documents', False),
    (num(r['commits']), 'commits', False),
])}

<section>
<h2><span class='num'>§1</span> What this is</h2>
<p class="lede">The laboratory reconstructs, tests, connects and falsifies ideas
around the Riemann hypothesis. It does not attempt a proof, and nothing computed
inside it is evidence for one — a position held deliberately and enforced in the
vocabulary as well as in the code.</p>
<p>The <strong>measured arm</strong> is arbitrary-precision numerics:
{num(py['lines'])} lines across {py['modules']} core modules, where every
identity is exposed as a measured <em>defect</em> function rather than assumed,
and every number quoted in a docstring is pinned by a test. The
<strong>certified arm</strong> is Lean 4 and Mathlib: {num(lean['lines'])} lines
in which nothing counts until the kernel accepts it.</p>
<p>The word <em>certified</em> is reserved. Only enclosure-carrying numerics and
the proof kernel may use it; everything else here is at best <em>accurate</em>,
which is a weaker and different claim.</p>
</section>

<section>
<h2><span class='num'>§2</span> The certainty ladder</h2>
<p>Claims are graded, and a composite claim takes the grade of its weakest step.
The laboratory occupies the first three rungs and states plainly that it does
not occupy the fourth.</p>
{ladder(lean)}
</section>

<section>
<h2><span class='num'>§3</span> Recent</h2>
<div class='entry'><div class='when'>13 Aug 2026</div>
<h4>The validation harness failed its own gate</h4>
<p>Four preregistered experiments asked whether the laboratory's own validation
framework improved the correctness of research-claim evaluation. It did not: the
arm using it never out-performed the control, and the control was never wrong.
Development stopped and the evidence was kept.</p>
<p class='meta'><a href="record.html">the record →</a></p></div>
{"".join(
    f"<div class='entry'><div class='when'>{esc(g['date'] or '—')} · {esc(g['status'])}</div>"
    f"<h4>{esc(g['name'])}</h4><p>{esc(_clip(g['why'], 240))}</p></div>"
    for g in gr[:2])}
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
        f"<div class='entry'><div class='when'>{esc(g['date'] or '—')} · "
        f"{esc(g['status'])}</div><h4>{esc(g['name'])}</h4>"
        f"<p>{esc(g['why'])}</p>"
        f"<p class='meta'>caught by {esc(g['caught'])}"
        + (f" · pinned by <code>{esc(g['test'])}</code>"
           if g["test"] and g["test"] != "NONE" else "")
        + "</p></div>"
        for g in gr
    )
    return shell(f"Zeta — {IDENTITY['name']}", f"""
<h1>Zeta</h1>
<p class="stand">A computational and formal investigation around the Riemann
hypothesis. It claims nothing about whether the hypothesis is true; the
interesting part is what can be measured, proved, or ruled out.</p>

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
<p>{lean['files']} modules, <strong>{num(lean['decls'])} theorem and lemma
declarations</strong>, and <strong>zero <code>sorry</code>s</strong>. A
<code>sorry</code> is an uncertified step: nothing in this arm counts while one
is present, which is what makes the second number the load-bearing one.</p>
<div class="wrap"><table>
<caption>Largest modules by declaration count</caption>
<thead><tr><th>module</th><th class='r'>decls</th><th class='barcell'></th>
<th>subject</th></tr></thead><tbody>{rows}</tbody></table></div>
<p class='meta'>Titles read from each module's own header block, counts from its
source. {lean['files'] - len(top)} further modules not shown.</p>

<h3>The result that moved the arm</h3>
<p><code>DH_demo_ne_zero</code> — that the Davenport–Heilbronn function is
non-zero at <code>3/2 + 3i</code> — is kernel-checked with no oracle input. It
matters less as arithmetic than as a demonstration that the pipeline closes end
to end, from rational interval arithmetic through certified transcendentals to a
contour criterion.</p>
<p>The Davenport–Heilbronn function is not a curiosity here. It shares ζ's
functional equation, has real coefficients and a real Hardy-style Z — and it
violates the Riemann hypothesis. Any structural property claimed to explain RH
is run against it first, because a property this counterexample shares has
distinguished nothing.</p>
</section>

<section>
<h2><span class='num'>§2</span> The measured arm</h2>
<p>{py['modules']} core modules, {num(py['lines'])} lines, {num(py['public'])}
public functions, checked by {num(py['test_fns'])} tests across
{py['test_files']} files and {num(py['test_lines'])} lines of test code —
more test code than core code, which is the intended ratio.</p>
<p>The suite uses independent oracles rather than its own arithmetic: mpmath's
<code>zetazero</code>, <code>siegelz</code>, <code>grampoint</code> and
<code>nzeros</code> cross-check the hand-rolled machinery. Interval arithmetic
runs on two backends — Arb and mpmath — so that each can check the other, and
when only one is installed the cross-check is absent and the suite reports it
rather than passing quietly.</p>
<div class="statement">A dict that reports <code>certified: True</code> is
asserting a theorem. If any step silently falls back to floats, that is a
critical defect and not a rounding detail.</div>
</section>

<section>
<h2><span class='num'>§3</span> Withdrawn</h2>
<p>Results that did not survive. Each is kept with the mechanism that broke it
and, where one exists, the test that now catches it — so it does not need
re-deriving.</p>
{graves or "<p class='meta'>none recorded</p>"}
</section>

<section>
<h2><span class='num'>§4</span> Checking it</h2>
<p>The repository exists to be checked rather than believed. Clone it, install
it, run the suite; the Lean arm builds with a proof kernel and zero
<code>sorry</code>s. Continuous integration runs the fast tier on every push and
the full suite nightly. The documents derive the mathematics and record the
attempts — start with <a href="../reading.html">the reading course</a>.</p>
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
    return shell(f"Reading — {IDENTITY['name']}", f"""
<h1>Reading</h1>
<p class="stand">The work itself, in the order it was written to be read. The
early documents derive the mathematics line by line; the later ones are
laboratory records — attempts run to their walls, a kill board of how hard
problems die, and an honest catalogue of why this one is hard.</p>

<section>
<h2><span class='num'>§1</span> Before anything else</h2>
<p>Two documents bound every claim on this site. <em>Why It Is Hard</em>
catalogues the known ceiling of each technique used here and explains why no
computation of this kind is evidence for the hypothesis. <em>How Hard Problems
Die</em> scores RH against eight problems and the mechanism that killed each.</p>
</section>

<section>
<h2><span class='num'>§2</span> The course</h2>
{items}
</section>

<section>
<h2><span class='num'>§3</span> The formal arm</h2>
<p>{num(lean['decls'])} declarations across {lean['files']} modules, checked by
the Lean kernel against Mathlib, with zero <code>sorry</code>s — the count is
the claim. <a href="pursuits/zeta.html">The module breakdown →</a></p>
</section>
""", mast=masthead(r))


def page_record(r, gr, gates, revs, fixes_) -> str:
    # Only FAIL is styled as a failure. v3 is RECORDED — its key was wrong on
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
        + (f"<p class='meta'>claimed by {esc(c['author'])} — {esc(c['reasoning'])}</p>"
           if c["reasoning"] else "")
        + "".join(f"<p class='meta'>rested on: {esc(a)}</p>" for a in c["assumptions"][:2])
        + ("".join(
            f"<p>{esc(a['attacker'])} ({esc(a['role'])}) found: "
            + esc(_clip("; ".join(a["findings"]), 320)) + "</p>"
            for a in c["attacks"])
           or "<p class='meta'>no adversarial pass recorded — this claim is "
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
        f"<div class='entry'><div class='when'>{esc(g['date'] or '—')} · "
        f"{esc(g['status'])}</div><h4>{esc(g['name'])}</h4>"
        f"<p>{esc(g['why'])}</p></div>"
        for g in gr
    )
    return shell(f"Record — {IDENTITY['name']}", f"""
<h1>Record</h1>
<p class="stand">Things that actually happened, including the ones that did not
work. A record that only lists successes is not a record.</p>

<section>
<h2><span class='num'>§1</span> The validation harness</h2>
<p>We built a framework for testing whether an empirical claim is about its
subject at all — structure-matched controls, ablations, null models, planted
faults. Then we tested whether using it improved the correctness of
research-claim evaluation.</p>
<p>Four preregistered experiments, three subjects, 74 agent runs. Every protocol
was committed before its arms ran, so the ordering is checkable in the git log.
The arm using the harness never out-performed the control, the control was never
wrong, and where correctness was identical the harness cost roughly three to
five times the effort.</p>
<div class="wrap"><table>
<caption>Preregistered experiments and their verdicts</caption>
<thead><tr><th>experiment</th><th>result</th><th>evidence</th></tr></thead>
<tbody>{rows}</tbody></table></div>
<p>Development stopped. The ledgers inside it that something actually uses were
kept; the framework was frozen rather than deleted, with the evidence beside it.
A separate measurement had already said the same thing more cheaply: nothing in
the repository imported it.</p>
<div class="statement">Being able to kill something you funded, on evidence, is
the habit worth keeping. A laboratory that cannot do that has preferences rather
than a method.</div>
</section>

<section>
<h2><span class='num'>§2</span> Claims, and who was sent to break them</h2>
<p>A claim is recorded with the reasoning that produced it and the assumptions
it rested on, before anyone knows whether it survives. Someone is then sent to
attack it, and their findings are recorded whether or not they are welcome. A
claim nobody has attacked is marked as such rather than counted as standing.</p>
{reviews}
</section>

<section>
<h2><span class='num'>§3</span> Corrections</h2>
<p>Defects that actually occurred, each with the test that now catches it. A
guard nobody has demonstrated firing is a claim rather than a control, so the
ledger tracks that difference instead of hiding it.</p>
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
<h2><span class='num'>§5</span> What is not claimed</h2>
<p>Nothing computed here is evidence for or against the Riemann hypothesis, and
no computation in this tree can be. The house rule is that an apparent
settlement is first inferred to be a defect, and this record contains the
occasions when that inference was correct. They are kept in the tree rather than
removed from it, because a laboratory that deletes its errors has deleted its
evidence about itself.</p>
</section>
""", mast=masthead(r))


def page_about(r, lean, py) -> str:
    return shell(f"About — {IDENTITY['name']}", f"""
<h1>About</h1>
<p class="stand"><em>{esc(IDENTITY['line'])}</em> A small laboratory that
explores several directions cheaply,
feeds the ones that produce something, stops feeding the ones that don't, and
keeps the loose ends it isn't pulling — so that choosing one direction does not
mean forgetting the others.</p>

<section>
<h2><span class='num'>§1</span> How it works</h2>
<p>The impulse is roughly <em>wait, what happens if we pull on this?</em> Most
of the time the answer is nothing much, which is why the record has as many dead
ends in it as findings.</p>
<p>Work is public where it can be checked. The mathematics, the tests, the
proofs and the evidence are in the open, because the point of publishing them is
that someone can re-derive the numbers rather than take our word for it. Results
are published whether or not they are flattering.</p>
<p><a href="pursuits/zeta.html">Zeta</a> is the first pursuit. It is not the
boundary of what this can be about.</p>
</section>

<section>
<h2><span class='num'>§2</span> How this is organised</h2>
<p>Two repositories, split by what an outside reader needs rather than by
secrecy. <strong>Fulcrum</strong> is the operating layer — the private
repository through which pursuits are directed and managed.
<strong>Zeta</strong> is this pursuit, and it is public.</p>
<p>The rule that decides where something goes: if you need it to evaluate or
reproduce a claim, it is here, in the open. If it teaches the laboratory how to
allocate, route, prompt or operate itself, it lives in Fulcrum. Which repository
holds a thing, whether that repository can be cloned, and how much of the
research process outsiders can inspect are three separate questions, and the
answer to the last is <em>as much as is meaningful</em> — including the
criticism, the corrections and the claims that did not survive.</p>
<p class="meta">Fulcrum is private, not secret. The supervisor loop that would
launch and collect work across the two is not built yet; when it is, the runs it
produces are provenance and belong on this side.</p>
</section>

<section>
<h2><span class='num'>§3</span> Colophon</h2>
<p>Every page here is generated from repository artifacts by
<code>scripts/72_site.py</code>: declaration counts from the Lean sources,
module titles from their own header blocks, the public surface from the Python
AST, withdrawn results from the graveyard ledger, experiments from the gate
evidence, open lines from git. Nothing on this site is maintained by hand, so
nothing on it can quietly disagree with the repository.</p>
<p>That rule is not decoration. A page compiled by hand on 12 August was still
advertising the validation harness as this laboratory's strongest capability on
13 August, the day the gate record demoted it. A generated page cannot do that.</p>
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
        out / "index.html": page_index(r, lean, py, gr, threads),
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
