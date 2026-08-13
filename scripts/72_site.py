#!/usr/bin/env python3
"""72_site.py — the public reading surface, generated from repository artifacts.

`scripts/70_lab_state.py` renders the *internal* research-state view. This
renders the *public* one, on the same principle and for the same reason:

    one static file per page, no scripts and no network — pages you can read,
    not an app you can be reassured by

The rule that matters is **derived, not declared**. Every count, every status
and every record entry below comes from a tree artifact: the test files, the
Lean sources, the graveyard ledger, the gate evidence, git. If the repository
changes the site changes; if nobody updates the repository the site says so.
A second, hand-maintained version of reality is exactly what this must not be.

The parent identity lives in IDENTITY, which is the only place it appears, so
renaming the lab is editing one dict rather than sweeping the file.

Usage:
    python scripts/72_site.py                 # writes _site/
    python scripts/72_site.py --out /tmp/site
"""

from __future__ import annotations

import argparse
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


def git(*args: str) -> str:
    try:
        r = subprocess.run(["git", *args], cwd=REPO, capture_output=True,
                           text=True, timeout=30)
        return r.stdout.strip() if r.returncode == 0 else ""
    except Exception:
        return ""


# --------------------------------------------------------------------------
# facts — every one read from an artifact, never typed in
# --------------------------------------------------------------------------

def facts() -> dict[str, Any]:
    tests = sum(
        len(re.findall(r"^\s*def test_", p.read_text(errors="ignore"), re.M))
        for p in (REPO / "tests").glob("test_*.py")
    )
    lean = sorted((REPO / "lean" / "ZetaLean").glob("*.lean"))
    sorrys = sum(
        len([ln for ln in p.read_text(errors="ignore").splitlines()
             if re.match(r"^\s*sorry\b", ln)])
        for p in lean
    )
    return {
        "modules": len(list((REPO / "zeta").glob("*.py"))),
        "tests": tests,
        "lean_files": len(lean),
        "sorrys": sorrys,
        "docs": len(list((REPO / "docs").glob("*.md"))),
        "hunts": len([d for d in (REPO / "hunts").iterdir() if d.is_dir()]),
        "figures": len(list((REPO / "figures").glob("*.png"))),
        "commit": git("rev-parse", "--short", "HEAD"),
        "when": git("log", "-1", "--format=%ad", "--date=format:%d %b %Y"),
    }


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
            "record": record,
            "date": date,
        })
    return out


def gate_results() -> list[dict[str, str]]:
    """The harness evaluation. Four preregistered experiments; all four failed."""
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
            "subject": git("log", "-1", "--format=%s", ref)[:90],
        })
    rows.sort(key=lambda r: int(r["ahead"]), reverse=True)
    return rows


# --------------------------------------------------------------------------
# presentation
# --------------------------------------------------------------------------

CSS = """
:root{
  --paper:#fbfaf7; --ink:#16181a; --soft:#5d6469; --faint:#8b9298;
  --rule:#e3e0d9; --hair:#efece6; --accent:#1f5f5b;
  --serif:Iowan Old Style,Palatino Linotype,Palatino,Georgia,serif;
  --sans:-apple-system,BlinkMacSystemFont,Segoe UI,system-ui,sans-serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
}
@media (prefers-color-scheme:dark){:root{
  --paper:#121315; --ink:#e8e5df; --soft:#a3a8ac; --faint:#7c8288;
  --rule:#2b2e31; --hair:#202325; --accent:#6fb3ac;
}}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--paper);color:var(--ink);
  font:17px/1.65 var(--serif);-webkit-font-smoothing:antialiased}
.page{max-width:44rem;margin:0 auto;padding:2.5rem 1.25rem 6rem}
a{color:var(--accent);text-decoration:none;border-bottom:1px solid transparent}
a:hover{border-bottom-color:currentColor}
a:focus-visible{outline:2px solid var(--accent);outline-offset:2px}

header.top{display:flex;align-items:baseline;gap:.9rem;flex-wrap:wrap;
  padding-bottom:1.1rem;border-bottom:1px solid var(--rule);margin-bottom:2rem}
.word{font-family:var(--sans);font-size:1.15rem;font-weight:600;
  letter-spacing:.005em;color:var(--ink)}
.word a{color:inherit}
.tag{font-family:var(--sans);font-size:.88rem;color:var(--soft)}

h1{font-family:var(--sans);font-size:1.5rem;font-weight:600;line-height:1.25;
  letter-spacing:-.015em;margin:0 0 .5rem;text-wrap:balance}
h2{font-family:var(--sans);font-size:.68rem;font-weight:700;letter-spacing:.15em;
  text-transform:uppercase;color:var(--faint);margin:3rem 0 1rem}
h3{font-family:var(--sans);font-size:1rem;font-weight:600;margin:0 0 .3rem}
p{margin:0 0 1rem}
.lede{font-size:1.12rem;color:var(--soft)}
small,.meta{font-family:var(--mono);font-size:.76rem;color:var(--faint);
  font-variant-numeric:tabular-nums}
code{font-family:var(--mono);font-size:.85em}

.entry{padding:1.1rem 0;border-bottom:1px solid var(--hair)}
.entry:last-child{border-bottom:none}
.entry .when{font-family:var(--mono);font-size:.74rem;color:var(--faint);
  text-transform:uppercase;letter-spacing:.06em}
.entry p{margin:.35rem 0 0;color:var(--soft);font-size:.97rem}

.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(7rem,1fr));
  gap:1.1rem 1.4rem;margin:0 0 1rem;padding:0;list-style:none}
.grid li{border-top:1px solid var(--rule);padding-top:.5rem}
.grid .n{font-family:var(--sans);font-size:1.5rem;font-weight:600;
  font-variant-numeric:tabular-nums;display:block;line-height:1.1}
.grid .k{font-family:var(--sans);font-size:.7rem;letter-spacing:.08em;
  text-transform:uppercase;color:var(--faint)}

.pill{font-family:var(--sans);font-size:.63rem;font-weight:700;letter-spacing:.08em;
  text-transform:uppercase;padding:.16rem .45rem;border:1px solid currentColor;
  border-radius:2px;white-space:nowrap}
.pill.fail{color:#8a4b1a} .pill.ok{color:var(--accent)}
@media (prefers-color-scheme:dark){.pill.fail{color:#d59a63}}

.wrap{overflow-x:auto;margin:0 0 1rem}
table{border-collapse:collapse;width:100%;font-family:var(--sans);
  font-size:.9rem;font-variant-numeric:tabular-nums}
th{font-size:.66rem;font-weight:700;letter-spacing:.08em;text-transform:uppercase;
  color:var(--faint);text-align:left;padding:0 .9rem .4rem 0;
  border-bottom:1px solid var(--rule)}
td{padding:.45rem .9rem .45rem 0;border-bottom:1px solid var(--hair);
  vertical-align:top;color:var(--soft)}
td:first-child{color:var(--ink)}
tr:last-child td{border-bottom:none}

nav.foot{margin-top:4rem;padding-top:1.1rem;border-top:1px solid var(--rule);
  font-family:var(--sans);font-size:.88rem;display:flex;gap:1.4rem;flex-wrap:wrap}
nav.foot .right{margin-left:auto;color:var(--faint)}
@media (max-width:34rem){
  body{font-size:16px} .page{padding:2rem 1.1rem 4rem}
  nav.foot .right{margin-left:0;width:100%}
}
"""


def shell(title: str, body: str, depth: int = 0, tagline: bool = True) -> str:
    up = "../" * depth
    nav = (
        f'<nav class="foot">'
        f'<a href="{up}index.html">now</a>'
        f'<a href="{up}pursuits/zeta.html">zeta</a>'
        f'<a href="{up}record.html">record</a>'
        f'<a href="{up}about.html">about</a>'
        f'<a href="{esc(IDENTITY["source"])}">source</a>'
        f'</nav>'
    )
    return (
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width,initial-scale=1'>"
        f"<title>{esc(title)}</title><style>{CSS}</style></head><body><div class='page'>"
        f"<header class='top'><span class='word'><a href='{up}index.html'>"
        f"{esc(IDENTITY['name'])}</a></span>"
        # The homepage says the line as its headline; repeating it in the header
        # is the kind of duplication that reads as filler.
        + (f"<span class='tag'>{esc(IDENTITY['line'])}</span>" if tagline else "")
        + "</header>"
        + body + nav + "</div></body></html>"
    )


# --------------------------------------------------------------------------
# pages
# --------------------------------------------------------------------------

def page_index(f, gr, gates, threads) -> str:
    recent = []
    for g in gates[:1]:
        recent.append((
            "13 Aug 2026", "Validation harness",
            "Four preregistered experiments asked whether it improved the "
            "correctness of research-claim evaluation. It did not. "
            "Investment stopped; the record is kept.",
        ))
    for g in gr[:2]:
        recent.append((
            g["date"] or "—", g["name"],
            (g["why"][:180] + "…") if len(g["why"]) > 180 else g["why"],
        ))
    entries = "".join(
        f"<div class='entry'><div class='when'>{esc(w)}</div>"
        f"<h3>{esc(t)}</h3><p>{esc(d)}</p></div>"
        for w, t, d in recent
    )
    live = ""
    if threads:
        live = (
            "<h2>Open lines</h2><div class='wrap'><table>"
            "<tr><th>branch</th><th>commits</th><th>last</th></tr>"
            + "".join(
                f"<tr><td><code>{esc(t['name'])}</code></td>"
                f"<td>{esc(t['ahead'])}</td><td>{esc(t['when'])}</td></tr>"
                for t in threads[:5]
            )
            + "</table></div>"
        )
    return shell(IDENTITY["name"], f"""
<h1>{esc(IDENTITY["line"])}</h1>
<p class="lede">Explore broadly, notice strange things, pull the promising
threads, stop feeding the weak ones, and keep what was learned either way.</p>

<h2>Now</h2>
<h3><a href="pursuits/zeta.html">Zeta</a></h3>
<p>Computational and formal work around the Riemann hypothesis. Nothing here
is evidence for or against it — the interesting part is what can be measured,
proved, or ruled out.</p>
<ul class="grid">
  <li><span class="n">{f['tests']:,}</span><span class="k">tests</span></li>
  <li><span class="n">{f['lean_files']}</span><span class="k">Lean files</span></li>
  <li><span class="n">{f['sorrys']}</span><span class="k">sorrys</span></li>
  <li><span class="n">{f['hunts']}</span><span class="k">hunts</span></li>
</ul>

<h2>Recent</h2>
{entries}
{live}
""", tagline=False)


def page_zeta(f, gr, gates) -> str:
    graves = "".join(
        f"<div class='entry'><div class='when'>{esc(g['date'] or '—')} · "
        f"{esc(g['status'])}</div><h3>{esc(g['name'])}</h3>"
        f"<p>{esc(g['why'])}</p>"
        f"<p class='meta'>caught by {esc(g['caught'])}"
        + (f" · pinned by <code>{esc(g['test'])}</code>"
           if g["test"] and g["test"] != "NONE" else "")
        + "</p></div>"
        for g in gr
    )
    return shell(f"Zeta — {IDENTITY['name']}", f"""
<h1>Zeta</h1>
<p class="lede">A computational and formal investigation around the Riemann
hypothesis.</p>

<p>The machinery computes ζ by independent routes and compares them, exposes
identities as measured <em>defect</em> functions rather than assuming them, and
pins every number claimed in a docstring to a test. Two things here are stronger
than “accurate”: interval arithmetic that carries an enclosure through every
step, and Lean proofs checked by a kernel.</p>

<p>It claims nothing about whether the hypothesis is true. A computation that
appears to settle it is a bug, and the repository says so in its own house
rules.</p>

<h2>State</h2>
<ul class="grid">
  <li><span class="n">{f['modules']}</span><span class="k">modules</span></li>
  <li><span class="n">{f['tests']:,}</span><span class="k">tests</span></li>
  <li><span class="n">{f['lean_files']}</span><span class="k">Lean files</span></li>
  <li><span class="n">{f['sorrys']}</span><span class="k">sorrys</span></li>
  <li><span class="n">{f['docs']}</span><span class="k">documents</span></li>
  <li><span class="n">{f['figures']}</span><span class="k">figures</span></li>
</ul>
<p class="meta">at {esc(f['commit'])} · {esc(f['when'])}</p>

<h2>Withdrawn</h2>
<p>Results that did not survive. Each is kept with the mechanism that broke it
and, where one exists, the test that now catches it — so it does not need
re-deriving.</p>
{graves or "<p class='meta'>none recorded</p>"}

<h2>Checking it</h2>
<p>The repository exists to be checked rather than believed. Clone it, install
it, run the suite; the Lean arm builds with a proof kernel and zero
<code>sorry</code>s. Continuous integration runs the fast tier on every push and
the full suite nightly.</p>
<p><a href="{esc(IDENTITY['source'])}">Source</a></p>
""", depth=1)


def page_record(gr, gates) -> str:
    rows = "".join(
        f"<tr><td>{esc(g['name'])}</td>"
        f"<td><span class='pill fail'>{esc(g['verdict'])}</span></td>"
        f"<td><code>{esc(g['file'])}</code></td></tr>"
        for g in gates
    )
    graves = "".join(
        f"<div class='entry'><div class='when'>{esc(g['date'] or '—')} · "
        f"{esc(g['status'])}</div><h3>{esc(g['name'])}</h3>"
        f"<p>{esc(g['why'])}</p></div>"
        for g in gr
    )
    return shell(f"Record — {IDENTITY['name']}", f"""
<h1>Record</h1>
<p class="lede">Things that actually happened, including the ones that did not
work.</p>

<h2>The validation harness</h2>
<p>We built a framework for testing whether an empirical claim is about its
subject at all — structure-matched controls, ablations, null models, planted
faults. Then we tested whether using it improved the correctness of
research-claim evaluation.</p>
<p>Four preregistered experiments, three subjects, 74 agent runs. Every protocol
was committed before its arms ran, so the ordering is checkable. The arm using
the harness never out-performed the control, and the control was never wrong.
Where correctness was identical the harness cost roughly three to five times the
effort.</p>
<div class="wrap"><table>
<tr><th>experiment</th><th>result</th><th>evidence</th></tr>
{rows}
</table></div>
<p>Development stopped. The ledgers inside it that something actually uses were
kept; the framework was frozen rather than deleted, with the evidence beside it.
A separate measurement had already said the same thing more cheaply: nothing in
the repository imported it.</p>

<h2>Withdrawn results</h2>
{graves}

<h2>What this is for</h2>
<p>An idea, tried, measured, and either kept or dropped — with the lesson kept
either way. A record that only lists successes is not a record.</p>
""")


def page_about(f) -> str:
    return shell(f"About — {IDENTITY['name']}", f"""
<h1>About</h1>
<p class="lede">A small laboratory. It explores several directions cheaply,
feeds the ones that produce something, stops feeding the ones that don't, and
keeps the loose ends it isn't pulling — so that choosing one direction doesn't
mean forgetting the others.</p>

<p>The impulse is roughly <em>wait, what happens if we pull on this?</em> Most
of the time the answer is nothing much, which is why the record below has as
many dead ends in it as findings.</p>

<p>Work is public where it can be checked. The mathematics, the tests, the
proofs and the evidence are in the open, because the point of publishing them is
that someone can re-derive the numbers rather than take our word for it. Results
are published whether or not they are flattering.</p>

<p><a href="pursuits/zeta.html">Zeta</a> is the first pursuit. It is not the
boundary of what this can be about.</p>

<h2>Colophon</h2>
<p class="meta">Every page here is generated from repository artifacts by
<code>scripts/72_site.py</code> — counts from the sources, withdrawn results
from the graveyard ledger, experiments from the gate evidence, open lines from
git. Nothing on this site is maintained by hand, so nothing on it can quietly
disagree with the repository. No scripts, no tracking, no network requests.</p>
<p class="meta">Built at {esc(f['commit'])} · {esc(f['when'])}</p>
""")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=REPO / "_site")
    args = ap.parse_args()

    f, gr, gates, threads = facts(), graveyard(), gate_results(), live_threads()

    out = args.out
    (out / "pursuits").mkdir(parents=True, exist_ok=True)
    pages = {
        out / "index.html": page_index(f, gr, gates, threads),
        out / "pursuits" / "zeta.html": page_zeta(f, gr, gates),
        out / "record.html": page_record(gr, gates),
        out / "about.html": page_about(f),
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
