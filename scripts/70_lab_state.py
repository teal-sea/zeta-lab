"""70_lab_state.py — the read-only research-state view, rendered from artifacts.

The specification's control-layer rule (docs/reviews, the next-phase memo;
adopted with its emphasis reversed onto state): the view shows *research
state, not agent activity*, and its headline question is

    what do we know now that we did not know before, and why are we
    entitled to believe it?

Everything rendered here comes from durable tree artifacts — the graveyard
ledger, the guard ledger, the review ledger, the independence declarations,
the hunts' case log and HuntSpec blocks. Nothing comes from any
orchestration layer, because evidence does not live there. The output is one
static HTML file with no scripts and no network: a page you can read, not an
app you can be reassured by.

Usage:
    .venv/bin/python scripts/70_lab_state.py [--out figures/lab_state.html]

The **attention queue** section is the human-decision worklist the memo asks
for, derived rather than declared: undemonstrated guards, unguarded graves,
reviews missing an attack, and hunts without a HuntSpec (informational for
hunts predating the primitive).
"""

from __future__ import annotations

import argparse
import html
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT))

from harness.departments.graveyard_ledger import GRAVES  # noqa: E402
from harness.departments.guard_ledger import GUARDS  # noqa: E402
from harness.departments.review_ledger import CLAIMS, OUTCOMES  # noqa: E402
from harness.departments.zeta_department import (  # noqa: E402
    rigor_backend_independence,
)
from harness.graveyard import unguarded  # noqa: E402
from harness.guards import offensive_worklist, undemonstrated  # noqa: E402
from harness.independence import agreement_bounds  # noqa: E402
from harness.review import standing_reasons  # noqa: E402

_HUNTSPEC_BLOCK = re.compile(r"```huntspec\n", re.DOTALL)


def _esc(text: str) -> str:
    return html.escape(text, quote=True)


def _hunts() -> list[dict]:
    rows = []
    hunts_dir = REPO_ROOT / "hunts"
    for child in sorted(hunts_dir.iterdir()):
        if not child.is_dir() or child.name.startswith((".", "_")):
            continue
        mission = child / "MISSION.md"
        first_line = ""
        has_spec = False
        if mission.is_file():
            text = mission.read_text(encoding="utf-8", errors="ignore")
            has_spec = bool(_HUNTSPEC_BLOCK.search(text))
            for line in text.splitlines():
                stripped = line.strip().lstrip("# ")
                if stripped:
                    first_line = stripped
                    break
        rows.append({"name": child.name, "title": first_line, "huntspec": has_spec})
    return rows


def _attention_queue() -> list[str]:
    queue: list[str] = []
    queue.extend(offensive_worklist(GUARDS))
    queue.extend(unguarded(GRAVES))
    for claim in CLAIMS:
        queue.extend(standing_reasons(claim, OUTCOMES))
    return queue


def _git(*args: str) -> str:
    """Read-only git, from the repository root. Empty string on any failure."""
    import subprocess

    try:
        out = subprocess.run(
            ["git", *args],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
        return out.stdout if out.returncode == 0 else ""
    except Exception:  # noqa: BLE001 - a state page must never fail on git
        return ""


def _threads() -> list[dict]:
    """Who is holding what, derived from git rather than declared.

    Several agents and sessions work this repository in parallel, and until now
    the only way to find out what was live was to read commit logs by hand —
    which is how one session concluded, wrongly, that nobody was attacking the
    transplant chain. A hand-maintained registry would answer that, and would
    also rot silently and then read as authoritative, which is the same failure
    class as an import nobody ran or an axiom audit nobody imported.

    So this is derived: every branch carrying commits that are not on
    `origin/main`, with its last commit's age and subject. It is right by
    construction or it is empty, and it needs nobody to remember to update it.
    """
    rows: list[dict] = []
    listing = _git("for-each-ref", "--format=%(refname:short)", "refs/heads", "refs/remotes")
    for ref in listing.splitlines():
        ref = ref.strip()
        if not ref or ref in ("origin/main", "origin/HEAD") or ref.endswith("/HEAD"):
            continue
        # Refs under `deploy/` are written by CI, not by anyone working. A
        # publishing branch is not a line of research and must not read as one.
        if ref.replace("origin/", "").startswith("deploy/"):
            continue
        count = _git("rev-list", "--count", f"origin/main..{ref}").strip()
        if not count or count == "0":
            continue
        last = _git("log", "-1", "--format=%cr\t%s", ref).strip()
        when, _, subject = last.partition("\t")
        rows.append(
            {
                "ref": ref,
                "ahead": count,
                "when": when,
                "subject": subject[:90],
            }
        )
    rows.sort(key=lambda r: int(r["ahead"]), reverse=True)
    return rows


def _pill(power: str) -> str:
    """A measured guard and an undemonstrated one should not read alike."""
    if power.startswith("fires"):
        rest = power.split("—", 1)[1].strip() if "—" in power else ""
        tail = f" <code class='muted'>{_esc(rest)}</code>" if rest else ""
        return f"<span class='pill ok'>fires</span>{tail}"
    return "<span class='pill open'>never demonstrated</span>"


def render() -> str:
    parts: list[str] = []
    parts.append(
        "<!doctype html><html><head><meta charset='utf-8'>"
        "<title>Zeta Lab — research state</title><style>"
        ":root{--ink:#15181c;--soft:#5a636d;--faint:#868f99;--rule:#dfe3e8;"
        "--hair:#eceff2;--paper:#fcfcfa;--card:#f6f6f2;--warn:#8a4b1a;"
        "--good:#2f6b45;--mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}"
        "@media(prefers-color-scheme:dark){:root{--ink:#e4e7ea;--soft:#a3acb6;"
        "--faint:#7d868f;--rule:#2f353c;--hair:#242a30;--paper:#14171a;"
        "--card:#1c2126;--warn:#d59a63;--good:#7fb894}}"
        "*{box-sizing:border-box}"
        "body{font:16px/1.6 -apple-system,BlinkMacSystemFont,\"Segoe UI\",system-ui,sans-serif;"
        "margin:0 auto;max-width:58rem;padding:3rem 1.25rem 6rem;color:var(--ink);"
        "background:var(--paper);-webkit-font-smoothing:antialiased}"
        "h1{font-size:1.55rem;font-weight:600;letter-spacing:-.01em;margin:0 0 .4rem}"
        "h2{font-size:.72rem;font-weight:700;letter-spacing:.14em;text-transform:uppercase;"
        "color:var(--faint);margin:3.2rem 0 .9rem;padding-bottom:.5rem;"
        "border-bottom:1px solid var(--rule)}"
        "h2 .n{color:var(--faint);font-weight:500}"
        "p{margin:0 0 1rem}"
        ".muted{color:var(--soft);font-size:.92rem}"
        "code{font-family:var(--mono);font-size:.86em}"
        "table{border-collapse:collapse;width:100%;font-size:.92rem;"
        "font-variant-numeric:tabular-nums}"
        "th{font-size:.68rem;font-weight:700;letter-spacing:.08em;text-transform:uppercase;"
        "color:var(--faint);text-align:left;padding:0 .8rem .45rem 0;"
        "border-bottom:1px solid var(--rule)}"
        "td{padding:.5rem .8rem .5rem 0;border-bottom:1px solid var(--hair);"
        "vertical-align:top}"
        "tr:last-child td{border-bottom:none}"
        ".wrap{overflow-x:auto}"
        "ul{margin:0;padding:0;list-style:none}"
        ".item{padding:.7rem 0;border-bottom:1px solid var(--hair);display:grid;"
        "grid-template-columns:minmax(0,22rem) minmax(0,1fr);gap:.2rem 1.4rem}"
        ".item:last-child{border-bottom:none}"
        ".item .who{font-family:var(--mono);font-size:.78rem;color:var(--ink);"
        "word-break:break-word}"
        ".item .gap{color:var(--soft);font-size:.92rem}"
        ".item .verb{display:block;font-size:.68rem;letter-spacing:.07em;"
        "text-transform:uppercase;color:var(--warn);margin-top:.15rem}"
        ".card{background:var(--card);border:1px solid var(--rule);border-radius:2px;"
        "padding:1rem 1.15rem;margin:0 0 .8rem}"
        ".card .title{font-weight:600;margin-bottom:.6rem}"
        ".card dl{display:grid;grid-template-columns:minmax(0,10rem) minmax(0,1fr);"
        "gap:.35rem 1.2rem;margin:0;font-size:.9rem}"
        ".card dt{font-size:.65rem;letter-spacing:.08em;text-transform:uppercase;"
        "color:var(--faint);padding-top:.15rem}"
        ".card dd{margin:0;color:var(--soft)}"
        ".pill{display:inline-block;font-size:.64rem;font-weight:700;letter-spacing:.07em;"
        "text-transform:uppercase;padding:.15rem .45rem;border-radius:2px;"
        "border:1px solid currentColor;white-space:nowrap}"
        ".pill.ok{color:var(--good)} .pill.open{color:var(--warn)}"
        "@media(max-width:44rem){.item,.card dl{grid-template-columns:1fr}"
        ".item .who{font-size:.74rem}}"
        "</style></head><body>"
    )
    parts.append("<h1>Zeta Lab — research state</h1>")
    parts.append(
        "<p class='muted'>Rendered from tree artifacts only (ledgers, "
        "declarations, case logs). No orchestration state, no agent "
        "activity. The question this page answers: <em>what do we know now "
        "that we did not know before, and why are we entitled to believe "
        "it?</em> Regenerate with <code>scripts/70_lab_state.py</code>.</p>"
    )

    queue = _attention_queue()
    parts.append(f"<h2>Attention queue ({len(queue)})</h2>")
    if queue:
        # Each item reads "<kind> '<name>' <verb>: <gap>". Splitting it puts the
        # subject and the gap in separate columns instead of one run-on line;
        # anything that does not match that shape is rendered whole rather than
        # mangled to fit.
        parts.append("<ul>")
        for item in queue:
            m = re.match(r"^(guard|claim) '(.+?)' (.+?): (.+)$", item, re.S)
            if m:
                _kind, name, verb, gap = m.groups()
                parts.append(
                    f"<li class='item'><div class='who'>{_esc(name)}"
                    f"<span class='verb'>{_esc(verb)}</span></div>"
                    f"<div class='gap'>{_esc(gap)}</div></li>"
                )
            else:
                parts.append(f"<li class='item'><div class='gap'>{_esc(item)}</div></li>")
        parts.append("</ul>")
    else:
        parts.append("<p>Empty — which is a statement about the ledgers' coverage.</p>")

    threads = _threads()
    parts.append(f"<h2>Live threads ({len(threads)})</h2>")
    parts.append(
        "<p class='muted'>Every branch carrying commits not on <code>origin/main</code>, "
        "newest work first. Derived from git, not declared: it is right by construction "
        "or it is empty, and nobody has to remember to update it. Parallel sessions are "
        "normal here — an unmerged branch is usually live work, not debris, so read this "
        "before assuming a lane is unattended.</p>"
    )
    if threads:
        parts.append(
            "<table><tr><th>branch</th><th>ahead</th><th>last commit</th>"
            "<th>subject</th></tr>"
        )
        for row in threads:
            parts.append(
                f"<tr><td><code>{_esc(row['ref'])}</code></td>"
                f"<td>{_esc(row['ahead'])}</td><td>{_esc(row['when'])}</td>"
                f"<td>{_esc(row['subject'])}</td></tr>"
            )
        parts.append("</table></div>")
    else:
        parts.append(
            "<p>Nothing unmerged — either everything landed, or git was unreadable "
            "from here. This section never guesses.</p>"
        )

    parts.append(f"<h2>Graveyard ({len(GRAVES)})</h2>")
    parts.append(
        "<p class='muted'>Withdrawn results and closed routes, each with its "
        "mechanism and its guard. These are load-bearing: every card is a "
        "failure that will not need re-deriving.</p>"
    )
    for grave in GRAVES:
        # grave.card() is "TITLE\nLABEL  value" lines. A <pre> preserves the
        # alignment and nothing else; a definition list makes the labels
        # scannable and lets the values wrap.
        lines = [ln for ln in grave.card().splitlines() if ln.strip()]
        title, rows = lines[0], []
        for ln in lines[1:]:
            m = re.match(r"^([A-Z][A-Z ?'()]+?)\s{2,}(.+)$", ln)
            rows.append(m.groups() if m else ("", ln.strip()))
        body = "".join(
            f"<dt>{_esc(k.strip().lower())}</dt><dd>{_esc(v)}</dd>" for k, v in rows
        )
        parts.append(
            f"<div class='card'><div class='title'>{_esc(title)}</div>"
            f"<dl>{body}</dl></div>"
        )

    parts.append(f"<h2>Guard ledger ({len(GUARDS)})</h2>")
    parts.append("<div class='wrap'><table><tr><th>guard</th><th>guards against</th><th>power</th></tr>")
    for guard in GUARDS:
        power = {
            True: f"fires — {guard.demonstrated_by}",
            False: f"DOES NOT FIRE — {guard.demonstrated_by}",
            None: "never demonstrated",
        }[guard.fired]
        parts.append(
            f"<tr><td><code>{_esc(guard.name)}</code></td>"
            f"<td>{_esc(guard.guards_against)}</td>"
            f"<td>{_pill(power)}</td></tr>"
        )
    parts.append("</table></div>")
    open_guards = undemonstrated(GUARDS)
    if open_guards:
        parts.append(
            f"<p class='muted'>Power never demonstrated: {_esc(', '.join(open_guards))}.</p>"
        )

    parts.append("<h2>Verification independence</h2>")
    report = rigor_backend_independence()
    parts.append(f"<pre>{_esc(report.describe())}</pre><ul>")
    parts.extend(f"<li>{_esc(reason)}</li>" for reason in agreement_bounds(report))
    parts.append("</ul>")

    parts.append(f"<h2>Standing reviews ({len(CLAIMS)})</h2>")
    parts.append("<div class='wrap'><table><tr><th>claim</th><th>status</th></tr>")
    for claim in CLAIMS:
        missing = standing_reasons(claim, OUTCOMES)
        withdrawn = any(
            o.claim_withdrawn for o in OUTCOMES if o.claim_name == claim.name
        )
        if withdrawn:
            status = "withdrawn under attack (see graveyard)"
        elif missing:
            status = "; ".join(missing)
        else:
            status = "standing: both attacks recorded"
        parts.append(f"<tr><td>{_esc(claim.name)}</td><td>{_esc(status)}</td></tr>")
    parts.append("</table></div>")

    hunts = _hunts()
    parts.append(f"<h2>Hunts ({len(hunts)})</h2>")
    parts.append(
        "<p class='muted'>Exploratory studies; nothing here is a result "
        "(hunts/README.md). HuntSpec applies to hunts opened after "
        "2026-08-11.</p><table><tr><th>hunt</th><th>mission</th><th>huntspec</th></tr>"
    )
    for hunt in hunts:
        parts.append(
            f"<tr><td>{_esc(hunt['name'])}</td><td>{_esc(hunt['title'])}</td>"
            f"<td>{'yes' if hunt['huntspec'] else '—'}</td></tr>"
        )
    parts.append("</table></div>")

    parts.append("</body></html>")
    return "".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(REPO_ROOT / "figures" / "lab_state.html"),
        help="output path for the rendered page",
    )
    args = parser.parse_args()
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render(), encoding="utf-8")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
