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


def render() -> str:
    parts: list[str] = []
    parts.append(
        "<!doctype html><html><head><meta charset='utf-8'>"
        "<title>Zeta Lab — research state</title><style>"
        "body{font:15px/1.5 -apple-system,system-ui,sans-serif;margin:2rem auto;"
        "max-width:60rem;padding:0 1rem;color:#1a1a1a;background:#fbfbf9}"
        "h1,h2{line-height:1.2} h2{margin-top:2.2rem;border-bottom:1px solid #ddd}"
        "pre{background:#f2f1ec;padding:.8rem 1rem;overflow-x:auto;font-size:13px}"
        "table{border-collapse:collapse;width:100%} td,th{border:1px solid #ddd;"
        "padding:.35rem .6rem;text-align:left;vertical-align:top}"
        "th{background:#f2f1ec} .muted{color:#666} .attn{color:#8a3b00}"
        "@media(prefers-color-scheme:dark){body{color:#e8e6e0;background:#191919}"
        "pre,th{background:#242424} td,th,h2{border-color:#3a3a3a} .muted{color:#9a9a9a}"
        ".attn{color:#e0a060}}"
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
        parts.append("<ul>")
        parts.extend(f"<li class='attn'>{_esc(item)}</li>" for item in queue)
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
        parts.append("</table>")
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
        parts.append(f"<pre>{_esc(grave.card())}</pre>")

    parts.append(f"<h2>Guard ledger ({len(GUARDS)})</h2>")
    parts.append("<table><tr><th>guard</th><th>guards against</th><th>power</th></tr>")
    for guard in GUARDS:
        power = {
            True: f"fires — {guard.demonstrated_by}",
            False: f"DOES NOT FIRE — {guard.demonstrated_by}",
            None: "never demonstrated",
        }[guard.fired]
        parts.append(
            f"<tr><td>{_esc(guard.name)}</td><td>{_esc(guard.guards_against)}</td>"
            f"<td>{_esc(power)}</td></tr>"
        )
    parts.append("</table>")
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
    parts.append("<table><tr><th>claim</th><th>status</th></tr>")
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
    parts.append("</table>")

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
    parts.append("</table>")

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
