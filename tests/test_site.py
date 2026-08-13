"""Tests for ``scripts/72_site.py`` — the public reading surface.

Two things are worth pinning and nothing else is. The site must stay a thing
you can read offline, and the parent identity must stay replaceable — Website
v0 exists partly to find out whether the name survives contact with the work,
which is only true if changing it is cheap.

Nothing here checks prose. A test that graded the copy would be the same
mistake recorded in ``harness/VERDICT.md``.

Stdlib + pytest only.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
SITE = REPO / "scripts" / "72_site.py"


@pytest.fixture(scope="module")
def built(tmp_path_factory) -> Path:
    out = tmp_path_factory.mktemp("site")
    r = subprocess.run([sys.executable, str(SITE), "--out", str(out)],
                       capture_output=True, text=True, timeout=300)
    assert r.returncode == 0, r.stdout + r.stderr
    return out


def _pages(root: Path) -> list[Path]:
    return sorted(root.rglob("*.html"))


def test_the_site_builds_every_page(built: Path) -> None:
    names = {p.relative_to(built).as_posix() for p in _pages(built)}
    assert names == {"index.html", "record.html", "about.html", "pursuits/zeta.html"}


def test_no_page_runs_a_script(built: Path) -> None:
    """A page you can read, not an app you can be reassured by."""
    for p in _pages(built):
        assert "<script" not in p.read_text(errors="ignore").lower(), p.name


def test_no_page_makes_an_external_request(built: Path) -> None:
    """Offline-readable. The only outbound links are to the public source."""
    for p in _pages(built):
        for url in re.findall(r"https?://[^\"'\s<>]+", p.read_text(errors="ignore")):
            assert url.startswith("https://github.com/"), f"{p.name}: {url}"


def test_every_page_is_navigable_and_declares_a_viewport(built: Path) -> None:
    for p in _pages(built):
        text = p.read_text(errors="ignore")
        assert "width=device-width" in text, f"{p.name} is not usable on a phone"
        assert "nav class='foot'" in text or 'nav class="foot"' in text, p.name


def test_internal_links_resolve(built: Path) -> None:
    """A front door that opens onto a wall is worse than no door."""
    for p in _pages(built):
        for href in re.findall(r'href=[\'"]([^\'"]+)[\'"]', p.read_text(errors="ignore")):
            if href.startswith(("http://", "https://", "#", "mailto:")):
                continue
            assert (p.parent / href).resolve().is_file(), f"{p.name} -> {href}"


def test_the_parent_identity_is_a_single_edit() -> None:
    """The name is provisional; renaming must not be a refactor.

    Reads the name out of IDENTITY rather than hardcoding it, so this test
    survives the rename it exists to protect.
    """
    source = SITE.read_text(encoding="utf-8")
    name = re.search(r'"name":\s*"([^"]+)"', source).group(1)
    assert source.count(f'"name": "{name}"') == 1
    assert len(re.findall(re.escape(name), source)) == 1, (
        f"the parent name {name!r} appears outside IDENTITY; it must live in one place"
    )


def test_the_facts_come_from_artifacts_not_literals(built: Path) -> None:
    """The counts on the page must match what the tree actually contains."""
    lean = len(list((REPO / "lean" / "ZetaLean").glob("*.lean")))
    docs = len(list((REPO / "docs").glob("*.md")))
    zeta = (built / "pursuits" / "zeta.html").read_text(errors="ignore")
    assert f">{lean}<" in zeta, f"Lean file count {lean} not rendered"
    assert f">{docs}<" in zeta, f"document count {docs} not rendered"


def _load(path: Path):
    """Import a numbered script by path — `72_site` is not a module name."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(path.stem.lstrip("0123456789_"), path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CANNED_REFS = "origin/main\norigin/HEAD\norigin/deploy/site\norigin/claude/a-real-hunt\n"


def test_a_publishing_branch_is_not_a_line_of_research(monkeypatch) -> None:
    """CI force-pushes built pages to `deploy/site`. That is machinery, not work.

    Both views enumerate branches ahead of main to derive what is live, which
    is right by construction only while every such branch is somebody working.
    A publishing branch is always ahead of main and never anyone's research, so
    it would sit permanently at the top of both lists — the derived view's one
    failure mode, telling you something true about git and false about the lab.
    """
    site = _load(SITE)
    monkeypatch.setattr(site, "git", lambda *a: (
        CANNED_REFS if a[:1] == ("for-each-ref",) else "3" if a[:1] == ("rev-list",) else "x"
    ))
    names = {r["name"] for r in site.live_threads()}
    assert names == {"claude/a-real-hunt"}, f"deploy/ ref leaked into the public page: {names}"

    state = _load(REPO / "scripts" / "70_lab_state.py")
    monkeypatch.setattr(state, "_git", lambda *a: (
        CANNED_REFS if a[:1] == ("for-each-ref",) else "3" if a[:1] == ("rev-list",) else "x"
    ))
    refs = {r["ref"] for r in state._threads()}
    assert refs == {"origin/claude/a-real-hunt"}, f"deploy/ ref leaked into state view: {refs}"
