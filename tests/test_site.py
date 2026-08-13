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
    assert names == {"index.html", "reading.html", "record.html", "about.html",
                     "pursuits/zeta.html"}


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


def test_every_document_is_reachable_and_described(built: Path) -> None:
    """The site's job is to make the work readable, not to count it.

    Before the reading page existed a visitor could see how many documents
    there were and read none of them. Each must appear with its own title and
    a link to its source, so adding a document publishes it rather than only
    incrementing a number.
    """
    page = (built / "reading.html").read_text(errors="ignore")
    docs = sorted((REPO / "docs").glob("[0-9]*.md"))
    assert docs, "no numbered documents found"
    missing = [d.name for d in docs if d.name not in page]
    assert not missing, f"documents absent from the reading page: {missing}"


def test_an_unattacked_claim_is_not_presented_as_a_result(built: Path) -> None:
    """The record must not sanitize the process into a success story.

    A claim with no adversarial pass recorded is open, and the page has to say
    so in those terms. This is the property that makes the review trail worth
    publishing at all: if an unreviewed claim rendered identically to a
    survived one, the section would be decoration.
    """
    import importlib

    sys.path.insert(0, str(REPO))
    ledger = importlib.import_module("harness.departments.review_ledger")
    attacked = {getattr(o, "claim_name", "") for o in ledger.OUTCOMES}
    open_claims = [c for c in ledger.CLAIMS if getattr(c, "name", "") not in attacked]

    page = (built / "record.html").read_text(errors="ignore")
    for claim in open_claims:
        assert getattr(claim, "name", "") in page, "an open claim is missing entirely"
    if open_claims:
        assert "open, not confirmed" in page, (
            "an unattacked claim is rendered without saying it is unattacked"
        )
    for claim in ledger.CLAIMS:
        assert getattr(claim, "author", "") in page, (
            "a claim is published without whose reasoning produced it"
        )


def test_the_host_build_needs_no_scientific_stack() -> None:
    """The deploy build must stay stdlib-only, and `vercel.json` must say so.

    `70_lab_state.py` reaches numpy, mpmath and scipy through the harness
    departments; `72_site.py` reaches none of them. That difference is the
    whole reason the host can build this site in seconds with no install step,
    so it is worth pinning: an import added to the generator would be invisible
    here but would turn every deploy into a scientific-stack build, and the
    first symptom would be a slow or failing deploy rather than a test.
    """
    import json

    cfg = json.loads((REPO / "vercel.json").read_text(encoding="utf-8"))
    assert cfg["outputDirectory"] == "_site"
    assert SITE.name in cfg["buildCommand"], "the build must run the generator"
    assert cfg["installCommand"] == "", "an install step would defeat the point"

    stub = REPO / "tests" / "_no_deps"
    stub.mkdir(exist_ok=True)
    for mod in ("numpy", "scipy", "mpmath", "matplotlib", "sympy", "flint"):
        (stub / f"{mod}.py").write_text(f'raise ImportError("{mod} absent")\n')
    try:
        out = REPO / "tests" / "_no_deps_out"
        r = subprocess.run(
            [sys.executable, str(SITE), "--out", str(out)],
            capture_output=True, text=True, timeout=300,
            env={**__import__("os").environ, "PYTHONPATH": str(stub)},
        )
        assert r.returncode == 0, (
            "the generator reached a scientific dependency:\n" + r.stdout + r.stderr
        )
    finally:
        import shutil

        shutil.rmtree(stub, ignore_errors=True)
        shutil.rmtree(REPO / "tests" / "_no_deps_out", ignore_errors=True)
