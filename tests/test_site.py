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
    """Every headline number must match what the tree actually contains.

    Counted here independently of the generator — a second implementation of
    the same count, so the two have to agree for the test to pass. A number
    that drifted from its source would otherwise be invisible: it renders just
    as confidently as a correct one, which is the whole failure mode a
    generated page exists to prevent.
    """
    lean_files = sorted((REPO / "lean" / "ZetaLean").rglob("*.lean"))
    src = "\n".join(p.read_text(errors="ignore") for p in lean_files)
    thms = len(re.findall(r"^\s*theorem\b", src, re.M))
    lems = len(re.findall(r"^\s*lemma\b", src, re.M))
    sorrys = len(re.findall(r"^\s*sorry\b", src, re.M))
    docs = len(list((REPO / "docs").glob("[0-9]*.md")))

    zeta = (built / "pursuits" / "zeta.html").read_text(errors="ignore")
    index = (built / "index.html").read_text(errors="ignore")

    assert f">{len(lean_files)}<" in zeta, f"Lean module count {len(lean_files)} not rendered"
    assert f">{thms:,}<" in zeta, f"theorem count {thms} not rendered"
    assert f">{lems:,}<" in zeta, f"lemma count {lems} not rendered"
    assert f">{sorrys}<" in zeta, "the sorry count must be shown even at zero"
    assert f">{docs:,}<" in index, f"document count {docs} not rendered"

    # The front page counts both Lean corpora: the re-derived ladder in
    # lean/ZetaLean and the frontier work in hunts/frontier_math. Counting only
    # the first was the undercount that made the site report infrastructure as
    # if it were output, so the total is checked here against both trees.
    frontier_src = "\n".join(
        p.read_text(errors="ignore")
        for p in sorted((REPO / "hunts" / "frontier_math").rglob("*.lean"))
    )
    f_thms = len(re.findall(r"^\s*theorem\b", frontier_src, re.M))
    f_lems = len(re.findall(r"^\s*lemma\b", frontier_src, re.M))
    f_sorrys = len(re.findall(r"^\s*sorry\b", frontier_src, re.M))

    assert sorrys + f_sorrys == 0, "a sorry is present; these must not be called theorems"
    assert f">{thms + lems + f_thms + f_lems:,}<" in index, (
        "the front page's kernel-checked total does not match both Lean trees"
    )


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


def test_the_pages_add_no_em_dashes_of_their_own(built: Path) -> None:
    """House style: the generator's own prose uses no em dash.

    Quoted material is a different matter. Document blurbs, ledger entries,
    module titles and adversaries' findings are read out of repository
    artifacts, and silently repunctuating someone's recorded words to satisfy a
    style rule would be editing evidence. So the rule is not "no em dashes on
    the page" but "none the generator introduced": the count on every page must
    equal the count in the material it quotes.
    """
    import importlib.util

    spec = importlib.util.spec_from_file_location("site_gen_dash", SITE)
    site = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(site)

    quoted = 0
    for d in site.reading():
        quoted += d["blurb"].count("—") + d["title"].count("—")
    for m in site.lean_arm()["modules"]:
        quoted += m["title"].count("—")
    for g in site.graveyard():
        quoted += sum(str(v).count("—") for v in g.values())
    for c in site.review():
        quoted += str(c).count("—")
    for x in site.corrections():
        quoted += sum(str(v).count("—") for v in x.values())
    for x in site.frontier()["results"]:
        quoted += sum(str(v).count("—") for v in x.values())

    rendered = sum(p.read_text(errors="ignore").count("—") for p in _pages(built))
    assert rendered <= quoted, (
        f"{rendered - quoted} em dash(es) on the pages came from the generator's "
        f"own prose, not from quoted material"
    )


def test_a_truncated_history_is_not_reported_as_a_number(monkeypatch) -> None:
    """A shallow checkout must not become a published commit count.

    The host's git integration checks out at depth 10, so `rev-list --count`
    answered 10 and the front page told the world this laboratory had ten
    commits. It has hundreds. The number rendered exactly as confidently as a
    true one, which is the failure worth a test: a count that cannot be trusted
    is withheld rather than guessed, and the headline degrades to the plain
    label rather than asserting a span it cannot establish.
    """
    import importlib.util

    spec = importlib.util.spec_from_file_location("site_gen", SITE)
    site = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(site)

    real = site.git

    def shallow_git(*args):
        if args[:2] == ("rev-parse", "--is-shallow-repository"):
            return "true"
        if args[:1] == ("rev-list",):
            return "10"
        return real(*args)

    monkeypatch.setattr(site, "git", shallow_git)
    facts = site.repo_facts()
    assert facts["commits"] == 0, "a depth-limited count was reported as history"
    assert facts["since"] == "", "a truncated history claimed a start date"
    assert facts["days"] == 0, "a truncated history claimed an elapsed span"


def test_the_pages_commit_to_one_appearance(built: Path) -> None:
    """A record sent to people must look the same to all of them.

    While the pages followed `prefers-color-scheme`, the author screenshotted
    the light rendering and the reader on a dark system saw something else —
    same commit, same content, two appearances, and no way to tell which one a
    given reader got. The palette is now unconditional. This also requires an
    explicit background on `body`: without one the page borrows whatever ground
    the browser or an embedding host paints, which reintroduces the drift by
    another route.
    """
    for page in _pages(built):
        text = page.read_text(errors="ignore")
        assert "prefers-color-scheme" not in text, (
            f"{page.name} follows the reader's system theme; the look must be pinned"
        )
        assert re.search(r"body\{[^}]*background:", text), (
            f"{page.name} leaves the page background to the host"
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
    assert cfg["installCommand"] == "", "an install step would defeat the point"

    # The build reaches the generator through a script, so follow the chain
    # rather than only checking the command string: the point is that the
    # deployed pages come from this generator, however many hops away it is.
    chain = cfg["buildCommand"]
    for script in re.findall(r"[\w/]+\.sh", cfg["buildCommand"]):
        path = REPO / script
        if path.is_file():
            chain += "\n" + path.read_text(encoding="utf-8")
    assert SITE.name in chain, "the build does not reach the generator"

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
