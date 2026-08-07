"""Tests for ``scripts/13_discovery_run.py`` — the funnel's operator console.

Three things can actually be wrong with a console, and all three are tested
here:

* **the plumbing** — it runs, it exits zero, it writes to the ledger it was
  pointed at and to nothing else, and ``--dry-run`` writes nothing at all;
* **the arithmetic** — the waterfall it prints must agree with the funnel
  record it prints it from.  The one number that is easy to get wrong is the
  survivor count: the funnel records a *departure* at the terminal stage for
  every candidate, promoted or not, so a naive ``entered - left`` reports every
  run as barren.  That is pinned below;
* **the honest-scope statements** — the closing block must say that survivors
  are leads rather than results and that "not recognised offline" is not
  novelty.  Those are load-bearing claims about what the output means, so, per
  the house rule, they are tests and not comments.

Plus the one fact about the repository the console asserts in its own header:
the ledger directory is gitignored, and a fresh clone carries nothing but the
``.gitkeep``.

Every subprocess here is given ``--ledger`` inside ``tmp_path``: a test that
wrote to the real ``conjectures/`` notebook would silently corrupt the very
conversion rates the module exists to measure.
"""

from __future__ import annotations

import importlib.util
import io
import json
import os
import subprocess
import sys
from contextlib import redirect_stdout

import pytest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(REPO_ROOT, "scripts", "13_discovery_run.py")

#: A lead source that is cheap and reaches every interesting disposition:
#: catalogued constants (``known``), one reduction (``trivial``), one thing the
#: screens could not promote (``inconclusive``) and, because Xi(1) is not in the
#: catalogue, one survivor.
CHEAP = ["--generators", "constants", "--context", "xi_points=0,1", "--seed", "4242"]

#: Distinct from ``zeta_domain.DEFAULT_SEED``, so a candidate carrying it proves
#: ``--seed`` reached the provenance rather than the domain's own default.
SEED = 4242


def run_script(*args: str, expect: int = 0) -> str:
    """Run the console as a subprocess and return its stdout."""
    proc = subprocess.run(
        [sys.executable, SCRIPT, *args],
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )
    assert proc.returncode == expect, proc.stderr[-3000:]
    return proc.stdout


@pytest.fixture(scope="module")
def console():
    """The script imported as a module, for unit tests of its helpers.

    ``importlib`` rather than ``import``: the file name starts with a digit, so
    it is not a legal module name.
    """
    spec = importlib.util.spec_from_file_location("console13", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def live(tmp_path_factory):
    """One real run against a throwaway ledger; several tests read it."""
    path = tmp_path_factory.mktemp("ledger13") / "ledger.jsonl"
    out = run_script(*CHEAP, "--ledger", str(path))
    return path, out


# ---------------------------------------------------------------------------
# plumbing
# ---------------------------------------------------------------------------


def test_help_exits_zero_and_explains_what_the_thing_is():
    out = run_script("--help")
    assert "usage:" in out.lower()
    # the house rule: the help carries the subject, not just the flags
    assert len(out) > 900, len(out)
    lowered = out.lower()
    for phrase in ("survivor is a lead", "not a result", "novelty", "gitignored"):
        assert phrase in lowered, phrase


def test_list_names_the_plugins_and_runs_nothing():
    out = run_script("--list")
    assert "zeta_constants" in out
    assert "zeta_catalogue" in out
    assert "THE FUNNEL WATERFALL" not in out


def test_dry_run_writes_nothing_at_all(tmp_path):
    path = tmp_path / "ledger.jsonl"
    out = run_script(
        "--dry-run", "--generators", "structural", "--ledger", str(path)
    )
    assert "DRY RUN" in out
    assert not path.exists(), "a dry run must not create the ledger"
    assert not (tmp_path / "ledger.runs.jsonl").exists()
    assert not list(tmp_path.iterdir()), sorted(p.name for p in tmp_path.iterdir())


def test_live_run_writes_both_streams_and_they_parse(live):
    path, _ = live
    runs = path.with_name("ledger.runs.jsonl")
    assert path.exists() and runs.exists()
    candidates = [json.loads(line) for line in path.read_text().splitlines() if line]
    records = [json.loads(line) for line in runs.read_text().splitlines() if line]
    assert candidates and all(c["id"].startswith("cand-") for c in candidates)
    # a run is written twice: once on entry, once on completion (README §8.1)
    states = [r["state"] for r in records]
    assert states == ["started", "finished"], states
    # --seed reached the provenance, not just the header line
    assert {c["provenance"]["seed"] for c in candidates} == {SEED}
    # and no machine-local path was written anywhere in the log
    assert "/Users/" not in path.read_text()
    assert "/home/" not in path.read_text()


def test_seed_reaches_the_generators_and_not_only_the_header(tmp_path):
    """``--seed`` must change what is *drawn*, not just what is printed.

    The stochastic generator's draws live in the candidate evidence rather than
    in the claim, so two seeds give the same ids and different witnesses.  A
    console that printed the seed in its header but never put it in the
    generator context would produce identical evidence, and this would fail.
    """

    def drawn(seed: int) -> list[str]:
        path = tmp_path / f"s{seed}" / "ledger.jsonl"
        path.parent.mkdir()
        run_script(
            "--generators", "structural", "--seed", str(seed), "--ledger", str(path)
        )
        latest: dict[str, dict] = {}
        for line in path.read_text().splitlines():
            if line:
                record = json.loads(line)
                latest[record["id"]] = record
        rows = [r for r in latest.values() if r["provenance"]["stochastic"]]
        assert rows, "the domain marked nothing stochastic"
        assert {r["provenance"]["seed"] for r in rows} == {seed}
        return [json.dumps(r["evidence"].get("witnesses"), sort_keys=True) for r in rows]

    assert drawn(7) != drawn(8), "the seed never reached the generator"


def test_sections_appear_in_the_required_order(live):
    _, out = live
    order = [
        "1)  WHAT WAS GENERATED",
        "2)  THE FUNNEL WATERFALL",
        "3)  SURVIVORS",
        "4)  GENERATOR SCORECARD",
        "READ THIS BEFORE QUOTING ANY NUMBER ABOVE",
    ]
    positions = [out.index(marker) for marker in order]
    assert positions == sorted(positions), positions


def test_waterfall_labels_the_five_required_stages(live):
    _, out = live
    table = out.split("2)  THE FUNNEL WATERFALL")[1].split("3)  SURVIVORS")[0]
    for label in ("generated", "deduped", "known", "screened", "SURVIVING"):
        assert label in table, label


def test_scorecard_carries_the_five_required_columns(live):
    _, out = live
    card = out.split("4)  GENERATOR SCORECARD")[1]
    header = [line for line in card.splitlines() if "generator" in line][0]
    for column in ("made", "known", "refut", "surv", "sec/surv"):
        assert column in header, column
    assert "zeta_constants" in card


def test_survivors_are_printed_with_their_provenance(live):
    _, out = live
    block = out.split("3)  SURVIVORS")[1].split("4)  GENERATOR SCORECARD")[0]
    assert "LEADS, NOT RESULTS" in block
    if "cand-" in block:  # a survivor was found: it must carry its provenance
        for field in (
            "generator",
            "lab object",
            "parameters",
            "precision",
            "seed",
            "code revision",
            "captured",
            "reproducible",
            "proof gap",
        ):
            assert field in block, field


def test_second_run_over_the_same_ledger_is_all_duplicates(live, tmp_path):
    """The measurement the ledger exists to make: re-mining covered ground."""
    path, _ = live
    copy = tmp_path / "ledger.jsonl"
    copy.write_text(path.read_text())
    copy.with_name("ledger.runs.jsonl").write_text(
        path.with_name("ledger.runs.jsonl").read_text()
    )
    out = run_script(*CHEAP, "--ledger", str(copy))
    table = out.split("2)  THE FUNNEL WATERFALL")[1].split("3)  SURVIVORS")[0]
    duplicate = [line for line in table.splitlines() if line.strip().startswith("duplicate")]
    assert duplicate and "100.0%" in duplicate[0], duplicate
    assert "SURVIVING — leads, not results" in table


def test_report_reads_the_ledger_and_generates_nothing(live, tmp_path):
    path, _ = live
    before = path.read_text()
    out = run_script("--report", "--dashboard", "--ledger", str(path))
    assert "REPORT (read-only)" in out
    assert "WHAT HAS BEEN GENERATED  (whole ledger)" in out
    assert "GENERATOR SCORECARD  (whole ledger)" in out
    # --dashboard appends the metrics module's own tables, unedited
    assert "APPENDIX" in out and "STAGE AND SCREEN COSTS" in out
    assert path.read_text() == before, "--report must not write"


def test_report_on_an_empty_ledger_says_so_rather_than_printing_zero_rates(tmp_path):
    out = run_script("--report", "--ledger", str(tmp_path / "nothing.jsonl"))
    assert "no run has been recorded" in out
    assert "no generator invocation" in out
    closing = out.split("READ THIS BEFORE QUOTING ANY NUMBER ABOVE")[1]
    # the honest-scope line must survive the case where nothing survived
    assert "NOTHING SURVIVED" in closing
    assert "LEADS, NOT RESULTS" in closing


def test_limit_caps_production_and_records_the_skipped_source(tmp_path):
    out = run_script(
        "--dry-run",
        "--limit", "2",
        "--generators", "structural,finite_field",
        "--ledger", str(tmp_path / "ledger.jsonl"),
    )
    generated = out.split("1)  WHAT WAS GENERATED")[1].split("2)  THE")[0]
    total = [line for line in generated.splitlines() if line.strip().startswith("TOTAL")][0]
    assert total.split()[1] == "2", total
    assert "skipped (limit)" in generated


def test_unknown_generator_is_refused_with_the_alternatives(tmp_path):
    proc = subprocess.run(
        [sys.executable, SCRIPT, "--generators", "nope",
         "--ledger", str(tmp_path / "l.jsonl")],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    assert proc.returncode == 1
    assert "no generator named" in proc.stderr
    assert "zeta_constants" in proc.stderr
    assert not (tmp_path / "l.jsonl").exists()


def test_report_and_dry_run_together_are_refused(tmp_path):
    proc = subprocess.run(
        [sys.executable, SCRIPT, "--report", "--dry-run",
         "--ledger", str(tmp_path / "l.jsonl")],
        capture_output=True, text=True, cwd=REPO_ROOT,
    )
    assert proc.returncode == 2
    assert "--dry-run is redundant" in proc.stderr


# ---------------------------------------------------------------------------
# the honest-scope statements
# ---------------------------------------------------------------------------


def test_closing_block_says_survivors_are_leads_not_results(live):
    _, out = live
    closing = out.split("READ THIS BEFORE QUOTING ANY NUMBER ABOVE")[1]
    flat = " ".join(closing.split())
    assert "LEADS, NOT RESULTS" in flat
    assert "not a theorem" in flat
    assert "not evidence for the Riemann Hypothesis" in flat
    assert "proof_gap stating what is missing" in flat


def test_closing_block_refuses_to_call_an_offline_miss_novelty(live):
    _, out = live
    closing = out.split("READ THIS BEFORE QUOTING ANY NUMBER ABOVE")[1]
    assert '"NOT RECOGNISED OFFLINE" IS NOT NOVELTY' in closing
    assert "OEIS" in closing and "arXiv" in closing


def test_no_output_anywhere_claims_a_discovery_is_new(live):
    """The integrity rule of ``ontology.knownness``, enforced on this console.

    The console may print the *word* novelty only inside a statement denying it.
    Every other spelling of "this is new" is refused outright.
    """
    _, out = live
    lowered = out.lower()
    for word in ("unpublished", "never seen before", "new discovery", "we discovered"):
        assert word not in lowered, word
    for line in lowered.splitlines():
        if "novel" in line:
            assert "not novelty" in line or "never a novelty" in line, line


# ---------------------------------------------------------------------------
# the arithmetic
# ---------------------------------------------------------------------------


class _Tally:
    """The minimum a stage tally must expose; both real ones satisfy it."""

    def __init__(self, stage, entered, left, seconds=0.0):
        self.stage = stage
        self.entered = entered
        self.left = left
        self.seconds = seconds


def _waterfall_text(console, tallies, dispositions, generated):
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        survived = console.section_waterfall(tallies, dispositions, generated)
    return survived, buffer.getvalue()


def test_survivors_are_not_counted_as_removed_by_the_terminal_stage(console):
    """The funnel logs a departure for a survivor too; the waterfall must not.

    With ``entered - left`` taken literally at the terminal stage, a run with
    one survivor and one unpromotable candidate reports zero survivors — the
    console would then contradict its own disposition table.
    """
    tallies = [
        _Tally("generate", 8, 0),
        _Tally("deduplicate", 8, 0),
        _Tally("knownness", 8, 5),
        _Tally("cheap_screens", 3, 1),
        _Tally("expensive_screens", 2, 0),
        _Tally("terminal", 2, 2),
    ]
    dispositions = {"known": 5, "trivial": 1, "survives": 1, "inconclusive": 1}
    survived, text = _waterfall_text(console, tallies, dispositions, 8)
    assert survived == 1
    terminal = [ln for ln in text.splitlines() if ln.strip().startswith("terminal")][0]
    assert terminal.split()[-4:-1] == ["2", "1", "1"], terminal
    surviving = [ln for ln in text.splitlines() if "SURVIVING" in ln][0]
    assert surviving.split()[-1] == "1", surviving


def test_waterfall_totals_agree_with_the_disposition_table(console):
    tallies = [
        _Tally("generate", 4, 1),
        _Tally("deduplicate", 3, 1),
        _Tally("knownness", 2, 2),
        _Tally("cheap_screens", 0, 0),
        _Tally("expensive_screens", 0, 0),
        _Tally("terminal", 0, 0),
    ]
    dispositions = {"invalid": 1, "duplicate": 1, "known": 2}
    survived, text = _waterfall_text(console, tallies, dispositions, 4)
    assert survived == 0
    total = [ln for ln in text.splitlines() if ln.strip().startswith("TOTAL")][0]
    assert total.split()[1] == "4", total
    assert "100.0%" in total


def test_a_rate_over_an_empty_population_is_a_dash_not_zero(console):
    assert console._pct(0, 0) == "—"
    assert console._pct(1, 4) == "25.0%"
    assert console._opt_pct(None) == "—"
    assert console._opt_num(None) == "—"


# ---------------------------------------------------------------------------
# argument plumbing (pure functions, no subprocess)
# ---------------------------------------------------------------------------


def test_parse_context_types_its_values(console):
    ctx = console.parse_context(
        ["n_lambda=5", "tol=1.5", "flag=true", "xi_points=0,1,2", "windows=[[1,2]]"]
    )
    assert ctx == {
        "n_lambda": 5,
        "tol": 1.5,
        "flag": True,
        "xi_points": (0, 1, 2),
        "windows": [[1, 2]],
    }


def test_parse_context_refuses_a_bare_word(console):
    with pytest.raises(SystemExit):
        console.parse_context(["oops"])


def test_parse_context_handles_an_empty_and_a_textual_value(console):
    """``""`` is a substring of every string — the JSON branch must not eat it."""
    assert console.parse_context(["a=", "b=cauchy"]) == {"a": "", "b": "cauchy"}


def test_parse_context_refuses_malformed_json(console):
    with pytest.raises(SystemExit):
        console.parse_context(["windows=[1,"])


def test_select_generators_accepts_full_and_short_names(console):
    from ontology.domains import zeta_domain

    domain = zeta_domain.DOMAIN
    assert console.select_generators(domain, "all") == tuple(domain.generators)
    chosen = console.select_generators(domain, "constants, zeta_relations")
    assert [g.name for g in chosen] == ["zeta_constants", "zeta_relations"]


def test_select_generators_refuses_an_unknown_name(console):
    from ontology.domains import zeta_domain

    with pytest.raises(SystemExit) as excinfo:
        console.select_generators(zeta_domain.DOMAIN, "chemistry")
    assert "no generator named" in str(excinfo.value)


def test_capturing_proxy_is_transparent_and_keeps_what_it_saw(console):
    """The proxy must not change what the funnel records about a generator."""
    from ontology.domains import zeta_domain

    inner = zeta_domain.DOMAIN.generator("zeta_structural")
    sink = {}
    proxy = console.CapturingGenerator(inner, sink)
    assert (proxy.name, proxy.version) == (inner.name, str(inner.version))
    assert proxy.describe() == inner.describe()
    emitted = list(proxy.generate({"seed": 1, "jensen_d_max": 3, "jensen_n_max": 2}))
    assert emitted, "the structural generator emitted nothing to capture"
    assert sink == {c.id: c for c in emitted}


def _dispositions(out: str) -> dict[str, int]:
    """Parse the printed disposition table back out of the console's output."""
    table = out.split("2)  THE FUNNEL WATERFALL")[1].split("3)  SURVIVORS")[0]
    body = table.split("what it means")[1].split("TOTAL")[0]
    counts: dict[str, int] = {}
    for line in body.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[1].isdigit():
            counts[parts[0]] = int(parts[1])
    return counts


@pytest.mark.slow
def test_the_headline_numbers_quoted_in_the_readme_are_what_the_funnel_produces(tmp_path):
    """``README.md`` item 12 quotes this run; a number in a document is a test.

    Slow because it consults all seven generators; the Legendre-Weil screen
    escalations are served from the committed data/ sides cache, so a warm
    run stays in seconds.  If a generator's behaviour changes, this fails and
    the README sentence has to be rewritten — which is the intended coupling.

    No survivor by design: the Legendre Λ-mass constant that exercises the
    survivor path is opt-in (``legendre_mass_constant``), and its one
    recorded run — operator literature check included — is in ROADMAP.md.
    """
    out = run_script("--dry-run", "--ledger", str(tmp_path / "ledger.jsonl"))
    counts = _dispositions(out)
    assert counts == {
        "duplicate": 0,
        "invalid": 0,
        "known": 26,
        "trivial": 1,
        "refuted": 0,
        "survives": 0,
        "inconclusive": 5,
    }, counts
    assert sum(counts.values()) == 32
    assert "81.2%" in out, "the already-known share quoted in README item 12"


def test_a_raising_plugin_is_reported_and_then_re_raised(console, tmp_path):
    """A screen that throws is a defect, not a verdict.

    The console must not turn it into a quiet zero, and it must say the one
    thing the traceback does not: that the run record survived with the work
    the run had already done, so the conversion rates keep their denominator.
    """
    import dataclasses

    from ontology.domains import zeta_domain
    from ontology.ledger import Ledger

    class Boom:
        name = "boom"
        cost = "cheap"
        checks = ()

        def describe(self) -> str:
            return "a screen that always raises"

        def apply(self, candidate):
            raise RuntimeError("deliberate screen defect")

    # No detectors: otherwise the catalogue decides the candidate before the
    # broken screen is ever consulted, and the test would pass vacuously.
    domain = dataclasses.replace(
        zeta_domain.DOMAIN, screens=(Boom(),), detectors=()
    )
    store = Ledger(tmp_path / "ledger.jsonl")
    buffer = io.StringIO()
    with redirect_stdout(buffer), pytest.raises(RuntimeError, match="screen defect"):
        console.do_run(
            domain,
            store,
            generator_spec="structural",
            limit=1,
            dry_run=False,
            seed=1,
            context={},
            shown=3,
            dashboard=False,
        )
    text = buffer.getvalue()
    assert "THE RUN DID NOT COMPLETE" in text
    assert "state='crashed'" in text
    runs = [
        json.loads(line)
        for line in (tmp_path / "ledger.runs.jsonl").read_text().splitlines()
        if line
    ]
    assert [r["state"] for r in runs] == ["started", "crashed"], runs


def test_a_lead_source_that_raised_is_not_filed_as_one_that_found_nothing(
    console, tmp_path
):
    """"Found nothing" and "broke" are different problems.

    The cumulative view once had only an ``empty`` column, so a generator that
    raised was indistinguishable from one that ran cleanly and produced nothing
    — and a generator that raised *part-way through* was invisible entirely,
    because it keeps the candidates it had already yielded and so is not empty
    at all. Both are defects in the lead source, and the report has to be able
    to say which.
    """
    from ontology.ledger import Ledger

    store = Ledger(tmp_path / "ledger.jsonl")
    store.append_run(
        {
            "run_id": "r-1",
            "state": "finished",
            "started_at": "2026-01-01T00:00:00+00:00",
            "generators": [
                {"generator": "quiet", "version": "1", "produced": 0, "seconds": 1.0},
                {"generator": "broken", "version": "1", "produced": 2, "seconds": 1.0,
                 "error": "RuntimeError: deliberate"},
            ],
            # ``GeneratorStat.produced`` is counted from the outcomes, not from
            # the generator's own report: it is what reached a disposition.
            "outcomes": [
                {"candidate_id": f"cand-{i}", "generator": "broken",
                 "generator_version": "1", "kind": "constant", "stage": "terminal",
                 "disposition": "inconclusive", "seconds": 0.0}
                for i in range(2)
            ],
        }
    )
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        console.do_report(store, shown=3, dashboard=False)
    text = buffer.getvalue()
    header = next(l for l in text.splitlines() if "generator" in l and "empty" in l)
    assert "raised" in header, header
    quiet = next(l for l in text.splitlines() if l.strip().startswith("quiet"))
    broken = next(l for l in text.splitlines() if l.strip().startswith("broken"))
    # quiet: one empty invocation, nothing raised. broken: nothing empty (it
    # yielded two before dying), one raised.
    assert quiet.split() == ["quiet", "1", "1", "1", "0", "0", "1.000"]
    assert broken.split() == ["broken", "1", "1", "0", "1", "2", "1.000"]


# ---------------------------------------------------------------------------
# the ledger is private
# ---------------------------------------------------------------------------


def test_gitignore_excludes_the_ledger_but_keeps_the_directory():
    text = open(os.path.join(REPO_ROOT, ".gitignore"), encoding="utf-8").read()
    assert "conjectures/*" in text
    assert "!conjectures/.gitkeep" in text


def test_git_agrees_the_ledger_is_ignored_and_untracked():
    """A fresh clone must carry the empty directory and nothing else.

    Skipped rather than failed where ``git`` is unavailable or the tree is not
    a checkout: the console degrades the same way, and a test that cannot run
    must say so instead of passing.
    """
    try:
        inside = subprocess.run(
            ["git", "rev-parse", "--is-inside-work-tree"],
            capture_output=True, text=True, cwd=REPO_ROOT, timeout=10,
        )
    except (OSError, subprocess.SubprocessError):  # pragma: no cover - no git
        pytest.skip("git is unavailable")
    if inside.returncode != 0:  # pragma: no cover - not a checkout
        pytest.skip("not a git checkout")

    ignored = subprocess.run(
        ["git", "check-ignore", "-q", "conjectures/ledger.jsonl"],
        cwd=REPO_ROOT, timeout=10,
    )
    assert ignored.returncode == 0, "conjectures/ledger.jsonl is NOT gitignored"
    runs_ignored = subprocess.run(
        ["git", "check-ignore", "-q", "conjectures/ledger.runs.jsonl"],
        cwd=REPO_ROOT, timeout=10,
    )
    assert runs_ignored.returncode == 0, "the run stream is NOT gitignored"

    tracked = subprocess.run(
        ["git", "ls-files", "conjectures"],
        capture_output=True, text=True, cwd=REPO_ROOT, timeout=10,
    )
    names = [line for line in tracked.stdout.split() if line]
    assert names in ([], ["conjectures/.gitkeep"]), names
