"""Pins for the numbers `claim_halflife`'s `RESULTS.md`, `RUNS.md` and `docs/43` state.

Run from the repository root:

    .venv/bin/python -m pytest -q hunts/claim_halflife

Written 2026-10-10, when the hunt was landed on main as #131. The measurement is
of this repository's git history frozen at `2da62eb` (`corpus.CASE_LOG_REF`), and
the scripts read history from whatever is checked out, so every git call made
here is bounded at that commit; otherwise the corpus would grow with main and
the numbers would drift. The tests need the full history and skip, saying so,
on a shallow clone or one without that commit, which is the hazard the hunt
itself measured.

What is re-run here: the corpus, both classifiers on every event, the pinning
count against the tests as they stood at `2da62eb`, the depth table, both audit
samples and both blind-audit scores. What is not: the three planted-fault
ladders, which mutate other hunts' artifacts and run their tests; they were
re-run on 2026-10-10 in a scratch worktree at `2da62eb` (`RUNS.md`), and here
only their artifacts' arithmetic is checked. Nothing writes into the tree.

This measures the laboratory, not mathematics; nothing here bears on RH
(`docs/08`).
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ART = HERE / "artifacts"
# the scripts import their siblings as top-level modules, as they do when run
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import classify as C1  # noqa: E402
import classify2 as C2  # noqa: E402
import corpus as CORPUS  # noqa: E402

REF = "2da62eb9842db72d4f6bad09c6f13efe384d6ab7"


def _git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, check=True
                          ).stdout.decode("utf-8", "replace")


def _history_is_usable() -> str | None:
    try:
        if _git("rev-parse", "--is-shallow-repository").strip() == "true":
            return "shallow clone: run `git fetch --unshallow origin` (the hazard this hunt measured)"
        _git("cat-file", "-e", f"{REF}^{{commit}}")
    except subprocess.CalledProcessError:
        return f"commit {REF[:7]} is not in this clone"
    return None


needs_history = pytest.mark.skipif(_history_is_usable() is not None,
                                   reason=str(_history_is_usable()))


def _json(name: str):
    return json.loads((ART / name).read_text(encoding="utf-8"))


def _bounded(real):
    """git(...) with every `log` stopped at REF."""
    def wrapped(*args: str) -> str:
        if args and args[0] == "log":
            args = list(args)
            cut = args.index("--") if "--" in args else len(args)
            args.insert(cut, REF)
        return real(*args)
    return wrapped


# --- the corpus ------------------------------------------------------------------


@needs_history
def test_the_corpus_rebuilds_identically_at_its_commit(monkeypatch):
    monkeypatch.setattr(CORPUS, "git", _bounded(CORPUS.git))
    rows, commits = CORPUS.build(CORPUS.CASE_LOG_REF)
    from dataclasses import asdict
    blob = json.dumps({"rows": [asdict(r) for r in rows],
                       "commits": {s: asdict(c) for s, c in commits.items()}}, indent=1)
    masked, n = CORPUS._mask(blob)
    live = json.loads(masked)
    stored = _json("corpus.json")
    assert live["rows"] == stored["rows"]
    assert live["commits"] == stored["commits"]
    assert (stored["n_entries"], stored["n_with_directory_in_git"], len(commits)) == (95, 95, 428)
    assert n == _json("lexical_mask.json")["occurrences_masked"] == 5


@needs_history
def test_planted_fault_an_unbounded_corpus_is_not_the_frozen_one():
    """Without the bound, main's later commits join the corpus and the counts move."""
    rows, _ = CORPUS.build(CORPUS.CASE_LOG_REF)
    assert sum(len(r.later) for r in rows) > 414


# --- the classifiers -----------------------------------------------------------------


@needs_history
def test_both_classifiers_reproduce_every_event():
    corpus = _json("corpus.json")
    commits = corpus["commits"]
    for name, mod in (("classified.json", C1), ("classified2.json", C2)):
        for row in _json(name):
            for e in row["events"]:
                live = mod.classify_commit(e["sha"], row["directory"], commits)
                live["latency_days"] = C1.days_between(row["first_date"], live["date"])
                assert live == e, (name, row["directory"], e["sha"][:12])


@needs_history
def test_pinning_against_the_tests_as_they_stood():
    names = [n for n in _git("ls-tree", "--name-only", f"{REF}:tests").split() if n.endswith(".py")]
    sources = {n: _git("show", f"{REF}:tests/{n}") for n in names}
    for name in ("classified.json", "classified2.json"):
        for row in _json(name):
            pinned = sorted(n for n, t in sources.items() if row["directory"] in t)
            assert pinned == row["pinned_by"], row["directory"]


def test_the_headline_counts():
    c1, c2 = _json("classified.json"), _json("classified2.json")
    assert len(c1) == len(c2) == 95
    assert sum(r["asserts_a_finding"] for r in c1) == 80
    assert sum(bool(r["pinned_by"]) for r in c1) == 19
    assert sum(r["n_later_commits"] == 0 for r in c1) == 22
    assert sum(r["n_later_commits"] for r in c1) == sum(r["n_later_commits"] for r in c2) == 414
    # the first classifier's withdrawn rate: 21% at the medium level
    assert sum(any(e["medium"] for e in r["events"]) for r in c1) == 20
    strict = [(r, e) for r in c2 for e in r["events"] if e["strict"]]
    assert len(strict) == 73
    assert len({r["directory"] for r, _ in strict}) == 15
    assert Counter(e["countermeasure"] for _, e in strict) == {"none": 72, "test-added": 1}
    lat = sorted(e["latency_days"] for _, e in strict)
    assert (lat[len(lat) // 2], round(sum(lat) / len(lat), 1), max(lat)) == (1, 1.8, 13)
    assert round(100 * 73 / 414, 1) == 17.6
    assert round(0.40 * 73) == 29


# --- the depth table ---------------------------------------------------------------------


@needs_history
def test_the_depth_table():
    corpus = _json("corpus.json")

    def never_and_seen(keep):
        never = seen = 0
        for r in corpus["rows"]:
            later = [s for s in r["later"] if keep is None or s in keep]
            seen += len(later)
            never += not later
        return seen, never

    table = {d["depth"]: (d["later_commits_seen"], d["never_revisited"]) for d in _json("depth.json")}
    assert table == {"full": (414, 22), 100: (72, 91), 262: (168, 29), 500: (229, 23), 800: (367, 23)}
    for depth in (100, 262, 500, 800):
        keep = set(_git("log", f"-{depth}", "--format=%H", REF).split())
        assert never_and_seen(keep) == table[depth], depth
    assert int(_git("rev-list", "--count", REF)) == 1084
    assert [round(100 * table[d][1] / 95, 1) for d in ("full", 262, 100)] == [23.2, 30.5, 95.8]


# --- the blind audits -----------------------------------------------------------------------


def _score(tmp_path, monkeypatch, key, audit, dest):
    import score_audit as SA
    for f in ("audit_sample.json", "audit_sample2.json"):
        (tmp_path / f).write_bytes((ART / f).read_bytes())
    monkeypatch.setattr(SA, "ART", tmp_path)
    monkeypatch.setattr(sys, "argv", ["score_audit.py", str(key), str(audit), dest])
    SA.main()
    return json.loads((tmp_path / dest).read_text(encoding="utf-8"))


def test_the_first_blind_audit_scores(tmp_path, monkeypatch):
    live = _score(tmp_path, monkeypatch, ART / "audit_key.json", ART / "blind_audit_round1.json",
                  "audit_score.json")
    assert live == _json("audit_score.json")
    assert (round(live["agreement"] * 30), round(live["classifier_precision_against_audit"], 2),
            round(live["classifier_recall_against_audit"], 2)) == (16, 0.40, 0.55)


def test_the_second_blind_audit_scores(tmp_path, monkeypatch):
    key = tmp_path / "key2.json"     # score_audit picks the sample by a "2" in the key's name
    key.write_bytes((ART / "audit_key2_sample.json").read_bytes())
    live = _score(tmp_path, monkeypatch, key, ART / "blind_audit_round2.json", "audit_score2.json")
    assert live == _json("audit_score2.json")
    prec, rec = live["classifier_precision_against_audit"], live["classifier_recall_against_audit"]
    assert (round(live["agreement"] * 30), round(prec, 2), round(rec, 2)) == (22, 0.67, 0.77)
    assert round(100 * 73 / 414 * prec / rec, 1) == 15.3


def test_the_repaired_classifier_on_the_first_sample_is_fitted_21_of_30():
    labels = {}
    for r in _json("classified2.json"):
        for e in r["events"]:
            labels[(r["directory"], e["sha"][:12])] = e["strict"]
    audit = {row["row_id"]: row["is_revision"] for row in _json("blind_audit_round1.json")["rows"]}
    tp = tn = fp = fn = 0
    for row in _json("audit_sample.json"):
        k = labels[(row["hunt_directory"], row["commit"])]
        a = audit[row["row_id"]]
        tp += a and k
        tn += (not a) and (not k)
        fp += k and not a
        fn += a and not k
    assert (tp + tn, round(tp / (tp + fp), 2), round(tp / (tp + fn), 2)) == (21, 0.58, 0.64)
    stored = _json("audit_score_repaired_same_rows.json")
    assert round(stored["agreement"] * 30) == 21


_INDEX = re.compile(r"^index [0-9a-f]+\.\.[0-9a-f]+", re.MULTILINE)


@needs_history
def test_both_audit_samples_reproduce(tmp_path, monkeypatch):
    """Identical but for git's abbreviated-hash width in the diff headers, which
    grows with the size of the clone."""
    import make_audit_sample as S1
    import make_audit_sample2 as S2
    for f in ("classified.json", "classified2.json"):
        (tmp_path / f).write_bytes((ART / f).read_bytes())
    monkeypatch.setattr(S1, "ART", tmp_path)
    S1.main()
    (tmp_path / "audit_sample_first.json").write_bytes((tmp_path / "audit_sample.json").read_bytes())
    monkeypatch.setattr(S2, "ART", tmp_path)
    monkeypatch.setattr(sys, "argv", ["make_audit_sample2.py", str(tmp_path / "key2.json")])
    S2.main()

    def norm(rows):
        out = []
        for r in rows:
            r = dict(r)
            r["diff_first_8000_chars"] = _INDEX.sub("index", r["diff_first_8000_chars"])[:7900]
            out.append(r)
        return out

    assert norm(json.loads((tmp_path / "audit_sample_first.json").read_text())) == norm(_json("audit_sample.json"))
    assert json.loads((tmp_path / "audit_key.json").read_text()) == _json("audit_key.json")
    assert norm(json.loads((tmp_path / "audit_sample2.json").read_text())) == norm(_json("audit_sample2.json"))
    assert json.loads((tmp_path / "key2.json").read_text()) == _json("audit_key2_sample.json")


# --- the ladders, from their artifacts ------------------------------------------------------


def test_the_ladder_counts():
    first = _json("lesion.json")
    named = [r["n_artifacts_named"] for r in first if r.get("n_artifacts_named")]
    assert (len(named), sum(n > 1 for n in named), max(named)) == (26, 20, 37)
    second = Counter(str(r.get("rungA_all_leaves")) for r in _json("lesion2.json"))
    assert (second["caught"], second["caught"] + second["missed"]) == (9, 24)
    third = Counter(r["outcome"] for r in _json("lesion3.json"))
    assert third == {"no-mutable-artifact": 14, "reads-numbers": 11, "byte-pinned": 8,
                     "reads-no-numbers": 6}
    assert third["reads-numbers"] + third["byte-pinned"] == 19
    assert sum(third.values()) - third["no-mutable-artifact"] == 25


@needs_history
def test_the_byte_pinned_tests_compute_hashes():
    tests = {r["test"] for r in _json("lesion3.json") if r["outcome"] == "byte-pinned"}
    assert len(tests) == 8
    for t in tests:
        assert re.search(r"sha256|hashlib", _git("show", f"{REF}:tests/{t}")), t


@needs_history
def test_the_loose_tolerance_example_in_the_doors():
    src = _git("show", f"{REF}:tests/test_quotient_certificate.py")
    assert "1035.23393430" in src and "< 1e-4" in src
    data = json.loads(_git("show", f"{REF}:hunts/quotient_certificate/results.json"))
    row = [r for r in data["results"] if r["N"] == 100000][0]
    gap = abs(float(row["evaluations"][-1]["excess"]) - 1035.23393430)
    assert f"{gap:.2e}" == "1.05e-06"


@needs_history
def test_the_handoff_doctrine_as_the_file_stood():
    """RESULTS.md: 'every HANDOFF.md record in this tree carries a field called
    Now caught by:'. At the corpus commit the header states the format, and 3 of
    the 24 records carry the field (not reproduced; the note is in place)."""
    text = _git("show", f"{REF}:HANDOFF.md")
    records = re.split(r"^## Record", text, flags=re.MULTILINE)[1:]
    assert len(records) == 24
    assert sum("Now caught by" in r for r in records) == 3
    assert "what now catches the" in text[:400]


def test_the_pages_state_these_numbers():
    results = (HERE / "RESULTS.md").read_text(encoding="utf-8")
    door = (ROOT / "docs" / "43-what-happens-to-a-claim.md").read_text(encoding="utf-8")
    for s in ("entries never touched again                       22  (23.2%)",
              "| **262, the container's own** | 168 | 29 (30.5%) |",
              "| **repaired, disjoint sample** | **22/30 (73.3%)** | **0.67** | **0.77** |",
              "gives **`15.3%`**", "`17.6%`"):
        assert s in results, s
    for s in ("| full (1084) | 22 (23.2%) |", "Mean 1.8. Longest 13.", "19 of 95"):
        assert s in door, s
