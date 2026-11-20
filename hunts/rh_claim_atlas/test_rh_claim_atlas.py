"""Checks for the atlas of the Alpoge archive (hunt #160).

Three layers, none of which needs the archive:

1. `quotes.json` and `stats.json` are well formed, and consistent with
   `ATLAS.md`: every `path:line` the atlas cites has an entry, every entry is
   cited, every displayed quote equals its entry, and the headline numbers in
   the prose are the numbers in the tables.
2. `verify_quotes.py` shows red: on a tiny fixture tree made in a temporary
   directory it passes when the tree matches and fails on each planted fault.
3. The lexical rules of `hunts/` hold for this directory.

A fourth layer runs only when the archive is at hand: set `RH_CLAIM_ARCHIVE`
to the unpacked source directory (and `RH_CLAIM_MATHLIB` to a Mathlib checkout
at the pinned tag) to replay every citation; set `RH_CLAIM_RECOUNT=1` as well
to recount the whole tree (about three minutes, one core).

Nothing here writes into the repository.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ATLAS = (HERE / "ATLAS.md").read_text(encoding="utf-8")
QUOTES = json.loads((HERE / "quotes.json").read_text(encoding="utf-8"))
STATS = json.loads((HERE / "stats.json").read_text(encoding="utf-8"))
ENTRIES = QUOTES["entries"]

#: built from two halves so that this file does not contain the word itself
RESERVED = "certi" + "fied"
EM_DASH = chr(0x2014)


def _load(name: str):
    spec = importlib.util.spec_from_file_location(f"rh_claim_atlas_{name}", HERE / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


mq = _load("make_quotes")
vq = _load("verify_quotes")


def _sha(lines: list[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()


def _run_verifier(*args: str, env: dict | None = None) -> subprocess.CompletedProcess:
    clean = {k: v for k, v in os.environ.items() if k not in (vq.ENV_ARCHIVE, vq.ENV_MATHLIB)}
    clean.update(env or {})
    return subprocess.run(
        [sys.executable, "-I", str(HERE / "verify_quotes.py"), *args],
        capture_output=True, text=True, env=clean,
    )


# ------------------------------------------------------------ quotes.json


def test_quotes_file_has_the_declared_shape():
    assert QUOTES["schema"] == 1
    assert re.fullmatch(r"[0-9a-f]{64}", QUOTES["archive"]["tarball_sha256"])
    assert QUOTES["abbreviations"] == mq.ABBREVIATIONS
    assert len(ENTRIES) >= 100
    ids = [e["id"] for e in ENTRIES]
    assert len(set(ids)) == len(ids)
    keys = [(e["tree"], e["path"], e["first"], e["last"]) for e in ENTRIES]
    assert len(set(keys)) == len(keys), "one entry per cited range"
    for e in ENTRIES:
        assert e["tree"] in {"archive", "mathlib"}
        assert e["path"].endswith(".lean") and not e["path"].startswith("/") and ".." not in e["path"]
        assert isinstance(e["first"], int) and isinstance(e["last"], int)
        assert 1 <= e["first"] <= e["last"]
        assert re.fullmatch(r"[0-9a-f]{64}", e["sha256"])
        assert e["kind"] in {"quote", "pointer"}
        assert ("text" in e) == (e["kind"] == "quote")
        assert ("head" in e) == (e["kind"] == "pointer")
        assert (e["tree"] == "mathlib") == e["path"].startswith("Mathlib/")


def test_every_stored_quote_hashes_to_its_recorded_sha256():
    quotes = [e for e in ENTRIES if e["kind"] == "quote"]
    assert len(quotes) >= 40
    for e in quotes:
        lines = e["text"].split("\n")
        assert len(lines) == e["last"] - e["first"] + 1, e["id"]
        assert _sha(lines) == e["sha256"], e["id"]
        assert vq.lines_hash(lines) == e["sha256"], e["id"]


def test_quotes_are_short_statements_not_copied_files():
    for e in ENTRIES:
        if e["kind"] == "quote":
            assert e["last"] - e["first"] + 1 <= QUOTES["max_quote_lines"] == 12, e["id"]
        else:
            assert len(e["head"]) <= mq.HEAD_CHARS, e["id"]
    stored = sum(len(e.get("text", e.get("head", ""))) for e in ENTRIES)
    assert stored < 40_000, "quotes.json holds short statements only"


# ------------------------------------------------- ATLAS.md against quotes


def test_every_citation_in_the_atlas_has_an_entry_and_every_entry_is_cited():
    citations, problems = mq.parse_atlas(ATLAS)
    assert problems == []
    cited = {(c["tree"], c["path"], c["first"], c["last"]) for c in citations}
    recorded = {(e["tree"], e["path"], e["first"], e["last"]) for e in ENTRIES}
    assert cited - recorded == set(), "cited in ATLAS.md but missing from quotes.json"
    assert recorded - cited == set(), "in quotes.json but cited nowhere in ATLAS.md"


def test_every_displayed_quote_equals_its_entry():
    citations, _ = mq.parse_atlas(ATLAS)
    by_key = {(e["tree"], e["path"], e["first"], e["last"]): e for e in ENTRIES}
    shown = 0
    for c in citations:
        entry = by_key[(c["tree"], c["path"], c["first"], c["last"])]
        if "text" in c:
            shown += 1
            assert entry["kind"] == "quote", c["cited_as"]
            assert entry["text"] == c["text"], c["cited_as"]
        else:
            assert entry["kind"] == "pointer", c["cited_as"]
    assert shown == ATLAS.count("```lean") == sum(e["kind"] == "quote" for e in ENTRIES)


def test_the_parser_sees_a_block_that_drifts_from_its_citation():
    """The consistency check above must be able to fail."""
    quote = next(e for e in ENTRIES if e["kind"] == "quote" and e["path"] == "Main.lean")
    assert quote["text"] in ATLAS
    drifted = ATLAS.replace(quote["text"], quote["text"].replace("rhOfAll", "rhOfNone"), 1)
    citations, problems = mq.parse_atlas(drifted)
    assert problems == []
    got = next(c for c in citations if c["path"] == "Main.lean" and "text" in c)
    assert got["text"] != quote["text"]
    _, problems = mq.parse_atlas(ATLAS + "\n```lean\nno citation above\n```\n")
    assert any("exactly one citation" in p for p in problems)


def test_the_atlas_says_what_it_is_before_anything_else():
    first_paragraph = ATLAS.split("\n\n")[1]
    assert "text-level reading" in first_paragraph
    assert "No Lean was" in first_paragraph and "no kernel has checked" in first_paragraph
    assert "pending" in first_paragraph
    for name, directory in mq.ABBREVIATIONS.items():
        assert f"| `{name}` | `{directory}` |" in ATLAS
    for section in ("Scope and grade", "The statements", "The spine", "analytic interface",
                    "Euler product", "functional equation", "timeline items", "statistics",
                    "names that mislead", "By-products", "auditor", "Open questions"):
        assert section in ATLAS, section
    assert "hunts/rh_claim_interface/" in ATLAS and "hunts/alpoge_replay/" in ATLAS


def test_the_timeline_table_has_twenty_rows_and_its_count_adds_up():
    rows = re.findall(r"^\| (\d+) \| .*? \| ([QAN0])(?:, [a-z ]+)? \|", ATLAS, re.M)
    assert [int(n) for n, _ in rows] == list(range(1, 21))
    tally = {s: sum(1 for _, x in rows if x == s) for s in "QAN0"}
    assert tally == {"Q": 9, "A": 6, "N": 2, "0": 3}
    assert "9 located with a quoted statement" in ATLAS
    assert "6 by area only, 2 by name only, 3 not located" in ATLAS


# ------------------------------------------------------------- stats.json


def test_stats_tables_are_internally_consistent():
    tot = STATS["totals"]
    d1, d2 = STATS["dir_depth1"], STATS["dir_depth2"]
    assert len(d1) == 10 and len(d2) == 330
    assert sum(v["files"] for v in d1.values()) == tot["lean_files"] == 175187
    assert sum(v["lines"] for v in d1.values()) == tot["lines"]
    assert sum(v["files"] for v in d2.values()) == tot["lean_files"]
    assert sum(v["lines"] for v in d2.values()) == tot["lines"]
    for top, row in d1.items():
        if top == "(root)":
            continue
        below = [v for k, v in d2.items() if k.split("/")[0] == top]
        assert sum(v["files"] for v in below) == row["files"], top
    dag = STATS["dag"]
    assert sum(dag["depth_histogram_bin25"].values()) == tot["lean_files"]
    assert dag["modules_reachable_from_Main"] == tot["lean_files"]
    assert dag["max_depth"] == dag["depth_of_Main"]
    assert sum(v["import_leaves"] for v in d1.values()) == dag["import_leaves"]
    assert sum(v["import_leaves_mathlib_only"] for v in d1.values()) == dag["import_leaves_mathlib_only"]
    assert dag["internal_import_edges_distinct"] <= dag["import_lines_naming_archive_modules"]
    by_top = STATS["declarations_by_depth1_approx"]
    for kind, total in STATS["declarations_approx"].items():
        assert sum(v.get(kind, 0) for v in by_top.values()) == total, kind


def test_at_least_five_numbers_were_recomputed_and_disagreements_are_explained():
    checks = STATS["spot_checks"]
    assert sum(1 for c in checks if c["match"]) >= 5
    for c in checks:
        assert c["match"] == (c["reader_value"] == c["recount_value"]) or "rows" in str(c["reader_value"])
        if not c["match"]:
            assert c.get("note"), f"unexplained disagreement: {c['name']}"
    disagreements = {c["name"] for c in checks if not c["match"]}
    assert disagreements == {
        "declaration regex count: instance",
        "import edges between archive modules",
        "files with a line over 1000",
    }


def _fmt(n: int) -> str:
    return f"{n:,}"


def test_headline_numbers_in_the_atlas_are_the_numbers_in_the_tables():
    tot, dag = STATS["totals"], STATS["dag"]
    for n in (tot["lean_files"], tot["lines"], tot["bytes"], dag["internal_import_edges_distinct"],
              dag["import_lines_naming_archive_modules"], dag["import_leaves"],
              dag["import_leaves_mathlib_only"], STATS["file_shape"]["max_lines"],
              STATS["file_shape"]["files_with_a_line_over_1000_characters"]):
        assert _fmt(n) in ATLAS, n
    assert f"{dag['max_depth']} steps" in ATLAS
    for top, row in STATS["dir_depth1"].items():
        if top == "(root)":
            continue
        assert f"| `{top}` | {_fmt(row['files'])} |" in ATLAS, top
        assert f"| {_fmt(row['lines'])} |" in ATLAS, top
    hist = dag["depth_histogram_bin25"]
    assert "| modules | " + " | ".join(_fmt(hist[k]) for k in sorted(hist, key=int)) + " |" in ATLAS
    decl = STATS["declarations_approx"]
    order = ("theorem", "lemma", "def", "abbrev", "structure", "instance", "example", "inductive", "class")
    assert "| " + " | ".join(_fmt(decl[k]) for k in order) + " |" in ATLAS
    for root, c in STATS["import_closures"].items():
        assert re.search(rf"\| `{re.escape(root)}`[^|]*\| {_fmt(c['modules'])} \| {_fmt(c['lines'])} \|", ATLAS), root
    strings = STATS["strings"]
    for word in ("Stepanov", "Vandiver", "Guinand", "sixfold", "relative trace"):
        assert strings[word]["files"] == 0, word
    pub = STATS["published_namespace"]
    assert f"{pub['prop_defs']}" in ATLAS and f"{pub['with_one_line_theorem_of_that_type']} of them" in ATLAS


# ---------------------------------------- verify_quotes.py must show red


def _fixture(tmp_path: Path) -> tuple[Path, Path, list[dict]]:
    src = tmp_path / "lean" / "src"
    (src / "Sub").mkdir(parents=True)
    (src / "Main.lean").write_text("import Sub.A\n\ntheorem top : True := trivial\n", encoding="utf-8")
    body = ["import Mathlib", "", "def Claim : Prop :=", "  ∀ n : ℕ, n = n", "", "theorem claim : Claim := fun _ => rfl"]
    (src / "Sub" / "A.lean").write_text("\n".join(body) + "\n", encoding="utf-8")
    entries = [
        {"id": "Q001", "tree": "archive", "path": "Sub/A.lean", "first": 3, "last": 4,
         "sha256": _sha(body[2:4]), "kind": "quote", "text": "\n".join(body[2:4])},
        {"id": "Q002", "tree": "archive", "path": "Main.lean", "first": 3, "last": 3,
         "sha256": _sha(["theorem top : True := trivial"]), "kind": "pointer",
         "head": "theorem top : True := trivial"},
    ]
    quotes = tmp_path / "quotes.json"
    quotes.write_text(json.dumps({"schema": 1, "entries": entries}, ensure_ascii=False), encoding="utf-8")
    return src, quotes, entries


def test_the_verifier_passes_a_matching_tree(tmp_path):
    src, quotes, _ = _fixture(tmp_path)
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 0, done.stdout + done.stderr
    assert "2 entries: 2 match, 0 mismatch, 0 skipped" in done.stdout
    # a parent of the source directory is accepted, and so is the environment variable
    assert _run_verifier(str(tmp_path), "--quotes", str(quotes)).returncode == 0
    assert _run_verifier("--quotes", str(quotes), env={vq.ENV_ARCHIVE: str(src)}).returncode == 0


def test_the_verifier_rejects_a_planted_change_in_the_tree(tmp_path):
    src, quotes, _ = _fixture(tmp_path)
    target = src / "Sub" / "A.lean"
    target.write_text(target.read_text(encoding="utf-8").replace("n = n", "n = m"), encoding="utf-8")
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 1
    assert "Sub/A.lean:3-4: lines differ" in done.stdout
    assert "1 match, 1 mismatch" in done.stdout


def test_the_verifier_rejects_shifted_lines_missing_files_and_short_files(tmp_path):
    src, quotes, _ = _fixture(tmp_path)
    target = src / "Sub" / "A.lean"
    original = target.read_text(encoding="utf-8")
    target.write_text("-- a line inserted above\n" + original, encoding="utf-8")
    assert _run_verifier(str(src), "--quotes", str(quotes)).returncode == 1
    target.write_text("import Mathlib\n", encoding="utf-8")
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 1 and "file has 1 lines" in done.stdout
    target.unlink()
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 1 and "cannot read file" in done.stdout


def test_the_verifier_rejects_a_quote_text_edited_in_the_json(tmp_path):
    src, quotes, entries = _fixture(tmp_path)
    entries[0]["text"] = entries[0]["text"].replace("n = n", "n ≤ n")
    quotes.write_text(json.dumps({"schema": 1, "entries": entries}, ensure_ascii=False), encoding="utf-8")
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 1
    assert "stored text does not hash" in done.stdout


def test_the_verifier_refuses_to_run_without_an_archive(tmp_path):
    _, quotes, _ = _fixture(tmp_path)
    assert _run_verifier("--quotes", str(quotes)).returncode == 2
    empty = tmp_path / "empty"
    empty.mkdir()
    assert _run_verifier(str(empty), "--quotes", str(quotes)).returncode == 2


def test_mathlib_entries_are_skipped_and_counted_without_a_mathlib_tree(tmp_path):
    src, quotes, entries = _fixture(tmp_path)
    entries.append({"id": "Q003", "tree": "mathlib", "path": "Mathlib/X.lean", "first": 1, "last": 1,
                    "sha256": _sha(["def x := 1"]), "kind": "pointer", "head": "def x := 1"})
    quotes.write_text(json.dumps({"schema": 1, "entries": entries}, ensure_ascii=False), encoding="utf-8")
    done = _run_verifier(str(src), "--quotes", str(quotes))
    assert done.returncode == 0 and "2 match, 0 mismatch, 1 skipped" in done.stdout
    lib = tmp_path / "lib"
    (lib / "Mathlib").mkdir(parents=True)
    (lib / "Mathlib" / "X.lean").write_text("def x := 2\n", encoding="utf-8")
    assert _run_verifier(str(src), "--quotes", str(quotes), "--mathlib", str(lib)).returncode == 1


def test_make_quotes_builds_the_entries_the_verifier_accepts(tmp_path):
    src, _, _ = _fixture(tmp_path)
    atlas = "A claim.\n\n`Sub/A.lean:3-4`\n```lean\ndef Claim : Prop :=\n  ∀ n : ℕ, n = n\n```\n\nSee `Main.lean:3`.\n"
    data, problems = mq.build(atlas, {"archive": str(src), "mathlib": None})
    assert problems == []
    assert [e["kind"] for e in data["entries"]] == ["quote", "pointer"]
    assert vq.verify(data["entries"], {"archive": str(src), "mathlib": None})["mismatch"] == 0
    _, problems = mq.build(atlas.replace("n = n", "n = m"), {"archive": str(src), "mathlib": None})
    assert any("differs from the cited lines" in p for p in problems)


# -------------------------------------------------------- lexical rules


def test_no_file_here_uses_the_reserved_word_or_an_em_dash():
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".md", ".json", ".py"}:
            continue
        text = path.read_text(encoding="utf-8")
        assert RESERVED not in text.lower(), path.name
        assert EM_DASH not in text, path.name


def test_the_atlas_never_says_the_archive_proves_anything():
    prose = re.sub(r"```.*?```", "", ATLAS, flags=re.S)
    assert not re.search(r"\barchive (?:proves|proved|shows that|establishes)\b", prose)
    assert "The archive states" in prose or "the archive states" in prose


# --------------------------------------- the real thing, when it is at hand


@pytest.mark.skipif(not os.environ.get(vq.ENV_ARCHIVE), reason=f"{vq.ENV_ARCHIVE} is not set")
def test_every_citation_matches_the_unpacked_archive():
    args = [os.environ[vq.ENV_ARCHIVE]]
    if os.environ.get(vq.ENV_MATHLIB):
        args += ["--mathlib", os.environ[vq.ENV_MATHLIB]]
    done = subprocess.run([sys.executable, "-I", str(HERE / "verify_quotes.py"), *args],
                          capture_output=True, text=True)
    assert done.returncode == 0, done.stdout
    assert "0 mismatch" in done.stdout
    if os.environ.get(vq.ENV_MATHLIB):
        assert f"{len(ENTRIES)} entries: {len(ENTRIES)} match" in done.stdout


@pytest.mark.skipif(
    not (os.environ.get(vq.ENV_ARCHIVE) and os.environ.get("RH_CLAIM_RECOUNT")),
    reason=f"{vq.ENV_ARCHIVE} and RH_CLAIM_RECOUNT are not both set",
)
def test_a_fresh_recount_reproduces_the_tables(tmp_path):
    out = tmp_path / "recount.json"
    src = vq.resolve_src(os.environ[vq.ENV_ARCHIVE])
    subprocess.run([sys.executable, "-I", str(HERE / "recount.py"), src, "--out", str(out)], check=True)
    fresh = json.loads(out.read_text(encoding="utf-8"))
    assert fresh["n_lean_files"] == STATS["totals"]["lean_files"]
    assert fresh["total_lines"] == STATS["totals"]["lines"]
    assert fresh["total_bytes"] == STATS["totals"]["bytes"]
    assert fresh["dir_depth2"] == STATS["dir_depth2"]
    assert fresh["max_dag_depth"] == STATS["dag"]["max_depth"]
    assert fresh["dag_depth_histogram_bin25"] == STATS["dag"]["depth_histogram_bin25"]
    assert fresh["n_internal_import_edges"] == STATS["dag"]["internal_import_edges_distinct"]
    assert fresh["decls_total_approx"] == STATS["declarations_approx"]
    assert fresh["published_namespace"]["prop_defs"] == STATS["published_namespace"]["prop_defs"]
