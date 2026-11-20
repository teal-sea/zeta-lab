"""Checks for the atlas of the Alpoge archive (hunt #160).

Five layers, none of which needs the archive:

1. `quotes.json` and `stats.json` are well formed, and consistent with
   `ATLAS.md`: every `path:line` the atlas cites has an entry, every entry is
   cited, every displayed quote equals its entry, no file is reproduced
   piece by piece, and every count in the prose is the number in the table,
   checked sentence by sentence and row by row (`atlas_number_problems`).
2. `verify_quotes.py` shows red: on a tiny fixture tree made in a temporary
   directory it passes when the tree matches and fails on each planted fault.
3. `recount.py` and `ledger_count.py` count what they say they count, on
   fixture text with known answers.
4. The wording rules hold (`wording_problems`): a sentence that speaks of
   a proof, of the kernel or of the replay must carry a hedge. This is a
   tripwire for a careless sentence. It cannot show that no sentence
   overstates, and a hedged sentence can still be wrong.
5. The lexical rules of `hunts/` hold for this directory.

Layers 1 and 4 are themselves tested with planted faults, among them the
mutants a reviewer got past the first version of this file.

A sixth layer runs only when the archive is at hand: set `RH_CLAIM_ARCHIVE`
to the unpacked source directory (and `RH_CLAIM_MATHLIB` to a Mathlib checkout
at the pinned tag) to replay every citation; set `RH_CLAIM_RECOUNT=1` as well
to recount the whole tree with the arguments recorded in `stats.json`, rerun
the ledger count, rebuild the table and compare all of it (about five
minutes, one core).

Nothing here writes into the repository.
"""
from __future__ import annotations

import copy
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
RESULTS = (HERE / "RESULTS.md").read_text(encoding="utf-8")
MISSION = (HERE / "MISSION.md").read_text(encoding="utf-8")
RUNS = (HERE / "RUNS.md").read_text(encoding="utf-8")
QUOTES = json.loads((HERE / "quotes.json").read_text(encoding="utf-8"))
STATS = json.loads((HERE / "stats.json").read_text(encoding="utf-8"))
READER = json.loads((HERE / "reader_values.json").read_text(encoding="utf-8"))
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
lc = _load("ledger_count")
bs = _load("build_stats")


def _sha(lines: list[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()


def _run(script: str, *args: str, env: dict | None = None) -> subprocess.CompletedProcess:
    clean = {k: v for k, v in os.environ.items() if k not in (vq.ENV_ARCHIVE, vq.ENV_MATHLIB)}
    clean.update(env or {})
    return subprocess.run(
        [sys.executable, "-I", str(HERE / script), *args], capture_output=True, text=True, env=clean,
    )


def _run_verifier(*args: str, env: dict | None = None) -> subprocess.CompletedProcess:
    return _run("verify_quotes.py", *args, env=env)


def _prose(text: str) -> str:
    """The text without its fenced blocks."""
    return re.sub(r"```.*?```", "", text, flags=re.S)


def _norm(text: str) -> str:
    return " ".join(text.split())


def _fmt(n: int) -> str:
    return f"{n:,}"


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
    assert "@@" not in ATLAS.replace("`@@`", ""), "an unfilled placeholder block is left in ATLAS.md"


#: Files of which the displayed quotes show more than half the content lines.
#: Each is a file that holds little besides the one declaration quoted. The
#: list is closed: a new file above one half fails until it is put here and
#: in MISSION.md on purpose. Only `Main.lean`, the five one-line theorems that
#: are the claim itself, is shown whole.
MOSTLY_SHOWN = {
    "Main.lean": (5, 5),
    "Formalism/LocalToGlobal/IndefiniteReal/HeckeNonvanishing/Imports.lean": (4, 5),
    "Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean": (4, 6),
    "Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/lemmaL.lean": (10, 15),
    "Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean": (6, 11),
}


def _coverage_problems(quoted_files: dict) -> list[str]:
    problems = []
    for path, row in quoted_files.items():
        shown, total = row["displayed_content_lines"], row["content_lines"]
        if shown > total:
            problems.append(f"{path}: more lines shown than the file has")
        if 2 * shown > total and MOSTLY_SHOWN.get(path) != (shown, total):
            problems.append(f"{path}: {shown} of {total} content lines are displayed")
        if shown == total and path != "Main.lean":
            problems.append(f"{path}: the whole file is displayed")
    for path in MOSTLY_SHOWN:
        if path not in quoted_files:
            problems.append(f"{path}: listed as mostly shown but not quoted")
    return problems


def test_no_file_is_reproduced_piece_by_piece():
    """Block length alone cannot see two adjacent quotes that add up to a file."""
    files = QUOTES["quoted_files"]
    shown: dict[str, set[int]] = {}
    for e in ENTRIES:
        if e["kind"] == "quote" and e["tree"] == "archive":
            shown.setdefault(e["path"], set()).update(range(e["first"], e["last"] + 1))
    assert set(shown) == set(files)
    assert _coverage_problems(files) == []
    for path in MOSTLY_SHOWN:
        assert path.rsplit("/", 1)[-1] in MISSION, f"{path} is not declared in MISSION.md"
    # the first version showed all of Statements.lean in two adjacent blocks
    assert files["Statements.lean"]["displayed_content_lines"] * 2 <= files["Statements.lean"]["content_lines"]
    planted = copy.deepcopy(files)
    planted["Statements.lean"]["displayed_content_lines"] = planted["Statements.lean"]["content_lines"]
    assert any("Statements.lean" in p for p in _coverage_problems(planted))


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
    rows = re.findall(r"^\| (\d+) \| .*? \| ([QAN0])((?:, [a-z ]+)?) \|", ATLAS, re.M)
    assert [int(n) for n, _, _ in rows] == list(range(1, 21))
    tally = {s: sum(1 for _, x, _ in rows if x == s) for s in "QAN0"}
    assert tally == {"Q": 9, "A": 6, "N": 2, "0": 3}
    qualified = sum(1 for _, x, q in rows if x == "Q" and q)
    assert qualified == 4
    for text in (ATLAS, RESULTS):
        assert "9 located with a quoted statement (four of them in part or in shape)" in _norm(text)
        assert "6 by area only, 2 by name only, 3 not located" in _norm(text)
    # every item graded Q has a displayed statement, not only a pointer
    for n, x, _ in rows:
        if x == "Q" and int(n) not in (5, 19, 20):  # shown in S10, section 9 and section 1
            assert re.search(rf"^Item {n}[ ,(]", ATLAS, re.M), f"item {n} is graded Q without a displayed quote"


# ------------------------------------------------------------- stats.json


def test_stats_tables_are_internally_consistent():
    assert STATS["schema"] == 2
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
    assert dag["max_depth"] == dag["depth_of_Main"] == max(v["depth_max"] for v in d1.values())
    assert sum(v["import_leaves"] for v in d1.values()) == dag["import_leaves"]
    assert sum(v["import_leaves_mathlib_only"] for v in d1.values()) == dag["import_leaves_mathlib_only"]
    assert dag["internal_import_edges_distinct"] <= dag["import_lines_naming_archive_modules"]
    by_top = STATS["declarations_by_depth1_approx"]
    for kind, total in STATS["declarations_approx"].items():
        assert sum(v.get(kind, 0) for v in by_top.values()) == total, kind
    wide = STATS["declarations_scoped_and_local_included_approx"]
    assert {k for k in wide if wide[k] != STATS["declarations_approx"][k]} == {"instance"}
    for d, row in STATS["directories"].items():
        assert row["files"] >= row["files_directly_inside"] >= 0, d
        if "/" not in d:
            assert (row["files"], row["lines"]) == (d1[d]["files"], d1[d]["lines"]), d
        elif d.count("/") == 1:
            assert (row["files"], row["lines"]) == (d2[d]["files"], d2[d]["lines"]), d
        for s, n in row["files_containing_outside_import_lines"].items():
            assert n <= row["files_containing"][s] <= STATS["strings"][s]["files"], (d, s)
    led = STATS["ledger"]
    assert led["theorems"] == led["theorems_taking_O"] == (
        led["blocks_reading_a_field_of_O"] + led["blocks_passing_O_on_without_reading_a_field"]
        + led["blocks_not_mentioning_O"]
    )
    assert led["blocks_reading_a_field_of_O"] <= led["blocks_depending_on_a_field_transitively"]
    assert len(led["names_depending_on_a_field_transitively"]) == led["blocks_depending_on_a_field_transitively"]
    tokens = STATS["text_markers"]["line_tokens"]
    reach = tokens["reach_kexactB_by_name_or_macro"]
    parts = [tokens[k] for k in ("kexactB", "kc%", "kq%", "kd%", "tr_via", "tr_clause")]
    assert max(p["lines"] for p in parts) <= reach["lines"] <= sum(p["lines"] for p in parts)
    assert max(p["files"] for p in parts) <= reach["files"] <= sum(p["files"] for p in parts)


def test_the_zero_counts_were_scanned_and_are_zero():
    markers = STATS["text_markers"]
    for key in bs.EXPECTED_ZERO:
        assert key in markers["scanned"], f"{key} was not scanned, so its absence means nothing"
        assert key in markers["zero_hits"] and key not in markers["hits"], key
    for key, hits in markers["hits"].items():
        assert key in markers["scanned"] and hits > 0 and markers["files"][key] > 0, key
    # the letters "unsafe" occur only inside one option name
    assert markers["hits"]["unsafe_substring_any_case"] == markers["hits"]["allowUnsafeReducibility"]
    for word in ("Stepanov", "Vandiver", "Guinand", "sixfold", "relative trace", "Lichtenbaum",
                 "SignOnly", "sign_only", "Gabber", "pathQ"):
        assert STATS["strings"][word]["files"] == 0, word
    assert STATS["strings"]["Bost"]["files_outside_import_lines"] == 0
    named = STATS["declarations_named"]
    for name in ("riemannZeta", "RiemannHypothesis", "completedRiemannZeta", "vonMangoldt"):
        assert named[name]["count"] == 0, name
    assert named["LFunction"]["count"] == 2 and named["GoodFor"]["count"] == 4
    dirs = STATS["directories"]
    landau = dirs["Development/AutomorphicArithmetic/DedekindLFunctions"]["files_containing"]
    for s in ("completedLFunction_one_sub", "riemannZeta_one_sub", "LFunction_one_sub", "dedekindZeta"):
        assert s not in landau, f"{s} occurs in the directory of the Landau step"
    for s in ("riemannZeta", "vonMangoldt", "WeierstrassCurve"):
        assert s not in dirs["Development/WeilBound"]["files_containing_outside_import_lines"], s
    for s in ("riemannZeta", "vonMangoldt"):
        assert s not in dirs["PositivityTheory"]["files_containing_outside_import_lines"], s
    quillen = STATS["strings"]["Quillen"]["files"]
    stability = "Development/AutomorphicArithmetic/AutomorphicVarieties/LiteratureResults/KTheoryStability"
    assert dirs[stability]["files_containing"]["Quillen"] == quillen
    assert dirs["Development/AbelianVarietyTheory/Proofs"]["files_containing"]["weil_functional"] == (
        STATS["strings"]["weil_functional"]["files"]
    )


def test_names_said_to_occur_once_occur_once():
    words = STATS["whole_words"]
    once = ("BehrendBound", "MinkowskiIILower", "ArtinHasseIntegral", "KummerZp", "LocalExistence",
            "GlobalExistence", "RayClassFieldExistence", "ChebotarevDensity'", "FermatCount", "OCStep",
            "RiemannHypothesisOfLowerBounds", "RHofG", "ForcedSumCM", "everyE₂")
    for name in once:
        assert words[name]["lines_outside_import_lines"] == 1, name
        assert f"`{name}`" in ATLAS, name
    assert words["cpt_copy_thms"]["lines_outside_import_lines"] == 2  # defined once, invoked once
    assert words["plugAll"]["lines_outside_import_lines"] == 2  # defined, and named by everyE₂
    assert words["ZeroFreeAll"]["lines_outside_import_lines"] == 5  # defined, assumed once, concluded 3 times
    assert words["EveryCharacter"]["lines_outside_import_lines"] == 13  # defined, assumed 4 times, concluded 8
    assert words["zetaLandau"]["lines_outside_import_lines"] == 4  # stated, and applied at three places


def test_spot_checks_against_the_reader_are_complete_and_explained():
    checks = STATS["spot_checks"]
    assert len(checks) == 27 and sum(1 for c in checks if c["match"]) == 24
    for c in checks:
        assert c["match"] == (c["reader_value"] == c["recount_value"])
        if not c["match"]:
            assert c.get("note"), f"unexplained disagreement: {c['name']}"
    assert {c["name"] for c in checks if not c["match"]} == {
        "declaration regex count: instance",
        "import edges between archive modules",
        "files with a line over 1000",
    }
    # each disagreement is followed by the row that reconciles it
    for i, c in enumerate(checks):
        if not c["match"]:
            assert checks[i + 1]["match"] and checks[i + 1]["reader_value"] == c["reader_value"], c["name"]
    assert "27 comparisons" in RESULTS and "24 agree" in RESULTS
    # the reader's figures come from the frozen file and from nowhere else
    assert checks[0]["reader_value"] == READER["lean_files"]
    assert STATS["published_namespace_reader_rule"] == READER["published_namespace_by_the_by_products_reader"]
    assert bs.depth2_hash(STATS["dir_depth2"]) == READER["dir_depth2_sha256"]


# ----------------------------- the prose against the tables, row by row


def atlas_claims(stats: dict) -> list[tuple[str, str]]:
    """(label, sentence or table row) pairs that ATLAS.md must contain verbatim.

    Each fragment is built from `stats`, so a number changed in the atlas or
    in the table makes exactly one fragment go missing. Whitespace is
    normalised before comparison.
    """
    n = _fmt
    tot, dag, shape = stats["totals"], stats["dag"], stats["file_shape"]
    led, markers, strings = stats["ledger"], stats["text_markers"], stats["strings"]
    dirs, closures, tokens = stats["directories"], stats["import_closures"], stats["text_markers"]["line_tokens"]
    hits, kfiles = markers["hits"], markers["files"]
    decl = stats["declarations_approx"]
    wide = stats["declarations_scoped_and_local_included_approx"]
    pub, pubw, pubr = (stats["published_namespace"], stats["published_namespace_wide_rule"],
                       stats["published_namespace_reader_rule"])
    key = "with_one_line_theorem_of_that_type"
    aa = "Development/AutomorphicArithmetic/"
    out: list[tuple[str, str]] = []

    def add(label: str, fragment: str) -> None:
        out.append((label, fragment))

    add("files, section 0", f"It unpacks to {n(tot['lean_files'])} `.lean` files")
    add("files, section 1", f"A scan of all {n(tot['lean_files'])} files finds no declaration")
    # S4, the ledger
    add("ledger size", f"This file has {led['lines']} lines, {led['import_lines']} imports and "
                       f"{led['theorems']} theorems")
    add("ledger names", f"{led['theorem_names_with_of_literature']} have `_of_literature` in their name")
    field_lines = ", ".join(str(x) for x in led["lines_reading_a_field_of_O"])
    add("ledger row 1", f"| reads a field of `O` (lines {field_lines}) | {led['blocks_reading_a_field_of_O']} |")
    add("ledger row 2", "| does not read a field, passes `O` on to other theorems of the file | "
                        f"{led['blocks_passing_O_on_without_reading_a_field']} |")
    add("ledger row 3", f"| does not mention `O` | {led['blocks_not_mentioning_O']} |")
    add("ledger row 4", "| reads a field, or names a theorem of the file that does, transitively | "
                        f"{led['blocks_depending_on_a_field_transitively']} |")
    add("ledger sum", f"The first three rows add up to {led['theorems']}")
    add("ledger pass", f"{led['blocks_passing_O_on_without_reading_a_field']} pass it on")
    add("ledger reading", f"the file is a ledger that re-exports {led['theorems']} results")
    add("ledger echo", f"of the {led['theorems']} theorems of the ledger, {led['blocks_not_mentioning_O']} do not "
                       f"mention the hypothesis structure in their text, {led['blocks_reading_a_field_of_O']} read a "
                       f"field of it and {led['blocks_depending_on_a_field_transitively']} reach a field")
    # closures
    lemma_l = closures[aa.replace("/", ".") + "DedekindLFunctions.LandauTheorems.lemmaL"]
    add("lemmaL closure", f"the import closure of `lemmaL` inside the archive is {lemma_l['modules']} modules and "
                          f"{n(lemma_l['lines'])} lines")
    add("lemmaL modules again", f"What the {lemma_l['modules']} modules under `lemmaL` read from Mathlib")
    strip = closures[aa.replace("/", ".") + "CharacterBoxes.ClaimStrip"]
    add("ClaimStrip closure", f"The import closure of `ClaimStrip` is {strip['modules']} modules and "
                              f"{strip['lines']} lines")
    right = closures["Formalism.GammaFactorNonvanishing.RhOfRight"]
    add("RhOfRight size", f"Its file imports only Mathlib and is {right['lines']} lines")
    for root, c in closures.items():
        add(f"closure row {root}", f"| `{root}`")
        add(f"closure numbers {root}", f"| {n(c['modules'])} | {n(c['lines'])} |")
    for name, root in (("B1", "Formalism.SuccessiveMinima.MinkowskiIIUpper"),
                       ("B2", "ReciprocityTheory.Chebotarev.StatementHolds"),
                       ("B9", "Formalism.ZetaNonvanishing.ZetaLandau")):
        add(f"closure in {name}", f"Closure: {closures[root]['modules']} modules, {n(closures[root]['lines'])} lines")
    # section 6
    iw = strings["Iwasawa"]
    add("Iwasawa", f'The string "Iwasawa" occurs in {n(iw["files"])} files but in only '
                   f'{n(iw["files_outside_import_lines"])} outside import lines')
    add("GGP", f'("GGP" occurs in {strings["GGP"]["files"]} files)')
    add("seesaw", f'"seesaw" occurs in {n(strings["seesaw"]["files"])} files, '
                  f'{n(strings["seesaw"]["files_outside_import_lines"])} of them outside import lines')
    add("Bost", f'the {strings["Bost"]["files"]} files that match the letters')
    add("weil_functional", f'in {strings["weil_functional"]["files"]} files under `AVT/Proofs`')
    add("mass formula", "`Formalism/PeriodIntegrals/UnitaryGroupMassFormula` "
                        f"({n(dirs['Formalism/PeriodIntegrals/UnitaryGroupMassFormula']['files'])} files)")
    add("GL5", f"`Formalism/LocalToGlobal/GlobalTheory/GL5` ({dirs['Formalism/LocalToGlobal/GlobalTheory/GL5']['files']} files)")
    weil = dirs["Development/EtaleCohomology/WeilConjectures"]["files"]
    add("WeilConjectures", f"`Development/EtaleCohomology/WeilConjectures` ({weil} files)")
    add("WeilConjectures again", f"A {weil}-file plan toward Deligne's theorem")
    stability = dirs[aa + "AutomorphicVarieties/LiteratureResults/KTheoryStability"]["files"]
    add("Quillen", f'"Quillen" occurs in {strings["Quillen"]["files"]} files, all in a {stability}-file directory')
    add("SlopeIneq", f'{strings["SlopeIneq"]["files"]} files containing `SlopeIneq` in any letter case and '
                     f'{strings["slope_inequality"]["files"]} containing `slope_inequality`')
    fe = [strings[k] for k in ("completedLFunction_one_sub", "riemannZeta_one_sub", "LFunction_one_sub",
                               "rootNumber")]
    lines_, files_ = "lines_outside_import_lines", "files_outside_import_lines"
    add("functional equation, completed", f"stands on {fe[0][lines_]} lines in {fe[0][files_]} files and "
                                          f"`riemannZeta_one_sub` on {fe[1][lines_]} lines in {fe[1][files_]} files")
    add("functional equation, any", f"on {fe[2][lines_]} lines in {fe[2][files_]} files; and `rootNumber` on "
                                    f"{fe[3][lines_]} lines in {fe[3][files_]} files")
    add("tridiagonal", f'"tridiagonal" occurs in {strings["tridiagonal"]["files"]} files')
    add("zeroMode", f'"zeroMode" occurs in {strings["zeroMode"]["files"]} files')
    # section 7, first table
    add("row files", f"| `.lean` files | {n(tot['lean_files'])} |")
    add("row other files", f"| other files under the source directory | {tot['non_lean_files']} |")
    add("row lines", f"| lines | {n(tot['lines'])} |")
    add("row bytes", f"| bytes | {n(tot['bytes'])} |")
    add("row closure of Main", "| modules in the import closure of `Main` | "
                               f"{n(dag['modules_reachable_from_Main'])} (all) |")
    add("row edges", "| import edges between archive modules (distinct pairs) | "
                     f"{n(dag['internal_import_edges_distinct'])} |")
    add("row unresolved", f"| unresolved imports of archive modules | {dag['unresolved_internal_imports']} |")
    add("row cycles", f"| modules on an import cycle | {dag['modules_on_import_cycles']} |")
    add("row chain", f"| longest import chain | {dag['max_depth']} steps, ending at `Main` |")
    add("row leaves", f"| import leaves (no import of an archive module) | {n(dag['import_leaves'])}, of which "
                      f"{n(dag['import_leaves_mathlib_only'])} import Mathlib only |")
    add("row fan-in", f"| modules that nothing imports | {dag['modules_fan_in_zero']} (`Main`) |")
    add("row Mathlib imports", "| import lines naming Mathlib | "
                               f"{n(dag['external_import_lines_by_root']['Mathlib'])} |")
    add("row comments", "| occurrences of `--` anywhere, or of `/-` | 0 |")
    for top, row in stats["dir_depth1"].items():
        name = "(root: `Main`, `Statements`)" if top == "(root)" else f"`{top}`"
        add(f"depth-1 row {top}",
            f"| {name} | {n(row['files'])} | {100 * row['files'] / tot['lean_files']:.1f}% | {n(row['lines'])} | "
            f"{100 * row['lines'] / tot['lines']:.1f}% | {n(row['import_leaves'])} | "
            f"{row['depth_min']}..{row['depth_max']} |")
    largest = sorted(stats["dir_depth2"].items(), key=lambda kv: -kv[1]["files"])[:8]
    add("depth-2 rows", " ".join(f"| `{k}` | {n(v['files'])} | {n(v['lines'])} |" for k, v in largest))
    proofs = dirs["Development/AbelianVarietyTheory/Proofs"]
    add("depth-3 row", f"holds {n(proofs['files'])} files and {n(proofs['lines'])} lines, "
                       f"{round(100 * proofs['files'] / tot['lean_files'])}% of all files, in "
                       f"{proofs['subdirectories']} sub-directories")
    hist = dag["depth_histogram_bin25"]
    add("histogram", "| modules | " + " | ".join(n(hist[k]) for k in sorted(hist, key=int)) + " |")
    order = ("theorem", "lemma", "def", "abbrev", "structure", "instance", "example", "inductive", "class")
    add("declarations", "| " + " | ".join(n(decl[k]) for k in order) + " |")
    add("instance, wide", f"With those two modifiers accepted the count is {n(wide['instance'])}")
    add("instance, difference", f"undercounts instance declarations by {wide['instance'] - decl['instance']}")
    add("instance, first figure", f"recorded {n(decl['instance'])} against {n(wide['instance'])}")
    lines_naming = dag["import_lines_naming_archive_modules"]
    add("edges, both", f"The reader's import edge count is {n(lines_naming)}; the recount of distinct "
                       f"importer-imported pairs is {n(dag['internal_import_edges_distinct'])}")
    add("edges, repeats", f"{lines_naming - dag['internal_import_edges_distinct']} of which repeat")
    add("file shape", f"the median file has {shape['median_lines']} lines, the mean is {shape['mean_lines']}, and "
                      f"the largest has {n(shape['max_lines'])}")
    add("long lines", f"{n(shape['files_with_a_line_over_1000_characters'])} files have a line longer than 1,000 "
                      f"characters, and {n(shape['files_with_a_line_over_1000_bytes'])} have a line longer than "
                      "1,000 bytes")
    add("longest line", f"longest line is {shape['median_longest_line_characters']} characters")
    add("Formalism", f"`Formalism` has {shape['formalism_subdirectories']} sub-directories. In "
                     f"{shape['formalism_subdirectories_with_statement_files']} of them")
    add("Formalism, direct", f"and in {shape['formalism_subdirectories_with_statement_files_directly_inside']} it "
                             "lies directly inside")
    # section 8
    wb = "Development/WeilBound"
    add("WeilBound", f"| `{wb}` ({n(dirs[wb]['files'])} files) |")
    add("WeilBound parts", f"`CoreStatements` ({n(dirs[wb + '/CoreStatements']['files'])} files), "
                           f"`RepresentationTheoryGL` ({n(dirs[wb + '/RepresentationTheoryGL']['files'])}), "
                           f"`ThetaLifts` ({dirs[wb + '/ThetaLifts']['files']}) and "
                           f"{_word(dirs[wb]['subdirectories'] - 3)} small ones")
    add("PositivityTheory", f"| `PositivityTheory` ({dirs['PositivityTheory']['files']} files) |")
    inputs = dirs["PositivityTheory/AutomorphicForms/PublishedInputs"]
    add("PublishedInputs", f"({inputs['files']} of the files)")
    add("PublishedInputs parts", f"`CuspidalContinuity` and {_word(inputs['subdirectories'] - 4)} more")
    theorems = dirs["PositivityTheory/PublishedTheorems"]
    add("PublishedTheorems", f"{theorems['files']} files, {theorems['lines']} lines: two one-line import stubs")
    iwd = dirs["Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition"]
    add("IwasawaDecomposition", f"A mixed bag of {n(iwd['files'])} files, of which "
                                f"{iwd['files_containing_outside_import_lines']['Iwasawa']} contain the string")
    add("BehrendSets", f"{_word(dirs['Formalism/BehrendSets']['files']).capitalize()} files of statements")
    add("ArtinHasse", f"| {_word(dirs['Formalism/ArtinHasse']['files']).capitalize()} files. The integrality")
    add("ProductFormula", f"| {_word(dirs['Formalism/ProductFormula']['files']).capitalize()} file, "
                          "`StatementOCCM.lean`")
    add("GammaFactorNonvanishing", f"| The {_word(dirs['Formalism/GammaFactorNonvanishing']['files'])} files of "
                                   "section 5")
    # section 9
    add("published, reader", f"| a reader's (not re-run) | {pubr['prop_defs']} | {pubr[key]} |")
    add("published, narrow", f"| {pub['prop_defs']} | {pub[key]} |")
    add("published, wide", f"| {pubw['prop_defs']} | {pubw[key]} |")
    add("published, subset", f"The {pub['prop_defs']} names are a subset of the {pubw['prop_defs']}")
    add("published, range", f"{pubr['prop_defs']} to {pubw['prop_defs']} Props, {pubr[key]} to {pubw[key]} of them")
    add("published, rest", f"The remaining {pubr['prop_defs'] - pubr[key]} to {pubw['prop_defs'] - pubw[key]}")
    # section 10
    for tok in ("kexactB", "kc%", "kq%", "kd%", "tr_via", "tr_clause"):
        add(f"token {tok}", f"| `{tok}` | {tokens[tok]['lines']} | {tokens[tok]['files']} |")
    reach = tokens["reach_kexactB_by_name_or_macro"]
    add("token reach", f"| any of the six | {reach['lines']} | {reach['files']} |")
    add("token, first figure", f'"{tokens["kexactB"]["lines"]} lines in {tokens["kexactB"]["files"]} files, '
                               "counting a macro `kc%`\"")
    add("kcopy", f"it stands on {tokens['kcopy']['lines']} lines in {tokens['kcopy']['files']} files")
    add("run_tac", f"on {tokens['run_tac']['lines']} lines in {tokens['run_tac']['files']} files")
    add("run_tac, unread", f"the other {tokens['run_tac']['files'] - 2} files were not opened")
    add("meta lines", f"{hits['elab_macro_syntax_line_start']} lines in "
                      f"{kfiles['elab_macro_syntax_line_start']} files begin with `elab`, `macro` or `syntax`")
    add("print axioms", f"`#print axioms` occurs {hits['print_axioms']} times and `#check` "
                        f"{_times(hits['hash_check'])}, in {_word(kfiles['print_axioms'])} files")
    add("unsafe reducibility", f"occurs {hits['allowUnsafeReducibility']} times in "
                               f"{kfiles['allowUnsafeReducibility']} files")
    add("partial def", f"`partial def` occurs {_times(hits['partial_def'])}")
    add("run_cmd", f"{hits['run_cmd']} `run_cmd` lines")
    add("set_option", f"{n(hits['set_option'])} `set_option` occurrences and {hits['open_private']} "
                      "`open private` lines")
    add("addDecl", f"It is the {_word(kfiles['addDecl'])} file in the tree where `addDecl` occurs")
    add("hypothesis structures", f"The tree has {markers['structures_named_hypothes_literature_published']} "
                                 "`structure` declarations")
    add("input structures", f'{markers["structures_named_input"]} structures have "Input" in their name and '
                            f'{markers["defs_named_hypothes"]} `def`s have "Hypothes"')
    add("LocTied", f'"Nonempty (LocTied" occurs in {strings["Nonempty (LocTied"]["files"]} files')
    msb = dirs[aa + "MeanSquareBounds"]
    add("MeanSquareBounds", f"`{aa}MeanSquareBounds` ({msb['files']} files, {n(msb['lines'])} lines)")
    add("decide +kernel", f"{kfiles['decide_plus_kernel']} files contain `decide +kernel` "
                          f"({hits['decide_plus_kernel']} occurrences)")
    add("meta lines, question", f"Which of the {hits['elab_macro_syntax_line_start']} line-start `elab`, `macro` "
                                f"and `syntax` declarations, and of the {tokens['run_tac']['files']} files with "
                                "`run_tac`")
    return out


def results_claims(stats: dict) -> list[tuple[str, str]]:
    n = _fmt
    tot, dag, led = stats["totals"], stats["dag"], stats["ledger"]
    tokens, pub, pubw = (stats["text_markers"]["line_tokens"], stats["published_namespace_reader_rule"],
                         stats["published_namespace_wide_rule"])
    lemma_l = stats["import_closures"]["Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL"]
    reach = tokens["reach_kexactB_by_name_or_macro"]
    return [
        ("tree", f"The tree has {n(tot['lean_files'])} files, {n(tot['lines'])} lines, "
                 f"{n(dag['internal_import_edges_distinct'])} distinct import edges, a longest import chain of "
                 f"{dag['max_depth']}, {n(dag['import_leaves'])} import leaves"),
        ("lemmaL", f"is {lemma_l['modules']} modules and {n(lemma_l['lines'])} lines"),
        ("ledger", f"of its {led['theorems']} theorems {led['blocks_not_mentioning_O']} do not mention the "
                   f"hypothesis, {led['blocks_passing_O_on_without_reading_a_field']} pass it on, "
                   f"{led['blocks_reading_a_field_of_O']} read a field and "
                   f"{led['blocks_depending_on_a_field_transitively']} reach a field"),
        ("reach", f"{reach['lines']} lines in {reach['files']} files"),
        ("token", f"{tokens['kexactB']['lines']} lines in {tokens['kexactB']['files']} files"),
        ("published", f"{pub['prop_defs']} to {pubw['prop_defs']}"),
    ]


def _word(k: int) -> str:
    return {1: "one", 2: "two", 3: "three", 4: "four", 7: "seven", 14: "fourteen"}.get(k, str(k))


def _times(k: int) -> str:
    return {1: "once", 2: "twice"}.get(k, f"{k} times")


def number_problems(text: str, claims: list[tuple[str, str]]) -> list[str]:
    body = _norm(text)
    return [f"{label}: expected to read {fragment!r}" for label, fragment in claims if _norm(fragment) not in body]


def test_every_count_in_the_atlas_is_the_number_in_the_table():
    assert len(atlas_claims(STATS)) > 120
    assert number_problems(ATLAS, atlas_claims(STATS)) == []
    assert number_problems(RESULTS, results_claims(STATS)) == []


def _swap(text: str, old: str, new: str) -> str:
    assert text.count(old) >= 1, old
    return text.replace(old, new, 1)


def test_a_changed_number_in_the_atlas_or_in_the_table_is_seen():
    """The reviewer's mutants, which the first version of this file let through."""
    claims = atlas_claims(STATS)
    mutants = {
        "edge count in the table": _swap(
            ATLAS, "| import edges between archive modules (distinct pairs) | 753,261 |",
            "| import edges between archive modules (distinct pairs) | 753,262 |"),
        "a depth-2 row": _swap(ATLAS, "| 99,187 | 8,142,960 |", "| 99,187 | 8,142,961 |"),
        "a string count": _swap(ATLAS, "occurs in 14,698 files", "occurs in 24,698 files"),
        "the ledger size": _swap(ATLAS, "This file has 814 lines", "This file has 815 lines"),
        "the ledger table": _swap(ATLAS, "| does not mention `O` | 152 |", "| does not mention `O` | 191 |"),
        "the macro reach": _swap(ATLAS, "| any of the six | 469 | 72 |", "| any of the six | 234 | 50 |"),
        "a closure": _swap(ATLAS, "| 28 | 2,396 |", "| 28 | 2,397 |"),
    }
    for name, text in mutants.items():
        assert number_problems(text, claims) != [], f"not seen: {name}"
    # and the other way round: the table changes, the prose does not
    for path, value in (
        (("strings", "Iwasawa", "files"), 14699),
        (("ledger", "lines"), 815),
        (("ledger", "blocks_not_mentioning_O"), 191),
        (("dag", "internal_import_edges_distinct"), 753262),
        (("dir_depth2", "Development/AbelianVarietyTheory", "lines"), 8142961),
        (("text_markers", "line_tokens", "reach_kexactB_by_name_or_macro", "files"), 50),
        (("file_shape", "files_with_a_line_over_1000_bytes"), 11595),
        (("published_namespace_wide_rule", "prop_defs"), 468),
    ):
        changed = copy.deepcopy(STATS)
        node = changed
        for step in path[:-1]:
            node = node[step]
        assert node[path[-1]] != value
        node[path[-1]] = value
        assert number_problems(ATLAS, atlas_claims(changed)) != [], f"not seen: {path}"
    changed = copy.deepcopy(STATS)
    changed["totals"]["lines"] += 1
    assert number_problems(RESULTS, results_claims(changed)) != []


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
    roots = {"archive": str(src), "mathlib": None}
    data, problems = mq.build(atlas, roots)
    assert problems == []
    assert [e["kind"] for e in data["entries"]] == ["quote", "pointer"]
    assert vq.verify(data["entries"], roots)["mismatch"] == 0
    # Sub/A.lean has three content lines, two of them displayed
    assert data["quoted_files"] == {"Sub/A.lean": {"content_lines": 3, "displayed_content_lines": 2}}
    _, problems = mq.build(atlas.replace("n = n", "n = m"), roots)
    assert any("differs from the cited lines" in p for p in problems)
    # a placeholder block is filled from the cited lines, and only with a citation above it
    blank = "A claim.\n\n`Sub/A.lean:3-4`\n```lean\n@@\n```\n\nSee `Main.lean:3`.\n"
    filled, problems = mq.fill(blank, roots)
    assert problems == [] and filled == atlas
    _, problems = mq.fill("No citation here.\n\n```lean\n@@\n```\n", roots)
    assert any("exactly one citation" in p for p in problems)


# ------------------------------- the counting tools, on text with known answers


def _tree(tmp_path: Path) -> Path:
    src = tmp_path / "src"
    (src / "A" / "Deep").mkdir(parents=True)
    (src / "B").mkdir()
    (src / "Main.lean").write_text("import A.One\nimport B.Two\n\ntheorem top : Foo := foo\n", encoding="utf-8")
    (src / "A" / "One.lean").write_text(
        "import Mathlib\nimport A.Deep.Leaf\n\n"
        "def Foo : Prop := True\n"
        "scoped instance : Inhabited Nat := ⟨0⟩\n"
        "local instance : Inhabited Int := ⟨0⟩\n"
        "instance : Inhabited Bool := ⟨true⟩\n"
        "theorem foo : Foo := by kexactB trivial\n"
        "theorem FooBar : Foo := (kc% trivial)\n",
        encoding="utf-8")
    (src / "A" / "Deep" / "Leaf.lean").write_text(
        "import Mathlib\n\nlocal macro:max \"kc% \" e:term:max : term => `((by kexactB $e))\n"
        "def wide : String := \"" + "é" * 600 + "\"\n",
        encoding="utf-8")
    (src / "B" / "Two.lean").write_text(
        "import A.One\nimport A.One\n\nnamespace Zed\ndef GoodFor : Prop := Foo\nend Zed\n"
        "theorem uses : Foo := by\n  run_tac do\n    pure ()\n  exact foo\n",
        encoding="utf-8")
    return src


def test_recount_counts_what_it_says_on_a_tree_with_known_answers(tmp_path):
    src = _tree(tmp_path)
    out = tmp_path / "recount.json"
    done = _run("recount.py", str(src), "--out", str(out), "--strings", "kexactb", "absent", "--dirs", "A",
                "A/Deep", "--words", "Foo", "FooBar", "--decl-names", "GoodFor", "Foo", "--closure", "B.Two")
    assert done.returncode == 0, done.stdout + done.stderr
    r = json.loads(out.read_text(encoding="utf-8"))
    assert (r["n_lean_files"], r["total_lines"]) == (4, 27)
    # two import lines in B.Two name A.One: two lines, one edge
    assert r["import_lines_naming_archive_modules"] == 5 and r["n_internal_import_edges"] == 4
    assert r["max_dag_depth"] == r["depth_of_Main"] == 3 and r["n_import_leaves"] == 1
    assert r["n_modules_reachable_from_Main"] == 4 and r["n_modules_fan_in_zero"] == 1
    assert r["dir_depth1_dag"]["A"] == {"import_leaves": 1, "import_leaves_mathlib_only": 1,
                                        "depth_min": 0, "depth_max": 1}
    # `scoped` and `local` instances are seen only by the wider rule
    assert r["decls_total_approx"]["instance"] == 1
    assert r["decls_total_scoped_and_local_included_approx"]["instance"] == 3
    assert r["decls_total_approx"]["theorem"] == r["decls_total_scoped_and_local_included_approx"]["theorem"] == 4
    # the tactic by name on two lines, through the macro on one more: three lines in two files
    tokens = r["line_tokens"]
    assert (tokens["kexactB"]["lines"], tokens["kexactB"]["files"]) == (2, 2)
    assert (tokens["kc%"]["lines"], tokens["kc%"]["files"]) == (2, 2)
    reach = tokens["reach_kexactB_by_name_or_macro"]
    assert (reach["lines"], reach["files"]) == (3, 2)
    assert (tokens["run_tac"]["lines"], tokens["run_tac"]["files"]) == (1, 1)
    # 600 two-byte letters: over 1000 bytes, under 1000 characters
    assert r["file_shape"]["files_with_a_line_over_1000_bytes"] == 1
    assert r["file_shape"]["files_with_a_line_over_1000_characters"] == 0
    assert r["strings"]["kexactb"] == {"files": 2, "files_outside_import_lines": 2, "lines_outside_import_lines": 2}
    assert r["strings"]["absent"]["files"] == 0
    assert r["directories"]["A"]["files"] == 2 and r["directories"]["A"]["subdirectories"] == 1
    assert r["directories"]["A"]["files_directly_inside"] == 1
    assert r["directories"]["A/Deep"]["files_containing"] == {"kexactb": 1}
    # whole words: `Foo` is not found inside `FooBar`
    assert r["whole_words"]["FooBar"]["lines_outside_import_lines"] == 1
    assert r["whole_words"]["Foo"]["lines_outside_import_lines"] == 6
    assert r["declarations_named"]["GoodFor"] == {"count": 1, "at": ["B/Two.lean:5"]}
    assert r["declarations_named"]["Foo"] == {"count": 1, "at": ["A/One.lean:4"]}
    assert r["closures"]["B.Two"]["modules"] == 3
    # every keyword that is reported absent was looked for
    assert "sorry" in r["keywords_scanned"] and "sorry" not in r["keyword_hits"]
    assert r["keyword_hits"]["run_tac"] == 1


LEDGER_FIXTURE = """import Mathlib
structure Open : Prop where
  first : A
  second : B
theorem reads (O : Open) : A :=
  O.first
theorem passes (O : Open) : A :=
  reads O
theorem ignores (O : Open) : C :=
  somewhere_else
theorem through (O : Open) : D :=
  combine (passes O) ignores_of_literature
theorem ignores_of_literature (O : Open) : C :=
  (ignores)
"""


def test_the_ledger_count_tells_reading_passing_and_ignoring_apart():
    got = lc.count(LEDGER_FIXTURE)
    assert got["lines"] == 14 and got["import_lines"] == 1
    assert got["theorems"] == got["theorems_taking_O"] == 5
    assert got["lines_reading_a_field_of_O"] == [6]
    assert got["blocks_reading_a_field_of_O"] == 1
    assert got["blocks_passing_O_on_without_reading_a_field"] == 2
    assert got["blocks_not_mentioning_O"] == 2
    # `through` reaches the field by way of `passes`; `ignores_of_literature` does not
    assert got["names_depending_on_a_field_transitively"] == ["passes", "reads", "through"]
    assert got["theorem_names_with_of_literature"] == 1
    # the first version of the atlas counted every theorem that reads no field as ignoring `O`
    assert got["blocks_not_mentioning_O"] != got["theorems"] - got["blocks_reading_a_field_of_O"]


def test_build_stats_refuses_a_table_whose_zero_counts_are_not_zero(tmp_path):
    recount = tmp_path / "recount.json"
    ledger = tmp_path / "ledger.json"
    done = _run("recount.py", str(_tree(tmp_path)), "--out", str(recount))
    assert done.returncode == 0, done.stdout + done.stderr
    r = json.loads(recount.read_text(encoding="utf-8"))
    r["directories"] = {"Development/AbelianVarietyTheory/Proofs": {"files": 0, "lines": 0}}
    r["keyword_hits"]["sorry"] = 1
    recount.write_text(json.dumps(r), encoding="utf-8")
    ledger.write_text(json.dumps(lc.count(LEDGER_FIXTURE)), encoding="utf-8")
    done = _run("build_stats.py", str(recount), str(ledger), "--out", str(tmp_path / "stats.json"))
    assert done.returncode == 1 and "sorry" in done.stdout
    assert not (tmp_path / "stats.json").exists()


# ------------------------------------------------------------ wording rules


PROOF_VERBS = re.compile(
    r"\b(proves?|proved|proven|proof of|establish(?:es|ed)?|demonstrat(?:es|ed)|shows? that|showed that)\b", re.I)
VERDICT_SUBJECTS = re.compile(
    r"\b(kernel|replay|replays|replayed|compiles?|compiled|type-?checks?|type-?checked|builds? clean|axiom audit)\b",
    re.I)
#: a sentence about a proof, the kernel or the replay must carry one of these
HEDGES = re.compile(
    r"(\bno\b|\bnot\b|\bnever\b|\bnothing\b|\bneither\b|\bnor\b|\bwhether\b|\bpending\b|\bif\b|\bwould\b"
    r"|\bshould\b|\bwill\b|\bcannot\b|\bclaim(?:s|ed|ing)?\b|\bquestion\b|\bowns?\b|\bowned\b|\bfor the replay\b"
    r"|\bunless\b|\bbefore\b|\bto watch\b|\buntil\b|\bonly\b|\bneeds?\b|\bseparate\b|\?)", re.I)
#: phrases that name a tool or a rung and are not a verdict on the archive
NOT_A_VERDICT = re.compile(
    r"(quote replay|replay path|replays? (?:all|every|any|in|against)|replayed by `verify_quotes|replayable"
    r"|to replay|how to replay|## replay|can be replayed|kernel-checked arm|\*kernel-checked\*)", re.I)


def wording_problems(text: str) -> list[str]:
    """Sentences about a proof, the kernel or the replay that carry no hedge.

    A tripwire, not a judge: it catches the plain forms planted below and
    lets through any sentence that contains a hedge word, right or wrong.
    """
    problems = []
    body = _prose(text)
    body = re.sub(r"`[^`\n]*`", "`code`", body)  # identifiers and commands are not prose
    for raw in re.split(r"(?<=[.?!])\s+|\n\s*\n|\n(?=\||[-*] |\d+\. |#)", body):
        sentence = _norm(raw)
        if not sentence:
            continue
        cleaned = NOT_A_VERDICT.sub("", sentence)
        if (PROOF_VERBS.search(cleaned) or VERDICT_SUBJECTS.search(cleaned)) and not HEDGES.search(cleaned):
            problems.append(sentence)
    return problems


def test_no_document_says_that_anything_is_proved_or_states_a_verdict():
    for name, text in (("ATLAS.md", ATLAS), ("RESULTS.md", RESULTS), ("MISSION.md", MISSION), ("RUNS.md", RUNS)):
        assert wording_problems(text) == [], name
        assert not re.search(r"\barchive (?:proves|proved|shows that|establishes)\b", _prose(text)), name
    prose = _prose(ATLAS)
    assert "The archive states" in prose or "the archive states" in prose


def test_the_wording_check_sees_planted_sentences():
    """Two of these are the reviewer's mutants, which the first regex let through."""
    planted = (
        "The archive's last file proves five theorems.",
        "The kernel accepts all five theorems of `Main.lean`.",
        "The replay finished and the archive compiles.",
        "This is a proof of the Riemann hypothesis.",
        "The chain of section 2 establishes the half-plane statement.",
        "The five theorems typecheck at the pinned toolchain.",
        "| 21 | the build | Q | The archive compiled in nine hours. |",
    )
    for sentence in planted:
        seen = wording_problems(ATLAS + "\n\n" + sentence + "\n")
        assert len(seen) == 1 and seen[0] in _norm(re.sub(r"`[^`\n]*`", "`code`", sentence)), sentence
    for sentence in (
        "No kernel has checked the archive.",
        "Whether the archive compiles is the replay's question.",
        "It never means the statement is proved.",
        "The replay is pending.",
    ):
        assert wording_problems(sentence) == [], sentence


# -------------------------------------------------------- lexical rules


def test_no_file_here_uses_the_reserved_word_or_an_em_dash():
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".md", ".json", ".py"}:
            continue
        text = path.read_text(encoding="utf-8")
        assert RESERVED not in text.lower(), path.name
        assert EM_DASH not in text, path.name


def test_no_document_names_a_path_on_the_machine_that_wrote_it():
    for path in sorted(HERE.iterdir()):
        if path.suffix not in {".md", ".json"}:
            continue
        text = path.read_text(encoding="utf-8")
        for root in ("/home/", "/tmp/", "/root/", "/Users/"):
            assert root not in text, f"{path.name} contains {root}"


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
        # quotes.json is what make_quotes.py builds from the atlas and the two trees today
        done = subprocess.run([sys.executable, "-I", str(HERE / "make_quotes.py"), *args, "--check"],
                              capture_output=True, text=True)
        assert done.returncode == 0 and "quotes.json is current" in done.stdout, done.stdout


@pytest.mark.skipif(not os.environ.get(vq.ENV_ARCHIVE), reason=f"{vq.ENV_ARCHIVE} is not set")
def test_the_ledger_count_reproduces_its_table(tmp_path):
    out = tmp_path / "ledger.json"
    src = vq.resolve_src(os.environ[vq.ENV_ARCHIVE])
    subprocess.run([sys.executable, "-I", str(HERE / "ledger_count.py"), src, "--out", str(out)], check=True)
    assert json.loads(out.read_text(encoding="utf-8")) == STATS["ledger"]


@pytest.mark.skipif(
    not (os.environ.get(vq.ENV_ARCHIVE) and os.environ.get("RH_CLAIM_RECOUNT")),
    reason=f"{vq.ENV_ARCHIVE} and RH_CLAIM_RECOUNT are not both set",
)
def test_a_fresh_recount_rebuilds_the_whole_table(tmp_path):
    """Every field of stats.json, not a sample: strings, closures, zero counts, directories."""
    recount, ledger = tmp_path / "recount.json", tmp_path / "ledger.json"
    src = vq.resolve_src(os.environ[vq.ENV_ARCHIVE])
    args: list[str] = []
    for flag, values in STATS["recount_arguments"].items():
        args += ["--" + flag, *values]
    subprocess.run([sys.executable, "-I", str(HERE / "recount.py"), src, "--out", str(recount), *args], check=True)
    subprocess.run([sys.executable, "-I", str(HERE / "ledger_count.py"), src, "--out", str(ledger)], check=True)
    fresh = bs.build(json.loads(recount.read_text(encoding="utf-8")),
                     json.loads(ledger.read_text(encoding="utf-8")), READER)
    differ = sorted(k for k in set(fresh) | set(STATS) if k != "recount_seconds" and fresh.get(k) != STATS.get(k))
    assert differ == [], f"stats.json is not what the archive gives, in: {differ}"
    done = subprocess.run([sys.executable, "-I", str(HERE / "build_stats.py"), str(recount), str(ledger), "--check"],
                          capture_output=True, text=True)
    assert done.returncode == 0, done.stdout
