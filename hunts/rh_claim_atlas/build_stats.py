"""Assemble stats.json from the outputs of recount.py and ledger_count.py.

Every number of stats.json comes from one of three places, and this script
is the only thing that writes the file:

* the output of `recount.py` (all whole-tree counts),
* the output of `ledger_count.py` (the counts on the ledger file of S4),
* `reader_values.json`, a frozen copy of the readers' figures, which are
  only ever compared against and are kept under the keys `reader_value`
  and `reader_only`.

Usage:

    python -I build_stats.py RECOUNT_JSON LEDGER_JSON [--out FILE] [--check]

Without `--out` the target is stats.json beside this script. `--check`
writes nothing and exits non-zero if the rebuilt table differs from the
committed stats.json in anything but the timing of the recount. Standard
library only; the archive is not read here.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

#: keywords for which the atlas claims zero occurrences
EXPECTED_ZERO = (
    "sorry", "sorry_substring_any_case", "admit", "native_decide", "axiom_decl", "axiom_word",
    "implemented_by", "extern_attr", "unsafe_word", "line_comment_at_line_start",
    "double_dash_anywhere", "block_comment_open",
)


def depth2_hash(rows: dict) -> str:
    table = {k: [v["files"], v["lines"]] for k, v in rows.items()}
    blob = json.dumps(table, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def build(m: dict, ledger: dict, r: dict) -> dict:
    checks: list[dict] = []

    def chk(name, reader_value, recount_value, note=None):
        c = {"name": name, "reader_value": reader_value, "recount_value": recount_value,
             "match": reader_value == recount_value}
        if note:
            c["note"] = note
        checks.append(c)

    chk("number of .lean files", r["lean_files"], m["n_lean_files"])
    chk("total lines", r["total_lines"], m["total_lines"])
    chk("total bytes", r["total_bytes"], m["total_bytes"])
    chk("all 10 depth-1 rows (files, lines)", r["dir_depth1"],
        {k: [v["files"], v["lines"]] for k, v in m["dir_depth1"].items()})
    chk("all 10 depth-1 rows (import leaves, leaves importing Mathlib only, depth range)",
        r["dir_depth1_dag"], m["dir_depth1_dag"])
    chk(f"all {r['dir_depth2_rows']} depth-2 rows (files, lines), as a sha256 of the table",
        r["dir_depth2_sha256"], depth2_hash(m["dir_depth2"]))
    for d, (files, lines) in r["dir_depth3"].items():
        chk(f"depth-3 row {d} (files, lines)", [files, lines],
            [m["directories"][d]["files"], m["directories"][d]["lines"]])
    chk("longest import chain (max DAG depth)", r["max_dag_depth"], m["max_dag_depth"])
    chk("DAG depth histogram, bins of 25", r["dag_depth_histogram_bin25"], m["dag_depth_histogram_bin25"])
    chk("modules that nothing imports", r["modules_fan_in_zero"], m["n_modules_fan_in_zero"])
    chk("modules not reachable from Main", r["modules_not_reachable_from_Main"],
        m["n_lean_files"] - m["n_modules_reachable_from_Main"])
    for kw in ("theorem", "lemma", "def", "abbrev", "structure", "example", "inductive", "class"):
        chk(f"declaration regex count: {kw}", r["declarations_approx"][kw], m["decls_total_approx"].get(kw, 0))
    chk("declaration regex count: instance", r["declarations_approx"]["instance"],
        m["decls_total_approx"].get("instance", 0),
        "first recorded as not reconciled; reconciled in review: the reader's pattern accepts "
        "`scoped instance` and `local instance`, the recount's first pattern does not; see the next row")
    chk("declaration regex count: instance, with scoped and local accepted",
        r["declarations_approx"]["instance"],
        m["decls_total_scoped_and_local_included_approx"].get("instance", 0))
    chk("import edges between archive modules", r["import_edges_as_the_reader_counted_them"],
        m["n_internal_import_edges"],
        "the reader counted import lines naming an archive module (see the next row); the recount "
        "counts distinct importer-imported pairs; the difference is the import lines that repeat an import")
    chk("import lines naming an archive module, duplicates included",
        r["import_edges_as_the_reader_counted_them"], m["import_lines_naming_archive_modules"])
    chk("median lines per file", r["median_lines"], m["file_shape"]["median_lines"])
    chk("largest file, lines", r["max_lines"], m["file_shape"]["max_lines"])
    chk("files with a line over 1000", r["files_with_a_line_over_1000"],
        m["file_shape"]["files_with_a_line_over_1000_characters"],
        "first recorded as not reconciled; reconciled in review: the recount's figure is in "
        "characters and the reader's is in bytes; see the next row")
    chk("files with a line over 1000 bytes", r["files_with_a_line_over_1000"],
        m["file_shape"]["files_with_a_line_over_1000_bytes"])

    d1 = {k: dict(v, **m["dir_depth1_dag"][k]) for k, v in m["dir_depth1"].items()}
    scanned = m["keywords_scanned"]
    return {
        "schema": 2,
        "what": "every count behind ATLAS.md: whole-tree statistics, string counts, and the ledger file",
        "grade": (
            "measured count: text of the unpacked tree only, no Lean run; declaration counts are "
            "regex counts and approximate"
        ),
        "sources": {
            "recount": "hunts/rh_claim_atlas/recount.py, run on the unpacked tree with recount_arguments",
            "ledger": "hunts/rh_claim_atlas/ledger_count.py, run on the unpacked tree",
            "reader": (
                "hunts/rh_claim_atlas/reader_values.json, used only under the keys reader_value, "
                "reader_only and published_namespace_reader_rule"
            ),
            "writer": "hunts/rh_claim_atlas/build_stats.py",
        },
        "recount_arguments": m["arguments"],
        "totals": {"lean_files": m["n_lean_files"], "non_lean_files": m["n_non_lean_files"],
                   "lines": m["total_lines"], "bytes": m["total_bytes"]},
        "dir_depth1": d1,
        "dir_depth2": m["dir_depth2"],
        "directories": m["directories"],
        "dag": {
            "internal_import_edges_distinct": m["n_internal_import_edges"],
            "import_lines_naming_archive_modules": m["import_lines_naming_archive_modules"],
            "unresolved_internal_imports": m["n_unresolved_internal_imports"],
            "modules_on_import_cycles": m["n_modules_in_import_cycles"],
            "max_depth": m["max_dag_depth"],
            "depth_of_Main": m["depth_of_Main"],
            "depth_histogram_bin25": {
                k: m["dag_depth_histogram_bin25"][k] for k in sorted(m["dag_depth_histogram_bin25"], key=int)
            },
            "import_leaves": m["n_import_leaves"],
            "import_leaves_mathlib_only": m["n_import_leaves_mathlib_only"],
            "modules_fan_in_zero": m["n_modules_fan_in_zero"],
            "modules_reachable_from_Main": m["n_modules_reachable_from_Main"],
            "external_import_lines_by_root": m["external_import_lines_by_root"],
        },
        "declarations_approx": m["decls_total_approx"],
        "declarations_scoped_and_local_included_approx": m["decls_total_scoped_and_local_included_approx"],
        "declarations_by_depth1_approx": m["decls_by_depth1_approx"],
        "text_markers": {
            "scanned": scanned,
            "zero_hits": [k for k in scanned if k not in m["keyword_hits"]],
            "hits": m["keyword_hits"],
            "files": m["keyword_files"],
            "first_files_in_tree_order": m["keyword_file_sample"],
            "line_tokens": m["line_tokens"],
            "structures_named_hypothes_literature_published": m["n_structures_named_hypothes_literature_published"],
            "structures_named_input": m["n_structures_named_input"],
            "defs_named_hypothes": m["n_defs_named_hypothes"],
        },
        "file_shape": dict(
            m["file_shape"],
            formalism_subdirectories=m["formalism_subdirectories"],
            formalism_subdirectories_with_statement_files=m["formalism_subdirectories_with_statement_files"],
            formalism_subdirectories_with_statement_files_directly_inside=m[
                "formalism_subdirectories_with_statement_files_directly_inside"
            ],
        ),
        "published_namespace": m["published_namespace"],
        "published_namespace_wide_rule": m["published_namespace_wide_rule"],
        "published_namespace_reader_rule": r["published_namespace_by_the_by_products_reader"],
        "strings_rule": "fixed strings matched without regard to case; files = files containing the string anywhere",
        "strings": m["strings"],
        "whole_words_rule": "case-sensitive whole words on lines that are not import lines; first 16 places listed",
        "whole_words": m["whole_words"],
        "declarations_named": m["declarations_named"],
        "import_closures": m["closures"],
        "ledger": ledger,
        "reader_only": {"longest_chain_directory_sequence": r["longest_chain_directory_sequence"]},
        "spot_checks": checks,
        "recount_seconds": m["seconds"],
    }


def comparable(stats: dict) -> dict:
    return {k: v for k, v in stats.items() if k != "recount_seconds"}


def main(argv: list[str]) -> int:
    args = argv[1:]
    out = os.path.join(HERE, "stats.json")
    check = False
    inputs: list[str] = []
    while args:
        arg = args.pop(0)
        if arg == "--out" and args:
            out = args.pop(0)
        elif arg == "--check":
            check = True
        elif arg.startswith("--"):
            print(f"unknown or incomplete option {arg!r}\n\n{__doc__}")
            return 2
        else:
            inputs.append(arg)
    if len(inputs) != 2:
        print(__doc__)
        return 2
    with open(inputs[0], encoding="utf-8") as fh:
        recount = json.load(fh)
    with open(inputs[1], encoding="utf-8") as fh:
        ledger = json.load(fh)
    with open(os.path.join(HERE, "reader_values.json"), encoding="utf-8") as fh:
        reader = json.load(fh)
    stats = build(recount, ledger, reader)
    missing = [k for k in EXPECTED_ZERO if k not in stats["text_markers"]["zero_hits"]]
    if missing:
        print("expected zero occurrences, found some:", missing)
        return 1
    if check:
        with open(out, encoding="utf-8") as fh:
            committed = json.load(fh)
        new, old = comparable(stats), comparable(committed)
        if new != old:
            differ = sorted(k for k in set(new) | set(old) if new.get(k) != old.get(k))
            print("stats.json differs from the rebuilt table in:", differ)
            return 1
        print("stats.json is what the recount and the ledger count give")
        return 0
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(stats, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    agree = sum(1 for c in stats["spot_checks"] if c["match"])
    print(f"wrote {out}: {len(stats['spot_checks'])} comparisons with the reader, {agree} agree; "
          f"disagree: {[c['name'] for c in stats['spot_checks'] if not c['match']]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
