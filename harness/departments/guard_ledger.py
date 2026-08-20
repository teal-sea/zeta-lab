"""The repository's guard ledger — the guard offensive's opening entries.

Machinery in :mod:`harness.guards`; this file is the subject side, where real
tests and real incidents may be named. Three records open the ledger with
their power demonstrated live in ``tests/test_guard_ledger.py`` (each
demonstration constructs the smallest mutant and watches the guard fire), and
two were recorded honestly as undemonstrated — the visible head of the
offensive's worklist, per the adopted decision in ``ROADMAP.md`` ("The
outside memos, triaged", adopted build 2).

The ledger grows one demonstrated record at a time. The rule for adding one:
``fired`` may only move off ``None`` in the same change that adds the
demonstration, and a demonstration is a runnable artifact, not a sentence.
The artifact need not live in ``tests/``: ``scripts/make_context.py --check``
moved to ``fired=True`` on 2026-08-13 carrying ``hunts/r_414eed/probe.py``,
a standalone mutation run, which is why the conformance test checks cited
paths exist rather than only cited test nodes. One entry
(``tests/test_doors.py``) is still open.
"""

from __future__ import annotations

from harness.guards import GuardRecord

GUARDS: tuple[GuardRecord, ...] = (
    GuardRecord(
        name="tests/test_rigor.py::test_a_numpy_float32_is_its_binary_value_not_its_repr",
        guards_against=(
            "zeta.rigor._exact taking an unrecognised numeric type's printed "
            "decimal as its exact value, silently moving the abscissa and "
            "producing a wrong proven_sign on both backends at once"
        ),
        smallest_mutant=(
            "parse np.float32(21.02203941345215) via Fraction(str(value)) "
            "instead of its binary value"
        ),
        fired=True,
        demonstrated_by=(
            "tests/test_guard_ledger.py::test_the_exact_guard_rejects_the_repr_parse"
        ),
        known_misses=(
            "faults in the layers the two backends share beyond parsing — "
            "contour policy, grid policy, S(T)/N(T) summation (declared in "
            "harness.departments.zeta_department.RIGOR_BACKEND_PATHS)",
        ),
        scope=(
            "pins the parsing layer only; the incident's standing consequence "
            "— a cross-check bounds only what is actually duplicated — is "
            "carried by the independence declaration, not by this guard"
        ),
        incident="docs/25-the-director-run.md (2026-08-11), defect #1",
    ),
    GuardRecord(
        name="tests/test_docs_numbering.py::test_no_two_docs_share_a_number",
        guards_against=(
            "two documents sharing a leading number, making every bare "
            "docs/NN reference ambiguous"
        ),
        smallest_mutant="a docs/ tree containing 05-a.md and 05-b.md",
        fired=True,
        demonstrated_by=(
            "tests/test_guard_ledger.py::test_the_numbering_guard_fires_on_a_duplicate"
        ),
        known_misses=(
            "a document renamed without its number changing when citations use "
            "bare references only, as sibling full-name ref test fires only on "
            "full paths (hunts/r_c62e44 mutants M02, M04, M07)",
            "content drift or complete body replacement under an existing filename "
            "(hunts/r_c62e44 mutants M05, M06): no test in the suite reads docs/*.md content",
            "nested docs under subdirectories (M17) or non-.md files (M16)",
        ),
        scope=(
            "uniqueness of the leading 2-digit number (00..N) in docs/*.md filenames; "
            "enforces nothing about document titles, content, or semantic citation validity"
        ),
        incident="two documents shared number 21 on 2026-08-10",
    ),
    GuardRecord(
        name="tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word",
        guards_against=(
            "a probe file under hunts/ using the reserved word and so "
            "claiming a certainty regime only zeta/rigor.py and lean/ carry"
        ),
        smallest_mutant=(
            "one hunt file whose text contains the reserved word, in any "
            "casing, even inside a disclaimer"
        ),
        fired=True,
        demonstrated_by=(
            "tests/test_guard_ledger.py::test_the_reserved_word_guard_fires_on_a_probe_file"
        ),
        known_misses=(
            "synonyms — 'verified', 'confirmed', 'definitively', 'proves' "
            "are separately banned but by other checks; a hunt overclaiming "
            "in fresh vocabulary passes this guard",
            "file types outside .py/.md/.json (a .txt overclaim passes)",
        ),
        scope="a lexical scan of bytes under hunts/; intent is not consulted",
        incident="",
    ),
    GuardRecord(
        name="tests/test_doors.py",
        guards_against=(
            "a docs/doors/ entry page whose quoted command no longer runs — "
            "a front door that opens onto a wall"
        ),
        smallest_mutant=(
            "a door page quoting a command that exits non-zero (e.g. a "
            "renamed script)"
        ),
        fired=None,
        known_misses=(),
        scope="undetermined until demonstrated",
        incident="",
    ),
    GuardRecord(
        name="scripts/make_context.py --check",
        guards_against=(
            "CONTEXT.md drifting stale after a public function, doc or "
            "script is added or renamed"
        ),
        smallest_mutant=(
            "one added public symbol with CONTEXT.md left unregenerated"
        ),
        fired=True,
        demonstrated_by=(
            "hunts/r_414eed/probe.py (24 mutants against a throwaway copy of "
            "the tree; 17/17 in scope caught, results in "
            "hunts/r_414eed/results.json and RESULTS.md)"
        ),
        known_misses=(
            "public functions added under compiler/ — likewise unscanned "
            "(B02)",
            "documents added under docs/doors/ — doc_index globs docs/*.md, "
            "not docs/**/*.md (B03)",
            "test files whose names do not match test_*.py, e.g. "
            "tests/mutant_helper.py (B04)",
            "a public docstring changed below its first line — only the "
            "first line is indexed (B07, by construction)",
        ),
        scope=(
            "the invariant it actually enforces is 'CONTEXT.md is a "
            "byte-exact function of the scanned tree' (zeta/, ontology/, "
            "harness/, dossier/, docs/*.md, scripts/, tests/test_*.py), "
            "which is broader *and* shallower than 'the public API index is "
            "current': CONTEXT.md records a per-module line count, so any "
            "edit changing a scanned file's length fires the guard even when "
            "no symbol reaches the index. When __all__ is declared, module_api "
            "filters top-level definitions strictly by declared exports, so "
            "length-neutral in-place private helper renames in __all__ modules "
            "pass silently (measured by hunts/r_7ad39f/probe.py, 0/299 unexported "
            "private symbols caught, 0.0%), while renames in non-__all__ modules "
            "(4/4) and edits altering line count are 100% caught. Unscanned "
            "packages like meta/ are completely excluded from the index pipeline "
            "(measured by hunts/r_2946de/probe.py, 0/16 curated mutants and 0/32 "
            "public symbols detected, 0.0%)"
        ),
        incident="",
    ),
    GuardRecord(
        name=(
            "tests/test_zeta23ext_imports.py::"
            "test_no_module_imports_a_proving_service_namespace"
        ),
        guards_against=(
            "a Lean artifact landed into hunts/frontier_math/zeta23ext with "
            "the proving service's own module prefix (RequestProject) left in "
            "its import lines, so the package fails to assemble at the first "
            "module while every proof in it is good"
        ),
        smallest_mutant=(
            "one landed .lean file whose first line is "
            "'import RequestProject.Iv' instead of 'import Zeta23Ext.BandCert.Iv'"
        ),
        fired=True,
        demonstrated_by=(
            "tests/test_zeta23ext_imports.py::"
            "test_the_guard_fires_on_the_smallest_mutant"
        ),
        known_misses=(
            "an import naming an allowed prefix that nonetheless does not "
            "exist (e.g. 'Zeta23Ext.Nope') — the scan reads the root only",
            "whether a module actually builds; only the assembly build shows "
            "that, and this guard exists precisely because that build is too "
            "expensive to run in the fast tier",
        ),
        scope=(
            "the root of every import line under the package resolves to "
            "something the package could provide; nothing about proof content"
        ),
        incident=(
            "twice on 2026-08-12: all eight BandCert/ modules, then the five "
            "EForm/ modules landed after that fix — a repair that recurred, "
            "which is what turned it into a guard"
        ),
    ),
    GuardRecord(
        name=(
            "tests/test_zeta23ext_imports.py::test_no_module_is_orphaned_from_the_root"
        ),
        guards_against=(
            "a module that exists in the package but is reachable from no "
            "import chain out of Zeta23Ext.lean, so `lake build` never "
            "touches it: it rots silently while the package still reports "
            "success — strictly worse than a build error, which is at least "
            "loud"
        ),
        smallest_mutant=(
            "delete one 'import Zeta23Ext.Bridge' line from the root module "
            "while leaving Bridge.lean on disk"
        ),
        fired=True,
        demonstrated_by=(
            "tests/test_zeta23ext_imports.py::"
            "test_the_orphan_guard_fires_on_a_dropped_import"
        ),
        known_misses=(
            "a module reachable from the root but whose theorems nothing "
            "downstream uses — reachability is not relevance",
        ),
        scope=(
            "reachability of every .lean file from the package root; says "
            "nothing about whether the module builds or is used"
        ),
        incident=(
            "twice on 2026-08-12: 'import Zeta23Ext.Bridge' was replaced by "
            "another import in the root module by a one-line edit, twice, "
            "leaving a kernel-checked module unbuilt. Enabling it immediately "
            "found three further orphans (TruncEst.Poisson, .Autocorrelation "
            "and .Axioms — the last being that chain's own axiom audit, which "
            "was therefore never running)"
        ),
    ),
    GuardRecord(
        name=(
            "tests/test_pub1_status.py::"
            "test_docs_27_states_the_grade_the_obligations_file_declares"
        ),
        guards_against=(
            "docs/27's kernel-checked table stating a different grade for the "
            "Pub 1 strong closure than lean/ZetaLean/Pub1/OBLIGATIONS.md "
            "declares — the page a reader consults for what each piece "
            "assumes, disagreeing with the file that owns the answer"
        ),
        smallest_mutant=(
            "flip the bolded grade in the docs/27 item-3 row from "
            "**Unconditional** to **Conditional** while OBLIGATIONS.md still "
            "says 'status: CLOSED'"
        ),
        fired=True,
        demonstrated_by=(
            "tests/test_guard_ledger.py::"
            "test_the_pub1_status_guard_fires_on_a_flipped_grade"
        ),
        known_misses=(
            "whether the declared status is itself true — OBLIGATIONS.md is "
            "taken as the source, and a status wrong at the source is copied "
            "faithfully into docs/27 and passes; only `#print axioms` and the "
            "kernel decide what the proof actually assumes",
            "any other document that quotes the grade — the guard reads "
            "docs/27's item-3 row only, so a third file repeating the stale "
            "reading is not seen (the same shape "
            "tests/test_reading_of_record.py answers by enumerating quoters)",
            "prose inside the row that contradicts the bolded token, since "
            "only the bolded grade is read as the row's claim",
        ),
        scope=(
            "agreement between two files about one bolded word; says nothing "
            "about whether the closure is correct or the Lean proof sound"
        ),
        incident=(
            "2026-08-17: the obligations closed over 08-14/16 and "
            "OBLIGATIONS.md moved to 'status: CLOSED', while the docs/27 row "
            "went on reading **Conditional** and naming four hypotheses that "
            "no longer existed. Third instance of the class HANDOFF.md "
            "already records twice — a status quoted from a superseded row. "
            "This one underclaimed, which is the harmless direction and "
            "exactly why it survived three days unnoticed"
        ),
    ),
)
