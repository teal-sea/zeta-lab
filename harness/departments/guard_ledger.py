"""The repository's guard ledger — the guard offensive's opening entries.

Machinery in :mod:`harness.guards`; this file is the subject side, where real
tests and real incidents may be named. Three records open the ledger with
their power demonstrated live in ``tests/test_guard_ledger.py`` (each
demonstration constructs the smallest mutant and watches the guard fire), and
two are recorded honestly as undemonstrated — the visible head of the
offensive's worklist, per the adopted decision in ``ROADMAP.md`` ("The
outside memos, triaged", adopted build 2).

The ledger grows one demonstrated record at a time. The rule for adding one:
``fired`` may only move off ``None`` in the same change that adds the
demonstration, and a demonstration is a runnable artifact, not a sentence.
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
            "a document renamed without its number changing (references stay "
            "valid, content drifts from title) — no guard reads content",
        ),
        scope="uniqueness of the leading number, nothing about the contents",
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
        fired=None,
        known_misses=(),
        scope="undetermined until demonstrated",
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
)
