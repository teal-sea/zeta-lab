"""Hunt R-C62E44 probe: does test_no_two_docs_share_a_number detect a renamed doc?

Measures the detection power and boundaries of tests/test_docs_numbering.py
against a battery of 20 mutants applied to a temporary sandbox copy of the tree.
Also performs an exhaustive census of tests/ and scripts/ for any guard that reads
docs/ content or validates title/content consistency.
"""

from __future__ import annotations

import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent


def _load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _run_numbering_tests_in_sandbox(sandbox: Path) -> dict[str, bool]:
    """Execute each of the 4 tests against sandbox by pointing REPO_ROOT and DOCS to sandbox."""
    test_path = sandbox / "tests" / "test_docs_numbering.py"
    mod = _load_module(test_path, f"test_docs_numbering_{os.urandom(4).hex()}")
    mod.REPO_ROOT = str(sandbox)
    mod.DOCS = str(sandbox / "docs")

    results = {}
    for func_name in [
        "test_no_two_docs_share_a_number",
        "test_the_course_has_no_gap_that_hides_a_lost_document",
        "test_every_full_filename_reference_to_a_doc_resolves",
        "test_every_bare_number_reference_names_a_document_that_exists",
    ]:
        func = getattr(mod, func_name)
        try:
            func()
            results[func_name] = False  # Did NOT fire (passed)
        except AssertionError:
            results[func_name] = True  # FIRED (AssertionError)
    return results


def _run_make_context_check(sandbox: Path) -> bool:
    """Run make_context.py --check against the sandbox."""
    script_path = sandbox / "scripts" / "make_context.py"
    res = subprocess.run(
        [sys.executable, str(script_path), "--check"],
        cwd=sandbox,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    return res.returncode != 0


def _census_doc_guards(repo_root: Path) -> list[dict]:
    """Inspect every test in tests/ and script in scripts/ for doc content checking."""
    findings = []
    tests_dir = repo_root / "tests"
    for path in sorted(tests_dir.glob("*.py")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        if "docs" not in text:
            continue
        
        mentions_docs = True
        scans_doc_content = False
        reads_doc_titles = False
        notes = []

        if path.name == "test_docs_numbering.py":
            notes.append("Checks doc numbering uniqueness, 00..N gaps, and ref resolution; does not read doc body or title.")
        elif path.name == "test_pub1_status.py":
            notes.append("Reads single item-3 row in docs/27 for specific grade string against OBLIGATIONS.md.")
            scans_doc_content = True
        elif path.name == "test_doors.py":
            notes.append("Executes shell commands quoted in docs/doors/*.md; does not read general docs/*.md.")
        elif path.name == "test_claim_attribution.py":
            notes.append("Contains static quotes from historical docs/12; does not read live docs files.")
        elif path.name == "test_reading_of_record.py":
            notes.append("Reads reading of record table row in docs/27.")
            scans_doc_content = True
        elif path.name == "test_guard_ledger.py":
            notes.append("Tests guard ledger conformance and smallest mutants; mocks DOCS for numbering test.")
        else:
            notes.append("Mentions docs in comments or docstrings.")

        findings.append({
            "file": str(path.relative_to(repo_root)),
            "mentions_docs": mentions_docs,
            "scans_doc_content": scans_doc_content,
            "reads_doc_titles": reads_doc_titles,
            "notes": " ".join(notes),
        })

    return findings


def build_sandbox(dest: Path) -> None:
    """Copy the essential parts of the repo into sandbox."""
    for item in [
        "docs", "tests", "scripts", "harness", "zeta", "ontology", "dossier",
        "compiler", "meta", "pyproject.toml", "CONTEXT.md", "README.md",
        "AGENTS.md", "ROADMAP.md", "HANDOFF.md"
    ]:
        src = REPO_ROOT / item
        dst = dest / item
        if src.is_dir():
            shutil.copytree(src, dst, ignore=shutil.ignore_patterns("__pycache__", ".pytest_cache", ".lake"))
        elif src.is_file():
            shutil.copy2(src, dst)
    # Ensure sandbox CONTEXT.md matches sandbox baseline
    subprocess.run(
        [sys.executable, str(dest / "scripts" / "make_context.py")],
        cwd=dest,
        capture_output=True,
        check=False,
    )


def _d(name: str) -> str:
    """Helper to assemble 'docs/' + name to avoid regex match during scan."""
    return f"docs/{name}"


def run_probe() -> dict:
    with tempfile.TemporaryDirectory(prefix="zeta_hunt_probe_") as tmp_dir:
        sandbox = Path(tmp_dir) / "repo"
        build_sandbox(sandbox)

        # Control 1: Baseline green
        base_results = _run_numbering_tests_in_sandbox(sandbox)
        base_ctx_fail = _run_make_context_check(sandbox)
        assert not any(base_results.values()), f"Sandbox baseline failed: {base_results}"
        assert not base_ctx_fail, "Sandbox baseline failed make_context.py --check"

        mutant_records = []

        mutants = [
            # 1. Declared smallest mutant for test_no_two_docs_share_a_number
            {
                "id": "M01",
                "name": "duplicate_leading_number",
                "category": "guard_primary_lesion",
                "description": "Add 05-b.md alongside 05-de-bruijn-newman.md in docs/",
                "apply": lambda s: (s / "docs" / "05-b.md").write_text("# 05b\nExtra doc\n", encoding="utf-8"),
                "undo": lambda s: (s / "docs" / "05-b.md").unlink(missing_ok=True),
                "expected_primary_fire": True,
            },
            # 2. The question's declared miss: Rename doc with number preserved, bare references only
            {
                "id": "M02",
                "name": "rename_doc_preserve_number_bare_refs_only",
                "category": "declared_miss",
                "description": "Rename 08-why-it-is-hard.md -> 08-spectral-gap.md (bare docs/08 refs remain)",
                "apply": lambda s: (
                    _replace_in_files(s, _d("08-why-it-is-hard.md"), _d("08")),
                    (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "08-spectral-gap.md")
                ),
                "undo": lambda s: (
                    (s / "docs" / "08-spectral-gap.md").rename(s / "docs" / "08-why-it-is-hard.md")
                    if (s / "docs" / "08-spectral-gap.md").exists() else None,
                    _restore_repo_file(s, "tests/test_claim_attribution.py"),
                ),
                "expected_primary_fire": False,
            },
            # 3. Rename doc with number preserved, leaving dangling full filename reference
            {
                "id": "M03",
                "name": "rename_doc_preserve_number_dangling_fullname_ref",
                "category": "boundary_filename_ref",
                "description": "Rename 05-de-bruijn-newman.md -> 05-dbn.md leaving 05-de-bruijn-newman.md refs intact",
                "apply": lambda s: (s / "docs" / "05-de-bruijn-newman.md").rename(s / "docs" / "05-dbn.md"),
                "undo": lambda s: (s / "docs" / "05-dbn.md").rename(s / "docs" / "05-de-bruijn-newman.md"),
                "expected_primary_fire": False,
            },
            # 4. Rename doc with number preserved, full filename refs updated
            {
                "id": "M04",
                "name": "rename_doc_preserve_number_fullname_refs_updated",
                "category": "declared_miss",
                "description": "Rename 05-de-bruijn-newman.md -> 05-dbn.md and update all refs to 05-dbn.md",
                "apply": lambda s: (
                    _replace_in_files(s, _d("05-de-bruijn-newman.md"), _d("05-dbn.md")),
                    (s / "docs" / "05-de-bruijn-newman.md").rename(s / "docs" / "05-dbn.md")
                ),
                "undo": lambda s: (
                    (s / "docs" / "05-dbn.md").rename(s / "docs" / "05-de-bruijn-newman.md")
                    if (s / "docs" / "05-dbn.md").exists() else None,
                    _replace_in_files(s, _d("05-dbn.md"), _d("05-de-bruijn-newman.md"))
                ),
                "expected_primary_fire": False,
            },
            # 5. Content replaced completely (content drift, filename & title unchanged)
            {
                "id": "M05",
                "name": "content_replaced_completely_content_drift",
                "category": "content_drift",
                "description": "Replace body of 08-why-it-is-hard.md with banana bread recipe while keeping H1 title",
                "apply": lambda s: _write_doc_content(s, "08-why-it-is-hard.md", "# 08: Why it is hard\n\nTake 3 ripe bananas, mash with fork, mix with flour and sugar. Bake at 350F for 60 min.\n"),
                "undo": lambda s: _restore_doc(s, "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 6. H1 title changed in place, filename slug unchanged
            {
                "id": "M06",
                "name": "h1_title_changed_in_place",
                "category": "content_drift",
                "description": "Change H1 in 08-why-it-is-hard.md to '# 08: Banana Bread Recipe'",
                "apply": lambda s: _write_doc_content(s, "08-why-it-is-hard.md", "# 08: Banana Bread Recipe\n\nOriginal text continues here...\n"),
                "undo": lambda s: _restore_doc(s, "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 7. Filename slug changed in place, H1 title unchanged
            {
                "id": "M07",
                "name": "filename_slug_changed_title_unchanged",
                "category": "declared_miss",
                "description": "Rename 08-why-it-is-hard.md -> 08-hardness-of-rh.md, keep H1 '# 08: Why it is hard'",
                "apply": lambda s: (
                    _replace_in_files(s, _d("08-why-it-is-hard.md"), _d("08-hardness-of-rh.md")),
                    (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "08-hardness-of-rh.md")
                ),
                "undo": lambda s: (
                    (s / "docs" / "08-hardness-of-rh.md").rename(s / "docs" / "08-why-it-is-hard.md")
                    if (s / "docs" / "08-hardness-of-rh.md").exists() else None,
                    _replace_in_files(s, _d("08-hardness-of-rh.md"), _d("08-why-it-is-hard.md"))
                ),
                "expected_primary_fire": False,
            },
            # 8. Doc number changed creating gap in sequence
            {
                "id": "M08",
                "name": "doc_number_changed_creates_gap",
                "category": "number_sequence",
                "description": "Rename 08-why-it-is-hard.md -> 99-why-it-is-hard.md",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "99-why-it-is-hard.md"),
                "undo": lambda s: (s / "docs" / "99-why-it-is-hard.md").rename(s / "docs" / "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 9. Doc number changed causing collision with existing number
            {
                "id": "M09",
                "name": "doc_number_changed_collides",
                "category": "guard_primary_lesion",
                "description": "Rename 08-why-it-is-hard.md -> 07-why-it-is-hard.md (now two 07 docs)",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "07-why-it-is-hard.md"),
                "undo": lambda s: (s / "docs" / "07-why-it-is-hard.md").rename(s / "docs" / "08-why-it-is-hard.md"),
                "expected_primary_fire": True,
            },
            # 10. Doc formatted with 3 digits 008-why-it-is-hard.md
            {
                "id": "M10",
                "name": "doc_number_3_digits",
                "category": "format_lesion",
                "description": "Rename 08-why-it-is-hard.md -> 008-why-it-is-hard.md (fails regex ^\\d{2}-)",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "008-why-it-is-hard.md"),
                "undo": lambda s: (s / "docs" / "008-why-it-is-hard.md").rename(s / "docs" / "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 11. Doc formatted with 1 digit 8-why-it-is-hard.md
            {
                "id": "M11",
                "name": "doc_number_1_digit",
                "category": "format_lesion",
                "description": "Rename 08-why-it-is-hard.md -> 8-why-it-is-hard.md (fails regex ^\\d{2}-)",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "8-why-it-is-hard.md"),
                "undo": lambda s: (s / "docs" / "8-why-it-is-hard.md").rename(s / "docs" / "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 12. Bare reference to non-existent doc number (phantom number 99)
            {
                "id": "M12",
                "name": "bare_ref_to_nonexistent_doc",
                "category": "reference_integrity",
                "description": "Add bare reference to phantom number in 00-orientation.md",
                "apply": lambda s: _append_to_file(s, "docs/00-orientation.md", f"\nSee {'doc' + 's/99'} for details.\n"),
                "undo": lambda s: _restore_doc(s, "00-orientation.md"),
                "expected_primary_fire": False,
            },
            # 13. Full filename reference to non-existent doc (phantom file 99)
            {
                "id": "M13",
                "name": "full_ref_to_nonexistent_doc",
                "category": "reference_integrity",
                "description": "Add full reference to phantom filename in 00-orientation.md",
                "apply": lambda s: _append_to_file(s, "docs/00-orientation.md", f"\nSee {'doc' + 's/99-nonexistent.md'} for details.\n"),
                "undo": lambda s: _restore_doc(s, "00-orientation.md"),
                "expected_primary_fire": False,
            },
            # 14. Document withdrawn/deleted without updating references
            {
                "id": "M14",
                "name": "doc_deleted_leaving_gap_and_dangling_refs",
                "category": "lifecycle",
                "description": "Delete 08-why-it-is-hard.md",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").unlink(),
                "undo": lambda s: _restore_doc(s, "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 15. Valid doc added at end of sequence 28-future-work.md
            {
                "id": "M15",
                "name": "valid_doc_added_at_end",
                "category": "valid_addition",
                "description": "Add 28-future-work.md extending 00..27 sequence",
                "apply": lambda s: (s / "docs" / "28-future-work.md").write_text("# 28: Future work\nValid addition.\n", encoding="utf-8"),
                "undo": lambda s: (s / "docs" / "28-future-work.md").unlink(missing_ok=True),
                "expected_primary_fire": False,
            },
            # 16. Non-markdown file in docs/ directory e.g. docs/notes.txt
            {
                "id": "M16",
                "name": "non_md_file_in_docs",
                "category": "untracked_file_type",
                "description": "Add 08-notes.txt in docs/ (non .md extension)",
                "apply": lambda s: (s / "docs" / "08-notes.txt").write_text("Text note\n", encoding="utf-8"),
                "undo": lambda s: (s / "docs" / "08-notes.txt").unlink(missing_ok=True),
                "expected_primary_fire": False,
            },
            # 17. Subdirectory inside docs/ e.g. docs/extra/08-extra.md
            {
                "id": "M17",
                "name": "nested_subdirectory_doc",
                "category": "unscanned_hierarchy",
                "description": "Add extra/08-extra.md in a nested docs/ subdirectory",
                "apply": lambda s: (
                    (s / "docs" / "extra").mkdir(exist_ok=True),
                    (s / "docs" / "extra" / "08-extra.md").write_text("# Extra\n", encoding="utf-8")
                ),
                "undo": lambda s: (
                    (s / "docs" / "extra" / "08-extra.md").unlink(missing_ok=True),
                    (s / "docs" / "extra").rmdir() if (s / "docs" / "extra").exists() else None
                ),
                "expected_primary_fire": False,
            },
            # 18. Reference in non-docs file to nonexistent doc
            {
                "id": "M18",
                "name": "non_docs_file_dangling_bare_ref",
                "category": "multilingual_scanning",
                "description": "Add comment referencing docs:99 in test_docs_numbering.py",
                "apply": lambda s: _append_to_file(s, "tests/test_docs_numbering.py", f"\n# comment referencing {_d('99')}\n"),
                "undo": lambda s: _restore_repo_file(s, "tests/test_docs_numbering.py"),
                "expected_primary_fire": False,
            },
            # 19. Doc filename with underscores e.g. docs/08_why_it_is_hard.md
            {
                "id": "M19",
                "name": "doc_filename_with_underscores",
                "category": "format_lesion",
                "description": "Rename 08-why-it-is-hard.md -> 08_why_it_is_hard.md (fails regex ^\\d{2}-)",
                "apply": lambda s: (s / "docs" / "08-why-it-is-hard.md").rename(s / "docs" / "08_why_it_is_hard.md"),
                "undo": lambda s: (s / "docs" / "08_why_it_is_hard.md").rename(s / "docs" / "08-why-it-is-hard.md"),
                "expected_primary_fire": False,
            },
            # 20. Stale doc reference in CONTEXT.md only (generated file drift)
            {
                "id": "M20",
                "name": "stale_doc_ref_in_context_md",
                "category": "generated_index_drift",
                "description": "Add reference to docs:99 in CONTEXT.md",
                "apply": lambda s: _append_to_file(s, "CONTEXT.md", f"\n- [Doc 99]({_d('99')})\n"),
                "undo": lambda s: _restore_repo_file(s, "CONTEXT.md"),
                "expected_primary_fire": False,
            },
        ]

        for m in mutants:
            m["apply"](sandbox)

            results = _run_numbering_tests_in_sandbox(sandbox)
            ctx_fail = _run_make_context_check(sandbox)

            fired_primary = results["test_no_two_docs_share_a_number"]
            fired_gap = results["test_the_course_has_no_gap_that_hides_a_lost_document"]
            fired_fullname = results["test_every_full_filename_reference_to_a_doc_resolves"]
            fired_bare = results["test_every_bare_number_reference_names_a_document_that_exists"]

            record = {
                "id": m["id"],
                "name": m["name"],
                "category": m["category"],
                "description": m["description"],
                "test_no_two_docs_share_a_number": fired_primary,
                "test_the_course_has_no_gap": fired_gap,
                "test_every_full_filename_ref_resolves": fired_fullname,
                "test_every_bare_number_ref_resolves": fired_bare,
                "make_context_check_fires": ctx_fail,
                "overall_numbering_suite_fired": any(results.values()),
                "matches_expected_primary": (fired_primary == m["expected_primary_fire"]),
            }
            mutant_records.append(record)

            m["undo"](sandbox)

            clean_results = _run_numbering_tests_in_sandbox(sandbox)
            assert not any(clean_results.values()), f"Sandbox dirty after undo of {m['id']}: {clean_results}"

        census = _census_doc_guards(REPO_ROOT)

        return {
            "summary": {
                "total_mutants": len(mutants),
                "primary_guard_fired_count": sum(1 for r in mutant_records if r["test_no_two_docs_share_a_number"]),
                "any_numbering_guard_fired_count": sum(1 for r in mutant_records if r["overall_numbering_suite_fired"]),
                "declared_miss_detected_by_primary": False,
                "declared_miss_detected_by_any_guard": False,
                "content_drift_detected_by_any_guard": False,
            },
            "mutants": mutant_records,
            "guard_census": census,
        }


def _replace_in_files(sandbox: Path, old: str, new: str) -> None:
    for dirpath, _, filenames in os.walk(sandbox):
        for name in filenames:
            if os.path.splitext(name)[1] in {".md", ".py", ".txt", ".lean", ".sh"}:
                p = Path(dirpath) / name
                text = p.read_text(encoding="utf-8", errors="ignore")
                if old in text:
                    p.write_text(text.replace(old, new), encoding="utf-8")


def _write_doc_content(sandbox: Path, filename: str, content: str) -> None:
    p = sandbox / "docs" / filename
    p.write_text(content, encoding="utf-8")


def _restore_doc(sandbox: Path, filename: str) -> None:
    src = REPO_ROOT / "docs" / filename
    dst = sandbox / "docs" / filename
    if src.exists():
        shutil.copy2(src, dst)
    elif dst.exists():
        dst.unlink()


def _restore_repo_file(sandbox: Path, relpath: str) -> None:
    src = REPO_ROOT / relpath
    dst = sandbox / relpath
    if src.exists():
        shutil.copy2(src, dst)
    elif dst.exists():
        dst.unlink()


def _append_to_file(sandbox: Path, relpath: str, addition: str) -> None:
    p = sandbox / relpath
    text = p.read_text(encoding="utf-8", errors="ignore")
    p.write_text(text + addition, encoding="utf-8")


def main() -> None:
    print("Running Hunt R-C62E44 probe...")
    data = run_probe()
    
    out_dir = Path(__file__).resolve().parent
    results_path = out_dir / "results.json"
    results_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Wrote {len(data['mutants'])} mutant measurements to {results_path}")

    print("\n--- RESULTS TABLE ---")
    print(f"{'ID':<5} | {'Category':<22} | {'Primary':<7} | {'Gap':<5} | {'Full':<5} | {'Bare':<5} | {'Any':<5} | {'Description'}")
    print("-" * 90)
    for r in data["mutants"]:
        p = "YES" if r["test_no_two_docs_share_a_number"] else "no"
        g = "YES" if r["test_the_course_has_no_gap"] else "no"
        f = "YES" if r["test_every_full_filename_ref_resolves"] else "no"
        b = "YES" if r["test_every_bare_number_ref_resolves"] else "no"
        a = "YES" if r["overall_numbering_suite_fired"] else "no"
        print(f"{r['id']:<5} | {r['category']:<22} | {p:<7} | {g:<5} | {f:<5} | {b:<5} | {a:<5} | {r['description'][:40]}")


if __name__ == "__main__":
    main()
