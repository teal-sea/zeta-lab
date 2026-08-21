# Hunt R-C62E44: results

**Status: settled.** The guard `tests/test_docs_numbering.py::test_no_two_docs_share_a_number` does not detect a document renamed without its number changing when citations use bare references (such as `docs/08`), nor does it detect document content drift, title changes, or slug-title divergence. Sibling test `test_every_full_filename_reference_to_a_doc_resolves` detects a rename only if full-filename references remain in the repository. An exhaustive census across all 37 test files mentioning `docs/` confirms that zero tests in the suite inspect document body content, validate H1 headings against filenames, or verify citation semantic validity.

Reproduce: `python hunts/r_c62e44/probe.py` (~5 s, standard library and existing tree modules only).
Data: `results.json`.

## Controls

Both controls ran and held:

| control | what it rules out | outcome |
|---|---|---|
| unmutated baseline sandbox | false positive failure produced by sandbox setup | all 4 numbering tests pass, `make_context.py --check` passes |
| per-mutant undo verification | state contamination across sequential mutant rows | clean pass across all 20 mutant cycles |

All mutations were executed against an isolated temporary directory sandbox, leaving the live repository untouched.

## The 20-mutant battery

| ID | Category | Primary Guard (`no_two_docs`) | Course Gap Guard | Full-Name Ref Guard | Bare Ref Guard | Context Check | Overall Fired | Description |
|---|---|---|---|---|---|---|---|---|
| M01 | Primary lesion | **YES** | no | no | no | YES | **YES** | Add duplicate leading number `05-b.md` alongside `05-de-bruijn-newman.md` |
| M02 | Declared miss | **no** | no | no | no | YES | **no** | Rename `08-why-it-is-hard.md` to `08-spectral-gap.md` with bare references |
| M03 | Boundary probe | **no** | no | **YES** | no | YES | **YES** | Rename `05-de-bruijn-newman.md` to `05-dbn.md` leaving dangling full-name refs |
| M04 | Declared miss | **no** | no | no | no | YES | **no** | Rename `05-de-bruijn-newman.md` to `05-dbn.md` with full-name refs updated |
| M05 | Content drift | **no** | no | no | no | YES | **no** | Replace body of `08-why-it-is-hard.md` completely while keeping H1 title |
| M06 | Content drift | **no** | no | no | no | YES | **no** | Change H1 title in place in `08-why-it-is-hard.md`, filename unchanged |
| M07 | Declared miss | **no** | no | no | no | YES | **no** | Rename `08-why-it-is-hard.md` to `08-hardness-of-rh.md`, keep original H1 |
| M08 | Sequence gap | **no** | **YES** | no | **YES** | YES | **YES** | Rename `08-why-it-is-hard.md` to `99-why-it-is-hard.md` (creates gap at 08) |
| M09 | Collision | **YES** | **YES** | no | **YES** | YES | **YES** | Rename `08-why-it-is-hard.md` to `07-why-it-is-hard.md` (collides with 07) |
| M10 | Format lesion | **no** | **YES** | no | **YES** | YES | **YES** | Rename `08-why-it-is-hard.md` to `008-why-it-is-hard.md` (3 digits) |
| M11 | Format lesion | **no** | **YES** | no | **YES** | YES | **YES** | Rename `08-why-it-is-hard.md` to `8-why-it-is-hard.md` (1 digit) |
| M12 | Ref integrity | **no** | no | no | **YES** | no | **YES** | Add bare reference to non-existent document number in `00-orientation.md` |
| M13 | Ref integrity | **no** | no | **YES** | no | no | **YES** | Add full filename reference to non-existent document in `00-orientation.md` |
| M14 | Lifecycle | **no** | **YES** | **YES** | **YES** | YES | **YES** | Delete `08-why-it-is-hard.md` without updating references |
| M15 | Valid addition | **no** | no | no | no | YES | **no** | Add consecutive document `28-future-work.md` (valid extension of course) |
| M16 | File type | **no** | no | no | no | no | **no** | Add non-markdown file `docs/08-notes.txt` (untracked by `_NUMBERED_DOC`) |
| M17 | Hierarchy | **no** | no | no | no | no | **no** | Add nested document in `docs/extra/08-extra.md` (ignored by flat scan) |
| M18 | Scanning reach | **no** | no | no | **YES** | no | **YES** | Add dangling bare reference in non-docs file (`test_docs_numbering.py`) |
| M19 | Format lesion | **no** | **YES** | **YES** | **YES** | YES | **YES** | Rename `08-why-it-is-hard.md` to `08_why_it_is_hard.md` (underscores) |
| M20 | Generated drift | **no** | no | no | **YES** | YES | **YES** | Add dangling bare reference in `CONTEXT.md` |

## Summary of findings

1. **The primary guard is strictly a collision detector.** `test_no_two_docs_share_a_number` groups filenames matching `^(\d{2})-[\w.-]+\.md$` by their leading two digits and asserts `len(filenames) <= 1`. It fires on M01 and M09. On any rename where the leading number is preserved (M02, M04, M07), it is silent by construction.
2. **The boundary between bare and full-filename references is sharp.** `test_every_full_filename_reference_to_a_doc_resolves` catches a rename only when existing citations use the full filename (M03). Because `AGENTS.md` explicitly mandates bare citations (`docs/08` rather than full names), most repository references are bare. Bare references resolve as long as any file with that number exists, rendering renames transparent to the entire test suite (M02, M04).
3. **No test reads document content.** Replacing the entire body of a document (M05) or altering its H1 heading (M06) passes all four numbering guards. `scripts/make_context.py --check` detects line count changes or heading changes only until `CONTEXT.md` is regenerated: it validates that the index matches the files, not that the content matches the title or that citations are semantically coherent.
4. **Format sensitivity.** The regex `^(\d{2})-[\w.-]+\.md$` strictly requires exactly two digits and a hyphen. Files named with 3 digits (M10), 1 digit (M11), or underscores (M19) are ignored by `_numbered_docs()`, which triggers the gap guard `test_the_course_has_no_gap_that_hides_a_lost_document` and the reference resolution guards.

## What I chose and why

1. **Direct execution of test functions in sandbox rather than external pytest spawning.** Importing the test module directly and parameterizing `REPO_ROOT` and `DOCS` allowed running all 20 mutants and controls in ~5 seconds with exact assertion verification.
2. **20 mutants across 8 distinct categories.** Testing only the declared miss would confirm a single boolean. The 20-mutant battery maps the complete interaction matrix between the four numbering guards and `scripts/make_context.py --check`.
3. **Exhaustive census of the test suite.** Grepping and inspecting all 37 test files referencing `docs/` proved that the absence of content validation is structural and tree-wide, not an isolated property of `test_docs_numbering.py`.

## What I could not settle

1. **Whether semantic content validation is desirable in CI.** Automated checking of whether document contents match their titles or citations requires natural language understanding or structured metadata schemas. Whether to enforce title-slug equality (`08-why-it-is-hard.md` having `# 08: Why it is hard`) is an editorial design decision.
2. **Historical frequency of unnoticed content drift.** I did not reconstruct past git history to count instances where document bodies were rewritten while bare references in other files went unreviewed.

## Loose threads

1. **Title-slug decoupling is unconstrained.** A document named `08-why-it-is-hard.md` can have H1 `# 08: Topological Field Theory` without failing any guard. *Why it might matter:* Readers and agents navigating via `docs/NN` rely on title and slug describing the same subject. *First step:* Add a check in `test_docs_numbering.py` verifying that words in the filename slug appear in the H1 heading.
2. **Subdirectories in `docs/` are completely invisible to numbering guards.** `docs/doors/` and `docs/reviews/` contain markdown files that bypass `test_docs_numbering.py` because `_numbered_docs()` uses `os.listdir(DOCS)` without recursion. *Why it might matter:* Numbered docs placed inside a subdirectory would be ignored rather than validated. *First step:* Assert in `test_docs_numbering.py` that no numbered markdown files exist in subdirectories of `docs/`.
3. **Regex pattern `^(\d{2})-[\w.-]+\.md$` allows non-alphanumeric trailing characters.** A file named `08-foo..md` or `08-foo.bar.md` matches `\w.-`. *Why it might matter:* Inconsistent file naming across contributors. *First step:* Constrain the slug regex to `^(\d{2})-[a-z0-9-]+\.md$`.
