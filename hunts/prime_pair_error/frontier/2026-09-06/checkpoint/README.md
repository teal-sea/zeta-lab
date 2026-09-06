# Start here: research preservation checkpoint

**2026-09-06. Preservation only; no new mathematical result or agent run.**

Read [CHECKPOINT.md](CHECKPOINT.md) for the complete chronology, mathematical objectives, claim grades, failed approaches, and precise open questions. It covers the original prime experiments, separate Möbius branch, CHHL passes, reviewed Wronskian work, upper-bound attempt, frequency drafts, direct arithmetic obstruction, and every factorial-certificate pass through combined-weight repair.

## Research notes newly saved in this directory

The following are byte-identical copies of the original notes inside their source ZIPs:

- [STRUCTURAL_STEP.md](source_notes/STRUCTURAL_STEP.md): omitted-prime obstruction and the period-30030 extension.
- [REFINEMENT.md](source_notes/REFINEMENT.md): reusable positive repair, five applications, and the complete error budget.
- [ROUTE_ASSESSMENT.md](source_notes/ROUTE_ASSESSMENT.md): fixed-recipe ceiling and the weaker combined-weight repair invariant.

These are **archived, unreviewed source notes**, not promoted theorems. Historical statements inside them such as 'not pushed' describe the original run. Script and JSON filenames mentioned there refer to their original package layouts, not to files asserted to exist next to these copied notes. The complete original code/data packages are stored as described below.

Git object checks against the source bytes, after fetching the new repository directory at `f1eff31956a6384776e752d064cf950b281b66ca`:

| Note | Bytes | Git blob SHA-1 |
|---|---:|---|
| STRUCTURAL_STEP.md | 8178 | `a45ad9bea8b5ed39f7f1f2461732860048fc8718` |
| REFINEMENT.md | 12255 | `44550fccf3fed5aebd4d2c1653c12c0d0e9497df` |
| ROUTE_ASSESSMENT.md | 11623 | `d99b55d2263e4a260d75f70052ce265b5fd46cd6` |

The checkpoint narrative's Git blob is `3230d5e9e95eb8396a0860de455e44a09774a0f7`; it also matches the local copy.

## Complete original bytes: persistent Library backup

Library folder: **`/Zeta Lab/Research snapshots/2026-09-06/`**.

The cumulative file is **`zeta_research_checkpoint_2026-09-06.zip`**, 1,524,467 bytes.

SHA-256:

`161575e3f8c88c263064099983cf586b89ad8abba2037c20766ce4eeaca257f9`

This ZIP contains 12 unchanged original research archives, 16 loose original companion files, byte-identical extractions of the latest three packages, a complete archive/member inventory, a narrative checkpoint, and `verify_snapshot.py`. Overlapping source archives are intentionally retained. The SHA manifest covers 56 payload files; the ZIPs contain 108 direct file members in total, with overlaps.

**Readback completed:** the newly saved Library ZIP was materialized into a different directory, compared byte for byte to the original, extracted into a fresh temporary directory, and its verifier executed successfully. Result: 56 files, 12 original archives, 108 direct archive members, PASS. This is byte-integrity evidence, not a fresh validation of the mathematics. The three latest standalone Library ZIP copies were independently read back and compared too.

The verifier fails on missing, empty, changed, or unlisted files and missing/invalid ZIP members. Separate fault-injection tests confirmed rejection of a missing archive, an empty archive, a one-byte change, an empty manifest, and an unlisted extra file. New computations must not overwrite the archived original results.

**Boundary (as written by the Library pass, kept as history):** the three latest raw ZIPs and this cumulative binary snapshot are saved in persistent Library, NOT committed as binaries in this GitHub PR. The earlier frontier handoff and factorial-pilot raw ZIPs are already on main. Do not describe this PR as uploading binary archives that it does not contain. A later binary import must retain these exact hashes and verify the repository bytes after landing.

## Repository import (2026-09-06, later the same day)

That later binary import is this section. The cumulative ZIP is now committed unchanged at
`checkpoint/archive/zeta_research_checkpoint_2026-09-06.zip` with the sidecar
`checkpoint/archive/SHA256SUMS`. Before it was copied in, the download was checked against
the size and SHA-256 above, listed for unsafe member paths (none: 57 members, all under the
top directory, no symlinks), extracted into a scratch directory, and its own
`verify_snapshot.py` was run there: PASS, 56 files, 12 original archives, 108 direct
archive members. The copy in the tree was hashed again after the copy.

The three newest packages are also imported as runnable working directories beside this
one, byte for byte from the archive's `latest_extracted/` tree, which is itself byte for
byte the content of the three nested original ZIPs:

| Working directory | Files | Source inside the archive |
|---|---:|---|
| `../certificate_structural_step/` | 7 | `latest_extracted/certificate_structural_step/` |
| `../certificate_refinement_rule/` | 7 | `latest_extracted/certificate_refinement_rule/` |
| `../certificate_route_test/` | 9 | `latest_extracted/certificate_route_test/` |

No vocabulary substitution was needed: none of the twenty-three files carries the word this
repository reserves for `zeta/rigor.py`, so the working copies are identical to the members
and the test demands identity. The three `source_notes/` copies remain the same bytes as
the notes inside those directories.

`tests/test_research_checkpoint_archive.py` pins all of this on every run: the archive's
presence, size and hash (against this README and the sidecar), a non-empty manifest with
every listed file inside at its recorded hash, the twelve nested archives and all 108 of
their members, the included verifier passing on a fresh extraction, and the working copies
equal to the members. A missing archive, an empty manifest, or a drifted copy fails; nothing
skips. Recorded outputs (`results.json`, `checked_results.json`, `aggregate_results.json`,
`original_results.json`) are the original measured records and are not to be overwritten;
reruns write new files. A review may add `BASELINE_REVIEW.md` and a `review/` subdirectory
beside a package's members, the layout `../factorial_certificate_pilot/` established, and
the test allows exactly those two names.

This import is byte preservation. It is not a review of the mathematics in the three
packages and it promotes nothing.

To verify a downloaded cumulative copy, extract it and run:

```bash
python zeta_research_checkpoint_2026-09-06/verify_snapshot.py
```

It checks bytes and member inventories only. It does not run the research experiments or a Lean build.

## Existing work preserved without changing its review state

PR #196 remains open and unmerged at `46fdb433752a1b26abba516fc24d6db21543b2b8`. An additional branch, `snapshot/2026-09-06-factorial-comparisons`, points to that exact commit so this checkpoint does not depend solely on the mutable working branch. Its two experiment reports and all data remain there. No pending research review was bypassed.

PRs #189, #192, #193, and #195 were already merged before this pass. No prior archive, result, review, test, or active research branch was overwritten. There is no new mathematical work hidden off-repo beyond the original artifacts explicitly indexed here. Unseen desktop files and the full raw conversation transcript are outside the scope of this artifact snapshot.
