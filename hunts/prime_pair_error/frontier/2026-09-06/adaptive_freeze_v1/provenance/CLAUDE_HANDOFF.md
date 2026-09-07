# Claude handoff: preservation only

Thomas has paused the research. Finish one clean repository checkpoint, then stop. Do not resume mathematical exploration in this task.

## Input

The exact outer package is `zeta_adaptive_freeze_v1.zip`. Use the SHA-256 and byte count supplied by Thomas with this handoff. The archive expands to `zeta_adaptive_freeze_v1/`. It contains this file, `FREEZE.md`, `FILE_MANIFEST.json`, `ARCHIVE_CONTENTS.json`, `IMPORT_MAP.json`, `REPO_STATE.json`, `LOCAL_VALIDATION.json`, `verify_freeze.py`, 17 unchanged original archives, three runnable latest extractions and companion files.

This package is a NEW DOWNLOAD, not a file to locate on unmerged branches. First inspect the ZIP for unsafe paths, duplicate members or symlinks. Hash it before extraction. If the requested bytes are unavailable or the hash differs, report that exact blocker; do not substitute a similarly named older checkpoint. Run the included stdlib-only verifier on a scratch extraction. Do not run scientific scripts during this preservation task.

## Repository actions

1. Read `teal-sea/zeta-lab`'s current instructions, fetch origin and use a dedicated preservation worktree. Do not switch or reset a dirty shared checkout. Recheck current refs rather than relying on the snapshot's historical PR status.
2. Read `FREEZE.md` and `IMPORT_MAP.json`. Preserve the outer ZIP unchanged, with a SHA256SUMS sidecar, under `hunts/prime_pair_error/frontier/2026-09-06/adaptive_freeze_v1/archive/`. Copy FREEZE.md, IMPORT_MAP.json and the inventory/verification files alongside it as provenance. Preserve the original inventories even when their references are relative to the original package; describe that layout rather than changing the evidence.
3. Import the three `latest_extracted/` package directories into the proposed destinations in IMPORT_MAP.json. Their originals are unreviewed source packages. If a destination already exists, compare all bytes and include what matches; do not overwrite differing work. Record and resolve any genuine difference explicitly. Original nested ZIPs and recorded outputs must remain unchanged. Any necessary runnable-path or repository-vocabulary adaptation belongs in a separate working copy with a documented exact transformation and a test against the original. Do not weaken existing integrity checks to make an import pass.
4. Add a focused archive-integrity test. Pin the outer hash and byte count independently; demand a nonempty, complete manifest; check all required latest packages; verify the imported files against archive members; reject missing, empty, changed, extra and linked material. Run the shipped verifier against a scratch extraction, not an expanded tree polluted by generated files.
5. Add a dated pointer to the frontier README. Record the three latest stages as not yet independently reviewed. The separate reviews in #199 and #200 apply only to their named earlier objects. Preserve their commit references, and #196's experiment references, without merging or changing those PRs. No Palomar/journal submission, novelty claim or RH announcement.
6. Run the repository's applicable archive, scope, hygiene, secrets and generated-context checks. Report exactly which tests ran. Commit and push one preservation-only PR. Merge only this PR once the applicable checks pass and there are no unresolved blockers; never bypass a failing gate. A storage merge does not promote the mathematics.
7. Fetch a fresh clone or clean worktree of origin/main at the resulting commit. Recompute the committed outer hash, extract those committed bytes, run verify_freeze.py, and byte-compare the imported package files. A successful upload response, tree listing or PR body is NOT this readback verification.
8. After that succeeds, create and push the non-overwriting tag `research/adaptive-block-v1` at the verified commit. If that tag already identifies a different commit, report the conflict; do not force-move it.
9. Save a compact preservation receipt in the PR conversation: snapshot ID, archive size/hash, main commit, tag, verifier counts, imported paths, tests and any unresolved item. The exact main commit goes in the final report, not inside an archive rewritten after hashing.

## Stop condition and exclusions

Stop after the preservation report. No search expansion, new corrections, re-optimization, review restart, large numerical reproduction, external publication or agent orchestration. Do not delete pending review worktrees. This package does not grant permission to publish unrelated uncommitted desktop files; identify them to Thomas instead of sweeping them into the commit.

A pending merge or readback is a pending task. Say so rather than describing a pushed branch as main. Keep all original evidence and historical failure notes intact.
