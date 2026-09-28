# zeta-adaptive-freeze-v1

A preservation checkpoint through the adaptive 23-correction block. Read `FREEZE.md` for the detailed claim/status ledger and the exact unresolved question. The latest three packages have not yet received a separate-agent review. This checkpoint changes no mathematical claim.

## Verify

First check the SHA-256 of the downloaded outer ZIP against the independent handoff value. Inspect paths, extract into a new scratch directory, then run:

```bash
python zeta_adaptive_freeze_v1/verify_freeze.py
```

This stdlib-only script verifies the snapshot files, all original archives recursively, and byte-identical latest extractions. It does not run experiments or prove mathematics. It returns nonzero on missing, empty, corrupted, linked or unlisted payloads. Write logs outside the immutable extracted snapshot.

## Contents

- `original_archives/`: 17 original ZIPs, unchanged; overlaps are intentional.
- `latest_extracted/`: support-obstruction, repair-cost and adaptive-block packages.
- `companion_files/`: eight separately delivered original documents/receipts.
- `ARCHIVE_CONTENTS.json`: 558 recursively nested member occurrences, including intentional duplicates.
- `FILE_MANIFEST.json`: exhaustive payload size/hash inventory.
- `IMPORT_MAP.json`: explicit proposed repository destinations for the three latest packages.
- `REPO_STATE.json`: GitHub references observed at freeze time, not a Git mirror.
- `LOCAL_VALIDATION.json`: archive and standalone Library readback checks performed in this pass.
- `CLAUDE_HANDOFF.md`: the complete preservation-only repository assignment.

## Storage status

The latest four original archives were saved to persistent Library and read back byte for byte before this packet was assembled. The sealed outer packet is to be saved and independently read back next; its external preservation receipt records that result. Repository import of these newest packages is a separate, explicitly unfinished step until Claude reports a clean-clone verification on main. Do not infer deployment from this README.

This is a backup of the inventoried research artifacts, not a verbatim chat export, a full repository mirror, or a copy of unseen desktop work. Registration means a named artifact checkpoint and eventual Git tag, not registration of a theorem.
