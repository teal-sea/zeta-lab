# Hunt R-365C6C: file-type boundary of the hunt reserved-word guard

**Status: settled.** The guard `tests/test_hunt_probe_discipline.py::test_no_hunt_claims_the_reserved_word` enforces an explicit suffix whitelist: `path.suffix.lower() in {".py", ".md", ".json"}`. Every file type outside this three-extension set passes unconditionally, allowing an overclaim to pass undetected in `.txt`, `.lean`, `.sh`, `.toml`, `.yaml`, `.csv`, `.rst`, `.tex`, `.html`, `.jsonl`, or extensionless files.

Reproduce: `python3 hunts/r_365c6c/probe.py` (~40 s, standard library and pytest only).
Data: `results.json`.

## Controls

The sandbox harness in `probe.py` applies three strict controls:
1. **Empty specimen control:** The sandbox guard is executed against an empty specimen directory and passes (exit 0). Every failure below is caused strictly by the planted specimen.
2. **Restore control:** After each specimen run, the specimen is deleted and the sandbox is verified to return to clean green status (exit 0) before proceeding to the next specimen.
3. **Clean negative controls:** Clean files with sanctioned vocabulary (`clean.py`, `clean.md`, `clean.json`, `clean.txt`, `clean.lean`) are verified to produce no false alarms (0/5 caught).

## Result 1: Census of the `hunts/` tree

An exhaustive census of all 447 files under `hunts/` in the repository:

| Extension | Count | Percentage | Guard Status | Notes |
|---|---|---|---|---|
| `.py` | 167 | 37.4% | Scanned | Python probe scripts and modules |
| `.md` | 138 | 30.9% | Scanned | Documentation, MISSION.md, RESULTS.md |
| `.json` | 66 | 14.8% | Scanned | Measurement data and HANDBACK files |
| **Scanned Subtotal** | **371** | **83.0%** | **Covered** | **Checked by lexical scan** |
| `.lean` | 68 | 15.2% | **Unscanned** | Lean 4 formal proof modules (e.g. `frontier_math`) |
| `.png` | 4 | 0.9% | **Unscanned** | Binary plot images |
| `(no ext)` | 2 | 0.4% | **Unscanned** | `.gitignore`, `lean-toolchain` |
| `.sh` | 1 | 0.2% | **Unscanned** | Shell build script (`assemble.sh`) |
| `.toml` | 1 | 0.2% | **Unscanned** | Lean package config (`lakefile.toml`) |
| **Unscanned Subtotal** | **76** | **17.0%** | **Blind** | **Completely bypassed** |
| **Total** | **447** | **100.0%** | | |

Key findings from the corpus scan:
- 17.0% (76 files) of the tracked files under `hunts/` are completely invisible to the reserved-word guard.
- None of the 76 unscanned files currently contain the exact reserved word.
- 17 `.lean` files in `hunts/frontier_math/zeta23ext/` contain morphological stems such as `BandCert`, `FloorCert`, `certificate`, `cert`, and `depok`.

## Result 2: The Specimen Battery

Running the unmodified guard against 40 planted specimens in the isolated sandbox:

| Category | Tested (n) | Caught | Missed | Detection Rate | Examples |
|---|---|---|---|---|---|
| Scanned positive controls | 6 | 6 | 0 | **100%** | `.py`, `.md`, `.json`, uppercase `.PY`, `.MD`, `.JSON` |
| Scanned clean controls | 3 | 0 | 3 | **0% (clean)** | `clean.py`, `clean.md`, `clean.json` (no false alarms) |
| Unscanned clean controls | 2 | 0 | 2 | **0% (clean)** | `clean.txt`, `clean.lean` (no false alarms) |
| Plain text & data formats | 4 | 0 | 4 | **0%** | `.txt`, `.log`, `.out`, `.dat` (all missed) |
| Table data formats | 2 | 0 | 2 | **0%** | `.csv`, `.tsv` (all missed) |
| Structured config & interchange | 8 | 0 | 8 | **0%** | `.yaml`, `.yml`, `.toml`, `.ini`, `.cfg`, `.xml`, `.jsonl`, `.ndjson` (all missed) |
| Code & script formats | 10 | 0 | 10 | **0%** | `.lean`, `.sh`, `.bash`, `.zsh`, `.c`, `.cpp`, `.rs`, `.go`, `.js`, `.ts` (all missed) |
| Document & markup formats | 6 | 0 | 6 | **0%** | `.tex`, `.bib`, `.rst`, `.html`, `.htm`, `.svg` (all missed) |
| Extensionless files | 3 | 0 | 3 | **0%** | `NOTES`, `Makefile`, `Dockerfile` (all missed) |
| Compound extensions | 2 | 0 | 2 | **0%** | `.json.bak`, `.py.tmp` (all missed) |
| Dotfiles / hidden files | 2 | 0 | 2 | **0%** | `.notes.txt`, `.scratch` (all missed) |
| Binary formats | 2 | 0 | 2 | **0%** | `.png`, `.npy` (all missed) |

## What I chose and why

1. **Unmodified guard execution:** Rather than simulating or re-implementing the guard logic, `probe.py` copies `tests/test_hunt_probe_discipline.py` into a sandbox tempdir and executes `pytest` against it for every specimen. The reported detection status is the test process exit code itself.
2. **Comprehensive format battery:** Instead of testing `.txt` alone, the battery tests 35 non-scanned variants across text, configs, scripts, proofs, markup, extensionless files, compound extensions, and dotfiles.
3. **Non-modification of the guard test:** Widening the guard's extension filter in `tests/test_hunt_probe_discipline.py` is outside the scoped write permission of this hunt. The boundary is measured, documented, and recorded in `harness/departments/guard_ledger.py`.

## What could not be settled

- **Policy on non-Python proof files:** 68 `.lean` files exist under `hunts/frontier_math/`. If the guard is widened to scan `.lean` files, any legitimate occurrence of Lean vocabulary (such as `Certificate` or `BandCert`) might require careful handling if stem-matching is ever introduced.
- **Handling of binary files:** Binary files (`.png`, `.npy`, `.olean`) are unscanned. Scanning binary files with UTF-8 text decoders can raise encoding errors unless `errors="ignore"` is specified, and binary headers can occasionally contain false substring matches.

## Loose threads

1. **Lean proof files in hunts are completely unscanned.** `hunts/frontier_math/` contains 68 `.lean` files where proof claims and certificates are authored. *Why it might matter:* an overclaim in a `.lean` comment or theorem docstring inside a probe bypasses the guard entirely. *First step:* evaluate whether `.lean` should be added to the guard's whitelist in `tests/test_hunt_probe_discipline.py`.
2. **JSON Lines (`.jsonl`) logs are not scanned.** `.jsonl` files are increasingly used for structured logs and telemetry, but `path.suffix.lower()` evaluates to `".jsonl"`, which does not match `".json"`. *Why it might matter:* probes recording claims in `.jsonl` telemetry logs are blind to the guard. *First step:* add `".jsonl"` and `".ndjson"` to the allowed extension set in `test_no_hunt_claims_the_reserved_word`.
3. **Compound extensions like `.json.bak` and `.py.tmp` slip through.** Python's `pathlib.Path.suffix` only returns the final extension. *Why it might matter:* backup files or temporary scratch dumps containing overclaims are ignored. *First step:* consider checking all suffixes (`path.suffixes`) or checking whether any suffix matches the whitelist.
