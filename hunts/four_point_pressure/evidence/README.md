# Evidence: Lean kernel build of the c = 2330/10^6 four-point candidate

Recorded 2026-09-28. This is a local, independent kernel build of the generated
`FourPointCand` package at the pinned toolchain. It is **not** external review
and it is **not** a Palomar registration. Nothing here claims novelty.

## What was built

- Source commit: `5522b96314f7f63198ae3ec4e71d954255f93d1a`
  (branch `vizier/four-point-stronger-cert`).
- Compute: Modal app `ap-7zxzQj0YqTwlQUP6P06ecn` (profile `teal-sea`), serial
  layer-by-layer `lake build`, one build at a time, 2 cores, 8 GiB.
- Toolchain: `leanprover/lean4:v4.33.0-rc2` (`Lean 4.33.0-rc2, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17`).
- Result: 49 receipts (preflight plus 48 layers, `Base` through the whole
  library `FourPointCand`), all `ok`, zero sorry warnings, verifier
  `FPVERIFY ok: True` with no problems, axiom audit ok.
- The six advertised theorems (`F4_eq`, `cover1`, `four_point_cert`,
  `Phi_four`, `four_point_bound`, `four_point_bound_ratio`) each print
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Source hashes (recomputed from this tree on 2026-09-28, equal to the report)

| tree | files | sha256 |
|---|---|---|
| `hunts/ainta_seven_point/lean-four-point` (generated `.lean` files, root module, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) | 51 | `a72e89fc0b5f1d72a41d17ef5f5b7be892b238f15668384dd866382fe8962c82` |
| `lean/bridge` (excluding `.lake`, `.git`, `__pycache__`, `*.log`) | 84 | `a4931d8311da41b1a41cba4f63cda6a0313167bc447ad1674d28159a92f8d2ff` |

The tree hash is the sha256 of the concatenated lines `<file sha256>  <relpath>\n`
over the sorted file list. The Modal preflight (before any Lean) and the final
verify both reported the same two values.

## Files here

| file | what it is |
|---|---|
| `zeta-fourpoint-serial-result-final3.md` | The driver's result report, sanitized copy (two machine-local path appearances replaced, see below). Layer receipts, hashes, raw axiom lines, exact theorem statements, cost. |
| `modal-ap-7zxzQj0YqTwlQUP6P06ecn-client-stdout-stderr-launch-20260928t220203.log` | Complete client stdout and stderr of the final launch, sanitized copy (one machine-local path appearance replaced, see below). It contains the build output of layers 47 to 49 and `FPVERIFY_JSON`, which carries all 49 receipts. |
| `main-axioms-print-output.txt` | The six raw `#print axioms` output lines from `FourPointCand/Main.lean`, byte-exact. Checked equal to the lines in the report and in the log. |
| `SHA256SUMS` | sha256 of the three files above, as published here (the sanitized copies). |

## Sanitization, stated precisely

Exactly three machine-local path appearances were sanitized, by replacing the
operator's home-directory scratch prefix (`/Users/<operator>/.hermes/cache/scratch`)
with the label
`<PRIVATE-LOCAL-SCRATCH>` and changing nothing else:

1. Report line 122: the path of the complete client log.
2. Report line 132: the same path, in the file list.
3. Log line 1528: the path of `serial.py` in the Modal mount line.

The originals remain untouched in the operator's private local scratch
directory. Every other byte is unchanged, including `FPVERIFY_JSON` (49
receipts, no problems), the six axiom lines, the receipt evidence and both
source hashes. This was checked programmatically: substituting the prefix back
into each published file reproduces the original byte for byte. The
`SHA256SUMS` entries for the report and the log therefore differ from the
hashes of the original files.

## How the run was assembled, stated plainly

The build was resumed across several launches, not run in one piece. The final
launch started from saved Modal image `im-pPaMTYiPHyycO7KYBX1zPM`, whose
preflight found 46 receipts (preflight plus layers 1 to 45, `Base` through
`Chunks15`), and built only the last three layers (46 `Boxes`, 47 `Main`,
48 `WholeLibrary`). Its `FPVERIFY_JSON` then re-checked in one container that
all 49 receipts are `ok`, that every `.olean` is unchanged since its layer, that
no olean exists for a target that should not, and that both source hashes still
match.

Where each earlier receipt appears in the older launch logs (read from their
`FPRECEIPT_JSON` lines):

| launch | Modal app | bytes | sha256 of log | receipts in it | driver outcome |
|---|---|---|---|---|---|
| 20260928t111953 | `ap-3cla9s2JFv2UzKNl0WCJQu` | 69626 | `ac20c4c97abc00cf3d818b59d49140bc1d549b055d17cd267c251fab85e1097d` | preflight | |
| 20260928t115223 | `ap-ULRzRcuRMLOoW158yP1vW5` | 100727 | `bc14392f61f2dff8612a0981ca1be40cbf9df08bdb92736ef04a094bdc722cda` | preflight, `Base`, `Cells0`, `Cells1` | |
| 20260928t121506 | `ap-Eanf8DiK6uJkYsAleJtzyi` | 1088216 | `2b346eeed7d9a1272da6d08e708f72526697a97878f766abead5b6ca09350696` | `Cells2` to `Cells25`, `Cells`, `Cover`, `Chunks0` to `Chunks6` | |
| 20260928t161214 | `ap-otcHPDsIV2SQ27GzIZBb5W` | 339322 | `35c65144549e8256cf9b51c602bab9f2014a2c8af7d70ced4746ff5a04525be4` | `Chunks7` to `Chunks15` | client exit 1, no final verify |
| 20260928t185308 | `ap-NcP0sM650cVYfOqTvgBfyg` | 80193 | `b355f8996a59a2f41d186f933281b3a54c61054eb9c4add403685034b43ee6e1` | `Chunks8` (a rebuild) | cancelled by SIGTERM; driver note names `im-pPaMTYiPHyycO7KYBX1zPM` as its last saved image |
| 20260928t182604, 20260928t183632 | `ap-8U7hMDJ9LimVcDGCyJfjhX`, `ap-43xnnIA0ykNtFis00Z2l2l` | 3541, 3291 | not recorded | none | short attempts |

Every layer from `Base` to `Chunks15` has a receipt in at least one of these
logs, so no layer is unaccounted for. Two gaps are stated rather than hidden:

1. These older logs are **not committed** (about 1.7 MB, with failed and
   cancelled attempts). They remain on the operator's machine and are named
   here with hashes so a reader can ask for them.
2. From the logs alone I did not reconstruct the image lineage that put the
   `Chunks9` to `Chunks15` receipts, produced in launch 20260928t161214, into
   image `im-pPaMTYiPHyycO7KYBX1zPM`, which the driver attributes to launch
   20260928t185308. The mechanical guard is the final verifier above: it
   re-hashed the sources and every olean in one container. It is not a
   replay of every layer in one log.

## Scope and limits

- Compile record only. Kernel-checked at the pinned toolchain, by this
  laboratory, on Modal. Pending external verification.
- The theorem statements are those in `FourPointCand/Main.lean` and
  `Cover.lean` and are quoted in the report. The numeric constant
  `(14400000 * HD 1 - 17240) / 14366681` is the one already recorded in
  `../RUNS.md`. Nothing in this bundle changes it.
- The build did not run on GitHub Actions. The `checks` workflow does not
  compile Lean, so a green `checks` run says nothing about this build.
- The cpu.max and memory.max readings in the receipts are "unreadable" (no
  cgroup files in the container); the 2-core, 8 GiB figures are the requested
  Modal resources, not measured limits.
