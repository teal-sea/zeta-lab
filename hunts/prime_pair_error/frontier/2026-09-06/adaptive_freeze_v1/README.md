# Frozen research checkpoint: adaptive correction block v1 (preserved 2026-09-06)

Snapshot ID `zeta-adaptive-freeze-v1`. This directory is **storage**. Thomas paused the
research and asked for the evidence to be preserved; nothing here was reviewed, promoted
or extended by the pass that imported it, and importing a package does not promote its
mathematics.

The narrative is `provenance/FREEZE.md`, written by the originating session and copied
here unchanged. Read that first. This file says where the bytes are, what was checked
mechanically, and what remains unreviewed.

## The archive

`archive/zeta_adaptive_freeze_v1.zip` is the downloaded package, committed unchanged as a
binary. `archive/SHA256SUMS` carries its hash.

| | |
|---|---|
| Bytes | 4,185,414 |
| SHA-256 | `a264da2d6da781a3133ab75557f22842fe2581e210c7a628c0fddeff0c653681` |

Verify from the repository root:

```bash
cd hunts/prime_pair_error/frontier/2026-09-06/adaptive_freeze_v1/archive
shasum -a 256 -c SHA256SUMS
```

`tests/test_adaptive_freeze_archive.py` pins the hash and byte count independently of the
sidecar, so the file, the sidecar and this README cannot drift apart silently. It also runs
the archive's own verifier on a scratch extraction and byte-compares every imported file
against its archive member.

## Layout

```
adaptive_freeze_v1/
  README.md            this file, written in the repository
  archive/             the outer ZIP, unchanged, plus its SHA256SUMS sidecar
  provenance/          the archive's own top-level files, copied byte for byte
```

`provenance/` holds nine files exactly as the archive carries them: `FREEZE.md`,
`CLAUDE_HANDOFF.md`, `README.md` (the snapshot's own, not this one), `FILE_MANIFEST.json`,
`ARCHIVE_CONTENTS.json`, `IMPORT_MAP.json`, `REPO_STATE.json`, `LOCAL_VALIDATION.json` and
`verify_freeze.py`.

**Their paths are relative to the archive root, not to this directory.** `IMPORT_MAP.json`
names `original_archives/...` and `latest_extracted/...`, which exist inside the ZIP and
not beside it; `verify_freeze.py` expects to run against an extraction of the ZIP, with
`--root` pointing at the extracted `zeta_adaptive_freeze_v1/`. That layout is described
here rather than repaired, because rewriting an inventory to match a new location edits
the evidence. `REPO_STATE.json` likewise records the PR states observed when the snapshot
was sealed; the live states at import time are in the table below.

The archive carries **17 original research ZIPs**. Three of them are already committed
elsewhere in this tree and are byte-identical to the copies inside:
`zeta_frontier_handoff_2026-09-06.zip` (`../archive/`),
`factorial_certificate_pilot.zip` (`../factorial_certificate_pilot/archive/`) and
`zeta_research_checkpoint_2026-09-06.zip` (`../checkpoint/archive/`). The overlap is
deliberate. Do not deduplicate or recompress the originals.

## The three imported packages

`provenance/IMPORT_MAP.json` names three destinations, all one level up beside the earlier
imports. Each was extracted from the nested original ZIP inside the committed archive, so
the imported bytes are the original package bytes:

| Package | Files | Main document |
|---|---|---|
| `../joint_support_analysis/` | 22 | `SUPPORT_OBSTRUCTION.md` |
| `../repair_cost_rule/` | 12 | `REPAIR_COST.md` |
| `../adaptive_correction_block/` | 18 | `BLOCK_CORRECTIONS.md` |

No destination existed before this import, so nothing was overwritten and no difference
had to be resolved. No vocabulary substitution was needed either: none of the 52 files
carries the reserved word, so the imported copies are byte-identical to the originals with
no documented edit. Each package's own `SHA256SUMS.json` lists every one of its files
except itself, and all three verify. Two of the three manifests key size as `bytes` and
one (`repair_cost_rule`) keys it as `size`; both conventions are read, neither is
rewritten.

The recorded outputs in these directories are the originals. Rerun the scripts into new
output files rather than over them.

## Chronology since PR #198

The lineage, as `provenance/FREEZE.md` §3 records it:

```
reviewed combined-weight baseline (#199)
  -> reviewed joint candidate (#200)
    -> support-obstruction diagnostic (separate direction test)
      -> repair-cost rule, accepted direct steps at 20 and 21
        -> adaptive correction block, 23 corrections and 82 repairs
```

1. **Reviewed baseline.** The earlier cumulative checkpoint landed as PR #198, merged at
   `9ec3b6b3b86c25e256ce605f5116fbda3cbc7689`. The baseline review in PR #199, head
   `96ce564c89a38a89a4a28da61d28d335679d4efb`, reports the all-cutoff construction
   survives without mathematical repair.
2. **Reviewed joint candidate.** PR #200, head
   `85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38`, reports SURVIVES for the coordinated
   nine-amplitude candidate. The reviewer found a missing `kappa(D)>0` assertion in the
   producer script, checked it with margin, and added the assertion in the independent
   checker rather than in the candidate. The candidate bytes are unchanged.
3. **Support obstruction.** `joint_support_analysis/` records that the inherited repair
   dictionary forces the amplitude at 20 to vanish, leaving `W(20)=3`. That is a statement
   about the constrained construction, not a general impossibility theorem.
4. **Repair-cost rule.** `repair_cost_rule/` bounds the greedy repair bill by the initial
   deficits and applies corrections to the final majorant directly. Two steps, at 20 and
   then 21, lower the leading constant to `1.04590351044777010...`.
5. **Adaptive block.** `adaptive_correction_block/` selects 23 masked reciprocal-carry
   corrections from a 39-variable block, uses 82 positive repairs, and records a new
   leading constant of `1.03411910424755277...`.

## Review status: the last three stages are unreviewed

**This is the load-bearing line.** The reviews in #199 and #200 apply only to the earlier
objects they name. Neither covers the support-obstruction diagnostic, the repair-cost rule
or the adaptive block. The producing session's own `checks.json` says so in its own status
string: `"PASS: separate-code self-check, not an independent-agent or human review"`.

| Stage | Review status |
|---|---|
| Combined-weight baseline | reviewed, PR #199, survives |
| Joint correction candidate | reviewed, PR #200, survives |
| Support-obstruction diagnostic | **not independently reviewed** |
| Repair-cost rule and the steps at 20 and 21 | **not independently reviewed** |
| Adaptive correction block | **not independently reviewed** |

PR states observed at import time on 2026-09-06, by query rather than read from the
snapshot, with the head commits preserved so the refs survive independently of GitHub:

| PR | State at import | Head | Role |
|---|---|---|---|
| #196 | open | `46fdb433752a1b26abba516fc24d6db21543b2b8` | full-cost versus direct `B_N` objective comparisons |
| #198 | merged | `3e39e21799e84affd132399fd0a62006d9f8f6d1` | the preceding cumulative preservation |
| #199 | open | `96ce564c89a38a89a4a28da61d28d335679d4efb` | baseline review, survives |
| #200 | open | `85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38` | joint-candidate review, survives |

This preservation pass changed none of them, and archiving a reference does not authorize
merging it. The same table, as the snapshot recorded it when sealed, is in
`provenance/REPO_STATE.json`.

## What was checked, and what was not

Checked mechanically in this pass, all byte-level:

- The download's size and SHA-256 match the values supplied with the handoff, before
  extraction.
- The ZIP carries no absolute path, no `..` traversal, no symlink and no encrypted member.
- The shipped `verify_freeze.py`, run on a scratch extraction, reports PASS with 85 payload
  files, 17 original archives, 558 recursive archive member occurrences and 52 extracted
  files.
- All 52 imported files equal both the archive's own extraction and the member of the
  corresponding nested original ZIP.
- The four nested dependency links in `LOCAL_VALIDATION.json` hold: the adaptive block's
  input ZIP is the standalone repair-cost ZIP, whose input is the standalone
  support-analysis ZIP, whose inputs are the standalone joint-candidate and route-test
  ZIPs, byte for byte in each case.
- The three originals also committed elsewhere in this tree are identical to the copies
  inside the archive.

**Not** checked, and not claimed: the mathematics. The adaptive package records 99,999
prefix checks, 90,082 residue-table cases, 1,088,718 full-period cells and 1,532 factorial
prime-exponent identities. Those are the producing session's recorded counts. This pass did
not rerun them, and byte integrity is not a proof review.

## Limitations recorded with the block

Kept here because a preserved result that loses its caveats is worse than an unpreserved
one:

- The reported reduction of about 25.7% is a fraction of **one construction's leading
  excess** `C-1`. It is not a percentage of RH solved, and a fixed leading constant greater
  than one is not the required square-root-scale error bound.
- No package in this freeze establishes a certificate family with the necessary uniform
  refinement rate. The RH-sufficient target named in the source notes is
  `B(N) <= N + O_epsilon(N^(1/2+epsilon))` for every epsilon, at all sufficiently large
  cutoffs.
- The full-envelope improvement is claimed for every integer `N >= 10^6`. At `N = 10^4` the
  actual factorial expression improves but the conservative envelope worsens, and that
  unfavorable comparison is retained rather than dropped.
- The two shields are different quantities and must not be merged. The old double-lift
  shield stays `701/36`; the newer direct corrections accumulate a single-lift shield of
  `3281/108`. Replacing both by one combined coefficient would change the construction.
- Nothing here improves the completed upper bound on total CHHL `E(N)`, and no novelty,
  optimality, prime-counting record or formal verification is claimed.

## Rejected trials and alternatives, retained

- **A third step at 20**, after the accepted steps at 20 and 21, fails the sufficient test:
  the particular greedy construction increases the leading coefficient. It was run as a
  negative-control diagnostic and is not retained in the accepted state, but the diagnostic
  itself is preserved in `repair_cost_rule/`. Failure of the sufficient test is not a proof
  that all repairs there are impossible.
- **The direction test** in `joint_support_analysis/` introduces new repair locations and
  reaches about `1.0469800114`, but its complete conservative envelope is not better at
  every small cutoff. It is **not** the baseline the adaptive block was built on. Both it
  and the obstruction are preserved.
- **An envelope-oriented alternative** to the selected block is kept beside it as
  `adaptive_correction_block/alternative_envelope_candidate.json` (`H = 289/12`, actual
  `C ~ 1.0342645`), against the selected gain-policy block (`H = 2633/108`, actual
  `C ~ 1.0341191`). All 1,065 exploratory scout rows are kept in `scouting_scores.json`.
  The source calls the search exploratory; optimizer success is not treated as proof of
  feasibility or optimality.

## Registration

The snapshot ID and the hash inventories register an artifact version and nothing more.
This is not a Palomar entry, a journal submission, a novelty claim or an RH announcement,
and no such submission is authorized by it. The Git tag `research/adaptive-block-v1` marks
the verified preservation commit; it is a storage marker, not a release.

## The open question at the pause

Whether profitable correction blocks keep existing with controllable coefficient and shield
growth as the remaining excess shrinks. One accepted block does not establish that rate.
No new search, optimizer run or formalization pass was started here, and the next
independent review should cover the post-#200 support, repair and adaptive chain against
its own stated obligations.
