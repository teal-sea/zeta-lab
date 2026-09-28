# Frozen research checkpoint: adaptive correction block v1

**Snapshot ID:** `zeta-adaptive-freeze-v1`  
**Research lineage:** continuation of the 2026-09-06 Zeta Lab investigation.  
**Purpose:** pause research and preserve the evidence through `adaptive_correction_block.zip`.

This is an archival checkpoint, not a theorem registration, acceptance of an unreviewed proof, or a declaration of progress toward RH. No new mathematical experiment was run for this freeze. The values and proof claims below are attributed to their original packages or the separate repository reviews. This document does not silently strengthen those claims.

## 1. The stopping point

The latest producing-session package is `latest_extracted/adaptive_correction_block/`. Its main document is `BLOCK_CORRECTIONS.md`. It records a block of 23 masked reciprocal-carry corrections, their 82 positive repairs, their explicit tail shield, and the resulting factorial upper bound.

The package records:

| Quantity | Recorded value or claim |
|---|---|
| Starting leading constant | 1.04590351044777009789513972597752956057210283983286... |
| New leading constant | 1.03411910424755277273462747901643856176993858443824... |
| Actual leading-constant saving | 0.01178440620021732516... |
| Sufficient saving before constructing repairs | 0.0114171274843133750... |
| Corrections selected | 23, from a 39-variable block after 1,065 exploratory proposals |
| Nonzero raw deficits | 498 |
| Positive repairs actually used | 82 |
| First-level combined coefficient mass | 28306/27 |
| Additional shield for this block | 2633/108 |
| Accumulated direct, single-lift shield | 3281/108 |
| Original double-lift shield, unchanged | 701/36 |
| Claimed full-envelope comparison | Better than the preceding envelope for every integer N >= 10^6 |
| Unfavorable comparison retained | At N = 10^4 the actual factorial certificate improves, but the conservative envelope worsens |

These are not all the same sort of evidence. The package contains a written general argument, exact finite feasibility and logarithm checks, and a separate-code self-check from the producing session. **There has been no separate-agent or human review of this adaptive block, the preceding repair-cost rule, or the support-obstruction continuation in this handoff.** PR #200 reviewed the earlier joint candidate only.

The reported removal of about 25.7% refers to this particular construction's leading excess C-1. It is not a percentage of RH solved. A fixed leading constant greater than one is not the required square-root-scale error bound.

## 2. Objectives and mathematical boundaries

The original investigation studied the total CHHL prime-pair squared error. The last completed laboratory upper-bound report reproduced the classical logarithmic-saving level rather than obtaining its desired near-quadratic bound. The Wronskian A/B work and the later factorial-certificate work must not be relabeled as improvements to that total error.

The factorial branch instead builds explicit upper certificates B(N) for the von Mangoldt weighted count psi(N). Its long-term sufficient target is a family of certificates with B(N) <= N + O_epsilon(N^(1/2+epsilon)) for every epsilon > 0 at all sufficiently large integer cutoffs. The source notes identify that as RH-sufficient, not as a weakened preliminary milestone.

No package in this freeze establishes a family with the necessary uniform refinement rate. No novelty, optimization optimality, modern prime-counting record, Lean verification, or completed bound on total CHHL E(N) is claimed for the latest continuation. The task at this checkpoint is preservation, not choosing a new criterion or asserting a successful route is already complete.

## 3. Chronology since the preceding cumulative checkpoint

### 3.1 Reviewed combined-weight baseline

The earlier cumulative checkpoint and its three runnable packages were imported by PR #198, merged at `9ec3b6b3b86c25e256ce605f5116fbda3cbc7689`. The separate baseline review in PR #199, head `96ce564c89a38a89a4a28da61d28d335679d4efb`, reports that the all-cutoff construction survives without mathematical repair.

Its leading constant is about 1.0486636637932206, finite mass 2641/3, and tail coefficient 15. Its seed can be negative at some positions; the final lifted weight, not each separate contribution, is what must majorize one. The independent reviewer checked the prefix-plus-tail implication, signed-seed integrability, factorial identity, error budget, and the restricted fixed-recipe ceiling.

### 3.2 Reviewed joint candidate

`original_archives/joint_correction_candidate.zip` preserves the coordinated nine-amplitude candidate. PR #200, head `85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38`, reports SURVIVES. It records C about 1.0476239313792679, finite mass 56345/108, tail multiplier 701/36, and 172 repair locations from the prior allowed list of 411.

Composite correction starts are legitimate under the stated carry hypotheses. The reviewer identified a missing assertion in the producer script: kappa(D)>0, needed when discarding geometric tails. The reviewer checked it with margin and added an assertion in the independent checker. The original candidate bytes remain unchanged. That review is not a review of subsequent work.

### 3.3 Repair-support obstruction and a direction test

`latest_extracted/joint_support_analysis/SUPPORT_OBSTRUCTION.md` records an exact restriction imposed by the old list of allowed repair locations. The combination of the constraints at 13 and 220 forces the amplitude at 20 to vanish in that restricted search, leaving W(20)=3. This is a statement about the constrained construction, not a general impossibility theorem.

The package tests introducing new repair locations for a correction at 20. It lowers the recorded leading constant to about 1.0469800114 but increases complexity. Its complete conservative envelope is not better at every small cutoff. **This direction test is not the baseline on which the later adaptive block was built.** Its result and the obstruction are both preserved.

### 3.4 Direct final-weight repair-cost rule

`latest_extracted/repair_cost_rule/REPAIR_COST.md` records a general bound on the bill for positive repairs. Given an original deficit d_n, earlier nonnegative repairs cannot increase the shortfall at n, so the eventual greedy repair satisfies 0 <= lambda_n <= d_n. This supplies the weighted bill bound sum lambda_n k_n <= sum d_n k_n.

The corresponding sufficient gain compares the correction's weighted integral against the initial-deficit allowance and the entire new tail-protection cost. These corrections act on the final weight directly, rather than being automatically copied at every radix-15 scale.

Two accepted direct corrections, at 20 and then 21, give the recorded leading constant 1.0459035104477701... . The next attempt at 20 is rejected: making that cell flatter worsens the overall construction under the tested repair. Failure of the sufficient test is not claimed to prove all possible repairs impossible. The accepted state, rejected diagnostic, construction code, logs and self-checks are retained.

### 3.5 Adaptive reciprocal carries and masks

The adaptive block permits integer reciprocal triples with 1/a=1/b+1/c, rather than only the previous consecutive-denominator shape. For each triple it also chooses a mask from 1,2,6,30,210. The reciprocal carry is a zero-or-one floor-function carry; the masked correction may be signed.

The new draft reduces the global masked-carry bound to a finite table for coprime counts modulo the mask. It records H_1=1, H_2=1, H_6=1, H_30=2 and H_210=3, with a derivation that is independent of the size of the chosen reciprocal triple. It then uses a shared deficit bill to choose the whole block, rather than adding individual savings as though no corrections competed for the same slack.

The source explicitly calls the search exploratory. It retains all 1,065 scout rows, selection data, frozen rational amplitudes, and an alternative envelope-oriented candidate. The rounding procedure recomputes deficits and validates the actual rational construction; numerical optimizer success is not treated as proof of feasibility or optimality.

## 4. Exact latest accounting: do not mix the two shields

The adaptive document's notation is retained. Let l_N=1+log N, S1 be the radix-15 level sum, S1_R the shifted single-lift level sum, and S2 the shifted double-lift level sum. Empty sums are zero. The recorded sufficient envelope is

    U_new(N) = C_new N
      + (28306/27) l_N
      + (56345/108) [S1(N)-l_N]
      + (3505/12) S2(N)
      + (16405/36) S1_R(N).

The complete formulas, signs, truncation conditions and proof of the claimed eventual comparison are in `BLOCK_CORRECTIONS.md` Section 7. The old double-lift shield remains unchanged. The newer direct corrections accumulate a different, single-lift shield. Replacing both by one combined coefficient would change the construction and is not permitted as a transcription shortcut.

Geometric tails are discarded only after the relevant positive kappa hypotheses have been checked. Finite coefficient mass, leading constant, and the exact factorial expression are different quantities. Earlier objective experiments demonstrated that optimizing a loose sufficient allowance can move the actual factorial expression the wrong way; this distinction remains part of the record.

## 5. Evidence retained, and what was checked for this freeze

The adaptive package records 99,999 prefix checks, 90,082 residue-table cases, 1,088,718 full-period cells, and 1,532 factorial prime-exponent identities. These are the producing session's recorded checks. This freeze does not claim to rerun them or convert them into an independent proof review.

This preservation pass instead checked:

- All 17 available original ZIPs are copied unchanged into `original_archives/`.
- All direct and recursively nested ZIP members are read, CRC-checked, inspected for unsafe paths, duplicates, links and encryption, and inventoried by size and SHA-256.
- The latest three packages are extracted byte-identically into runnable directories.
- Their own nonempty SHA256SUMS manifests match their files, with each manifest's actual size-key convention respected.
- Four explicit nested input links match the independently available original archives byte for byte.
- The four newly stored standalone Library archives were read back into a separate directory and matched against the originals.
- The new snapshot verifier is exercised against missing, truncated, corrupt, unlisted and invalid-manifest material before handoff. The separate final receipt records the actual outcomes.

No result JSON, original ZIP, source note or research script has been rewritten. No screenshot or private device state is claimed as research data. Historic notes saying "not pushed" retain their original wording; dated storage addenda, not edits to old evidence, should describe later imports.

## 6. Recovery map

`original_archives/zeta_research_checkpoint_2026-09-06.zip` is the earlier cumulative freeze, unchanged. It and the other originals preserve the initial reverse-engineering, separate Mobius branch, modulo-3 work, zero-energy, sharp-transfer, multiscale, central-obstruction and factorial-certificate lineage.

The latest chain is:

    reviewed joint candidate (#200)
      -> support-obstruction diagnostic (separate direction test)
      -> repair-cost rule, accepted direct steps at 20 and 21
      -> adaptive correction block, 23 corrections and 82 repairs

The actual nested inputs are pinned in `LOCAL_VALIDATION.json`. The adaptive ZIP contains the repair-cost ZIP; that contains the support-analysis ZIP; that contains the original joint-candidate and route-test ZIPs. Copies overlap intentionally. Do not deduplicate or recompress the originals.

`IMPORT_MAP.json` gives the three new runnable package destinations. `REPO_STATE.json` records the commit references for repository-only research and reviews. Those review/experiment PRs are not mirrored byte for byte inside this backup; their exact commits remain on GitHub. This is not a full Git mirror or a backup of unseen uncommitted desktop files.

## 7. Registration and handoff boundary

The snapshot ID and hash inventories register the artifact version. They do not register a theorem with Palomar, an external registry or a journal. No such submission is authorized or made by this freeze.

The current Library destination is `/Zeta Lab/Research snapshots/adaptive-block-v1/`. A repository preservation PR is the remaining handoff task for Claude in the local checkout. Until that PR is merged and its bytes are checked from a clean clone of main, do not describe the latest archives as being on main.

Keep PRs #196, #199 and #200 in their existing review states. In particular, archiving their references does not authorize merging them. Preserve the older A/B review and do not reopen it. Preserve rejected diagnostics and alternative candidates alongside the retained block.

After the checkpoint is imported and checked from a clean clone, the agent may create a non-overwriting Git snapshot tag `research/adaptive-block-v1`. It must point to the verified preservation commit and must not be a mathematical release announcement. Conflicting tags must be reported, not force-moved.

## 8. The unresolved question at the pause

The next scientific question, not an assignment to run during preservation, is whether profitable correction blocks continue to exist with controllable coefficient and shield growth as the remaining excess decreases. One accepted block does not prove that rate. No new window, criterion switch, optimizer run, agent fleet or formalization pass is started here.

The next independent mathematical review should cover the post-#200 support/repair/adaptive chain and its exact stated obligations. It should not be conflated with byte-integrity verification or the already-completed reviews of earlier constructions.
