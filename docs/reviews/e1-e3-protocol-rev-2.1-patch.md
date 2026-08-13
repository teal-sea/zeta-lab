# REV 2.1 PATCH (four specification holes; patch only — Rev. 2 otherwise unchanged)

## A. Patch 1 — v0 kill / model sensitivity

**Accepted.** The asymmetry in Rev. 2 was inconsistent: success-shaped conclusions required both families, but KILL fired on either. With three runs per cell, a single-family negative is a cell, not a conclusion.

Revised outcome vocabulary (replaces the KILL entry and adds one outcome):

- **KILL (terminal):** in **both** model families, median D ≤ median A on the combined primary set, with both families above the competence floor (Patch 4).
- **MODEL-SENSITIVE (new, non-terminal):** one family shows the expected representation effect (D > A, with or without D > C) and the other does not, both above floor. This is not evidence the effect does not exist; it *is* adverse evidence for a model-independent platform thesis, and the disposition must say both. Treatment: as AMBIGUOUS — one design revision permitted (which may include swapping or adding a model family), then v1 or stop, owner's call. A v1 reached from MODEL-SENSITIVE must pre-register how family disagreement in v1 will be read.

Propagation: preregistration §5 outcome list, decision tree rows "E2 v0: KILL" (now requires both families) and a new row "E2 v0: MODEL-SENSITIVE → treat as AMBIGUOUS; one revision; any v1 must pre-register the family-disagreement reading," and the contract failure clause (Section E below).

## B. Patch 2 — L2 audit and the final D-set

**Audit outcome: the inconsistency is real, and L2 leaves the D-set.**

The hunt-discipline vocabulary test (`tests/test_hunt_probe_discipline.py`) reads prose governance artifacts (the hunts case log and vocabulary rules), not dossier state. Under the two-layer specification it cannot be D-only. The Rev. 2 manifest line "same as C, plus hunt-discipline vocabulary test" was a layer-assignment error, and there is no genuine D-only typed mechanism for L2: nothing in `dossier/` represents hunt claims or handoff content.

The audit also surfaced the general rule Rev. 2 lacked, which resolves this class of question permanently:

> **Layer-assignment rule for tests: a test belongs to the same layer as the artifacts it reads.** A test reading only stable-layer artifacts is stable (identical in A/C/D). A discipline test reading prose governance artifacts (hunt vocabulary, case log) travels with the prose layer: present in **C and D**, absent in A. A test reading dossier state is D-only.

Consequences:

- **Final D-set: {L1, L9, L10}, max 6.** Thin typed coverage is itself a finding and the report states it as such; no replacement machinery is added to inflate the set.
- **L2 remains in the C-set** (final C-set: {L2, L4, L5, L6}, max 8), where it now honestly measures prose discipline vs flat representation — including, in C/D, whether the agent runs and heeds the hunt-discipline test, which is a prose-layer mechanism shared by both.
- The manifest's L2 row is corrected: D column reads "same as C" with no addition.

## C. Patch 3 — E3-B decision rule (frozen operational definition of T > F)

**Accepted with two amendments**, both closing gaming/degeneracy holes rather than changing the shape:

1. **Per-trial binarization.** A profile comparison uses, per arm, the number of its 3 trials containing ≥1 flattening event (0–3). Raw event counts per trial are not compared — a verbose run would otherwise accumulate events and a terse one dodge them. Fewer flattening-trials wins the profile; equal counts tie.
2. **Structural-tie guard.** Some profiles cannot discriminate (e.g. all-strong: "proved" is warranted, flattening is impossible by construction; both arms score 0 and tie). Ties count as wins for neither. If **≥4 of 8 profiles tie in a family**, the profile set is declared insufficiently discriminating for that family — the E3-B analog of BENCHMARK-BROKEN — and the profiles are repaired for v1; no T-vs-F conclusion is drawn from that family.

**Frozen rule (both families independently, each of 8 profiles):** compare the 3 T trials with the 3 F trials by flattening-trial count; T wins a profile on strictly fewer, F symmetrically, equal ties. **T > F is declared iff, in both model families: T wins ≥ 5 of 8 profiles and F wins ≤ 1 of 8.** The same rule with T and B (and F and B) defines T > B and F > B for the interpretation table. Your proposed numbers are kept: with three trials per arm, a per-profile win is weak alone, and ≥5/8 with ≤1 reversal is a plain sign-consistency demand — direction reproduced across most independent evidence profiles with at most one reversal — which is as strong a claim as 48 trials per family can carry without significance theater.

## D. Patch 4 — competence floor

**Accepted as proposed, with the mechanical details fixed now:**

- "Detects a control" means scoring **≥1** (flagged-as-suspicious or better) on that control lesion under the frozen key.
- A **zero-control run** is one of the 9 primary runs in a family (3 conditions × 3 runs) detecting 0 of the 3 controls. It is flagged in the report and voids nothing by itself.
- A **model family is below the competence floor iff ≥5 of its 9 primary runs are zero-control runs.**
- A family below floor: all its cells are void; no KILL, no CANDIDATE-POSITIVE, and no MODEL-SENSITIVE classification may rest on it. If the other family is above floor, its results stand but no both-family conclusion is reachable, so the run outcome is at most AMBIGUOUS; the permitted repair cycle may replace the failed family with another model family. Both families below floor → BENCHMARK-BROKEN.

Why this rule over alternatives: it is per-run and per-family (a single bad sample cannot void a cell), it uses the already-frozen 0/1/2 key (no new judgment), and the majority criterion means a family is only disqualified when incompetence is its typical behavior, not its worst behavior.

## E. FINAL EXPERIMENT CONTRACT DELTAS

Exact replacement language to merge into the Rev. 2 contract:

**1. In "Primary measurements", replace the E2 sentence with:**

> E2: median lesion detection reported as two pre-registered sub-scores — D-set {L1, L9, L10} (max 6) for D-vs-C, C-set {L2, L4, L5, L6} (max 8) for C-vs-A — controls {L3, L7, L8} reported separately under the competence floor rule. Layer-assignment rule for tests: a test belongs to the same layer as the artifacts it reads; prose-discipline tests are present in C and D, dossier tests in D only.

**2. In "What counts as failure", replace the v0 KILL clause with:**

> v0 KILL (terminal) requires median D ≤ median A in **both** model families with both above the competence floor. A negative in one family with the expected effect in the other is MODEL-SENSITIVE: treated as AMBIGUOUS (one revision permitted; a v1 reached this way must pre-register how family disagreement will be read), and recorded as adverse evidence for a model-independent platform thesis but not against the underlying effect.

**3. In "What counts as success", replace the E3-B clause with:**

> E3-B success for the typing claim = T > F under the frozen rule: per family and per profile, arms compared by number of trials (of 3) containing ≥1 flattening event, strictly fewer wins, equal ties; T > F iff T wins ≥5/8 profiles and F wins ≤1/8, independently in both families. ≥4/8 tied profiles in a family voids that family's T-vs-F comparison and sends the profile set to repair for v1. T > B and F > B are defined by the same rule.

**4. In "Frozen before first run", append:**

> …; the competence-floor rule (a control counts as detected at score ≥1; a family is below floor iff ≥5 of its 9 primary runs detect zero of the three controls; a below-floor family's cells are void, may support no outcome classification, and may be replaced by another model family in the single permitted repair cycle; both families below floor is BENCHMARK-BROKEN); and the E3-B win rule of clause 3.

**5. In the outcome vocabulary (preregistration §5), insert after CANDIDATE-POSITIVE:**

> **MODEL-SENSITIVE** — the expected representation effect appears in one family and not the other, both above floor. Non-terminal; treated as AMBIGUOUS for promotion purposes; recorded as adverse to platform model-independence, neutral to the underlying effect.

No other Rev. 2 language changes. Patches B–D introduce no new machinery and remove one lesion from one sub-score; Patch A strictly weakens what v0 may conclude, in the kill direction only.
