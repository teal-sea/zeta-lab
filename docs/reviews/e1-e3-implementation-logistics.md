# E1–E3 Implementation Logistics (post-signature; still planning — nothing built yet)

Contract = Rev. 2 + Rev. 2.1 patch. This document adds no rules; it sequences the work and specifies the one procedure the contract references but does not define: blind lesion authoring by the consultant.

## 1. Blind lesion-authoring procedure (the consultant's two instances)

**The conflict to resolve first.** The contract gives the consultant two roles that collide: (a) author two lesion instances *without seeing the other planted lesions*, and (b) audit the full condition × lesion manifest for fact parity — which reveals every lesion. Resolution is sequencing plus a hash commitment:

1. **Owner sends the consultant** (before anything is planted): the frozen-HEAD *clean* snapshot (no lesions), the two-layer condition specification, the underlying-fact-statement format, the answer-key format with the frozen 0/1/2 boundary definitions, and the two lesion **classes** assigned to them — one PRIMARY (their choice of an L-class from the primary list, applied as a fresh instance) and one CONTROL class. Nothing else.
2. **File-space partition, agreed in advance.** Owner and consultant exchange lists of the files/directories each will touch, chosen so they don't intersect. Neither sees the other's diffs; the partition list itself reveals only locations, not content. If a partition can't be agreed without hinting (e.g. both need HANDOFF.md), the consultant's lesion is placed in a stable-layer scratch artifact instead and the owner adjusts nothing.
3. **Consultant authors blind:** for each of their two lesions — the underlying-fact statement, the per-condition representations (for the primary one), the plant diff against the clean snapshot, and the answer-key entry (correct diagnosis + the 1-vs-2 boundary). They send the owner **only a SHA-256 hash** of the bundle.
4. **Owner plants their eight**, writes their answer-key entries, and commits a hash of their own bundle to the consultant symmetrically.
5. **Reveal + parity audit.** Both bundles are exchanged and checked against the committed hashes. Only now does the consultant see the full manifest and run the fact-parity audit (their own two lesions are already frozen by hash, so the audit can't leak backward into their authoring). Owner audits the consultant's two for parity in return.
6. **Merge + freeze.** Owner merges all diffs into the three condition snapshots via the snapshot script; the complete answer key, fact list, and manifest are frozen and their hashes recorded in the prereg document; both parties sign.

Scorer note: the consultant as second scorer sees the full key anyway — that's fine, scoring happens after all runs are complete, and the key is frozen long before.

## 2. Order of operations (nothing starts before the signature)

1. Sign contract (Rev. 2 + 2.1).
2. **E1 starts immediately** — it needs only `conjectures/INTERVENTIONS.md` (schema + taxonomy + the `f47a490` calibration example) and the JSONL file in the private ledger repo. It runs passively alongside normal lab work from day one; nothing else waits on it.
3. Freeze the E2 HEAD hash (before any E3-A tripwire work — the Rev. 2 sequencing constraint).
4. Blind-authoring procedure (§1), producing frozen fact list, manifest, key.
5. Prereg document assembled (all frozen items + outcome vocabulary + thresholds-to-be-set-at-v1 note), hashes recorded, both signatures.
6. Snapshot script + three condition exports built and spot-checked against the manifest (stable layer byte-identical: verify by directory hash).
7. E2 v0 runs (launch checklist; owner does not interact post-launch), then scoring under the frozen key.
8. E3-A tripwire extensions + hash-before/after falsity check (public-tree tests; each justified as an ordinary lab test).
9. E3-B trials (144 prompts, can interleave with anything).
10. Disposition written into ROADMAP.md in the hunt-disposition idiom, whatever the outcomes.

## 3. Who holds what

| Artifact | Holder | Visibility |
|---|---|---|
| Clean frozen snapshot | both | shared |
| Owner's 8 lesion diffs + key entries | owner | consultant sees at reveal (step 5) only |
| Consultant's 2 lesion diffs + key entries | consultant | owner sees at reveal only |
| Hash commitments | both | exchanged before reveal |
| Frozen prereg (fact list, manifest, key, rules) | both, signed | fixed thereafter; repairs land in v1 only |
| Run transcripts + reports | owner | consultant receives reports for second-scoring |
| E1 intervention JSONL | owner (private ledger repo) | consultant sees aggregates, not raw lines, unless owner shares |

## 4. What remains undecided (owner calls, needed before step 6)

- Which two model families run v0 (the contract only requires two; pick before prereg signature so the familiarity probe can run cold).
- Which primary L-class the consultant instantiates.
- Where the private fork lives (any private remote; it never touches the public tree).

Nothing else in the protocol is open.
