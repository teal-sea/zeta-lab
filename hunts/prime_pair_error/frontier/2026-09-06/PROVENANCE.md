# Conversation-to-repository provenance — 2026-09-06

This file records the complete research lineage that led to the frontier drafts in this directory.

## Already canonical in Zeta Lab

- PR #181 — CHHL Table 1 replication / first `prime_pair_error` pass.
- PR #186 — residue-class corrections, moduli 1/3/30, exact decomposition and fresh-cutoff tests.
- PR #188 — Wronskian / character-weighted third pass.
- PR #189 — independent written-proof review and repairs for the third pass. This PR was originally closed because its base branch disappeared; on 2026-09-06 the exact author branch was recreated at `37c2a53a`, #189 was reopened, retargeted to `main`, and merged as `d6e9cb5a55d18116433f52c13c20d91db894e55f`.
- PR #191 — `UPPER_BOUND.md`, unconditional total-error upper-bound attempt and explicit unresolved components.

## Conversation-era precursor artifacts

These preceded or informed the canonical passes. Their scientific conclusions are preserved here by provenance even where the raw generated arrays/models are intentionally not promoted into the public hunt.

### Prime reverse-engineering experiment

Original bundle: `prime_reverse_engineering_bundle.zip`.

Contents included a deterministic notebook/scripts, prime-pair predictions, exact-next-gap models, holdout tests, and trillion-scale stress tests. It recovered the known Hardy–Littlewood pair correction, did not claim novelty, and did not produce an exact prime generator. This work is a computational precursor, not part of the analytic upper-bound proof chain.

### Möbius boundary-cancellation branch

Original bundle: `prime_mobius_review_bundle.zip`.

Contains exact/checkable four-number grouping identities, a partner-shortage obstruction for restricted matching rules, a broader matching proposal, and executable checks. It is a separate RH-related investigation and must not be conflated with the CHHL prime-pair upper-bound route.

### Modulo-3 follow-up

Original bundle: `prime_pair_q3_followup.zip`.

Contained an independently derived character-mod-3 correction and period-6 checker. The important mathematics was subsequently re-derived and superseded/integrated by the canonical PR #186. Preserve the precursor as provenance; use #186 as the canonical implementation.

## Frontier drafts preserved in this directory

- `FEASIBILITY.md` — zero-energy feasibility calculation, exact q=1 localization obstruction, and failed naive de-smoothing route.
- `SHARP_TRANSFER.md` — sharp-cutoff transfer for a square-root-scale band.
- `MULTISCALE.md` — multiscale sharp-frequency bounds, rational-region accounting, and general central localization inequality.
- `DIRECT_ATTACK.md` — head-on arithmetic attack on the central prime-counting remainder; records the factorization-feedback null-mode obstruction and a coarse-statistics countermodel.

These are **unreviewed proof drafts** unless a later review says otherwise. They do not improve the completed total `E(N)` bound as of this preservation pass.

## Original lossless conversation handoff

A ZIP assembled before repository preservation had:

- filename: `zeta_frontier_handoff_2026-09-06.zip`
- byte length: `629964`
- SHA-256: `61f4901f8659d13cd2c795b560475b1313db666650da78dabeccd7e03c1807de`

The public scientific residue needed for continued mathematical work is preserved as readable source in Zeta Lab rather than checking a nested binary archive into the hunt. Generated model arrays and other reproducible bulky intermediates remain noncanonical; if a later consumer requires them, regenerate them from the preserved precursor scripts or import them in a dedicated archival PR rather than silently mixing them into the proof record.

## Current frontier

The immediate mathematical obstruction is central: obtain an unconditional upper-bound mechanism that excludes a coherent prime-counting remainder `R(N)=psi(N)-N` above the RH scale. The direct factorization attempt showed that a natural aggregate convolution has Mellin multiplier `zeta(s)` and therefore suppresses precisely zeta-zero-shaped modes; a successful next mechanism must not be blind to those modes.
