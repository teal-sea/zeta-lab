# Prime-pair frontier preservation — 2026-09-06

This directory preserves the frontier work produced during the 2026-09-06 continuation of `hunts/prime_pair_error` before the next agent phase.

## Canonical status

- The parent hunt remains the canonical public record for established/reviewed work.
- PR #189 has been repaired, retargeted to `main`, and merged; its independent referee corrections are now canonical.
- The conversation-era frontier drafts preserved here are **not promoted results** unless a later independent review says otherwise.
- None of the new drafts currently improves the completed upper bound on total CHHL `E(N)`.

## Exact handoff archive

`archive/zeta_frontier_handoff_2026-09-06.zip` is the lossless handoff archive, committed
directly as a binary. `archive/SHA256SUMS` carries its hash, and
`tests/test_frontier_archive.py` checks on every run that the file is present, that its
SHA-256 matches the value below, and that every member listed in the archive's own
`SHA256SUMS.json` is inside it with the recorded hash and size.

Verify from the repository root:

```bash
sha256sum -c hunts/prime_pair_error/frontier/2026-09-06/archive/SHA256SUMS
```

Expected SHA-256:

`61f4901f8659d13cd2c795b560475b1313db666650da78dabeccd7e03c1807de`

**Correction, 2026-09-06.** The first version of this section described `archive/` as a
set of base64 chunks (`part-*.b64`) written through the GitHub text API, with a
reconstruction command. That upload never landed: `archive/` did not exist on `main` or on
any branch, and the documented command produced an empty file whose hash is the hash of
zero bytes. The archive was re-supplied from the originating session's attachment and
committed as the binary above; the hash it was expected to have is the hash it has. The
test exists so that a documented archive can no longer be missing without the suite
saying so.

The archive contains the original reverse-engineering experiment, Möbius branch, q3
follow-up, zero-energy feasibility draft, sharp-transfer draft, multiscale draft, direct
central arithmetic attack, runnable checkers/results, and source text used for the
referee/Möbius handoffs. Its own `MANIFEST.md` and `SHA256SUMS.json` inventory the
members. One line in that manifest is stale by construction: it records PR #189 as closed
unmerged, which was true when the archive was sealed and is not now (see `PROVENANCE.md`).
The archive is evidence and is not edited to catch up.

## Next phase

Before promoting any conversation-era analytic lemma, independently review it. The immediate mathematical frontier is the central prime-counting obstruction: obtain an unconditional upper-bound mechanism that rules out a coherent `R(N)=psi(N)-N` excursion larger than the RH scale, without merely restating RH or using an aggregate identity that annihilates zeta-zero modes.

## Factorial-certificate pilot (preserved and reviewed 2026-09-06)

`factorial_certificate_pilot/` preserves a separate downloaded attachment,
`factorial_certificate_pilot.zip`, hash-pinned in its own `archive/SHA256SUMS` and by
`tests/test_factorial_pilot_archive.py`. It is a Chebyshev-type factorial upper certificate
for psi(N) with an LP-chosen seed: 87 exact-rational certificates, all reproduced. The
independent review is `factorial_certificate_pilot/REVIEW.md`; the review's own checker and
its output live in `factorial_certificate_pilot/review/`. It is a pilot, not a prime-counting
record and not an RH result, and it does not touch the A/B referee record above.

## Cumulative research checkpoint and the three newest packages (preserved 2026-09-06)

`checkpoint/` is the research checkpoint: `checkpoint/CHECKPOINT.md` is the narrative
(chronology, claim grades, failed methods, open questions), `checkpoint/README.md` says
where every original byte lives, and `checkpoint/archive/zeta_research_checkpoint_2026-09-06.zip`
is the cumulative archive itself, committed unchanged and hash-pinned by its sidecar and by
`tests/test_research_checkpoint_archive.py`. It bundles all twelve original research ZIPs,
including the two already committed above, and its own verifier.

The three newest packages it carries are imported beside it as runnable working
directories, byte for byte: `certificate_structural_step/` (omitted-prime obstruction and
the period-30030 extension), `certificate_refinement_rule/` (positive repair rule, five
applications, full error budget) and `certificate_route_test/` (fixed-recipe ceiling and
the combined-weight repair; its `aggregate_results.json` is the current candidate baseline).
They are archived, unreviewed source packages, not promoted results, and none of them bears
on RH. Rerun them into new output files; the recorded outputs are the originals.

## Adaptive correction block freeze, and the research pause (preserved 2026-09-06)

`adaptive_freeze_v1/` is the checkpoint taken when Thomas paused the research. Its
`README.md` is the repository's account of what landed; `adaptive_freeze_v1/provenance/FREEZE.md`
is the originating session's narrative, copied unchanged. The archive itself is
`adaptive_freeze_v1/archive/zeta_adaptive_freeze_v1.zip`, committed unchanged, hash-pinned by
its sidecar and independently by `tests/test_adaptive_freeze_archive.py`:

`a264da2d6da781a3133ab75557f22842fe2581e210c7a628c0fddeff0c653681` (4,185,414 bytes)

It bundles seventeen original research ZIPs, which include the three already committed
above, and its own verifier. Three further packages are imported beside the earlier ones as
runnable working directories, byte for byte from the nested originals:
`joint_support_analysis/` (why the inherited repair dictionary freezes the weight at 20),
`repair_cost_rule/` (the repair-potential bound and the accepted direct steps at 20 and 21)
and `adaptive_correction_block/` (23 masked reciprocal-carry corrections, 82 positive
repairs).

**All three are unreviewed drafts.** The reviews in PR #199 and PR #200 cover only the
earlier objects they name: the combined-weight baseline and the joint correction candidate.
Neither covers the support-obstruction diagnostic, the repair-cost rule or the adaptive
block, and the producing session's own `checks.json` records its result as a separate-code
self-check rather than a review. Storing them does not promote their mathematics, the
reported reduction is a fraction of one construction's leading excess rather than progress
on RH, and nothing here improves the completed upper bound on total CHHL `E(N)`. The
rejected third step at 20, the direction test that is not the block's baseline, and the
envelope-oriented alternative candidate are all preserved alongside the accepted state.
