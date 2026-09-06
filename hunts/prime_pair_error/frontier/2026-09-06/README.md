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
