# Prime-pair frontier preservation — 2026-09-06

This directory preserves the frontier work produced during the 2026-09-06 continuation of `hunts/prime_pair_error` before the next agent phase.

## Canonical status

- The parent hunt remains the canonical public record for established/reviewed work.
- PR #189 has been repaired, retargeted to `main`, and merged; its independent referee corrections are now canonical.
- The conversation-era frontier drafts preserved here are **not promoted results** unless a later independent review says otherwise.
- None of the new drafts currently improves the completed upper bound on total CHHL `E(N)`.

## Exact handoff archive

`archive/` contains a lossless base64 encoding of `zeta_frontier_handoff_2026-09-06.zip`, split into ordered chunks because the GitHub text API used for this preservation pass cannot upload a binary attachment directly.

Reconstruct from the repository root:

```bash
cat hunts/prime_pair_error/frontier/2026-09-06/archive/part-*.b64 \
  | base64 --decode \
  > /tmp/zeta_frontier_handoff_2026-09-06.zip
sha256sum /tmp/zeta_frontier_handoff_2026-09-06.zip
```

Expected SHA-256:

`61f4901f8659d13cd2c795b560475b1313db666650da78dabeccd7e03c1807de`

The archive contains the original reverse-engineering experiment, Möbius branch, q3 follow-up, zero-energy feasibility draft, sharp-transfer draft, multiscale draft, direct central arithmetic attack, runnable checkers/results, and source text used for the referee/Möbius handoffs.

## Next phase

Before promoting any conversation-era analytic lemma, independently review it. The immediate mathematical frontier is the central prime-counting obstruction: obtain an unconditional upper-bound mechanism that rules out a coherent `R(N)=psi(N)-N` excursion larger than the RH scale, without merely restating RH or using an aggregate identity that annihilates zeta-zero modes.
