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

**Fail-closed rule:** the archive is not considered verified merely because chunk files exist or an upload call succeeded. It is verified only when reconstruction produces the expected SHA-256. `tests/test_prime_pair_frontier_archive.py` enforces this invariant and also checks that the three precursor bundles named in `PROVENANCE.md` are actually inside the reconstructed ZIP.

The archive contains the original reverse-engineering experiment, Möbius branch, q3 follow-up, zero-energy feasibility draft, sharp-transfer draft, multiscale draft, direct central arithmetic attack, runnable checkers/results, and source text used for the referee/Möbius handoffs.

## Next phase and scope

Before promoting any conversation-era analytic lemma, independently review it.

The endpoint target

`psi(x) - x = O_epsilon(x^(1/2+epsilon))` for every `epsilon > 0`

is itself an RH criterion (and under RH one has the standard stronger logarithmic form). It is therefore **not** a merely RH-adjacent intermediate target. Any partial result must be stated at the strength actually proved — for example a fixed power saving, a restricted frequency range, or a conditional implication — rather than described as progress to the full square-root bound unless it genuinely supplies such progress.

`DIRECT_ATTACK.md` records the current wall in the head-on route: the aggregate factorization-feedback operator tested there annihilates zeta-zero-shaped modes, so that mechanism cannot by itself control the dangerous coherent excursion. The next phase should seek an arithmetic mechanism that is sensitive to those modes and yields an unconditional upper bound, while preserving the total-`E(N)` accounting from `UPPER_BOUND.md`.
