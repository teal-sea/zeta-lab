# Pre-registration: rerun of target B on an omega grid (hunt #152)

Committed on 2026-10-26 in its own commit, before any rerun result exists. The
failed gate at omega = 727.95134 (RESULTS.md section 6) stays recorded as it is,
whatever this rerun finds.

## Hypothesis H

Revers's subsection 6.3 omega, printed "\omega=727.95134", is the
Saouter-Demichel 2010 value 727.951335792 (his own history table) rounded to
five decimals. His S* = -1.002922947193156 was computed at 727.951335792.

## Fixed in advance

- Parameters, unchanged from target B: alpha = 6e12, A = 6.85e7,
  T = 10379600 (N(T) = 22,000,000), sum as in `skewes_terms.lehman_sum`
  (Revers Theorem 3.1, both terms), zeros from Arb at 64 bits, sums at 128 bits.
- **Decisive evaluation points**: omega = 727.951335792 (H's value) and
  omega = 727.951335426 (Saouter-Trudgian-Demichel 2015's omega_0).
- **Control**: omega = 727.95134. The rerun's ball there must overlap the
  recorded S = [-0.99067672 +/- 1.89e-9]. If it does not, the rerun is
  inconsistent with production B and nothing below is evaluated until that is
  explained.
- **Descriptive grid**: 727.951335792 + k * 5e-8 for k = -40 .. 40. Every point
  is reported. No claim is made at any omega picked from the grid after the data.
  All 83 points are listed in `omega_grid.json`, committed with this file.

## The decision rule

Let S(w) be the ball sum over the 2.2e7 zeros at omega = w, and let
B = 2.60111e-5, Revers's stated worst-case zero budget (Delta S1 + Delta S2,
subsection 6.3).

- **H supported** iff every point of the ball S(727.951335792) lies within B
  of S*: |S - S*| + rad(S) <= B.
- **H not supported** iff that fails. If S(727.951335426) instead meets the
  same rule, that is recorded as an observation about which omega the printed
  S* matches. It does not support H, and it was not a hypothesis.
- If neither decisive point meets the rule, the discrepancy is not the rounding,
  and target B stays "attempt unresolved".

**Prediction under H**: S(727.951335792) is within B of -1.002922947. Revers's
float computation with zeros to 1e-9 typically lands much closer than the
worst-case B, so a gap above about 1e-6 would already be surprising under H.

## What may be claimed afterwards

- A ball-grade localization, meaning a positive lower bound -1 - S - R at
  Revers's tabulated eta values, is stated **only at a decisive point**
  (727.951335792 or 727.951335426). It holds whether or not H is supported,
  since the bound does not depend on matching Revers. Its grade is that of
  target A: a hardened computation on a cited derivation, with completeness on
  Arb alone and route 2 sampled.
- Grid values are descriptive. A positive bound at a non-decisive grid point is
  reported as a value, not as a localization claim.

## Planted faults, run on the rerun data

- Drop R4 at the decisive points and report the move.
- Replace gamma_1 by gamma_1 + 1e-6 at the decisive points and confirm the ball
  moves out of its own unfaulted position.
- The grid sum must equal the stored single-omega sums at 727.95134 and
  727.952018 on a small shard (`test_skewes_terms.py`). A grid shifted by one
  step must fail that test.
