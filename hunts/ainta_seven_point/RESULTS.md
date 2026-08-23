# Results: where the seven-point certificate ends

> Bounded outcome of Hunt #77. Labels: VERIFIED means run here and compared against a
> published record; REPORTED means stated by a record and not re-established; INFERRED
> means a float reconstruction with no interval enclosure. Nothing here audits the
> analytic bridge from the finite certificate to the asymptotic proportion.

## 1. Both outside certificates reproduce

| certificate | target | bound | status | match against published record |
|---|---|---|---|---|
| Ainta 3-point | ε₄ ≥ 221/10⁶ | 0.6725197671136778 | VERIFIED | every field except elapsed time |
| Ainta 7-point | F6 ≥ 19/5000 | 0.6730085279277798 | VERIFIED | every count, every component, kernel hash; one secondary hash differs |
| Gohms 7-point | F6 ≥ 191/50000 | 0.6730213619501665 | VERIFIED | nodes 786421, pruned 393575, depth 43: the three figures the issue reports |

Gohms's run is the published verifier with two constants changed. Nothing else in it is
new, and the issue says so. Its bound arithmetic,
`(13350000·H − 26600)/13300149` with `H = 3/2 − (1/√2)cot(1/√2)`, evaluates to the
claimed digits.

**The one discrepancy.** `second_derivative_table_sha256` is `7913c551…` in Ainta's
committed certificate and `db0327b0…` here, on every run. That table holds Arb lower
enclosures of `w''` on each grid cell; a looser lower enclosure is still a valid one, and
every pruning count downstream is identical, so the certificate is unaffected. The field
is not bit-reproducible across Arb builds. The cause is suspected, not shown: older
`python-flint` does not build on Python 3.14 here, so the version hypothesis was not
tested. This is the reproducibility item to report upstream.

## 2. The floor of the functional, and what sits on it

The seven-point functional, read off `verify_seven.py`:

    F6(g) = (1/3000) Σ gᵢ + Σ_{s=1}^{6} (2/(7−s)) Σ_{i} k(gᵢ + … + g_{i+s−1})²,
    k(x) = K(x)/K(0),  K(x) = ∫_{−1/2}^{1/2} cos(√2 t) cos(2πx t) dt.

A float minimisation (600 Nelder–Mead restarts seeded inside the verifier's three
surviving gap components) finds:

    apparent minimum  F6 = 0.0038262312114228695        INFERRED
    at gaps           (1.046, 1.989, 1.986, 1.042, 1.977, 1.045), sum 9.085

The gaps alternate near 1 and near 2, which is where `k` vanishes. The reading, which the
trust map should confirm or refute from the paper, is that the obstruction is geometric:
seven points cannot place all 21 pairwise differences on zeros of the kernel while the
1/3000 linear pressure holds the configuration in. The next distinct local minimum is
0.0039910746, well above both published targets.

The float kernel used for this search was checked against the verifier's own Arb table:
the table's lower enclosure never exceeds the float value on any of 12,000 cells.

## 3. Where the race ends

| | target c | distance below the apparent floor |
|---|---|---|
| Ainta | 0.003800 | 2.6 × 10⁻⁵ |
| Gohms | 0.003820 | 6.2 × 10⁻⁶ |
| floor | 0.0038262 | 0 |

The map from the certificate to the bound, reconstructed from the two published data
points (INFERRED, see §4), gives the remaining headroom above Gohms as about
**4 × 10⁻⁶ in the bound**, a ceiling near **0.673025** for this certificate at block size
267. Against Anthropic's configuration ceiling of 0.68185 (Remark 1.1, already in
`hunts/rogue_frontier/FRONTIER_MAP.md`) and the window ceiling of 0.6725007, this
certificate family extracts about **0.00052 of the 0.00935 available, roughly 5.6%**.
The rest is not reachable by tightening this target at any grid.

**The verifier reaches the floor.** Two probes with the published verifier at its
published grid 4000, changing nothing but the two target constants:

| target | distance from float floor | outcome | nodes | depth | wall |
|---|---|---|---|---|---|
| 153/40000 = 0.003825 | 1.2 × 10⁻⁶ below | accepted | 862,825 | 51 | 421 s |
| 1913/500000 = 0.003826 | 2.3 × 10⁻⁷ below | accepted | 907,537 | 58 | 439 s |

So the limit is the inequality's, not the grid's, down to at least 2 × 10⁻⁷. Both are, as
a by-product, stronger certificates than Gohms's at the same standard of evidence. This
hunt records them as probe outputs that locate the ceiling and does not headline them:
Φ(1913/500000, 267) ≈ 0.673025 and the floor caps the family at the same figure to the
sixth decimal. The interesting number is the gap between them, which is now below 10⁻⁶.

A third probe at 0.0038263, which is 6.9 × 10⁻⁸ *above* the float floor, tests kill
condition 2 from the other side: the verifier must refuse it. Its outcome is in RUNS.md.

## 4. The bound formula, and the hole in it

From the two published constants:

    Φ(c, m) = ( H − (m−1)/(500 m) ) / ( 1 − c (m−6)/m )

    Φ(19/5000, 269)   = 0.6730085279277798   (Ainta, to the last digit)
    Φ(191/50000, 267) = 0.6730213619501665   (Gohms, to the last digit)

Two exact matches on a two-parameter reconstruction is strong, and still INFERRED: Ainta's
`m = 269` was solved for from the number rather than read from the paper. And the form is
monotone increasing in `m`, which cannot be the whole story or nobody would optimise `m`
to 267. The coupling between `m`, the 1/3000 pressure term, and the bound is the **first
obligation for the trust map**. Every ceiling figure in §3 is conditional on it.

## 5. What this hunt does not claim

- It does not call the seven-point theorem verified. The finite certificates are; the
  analytic bridge (the stability-enhanced rank–trace inequality, the kernel
  approximation, the convex pinching, the sliding-window averaging, the passage to the
  asymptotic count) has not been read here. `TRUST-MAP.md` is the companion deliverable.
- It does not claim the floor is rigorous. No interval enclosure of the minimum was
  computed.
- It does not claim novelty for the ceiling. Remark 1.1 bounds the family from above; this
  hunt only locates where one member of the family stops.
- It did not contact anyone. A reproducibility report for Ainta is drafted for the owner.

## 6. Kill conditions

None fired. Both reproductions matched; no target above the float floor was accepted;
the bound formula reproduced both constants. The fourth condition (the bridge changes the
ceiling by more than the headroom) is the trust map's to fire.

## Prior art

Ainta was first recorded in this tree at commit `bb8fa70` (`FRONTIER_MAP.md` line ~552,
"reproduced locally: finite certificate verification passed") by a separate session on
2026-08-22, with no run record, environment, or field comparison. This hunt is that
reproduction done to the contract, plus Gohms, the floor, and the formula. The lab's own
gap-census transplant (0.6725106958) is prior art recorded in the same map and is not
re-proposed.
