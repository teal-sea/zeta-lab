# Results: where the seven-point certificate ends

> Bounded outcome of Hunt #79 (numbered #77 while in flight; #77 is AIMO-2 and #78 is `r_a7c12f`). Labels: VERIFIED means run here and compared against a
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
267. Against the configuration ceiling of **0.6818287** (the value `anthropics/zeta-23-lean`
proves; the 0.68185 this laboratory had been quoting from Remark 1.1 is a decimal with no
proof attached, see `TRUST-MAP.md`) and the window ceiling of 0.6725007, this certificate
family extracts about **0.00052 of the 0.00933 available, roughly 5.6%**.
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

**And it stops where the float search says it should.** A third probe at 0.0038263,
6.9 × 10⁻⁸ *above* the float floor, was refused in 121 s at the terminal single-cell box
`(4184, 7960, 7944, 4166, 7909, 4180)` on the 1/4000 grid: gaps
(1.046, 1.990, 1.986, 1.042, 1.977, 1.045). That is the configuration the float minimiser
found, reached independently by the verifier's exhaustive subdivision. Kill condition 2
did not fire.

**And the bracket is rigorous on both sides.** Run on Modal (`modal_ceiling.py`,
`artifacts/modal-results.json`): Arb at 256 bits evaluates F6 at the minimiser as
`0.0038262312115073`, an enclosure whose two ends agree to the printed digits. The value
of F6 at any point is an upper bound on its infimum, so:

    0.003826  ≤  inf F6  ≤  0.0038262312115073

Lower end: the accepted interval certificate at `1913/500000`. Upper end: the Arb
evaluation at the point. Width 2.3 × 10⁻⁷. The float minimiser's last digits
(`…2114`) and Arb's (`…2115`) differ by rounding at the sixteenth decimal.

**A defect in every raised-target run, found by the trust map and repaired here.** The
verifier's `PRESSURE_CUTOFF_CELLS = 45600` encodes the original target: at
`verify_seven.py:276` it prunes every box with gap-sum at least `45600/4000 = 11.4` on the
grounds that the linear term alone, `11.4/3000 = 0.0038`, exceeds the target. That is true
for `19/5000` and false for anything larger. Gohms's run changed only the target; so did
the three probes above. Each of those acceptances was therefore unsound as run: the 3,087
boxes pruned by that rule were never shown to exceed the raised target.

Re-run on Modal with the cutoff raised to 46,400 cells (gap-sum 11.6, sound for targets up
to 0.003867), `artifacts/modal-rerun-sound-cutoff.json`:

| target | grid | cutoff | outcome | nodes | depth |
|---|---|---|---|---|---|
| 191/50000 (Gohms) | 4000 | 46,400 | accepted | 786,085 | 43 |
| 153/40000 | 4000 | 46,400 | accepted | 862,961 | 51 |
| 1913/500000 | 4000 | 46,400 | accepted | 907,799 | 58 |
| 1913/500000 | 8000 | 92,800 | accepted | 899,055 | 57 |
| 1913/500000 (control) | 4000 | 60,000 | accepted | 907,761 | 58 |

Every result stands, and the node counts move by tens, which is what a prune that was
never load-bearing looks like. The lower end of the bracket below is the 46,400-cutoff
run, not the original. The refusal at 0.0038263 is unaffected, since a missing prune can
only make acceptance harder. Reported upstream in the same thread as the reproduction.

**The refusal is not the grid's.** The same two targets rerun with the verifier's grid
doubled to 8000 and its two grid-scaled constants doubled with it: `1913/500000`
accepted (898,669 nodes, depth 57, 233 s on Modal); `0.0038263` refused at cell
`(8368, 15919, 15889, 8333, 15816, 8360)/8000`, the same configuration to four decimals
at double resolution.

**Eight points, at the same pressure.** The natural analogue `F7` over seven gaps with
weights `2/(8−s)` and the same `1/3000` linear term has apparent floor **0.0043887**
(2,880 restarts on Modal), *higher* than the seven-point floor, at the perfect
alternation (1.044, 1.975, 1.040, 1.972, 1.040, 1.975, 1.044). This does not say eight
points is worse. It says the pressure `1/3000` is not the right scaling for eight points:
the linear term and the block size `m` are one parameter, and the map from certificate
to bound changes with `n`. That is the same hole §4 names, seen from the other side, and
it is the trust map's first obligation.

**The family's ceiling, verified.** `TRUST-MAP.md` finds the pressure denominator is a
tunable constant whose curve is unimodal with peak near `p = 3200`, the published `3000`
being very nearly optimal. Verified there (`artifacts/modal-peak-p3200.json`):

| target | grid | outcome | nodes | depth | m | Φ |
|---|---|---|---|---|---|---|
| 909/250000 | 4000 | accepted | 975,289 | 51 | 281 | 0.673027252 |
| **36369/10000000** | **4000** | **accepted** | **1,045,977** | **64** | **280** | **0.673027683** |
| 36369/10000000 | 8000 | accepted | 1,036,265 | 64 | 280 | 0.673027683 |
| 363695/100000000 | 4000 | refused | | | 280 | (0.673027716) |
| 36370/10000000 | 4000 | refused | | | 280 | (0.673027749) |

Both refusals land on the same terminal cell as at `p = 3000`, gaps ≈ (1.046, 1.989,
1.987, 1.042, 1.977, 1.045).

**The peak is at `p = 3400`, not 3200.** The trust map's pressure sweep did not sample 3400;
a finer sweep (`artifacts/npoint-sweep.json`, with an Arb enclosure at every argmin) puts
the seven-point peak there. Verified (`artifacts/modal-peak-p3400.json`): `34697/10000000`
accepted at grid 4000 (1,112,733 nodes, depth 57) and grid 8000 (1,114,059 nodes),
`34701/10000000` refused. With `m = 294`:

    liminf N_0^s(T,2T) / N(T,2T)  >=  0.673029553

1.9 × 10⁻⁶ above the `p = 3200` figure and 7.9 × 10⁻⁶ above Gohms. The sweep also shows the
family's reach grows with the point count, about 2 × 10⁻⁵ per added point at its own optimal
pressure (eight points ≈ 0.673054, nine ≈ 0.673071, float floors, optimistic), with the same
1-2-2-1 minimiser structure at every `n`. 
**Eight points, verified.** A generalisation of the published verifier to `n` points
(`verify_n.py`, in the upstream clone; `modal_verify_n.py` here), with the pressure cutoff
derived from the target rather than hardcoded, was validated first: forced to the
original cutoff at `n = 7` it reproduces Ainta's run bit for bit (707,901 nodes, 93,735
tangent prunes, both table hashes), and at `n = 3` it agrees with a brute-force scan. Then
at eight points, pressure 3200, grid 4000, sharded 64 ways on Modal
(`artifacts/verify-n8-41763-10000000-p3200.json`):

| target | outcome | shards | nodes | wall |
|---|---|---|---|---|
| 41763/10⁷ = 0.0041763 | **accepted** | 64/64 | 6,504,134 | 2,699 s |
| 417742/10⁸ = 0.00417742 | undecided (one shard at its node cap) | 63/64 | | |

The minimiser is the palindrome (1.046, 1.989, 1.987, 1.042, 1.987, 1.989, 1.046), the
seven-point structure extended by one more 2. Arb at the argmin gives the upper end, so

    0.0041763  ≤  inf F₇  ≤  0.0041773221

With `m` capped at 246 by `c(m−7) ≤ 1`, the stated `n`-point bound gives

    liminf N_0^s(T,2T) / N(T,2T)  >=  0.673052983        (n = 8)

2.3 × 10⁻⁵ above the best seven-point figure. **What is different about this one.** For seven
points Ainta's paper supplies the argument from certificate to percentage. For eight
points no paper exists: the bound uses this hunt's line-by-line generalisation of that
argument (`Φₙ(c,m,p) = (H − (n−1)(m−1)/(pm)) / (1 − c(m−(n−1))/m)`, windows of `n`
consecutive zeros, `m−(n−1)` windows per block, each gap charged at most `n−1` times, the
cap from `A₀ = c(m−(n−1)) ≤ 1`). It reproduces the verified `n = 7` formula exactly and is
the natural reading of every step in `TRUST-MAP.md`, and it is **stated, not proved**.
The certificate is rigorous; the bridge for `n = 8` is ours to prove, and it is the same
bookkeeping as the `n = 7` bridge with `6` replaced by `7`.

**Where the family runs out.** Nine points at its own optimum (p = 4000) has float floor
0.0039279261 (Arb upper 0.0039279261) and a stated bound of 0.673071; each added point
buys about 2 × 10⁻⁵ at exponentially growing verification cost, against 0.0088 still
under the configuration ceiling. The family is shallow, and the same 1-2 alternation on
the kernel's zeros is the obstruction at every `n` tried.

6.3 × 10⁻⁶ above the `191/50000` figure and 1.9 × 10⁻⁵ above Ainta's, with the next
target up refused at two grid sizes. This is recorded as the *ceiling of the method*,
which is this hunt's question, and not as a headline result: it is the same certificate,
the same verifier and the same analytic bridge, moved to the best point of its own
parameter. The bridge is mapped, not proved.

## 4. The bound formula, resolved by the trust map

From the two published constants this hunt reconstructed
`Φ(c, m) = (H − (m−1)/(500 m)) / (1 − c (m−6)/m)`, exact at both points but monotone in
`m`, which could not be the whole story. `TRUST-MAP.md` derives it rather than fits it:

    Φ(c, m, p) = ( H − 6(m−1)/(p m) ) / ( 1 − c (m−6)/m ),    p the pressure denominator,

reproducing both published constants to 40 digits, and recovers the missing constraint:
`A₀ = c(m−6) ≤ 1` (riemann.tex:375), forced by the `min{1, …}` in the block-defect lemma.
So `m` is capped at `6 + ⌊1/c⌋`, both Ainta (269) and Gohms (267) sit exactly at their
cap, raising the target lowers `m`, and the bound is sawtoothed in `c`. With the pressure
optimised (unimodal, peak near `p ≈ 3200`; `p = 3000` is very nearly optimal) the
family's ceiling is **0.673027719**, 6.4 × 10⁻⁶ above Gohms. The eight-point result in §3
is consistent with this: `p` is tied to `n` and `m`, not a free constant.

## 5. What this hunt does not claim

- It does not call the seven-point theorem verified. The finite certificates are; the
  analytic bridge (the stability-enhanced rank–trace inequality, the kernel
  approximation, the convex pinching, the sliding-window averaging, the passage to the
  asymptotic count) is mapped in `TRUST-MAP.md`, verdict one substantial analytic bridge,
  with six of sixteen steps already kernel-checked upstream. Mapped is not proved.
- It does not claim the minimiser is unique or that the floor is attained only there;
  the bracket on inf F6 is rigorous, the structure reading (kernel zeros) is not.
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
