# Rung-3 plan v2 — max-modulus + Cauchy + mean-value architecture

Plan file: `rung3_plan2.json`.  The naive boxed-s *lower*-bound evaluation is
gone; the small-square frontier is now certified by **point enclosures on a
grid + a Lipschitz bound L**, where L = M/(w2-w) comes from boxed-s *upper*
bounds on a big square (width tolerated, not fatal).  All coordinates are
exact rationals (denominators divide 2^12 * 10^6); every certificate-side
inequality was re-checked in exact Fraction arithmetic by an independent pass
(`v2_verify.py`, reads only the JSON): **3137 checks, 0 failed**.

**Headline**: small square w = 3/64 around (808517/1000000, 85699348/1000000),
eps' = 1/2000; big square w2 = 7/32; **L = 16 (= "16/1"), M = 25499/10000**;
**100 unique grid points** (104 entries; the 4 corners are shared pairwise,
duplicate entries carry identical data), **110 big boxes**, centre K = 361.
**Total certified-term cost = 77675 (grid 49360 + big 26510 +
centre 1805) -> wall-clock ~ 18.1 h at 0.84 s/term on 4 cores.**

## Chosen parameters and why

Scanned w in {1/32..1/8}, w2 in {3/16..5/16}, M-target in [0.6, 4.0],
eps' in {3e-4, 5e-4, 1e-3} with greedy covers under the stated width model.
The surface is flat near the optimum (76.6k..80k over a wide region):

- **w = 3/64**: the grid-point count is ~invariant in w (N ~ 5.5 L because
  both the frontier floor and the allowed gap scale with w), but per-point K
  falls with w while L = M/(w2-w) rises as w eats into the Cauchy gap;
  w = 3/64 balances this against w2 = 7/32 (gap 11/64).  cre - w =
  0.76195... > 1/2 (exact check).  Frontier floor max(|Re|,|Im|) = 0.0492;
  measured max |DH'| on the small frontier = 1.30.
- **w2 = 7/32**: pushing w2 left lowers sigma on the big square's left edge
  (re_lo = 0.5898), and both Sigma(K) and the tail exponent degrade fast
  below sigma ~ 0.6 — at w2 = 5/16 the big cover costs 4-10x more.  Pulling
  w2 in shrinks the Cauchy gap.  7/32 (with sigma_lo down to 4/7 on the left
  edge) is the measured sweet spot.
- **M-target = 2.5** (=> M = 25499/10000, L = 16): the explicit trade
  grid ~ c*L vs big-cover ~ falling in M; the scan minimum is at 2.5 with
  76,605 planned terms (2.2 -> 78.9k, 3.2 -> 79.8k).  Exact build lands at
  77675.
- **eps' = 1/2000**: 768x above ||DH(centre)|| = 6.51e-7; the centre now
  keeps a >= 25% margin (K_c = 361, r_c = 3.736e-4, margin 1.257e-04 =
  25.2% of budget).  eps' = 1e-3 saves ~400 centre terms but
  costs ~ the same on the grid: flat.

## The plan

- **Grid** (26 points per segment, incl. endpoints; corners shared):
  bottom K in 85..113, top 85..107, left 101..114,
  right 85..94.  Adaptive gaps h_i (larger where ||DH|| is larger):
  h from 141/32768 up to ~3x that.  Per point: sigma_lo = best k/d (d<=8)
  <= Re(p) — 3/4 on most of the frontier, 4/5 where Re >= 0.8; point tail
  r_i ~ (maxcomp - eps')/(sigma_lo+3), K_i minimal for it.
  Cell requirement (exact): min(beta_i, beta_i+1) - L h_i/2 - eps' >=
  (1/4)(min beta - eps'), with beta_i backed by mpmath dps-40 point values
  (pred_beta) minus a 2x sampling slack (2e-11).
- **Big boxes**: bottom 24, top 23, left 56, right 7 (the low-sigma left
  edge needs the most; the right edge, sigma_lo = 1, needs 7).  K in
  17..61.  Per box predM = max|Re| + max|Im| + 2*width + 2*r
  (see model note below), all predM <= M, and L*(w2-w) >= 1.1 * max predM
  (exact; headroom lands at 1.100).
- **Centre**: K = 361, sigma_lo = 4/5 (a/b = 14/5),
  r = 205390733/549755813888; ||DH(c)|| + slack + r < eps' with 25.2% margin.

## Verification (3137 checks, 0 failures)

1. Structure (exact): grid covers each segment end-to-end, gap_next matches
   successor differences exactly, last gap null; big boxes tile each big
   segment exactly with shared endpoints; degenerate coordinates exact; all
   denominators divide 2^12 * 10^6; corner duplicates agree field-by-field;
   every K <= 450; re_lo > 0 on every big box; im > 0 everywhere.
2. kappa_hi >= kappa proved exactly (integer-sqrt enclosures at 10^-25).
3. Exact chains everywhere (grid, big, centre): sigma_lo <= re, denominator
   <= 8; a/b = sigma_lo + 2 reduced; P^b (5K+1)^a >= 1 in integers;
   NS/NS1/NS2 >= normBound exactly; r >= (5/8)(3+kappa_hi) NS NS1 NS2 P b/a.
4. Grid betas: fresh mpmath dps-40 evaluation at all 100 unique points;
   pred_beta reproduced to < 1e-9; cells re-checked in exact rationals with
   beta reduced by 2x sampling slack.  **Worst three cell margins:
   0.270 (g_left_22->g_left_23), 0.270 (g_top_07->g_top_08), 0.270 (g_top_23->g_top_24)** — all >= the
   required 0.25 of budget (and >> 0.25 eps').
5. Big boxes: fresh 3x + midpoint resample per box (max|Re|, max|Im| with a
   2x derivative-based sampling guard), Sigma re-summed independently
   (math.fsum); every fresh predM <= stated predM <= M; the numpy EM sampler
   was spot-checked against mpmath dps-40 at 3 points per box (330 points,
   worst |diff| = 4.1e-14) — this matters because the big frontier
   reaches sigma ~ 0.59 where the sampler had not been validated before.
6. Centre at dps 50; margin 25.2% of budget (>= 25% required).

## Width-model plausibility (mandated check)

Model: enclosure width over a 1D box of extent delta ~ 1.30 * delta *
Sigma(K) + 5K 2^-50 + 1e-9, Sigma(K) = sum_{m<5K, m%5!=0} m^-sigma ln m.
Derivation: the kernel's series is sum a_m m^-s (|a_m| <= 1); over the box,
each term sweeps an arc of length <= delta * ln m * m^-sigma_min (mean value
in s); summing gives delta * Sigma.  Numbers at two boxes / two K each:

- worst box B_top_11 (sigma_lo = 2/3, delta = 0.01410):
  K = 44: Sigma = 41.9, width = 0.768;  K = 88: Sigma = 63.6, width = 1.165.
  Direct chord-sum cross-check at K = 44: sum |m^-s_a - m^-s_b| = 0.500 vs
  delta*Sigma = 0.591 (ratio 0.85) — Sigma is near-sharp; the 1.30 factor is
  the real safety.
- cheap box B_right_06 (sigma_lo = 1, delta = 0.02179): K = 17: Sigma = 7.9,
  width = 0.224; K = 34: Sigma = 10.6, width = 0.299; chord ratio 0.92.

The width term dominates predM exactly as anticipated: worst box breakdown
**predM = X + 2*width + 2*r = 0.384 + 1.536 + 0.580 = 2.4999** (X = true
max|Re| + max|Im| incl. sampling guard).

## Hostile-referee notes

1. **The normBound reading of predM is the load-bearing modelling choice.**
   The coordinator's literal model ("|DH| true max + halfwidth + r") gives
   max predM = 1.39 -> L = 8.87.  I used the L1-conservative reading
   (normBound sums per-component maxima, each padded by the full width and
   by r): max predM = 2.50 -> **L = 16**.  Ratio 1.8x.  I declared the
   conservative L because an *underdeclared* L fails the kernel check
   L(w2-w) >= M outright.  **If a pilot run of one big box shows the kernel's
   normBound tracks the literal model, re-planning with L ~ 9 cuts the grid
   to ~30k and the total to ~56k terms (~13 h).**  The failure mode of my
   choice is cost, not soundness.
2. **The width model assumes per-term arc/mean-value enclosures.**  If the
   kernel encloses m^-s by naive interval exp/log in re/im components, its
   width can exceed delta*Sigma (extra wrapping), M could exceed 25499/10000,
   and the L check fails — loudly, not silently.  The 1.30 factor plus the
   1.02 (M) and 1.10 (L) headrooms absorb ~43% combined; the chord check
   says Sigma itself is only ~10-18% conservative, so the total cushion over
   a mean-value kernel is ~1.5-1.7x, but a genuinely naive kernel would blow
   through it.  Verify the evaluator's form before spending 18 hours.
3. **The big-square detour buys less than it appears.**  Boxed-M total =
   77675; the closed-form fallback L = 40 (no big square at all) costs
   88,875 at its own best w (1/8), i.e. only ~14% more, with ~110 fewer
   kernel lemmas and no M/L machinery.  If proof-engineering time matters
   more than 2.4 h of compute, the fallback is defensible.  Conversely
   "more/smaller big boxes" does NOT fix the width model: pushing M-target
   to 1.0 costs 242k terms (608 boxes) — cost/length diverges as delta -> 0.
   The scan table in `v2_build` output records this.
4. **L = 16 vs measured |DH'| <= 1.31 on the small frontier**: the
   architecture pays ~12x over the true Lipschitz constant (Cauchy over a
   thin annulus plus L1 norms plus width padding).  Any future certified
   derivative bound |DH'| <= ~2 on the small square would collapse the grid
   to ~15 points and the total to ~10k terms.  Worth a rung of its own.
5. **Sampling exposure is now structural, not incidental**: cells need no
   interior samples at all (mean value covers between points; betas are
   mpmath-backed at the points).  The only sampled maxima left are the big
   boxes' X terms, guarded by 2x the derivative-based gap bound
   (9.7e-05) *and* sitting under the 1.30/1.02/1.10 stack.  The numpy
   sampler is validated to 4e-14 against mpmath dps-40 at sigma down
   to 0.59.
6. Deviation from the schema note: `centre` also carries "sigma_lo"/"a"/"b"
   (= 4/5, 14, 5) so the kernel need not hardcode the centre's exponent
   pair; unknown-key-tolerant parsers are unaffected.
7. Wall-clock 18.1 h is the honest price under my conservative model;
   the realistic range after a pilot box is ~13-18 h, or ~2.4 h more for the
   L = 40 fallback with a much simpler proof.

## Artifacts

- `rung3_plan2.json` — the plan (kernel input).
- `v2lib.py`, `v2_optimize.py` — models, Sigma tables, (w, w2, M, eps) scan.
- `v2_build.py` / `v2_build_extras.json` — refinement + exact build.
- `v2_verify.py` / `v2_verify_results.json` — independent verification
  (3137 passed / 0 failed).
