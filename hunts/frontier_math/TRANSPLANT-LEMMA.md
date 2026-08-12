# The transplant lemma, dissected: three windows, one live kernel

## Disposition

The candidate reading's most dangerous unproven step — "the transplant
lemma" connecting theta_full (proved at the hunt's window) to the
Cheer-Goldston floor (computed with the Montgomery-Taylor kernel) — is
now dissected into measured parts.  **There is no kernel-comparison
inequality to prove**; there is a chain re-run to do, at a window that is
now exactly identified, with entry constants measured 3x friendlier than
the ones the chain already survived.  Two would-be shortcuts are closed
by exact degeneracies, both measured to their exactness.

## The three windows (instrument: `transplant_lemma.py`)

| window | kernel zeros | CG mechanism | grid LAW D | retention entry |
|---|---|---|---|---|
| hunt (L=8 septic; levels 1-7) | ratios 1 : 2.0001 : 3.0003 | **DEAD** (arithmetic to 1e-4; bucket LP floor = 0.00e+00 exactly) | exact (level 1) | minW/sigma^2 = -1.2137 (LAW I), theta_full = 0.02 proved |
| Hann grid (phi = cos^2(pi u), width 1; the `blockpos.py` shape) | 6pi, 8pi, 10pi, 12pi | **DEAD EXACTLY** (2 lambda_1 - lambda_4 = -5e-13) | **exact**: B = 2 pi Phi2_h, defect 3.7e-8 | minW = -1.7e-5 (harmless field, worthless floor) |
| MT (phi = cos(sqrt2 t), width-1 box) | 1 : 1.9201 : 2.8566 : 3.7977 | **ALIVE** (CG 1993; c_u one-sided = 5.02e-6 at nu_on) | **exact** (the "0.53% alias" was truncation: defect scales 1/K, 3.8e-3 -> 6.0e-5 over K 80 -> 5120; a width-1 window cannot reach the +-2pi combs) | minW/sigma^2 = **-0.43**, band at 1.10-1.12 mean gaps |

Three exact identities anchor the table:

1. **g_MT is a window kernel**: the Montgomery-Taylor kernel is EXACTLY
   the normalised squared Fourier transform of cos(sqrt2 t) on the
   width-1 box (measured defect 2.5e-16).  Taylor's sqrt2 modulation is
   precisely what breaks the arithmetic zero structure — the entire
   ordered-gap floor mechanism lives in that modulation and nowhere else.
2. **The Hann grid form is alias-free**: B(z, w) = 2 pi Phi2_h(z - w) to
   3.7e-8 — the satellite structure of the width-1 Hann window cancels
   the +-2pi grid aliases exactly.  LAW D transplants verbatim to the
   pinned zero-side shape.
3. **Both shortcut windows are lesion-exact**: the hunt kernel's zeros
   are arithmetic to 1e-4 and its bucket floor is 0 to LP precision; the
   Hann kernel satisfies 2 lambda_1 = lambda_4 to 5e-13.  The CG floor's
   own lesion (`lesion_wrong_lambda2`) is not a hypothetical — two of the
   three natural kernels sit exactly on it.

## What "the transplant lemma" actually is now

- **T1 (the work): re-run the retention chain at the MT window.**  The
  machinery is window-parametric; the entry card says the trade is
  3x friendlier (damage envelope -0.43 sigma^2 vs -1.21 sigma^2, negative
  band at ~1.1 mean gaps — exactly the lambda_1 geometry the CG buckets
  occupy).  (A first report of a "0.53% alias defect to carry" was
  wrong - pure grid-sum truncation; LAW D is exact here too, see the
  T1 section below.)
- **T2 (census/normalization)**: grid unit x 2 pi = mean gap; measured
  consistent (the damage band lands at 1.10-1.12 mean gaps, where
  lambda_1 = 1.057-1.06 lives).
- **T3 (plumbing)**: CG's floor-to-constant conversion, calibrated
  against their printed 1993 values (already in `reconnect.py`).
- **T4 (taper/truncation)**: the upstream count's bookkeeping restated
  one-sided at the composed value (unchanged status).
- **T5 (the upstream pin)**: the in-repo zero-side regression shape is
  Hann; the Theorem-D kernel is MT; which window the pinned Lean
  zero-side actually carries is decided by `anthropics/zeta-23-lean`
  (external to this session's reach) and must be pinned before T1's
  result is composed.

## What this changes in the candidate's status

Nothing upward: the reading 0.6725009045 remains a candidate.  Downward
protection improved: the failure mode "the two kernels cannot be
compared" is eliminated (they need not be compared — the chain moves to
the floor's own kernel), and the failure mode "the floor dies at the
paper's kernel" is now a measured fact rather than a risk, with the MT
modulation identified as the unique escape.  The critical path is T1,
which is compute with existing machinery, then T5, which is a pin.

## Reproduction

```bash
.venv/bin/python hunts/frontier_math/transplant_lemma.py   # ~2 min
.venv/bin/python -m pytest -q -o addopts='' \
    hunts/frontier_math/test_transplant_lemma.py           # ~2 min
```


## T1, first session (`mt_chain.py`): what transplants, what breaks, what is named

**Transplants exactly:** LAW D (B = 2 pi Phi2_mt, truncation control
3.8e-3 -> 6.0e-5 over a 64x range — the earlier alias claim is corrected:
a width-1 window cannot reach the +-2pi combs); LAW K (grid pair-block
spectrum {2(1+sigma^2), -2 sigma^2} matched at y = 0.45); the LAW-I-style
envelope, one-sided: W >= -0.54 sigma^2 at y = 0.49 (-0.70 at 0.3), vs
the hunt window's -(1+m0) = -1.21.

**The trade itself is measured healthy** (explicit band-riding
adversary, one pair): at FULL charge (c = 1, i.e. theta = 0) the total
damage is D = 0.030 against slack 0.142 at y = 0.49 (0.011 vs 0.052 at
y = 0.3) — 4.7x inside, with only two zeros ever profitable (the
+-1.10-mean-gap band pair).  (A first version of this line said "even at
theta = 1"; that is false — at theta = 1 the charge is multiplied by
zero and the supremum is unbounded by stacking.  Corrected by the
adversary hunt, and the mislabel is kept in the record.)

**The level-4 chain DP does NOT transplant.**  Its cap fails at every
theta (0.44 vs slack 0.14) for a structural reason now pinned: at the MT
window the damage bands sit at the kernel zeros and persist with a
1/g^2 envelope (the box window's boundary jump), and the DP's interval
charge floors straddle those same zeros — min omega^2 over [delta,
3 delta] = 0.182 / 0.023 / 0.000 across the ladder — so the chain grants
every far band free.  The true repulsion at band separations is
pointwise and small but decisive (omega^2 = 0.017 at 6.11, 0.011 at
6.28, 0.001 at 12.3), which is exactly what the explicit adversary pays
and the interval DP ignores.  **The named T1 theorem object is a
band-lattice counting dual with point-separation charges** (charge the
k-th band pair its actual omega^2 at the near-arithmetic separation,
not an interval minimum).

**Status of the candidate reading after T1's first session:** unchanged
in value, re-founded in support.  The hunt-window theta_full cannot fund
the g-kernel floor (the hunt-kernel floor is 0 — finding 1), so the
reading now rests on: MT-window retention (measured healthy, awaiting
the band-lattice dual for configuration-freeness) + the one-sided
g-floor + calibrated plumbing + the census + T5.  No proportion is
claimed.


## T1 second session: the band-lattice dual — theta* = 0.995 at the MT window

Instruments: `band_dual.py` (the dual), `mt_pairs.py` (the pair layer),
`mt_adversary.py` (the kill-control hunt).  Controls in
`test_transplant_lemma.py`.

### The first session's obstruction was not one

The first session reported the uniform-cell chain DP failing at every
theta (cap 0.44 vs slack 0.14) and named a band/kernel-zero arithmetic
coincidence as the obstruction.  Both halves are now corrected:

- **the number was mostly an artifact.**  A uniform delta-cell partition
  of a +-600-unit range makes ~800 cells, each granted its own Lipschitz
  margin (~1.7e-3), i.e. ~1.3 of damage granted out of thin air.  The
  blanket margin, not the mathematics.  This is the THIRD occurrence of
  that failure mode in this hunt (level-5 resolution scare, level-7
  mid-zone blanket, here) and it has now been met three different ways;
  the standing lesson is that any per-cell allowance must be local and
  must scale with the quantity it is protecting.
- **the coincidence was never load-bearing.**  omega^2 is a *square*, so
  every cross-band internal charge may be dropped one-sidedly.  The dual
  needs no charge floor at band separations at all — precisely the
  quantity whose vanishing was blamed.

### The dual

Partition by the damage field's own structure, not by a ruler.  At MT the
damage lives in narrow, well-separated bands (width 0.97 grid units at
y = 0.49, recurring every ~1 mean gap, the first at 1.106 mean gaps),
with maxima decaying like 1/g^2 (measured ratios 4.93, 2.33, 1.80, 1.57
against the law's 4, 2.3, 1.8, 1.6).  Then

    cap(theta) = 2 sum_k max_m [ m F_k - (1-theta) m (m-1) K_k ]
                 + closed-form 1/g^2 tail,

with F_k the band maximum (local slope margin, from closed-form Phi2'),
K_k the one-sided min of omega^2 over the band width, cross-band charges
dropped.  **The partition is complete, not assumed**: a band is exactly
where q = Re(Phi2)^2 - Im(Phi2)^2 < 0, and an unresolved band would need
an interior dip of q, excluded whenever q > (1/8)|q''| step^2 off the
resolved bands.  Measured worst ratio 326 (y = 0.02) to 7347 (y = 0.49),
so the off-band allowance is **exactly zero** rather than a blanket.

### Results

| quantity | hunt window | MT window |
|---|---|---|
| free-band ratio (every band granted, zero charge) | — | **0.34-0.36, flat in depth** (0.357 at y = 0.02, 0.346 at 0.49) |
| secured single-pair theta* | 0.1 | **0.995** |
| what binds | the counting cap | same-band multiplicity only (double occupancy of the first band turns profitable below theta ~ 0.992-0.9997) |
| stacking floor (pair layer) | 0.255 mean gaps | **0.979 mean gaps** (~3.8x wider) |
| worst dipole cover factor | 2.8-6.7 | **8.84-9.91** |
| dense-deep pinch | +0.07 at nu_p 1.25-1.5 | **none**; only a ~10%-wide soft window at nu_p ~ 0.97 (T/slack -0.381), where nearest-neighbour spacing sits on the damage band |

The adversary cannot reach the slack even at theta = 1 with single
occupancy: the entire band sum, both sides, is about a third of it.  The
projection control holds (measured band-riding adversary 0.0102 <= cap
0.0179 at y = 0.3), theta = 1 makes the cap infinite as it must, and the
pair layer's LAW L defect is pure truncation (1/K scaling over a 16x
range), with three lesions rejecting.

### What this does and does not do to the decimal

theta* = 0.995 is the **single-pair reduction**.  The composed reading
needs theta_full, the JOINT value; at the hunt window the joint layer
cost a factor 5 (0.1 -> 0.02).  The MT pair layer is measurably
friendlier (no pinch, wider floor, larger cover), so the joint loss
should be smaller, but **the joint run at MT has not been done** and no
new reading is claimed.  For scale only, and explicitly conditional: if
theta_full^MT landed at 0.2 (the hunt window's 5x loss) the candidate
would move +2.0e-6 instead of +2.0e-7; at 0.995 it would be +1.0e-5.
Both are conditional arithmetic, not readings.  The reading of record
remains 0.6725009045, a candidate.

### Named next objects

1. the joint (on-line + pair) cap at MT — the direct joint-field dual of
   level 7 rebuilt on the band partition;
2. the nu_p ~ 0.97 soft window, now the pair layer's only kill control;
3. the arb pass over the band dual (same shape as `hardened_direct.py`);
4. T5, the upstream Lean window pin, unchanged and external.


## T1 third session: the joint cap, and the composition made coherent

Instrument: `mt_joint.py` (the joint cap on the band partition);
`mt_adversary.py` (the independent kill-control hunt).

### The joint layer costs nothing at MT

The level-7 direct route, rebuilt on the band partition: bands from the
JOINT field (never per pair), sub-partitioned into delta-cells with the
square completion per cell, cross-cell charges dropped, partition shown
complete (worst Q / curvature ratio 874-60889 across the sweep).

| configuration | pairs | budget | cap | margin |
|---|---|---|---|---|
| **isolated single pair y=0.49** (the binding case) | 1 | 0.1423 | 0.0653 | **+0.0771** |
| isolated single pair y=0.3 | 1 | 0.0524 | 0.0194 | +0.0331 |
| two pairs far apart y=0.49 | 2 | 0.2847 | 0.1308 | +0.1538 |
| two pairs at the worst dipole y=0.49 | 2 | 0.2203 | 0.0611 | +0.1592 |
| lattice nu=0.5 y=0.49 | 4 | 0.5304 | 0.0891 | +0.4414 |
| lattice nu=0.97 y=0.49 (the pair layer's soft window) | 7 | 0.6274 | 0.0837 | +0.5436 |
| lattice nu>=1.25, all depths, all battery shapes | 10-24 | 9.4-186 | **0.0000** | budget |

(margins at theta = 0.995; the nu >= 1.25 rows close at every theta.)

**At pair density >= ~1 per mean gap the joint damage field has no
positive region at all.**  Measured directly: the maximum of the summed
field over a 200-grid-unit halo is -7.5e-4 (at the far window edge, where
it approaches 0 from below), against -3.9 inside the lattice, versus a
single pair's +1.5e-2.  LAW M's positive mean, summed over enough pairs,
swamps every band — the on-line adversary has nowhere to stand.

So the ordering is **inverted relative to the hunt window**: there,
density was the danger and the joint layer cost a factor 5 (0.1 ->
0.02), with a dense-deep pinch needing an entire mutual-exclusion
argument.  Here density is the defence, and the binding configuration is
the ISOLATED pair — i.e. the joint layer imposes no loss at all and

    theta_full(MT)  =  theta*(MT)  =  0.995  (measured grade).

### The composition is now window-coherent

`c_u` is computed with the Montgomery-Taylor kernel g, and g is exactly
the normalised squared Fourier transform of the MT window (defect
2.5e-16).  The retention now comes from the same window.  The previous
composition drew its retention from the hunt window, whose own
ordered-gap floor is **0** — it sits on the floor's lesion — so that
pairing was never coherent.  That incoherence is what forced T1, and it
is now repaired:

    candidate = 0.6725007037 + 2 * 0.995 * 5.0212e-6 = **0.6725106958**

i.e. +9.99e-6 against the pinned constant, where the hunt-window
composition gave +2.01e-7.

**This is a candidate reading, not a proportion, and five named steps
remain open**: the transplant plumbing (linearity with coefficient 1),
the census conversion (measured consistent only), taper/truncation
restated one-sided, the arb pass over the band dual and the joint cap,
and T5 — which window the pinned upstream Lean zero-side carries, whose
arbiter is external to this session.  Any one of them alone withholds the
word improvement.

### The independent adversary hunt (`mt_adversary.py`) and one correction it forced

A separate search (exhaustive n = 1..6 with analytic gradients, band
lattices, multiplicity, phase offsets, depth and theta sweeps) found no
configuration beating the two-zero band pair: worst measured take
0.2091 of slack at y = 0.49, and a charge-free one-per-band envelope of
0.325-0.335 of slack across all depths — an independent measurement of
the same ~1/3 the band dual bounds one-sidedly at 0.34-0.36.  Its
measured largest safe theta is 0.9990 at y = 0.49, rising to ~1 at the
shallow end.  **So theta* is now sandwiched: 0.995 (one-sided dual) <=
theta* <= 0.999 (measured adversary) — the bound is within 0.4% of the
truth.**

The hunt also caught a wording error of ours, kept in the record: an
earlier line read "the trade stays inside the slack even at theta = 1".
False as written — at theta = 1 the internal charge is multiplied by
zero and stacking m zeros on one band is unbounded, which is exactly why
both duals report cap(theta = 1) = infinity.  The measured figure was
the FULL-charge case (c = 1, i.e. theta = 0).  Corrected in
`mt_chain.py`, here, and in the ledger.  It also recorded a
counter-control worth keeping: the natural concave-QP relaxation that
would give an upper bound overshoots by 66x, because fractional
multiplicities make the self-charge negative.


## T1 fourth session: the arb pass, and a kernel-pairing error found in our own composition

### The arb pass survives, and is *tighter* than the float pass

`hardened_band.py` hardens the single-pair band dual in ball arithmetic.
The notable difference from the previous window: **interval-argument
evaluation is essentially lossless here** (amplification 1.06 at g = 1.1,
falling to 0.0024 at g = 300, against ~1.8e5 at the hunt window), because
the MT form is three trigonometric terms with no ramp^2 integer assembly
and no moment recursion for interval radii to lose.  So the cover is by
genuine continuum enclosures and **no Lipschitz margin is granted
anywhere** — "no band narrower than the grid" becomes a property of the
cover rather than an inference.

| y | slack >= | cap <= | margin >= | cap/slack (float) |
|---|---|---|---|---|
| 0.02 | 2.304683e-4 | 7.739518e-5 | +1.530731e-4 | 0.336 (0.357) |
| 0.10 | 5.768282e-3 | 1.938606e-3 | +3.829677e-3 | 0.336 (0.341) |
| 0.30 | 5.241061e-2 | 1.778540e-2 | +3.462521e-2 | 0.339 (0.341) |
| 0.49 | 1.423407e-1 | 4.912314e-2 | +9.321760e-2 | 0.345 (0.346) |

The hardened cap comes in BELOW the float cap at every depth.  Largest
surviving theta **0.9988** (float boundary identical: clears 0.9988,
fails 0.9989), so hardening moves the answer by less than one scan step,
and the binding term remains multiplicity, never the damage sum.

### The kernel-pairing error, in our own composition

Asking what two symbols denote turned up a real defect in the reading:

- **theta_full** retains the paper's Frobenius/incidence mass
  R = sum omega^2(gaps) with omega = Phi2/Phi2(0), Phi2 = FT(phi^2) —
  because the grid bilinear form is proportional to Phi2 (LAW D);
- **c_u** is CG's bucket floor in the Montgomery-Taylor kernel g, which
  `transplant_lemma.py` measured to be exactly (FT phi / FT phi(0))^2.

**(FT phi^2) is not (FT phi)^2** — the first is a self-convolution, the
second a square.  Measured: the two agree at u = 0 by normalisation and
diverge at once (ratio 1.02 / 1.12 / 1.70 / 0.66 at u = 0.3 / 0.6 / 0.9 /
1.5), and their zeros differ by 6% (omega's first at 1.1208 mean gaps
against lambda_1 = 1.0573).  Multiplying theta_full by c_u was therefore
mixing two kernels, undeclared.

Both zero sets are non-arithmetic, so **both kernels carry a live floor**
(unlike the hunt window's omega, arithmetic to 1e-4 with floor exactly
0).  Computed on one ladder, stable across n = 600k / 1.2M / 2.4M, with
the lambda_2 lesion dying on both:

    c_u(g)      = 5.021179e-06        reading 0.6725106958
    c_u(omega^2) = 4.021769e-06       reading 0.6725087070   <- conservative

**The reading of record therefore becomes 0.6725087070** (+8.00e-6), the
conservative pairing.  Which pairing the upstream count actually requires
is the residual T3 — and it is now a sharp question about the paper's
Theorem D derivation (is its discarded mass an omega^2 sum or a g sum?)
rather than a vague worry about plumbing.  Instrument: `kernel_pairing.py`.


## Confidence audit: what would have to be true

Asked point-blank whether the reading is certain, the honest answer is
no, and the reasons are worth writing down in order of how much each
would cost.

**1. T3 is not a detail; it is the load-bearing unknown.**  The formula
`H + 2 * theta * c_u` is inherited from the arithmetic that was CLEAN
KILLED.  Two halves of it separate cleanly:

- *calibrated*: `H + 2 * floor` reproduces Cheer-Goldston's printed 1993
  constant from their own inputs (recomputed floor 0.00012638 against
  their 0.00012636; constant 0.6727535 against their 0.6727534).  So the
  coefficient 2 and the linearity are right **within CG's framework**.
- *not calibrated, and never derived anywhere*: that `theta` enters that
  formula **multiplicatively**.  CG's improvement is RH-conditional and
  lives in Montgomery's pair-correlation framework; `theta` is a
  retention in the paper's Frobenius/incidence framework.  Nothing in
  this hunt establishes that a retention in the second plugs into the
  arithmetic of the first.  **If it does not, the reading is vacuous no
  matter how large theta is.**

**2. The window identification rests on one number.**  The pinned
constant is exactly the Montgomery-Taylor constant (2 - MT_CONST =
0.67250070368, agreeing with the pinned digits to 2e-11 — pure
rounding).  That is real evidence that the paper's window is the MT
window, and it is the only evidence there is.  (Checking it also caught
two stale comments in the repo printing wrong digits for MT_CONST and
H_PAPER, one of which had already been copied into a third file here
before being noticed.  Corrected, and both facts are now tests.)

**3. T5 remains external.**  Which window the pinned upstream Lean
zero-side actually carries cannot be settled from this session.

**4. The measured error rate in this work is not small.**  This session
alone produced, and then caught, four defects of our own: the
blanket-margin artifact (three separate times, in three different
guises), a theta = 1 convention mislabel, the kernel-pairing mix, and a
propagated stale comment.  Every one was found by a control or by an
independent route rather than by inspection.  That is the argument for
the controls, and simultaneously the argument against confidence in any
step no control has yet touched.

**What would survive even if T3 fails:** the MT-window results
themselves — LAW D exact, the band structure, the free-band ratio ~1/3,
theta* sandwiched in [0.995, 0.999] by a one-sided dual and an
independent adversary hunt, arb-hardened at 0.9988, and the joint layer
costing nothing.  Those are statements about the window and are
cross-checked several ways.  What they are NOT is a proportion.
