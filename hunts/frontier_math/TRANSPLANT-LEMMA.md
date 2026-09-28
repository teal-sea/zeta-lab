# The transplant lemma, dissected: three windows, one live kernel

## Disposition

The candidate reading's most dangerous unproven step, "the transplant
lemma" connecting theta_full (proved at the hunt's window) to the
Cheer-Goldston floor (computed with the Montgomery-Taylor kernel), is
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
   precisely what breaks the arithmetic zero structure, the entire
   ordered-gap floor mechanism lives in that modulation and nowhere else.
2. **The Hann grid form is alias-free**: B(z, w) = 2 pi Phi2_h(z - w) to
   3.7e-8, the satellite structure of the width-1 Hann window cancels
   the +-2pi grid aliases exactly.  LAW D transplants verbatim to the
   pinned zero-side shape.
3. **Both shortcut windows are lesion-exact**: the hunt kernel's zeros
   are arithmetic to 1e-4 and its bucket floor is 0 to LP precision; the
   Hann kernel satisfies 2 lambda_1 = lambda_4 to 5e-13.  The CG floor's
   own lesion (`lesion_wrong_lambda2`) is not a hypothetical, two of the
   three natural kernels sit exactly on it.

## What "the transplant lemma" actually is now

- **T1 (the work): re-run the retention chain at the MT window.**  The
  machinery is window-parametric; the entry card says the trade is
  3x friendlier (damage envelope -0.43 sigma^2 vs -1.21 sigma^2, negative
  band at ~1.1 mean gaps, exactly the lambda_1 geometry the CG buckets
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
compared" is eliminated (they need not be compared, the chain moves to
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
3.8e-3 -> 6.0e-5 over a 64x range, the earlier alias claim is corrected:
a width-1 window cannot reach the +-2pi combs); LAW K (grid pair-block
spectrum {2(1+sigma^2), -2 sigma^2} matched at y = 0.45); the LAW-I-style
envelope, one-sided: W >= -0.54 sigma^2 at y = 0.49 (-0.70 at 0.3), vs
the hunt window's -(1+m0) = -1.21.

**The trade itself is measured healthy** (explicit band-riding
adversary, one pair): at FULL charge (c = 1, i.e. theta = 0) the total
damage is D = 0.030 against slack 0.142 at y = 0.49 (0.011 vs 0.052 at
y = 0.3): 4.7x inside, with only two zeros ever profitable (the
+-1.10-mean-gap band pair).  (A first version of this line said "even at
theta = 1"; that is false, at theta = 1 the charge is multiplied by
zero and the supremum is unbounded by stacking.  Corrected by the
adversary hunt, and the mislabel is kept in the record.)

**The level-4 chain DP does NOT transplant.**  Its cap fails at every
theta (0.44 vs slack 0.14) for a structural reason now pinned: at the MT
window the damage bands sit at the kernel zeros and persist with a
1/g^2 envelope (the box window's boundary jump), and the DP's interval
charge floors straddle those same zeros, min omega^2 over [delta,
3 delta] = 0.182 / 0.023 / 0.000 across the ladder, so the chain grants
every far band free.  The true repulsion at band separations is
pointwise and small but decisive (omega^2 = 0.017 at 6.11, 0.011 at
6.28, 0.001 at 12.3), which is exactly what the explicit adversary pays
and the interval DP ignores.  **The named T1 theorem object is a
band-lattice counting dual with point-separation charges** (charge the
k-th band pair its actual omega^2 at the near-arithmetic separation,
not an interval minimum).

**Status of the candidate reading after T1's first session:** unchanged
in value, re-founded in support.  The hunt-window theta_full cannot fund
the g-kernel floor (the hunt-kernel floor is 0, finding 1), so the
reading now rests on: MT-window retention (measured healthy, awaiting
the band-lattice dual for configuration-freeness) + the one-sided
g-floor + calibrated plumbing + the census + T5.  No proportion is
claimed.


## T1 second session: the band-lattice dual, theta* = 0.995 at the MT window

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
  needs no charge floor at band separations at all, precisely the
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
| free-band ratio (every band granted, zero charge) |, | **0.34-0.36, flat in depth** (0.357 at y = 0.02, 0.346 at 0.49) |
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

1. the joint (on-line + pair) cap at MT, the direct joint-field dual of
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
swamps every band, the on-line adversary has nowhere to stand.

So the ordering is **inverted relative to the hunt window**: there,
density was the danger and the joint layer cost a factor 5 (0.1 ->
0.02), with a dense-deep pinch needing an entire mutual-exclusion
argument.  Here density is the defence, and the binding configuration is
the ISOLATED pair, i.e. the joint layer imposes no loss at all and

    theta_full(MT)  =  theta*(MT)  =  0.995  (measured grade).

### The composition is now window-coherent

`c_u` is computed with the Montgomery-Taylor kernel g, and g is exactly
the normalised squared Fourier transform of the MT window (defect
2.5e-16).  The retention now comes from the same window.  The previous
composition drew its retention from the hunt window, whose own
ordered-gap floor is **0**, it sits on the floor's lesion, so that
pairing was never coherent.  That incoherence is what forced T1, and it
is now repaired:

    candidate = 0.6725007037 + 2 * 0.995 * 5.0212e-6 = **0.6725106958**

i.e. +9.99e-6 against the pinned constant, where the hunt-window
composition gave +2.01e-7.

**This is a candidate reading, not a proportion, and five named steps
remain open**: the transplant plumbing (linearity with coefficient 1),
the census conversion (measured consistent only), taper/truncation
restated one-sided, the arb pass over the band dual and the joint cap,
and T5, which window the pinned upstream Lean zero-side carries, whose
arbiter is external to this session.  Any one of them alone withholds the
word improvement.

### The independent adversary hunt (`mt_adversary.py`) and one correction it forced

A separate search (exhaustive n = 1..6 with analytic gradients, band
lattices, multiplicity, phase offsets, depth and theta sweeps) found no
configuration beating the two-zero band pair: worst measured take
0.2091 of slack at y = 0.49, and a charge-free one-per-band envelope of
0.325-0.335 of slack across all depths, an independent measurement of
the same ~1/3 the band dual bounds one-sidedly at 0.34-0.36.  Its
measured largest safe theta is 0.9990 at y = 0.49, rising to ~1 at the
shallow end.  **So theta* is now sandwiched: 0.995 (one-sided dual) <=
theta* <= 0.999 (measured adversary), the bound is within 0.4% of the
truth.**

The hunt also caught a wording error of ours, kept in the record: an
earlier line read "the trade stays inside the slack even at theta = 1".
False as written, at theta = 1 the internal charge is multiplied by
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
anywhere**, "no band narrower than the grid" becomes a property of the
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
  R = sum omega^2(gaps) with omega = Phi2/Phi2(0), Phi2 = FT(phi^2),
  because the grid bilinear form is proportional to Phi2 (LAW D);
- **c_u** is CG's bucket floor in the Montgomery-Taylor kernel g, which
  `transplant_lemma.py` measured to be exactly (FT phi / FT phi(0))^2.

**(FT phi^2) is not (FT phi)^2**, the first is a self-convolution, the
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
is the residual T3, and it is now a sharp question about the paper's
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
0.67250070368, agreeing with the pinned digits to 2e-11, pure
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
themselves: LAW D exact, the band structure, the free-band ratio ~1/3,
theta* sandwiched in [0.995, 0.999] by a one-sided dual and an
independent adversary hunt, arb-hardened at 0.9988, and the joint layer
costing nothing.  Those are statements about the window and are
cross-checked several ways.  What they are NOT is a proportion.


## T3/T5 from the source: the window pin and the kernel resolution

The paper itself (SHA-256 pinned below in the ledger) was read for the
two questions the confidence audit left open.  Instrument:
`paper_pin.py`; every sentence below that can be computed is a test.

**T5 is answered.**  Section 7.1 and the Theorem D proof pin the
upstream window completely: rho = 1, box of width L, ends mollified by
the fixed-width ramp, and, the sentence that decides everything,
*"Writing phi^2(u) = v(u/L) ... the constant is the scale-free
functional (7.3)"* with maximiser *v\*(s) = cos(sqrt2 s)*.  The
variational profile belongs to **phi squared**, and the Theorem D window
is phi(u) = cos(sqrt2 u/l)^(1/2) on the box (the proof checks
cos >= cos(1/sqrt2) > 0 on the support precisely so the square root is
admissible).  The external Lean double-check is thereby downgraded to
optional.

**The functional, implemented once, reproduces three constants.**
1/c(v) = (int v^2 + int int |s-s'| v v) / (int v)^2: Montgomery's
K(0)/(Khat(0) + int |Khat|) with K = |vhat|^2, gives

    v* = cos(sqrt2 s):  H = 0.6725006969 (n=4001; defect 6.8e-9, shrinking on the ladder)
    v  = 1:             H = 0.6666666562 (Montgomery's 2/3)
    v  = cos^2:         H = 0.6673241112

The third line is the new fact: **the T1 chain's window (phi = cos box,
so v-profile cos^2) is an admissible but strictly weaker member of the
class: 5.2e-3 below the optimum**, three orders of magnitude larger
than the 8e-6 floor under negotiation.

**T3's kernel half is answered, and the ambiguity dissolves.**  tr G^2
is the pair sum weighted by B^2, LAW D makes B proportional to
FT(phi^2), and for the paper's window FT(phi^2) is the transform of the
cos(sqrt2 .) box, already measured (`mt_kernel_identity`, defect
2.5e-16) to be the square root of the MT kernel.  So under the paper's
window **omega^2 IS g**: the mass kernel and the Cheer-Goldston floor
kernel coincide by construction, and (7.3) says so in words
(K = |vhat|^2).  The omega^2-vs-g split that forced the conservative
reading was an artifact of the T1 window putting the cos profile on phi
instead of phi^2; it is absent from the paper's chain.

**What this costs.**  The entire T1 re-run, mt_chain, band_dual,
mt_joint, the adversary hunt, the arb pass, theta* = 0.995, was
computed on the damage field of the WRONG class member: every field was
built from Phi2 = FT(cos^2 box) where the paper's chain has
Phi2 = FT(cos box).  The named burdens behind the candidate are now:

  (a) chain re-run at Phi2 = FT(cos box), same machinery, one kernel
      swap; until it lands, theta* = 0.995 is a measurement about a
      neighbouring window, not the paper's;
  (b) the ramp: theta* at the pure box vs the paper's ramp-mollified
      window, O(log l / l) constant corrections;
  (c) T3's multiplicative half, unchanged and still the load-bearing
      unknown: the paper's (L) consumes ||P+Q||_F^2 whole via
      *"(2 tr P - r) + (4 tr Q - 4b) plays the role that sum (2m-1)
      plays in Montgomery's argument"*; that the eroded on-line
      off-diagonal mass enters as theta times a CG floor in the paper's
      units is derived nowhere.

**Where the reading stands.**  The conservative figure 0.6725087070 was
the right thing to report while the pairing was unknown.  With the
pairing settled in favour of g, the correctly-paired figure would be
0.6725106958, but only after burden (a) re-establishes theta at the
correct field.  Until then the reading of record stays **0.6725087070,
a candidate**, and no proportion is claimed.


## Burden (a) discharged: the chain at the paper's field

Instrument: `paper_chain.py` (an agent build, coordinator-reviewed);
controls in `test_paper_chain.py` (11 tests).

The band-dual chain was re-run with the incidence kernel swapped to the
paper's field, Phi2 = FT(cos box) = the v*-transform (A = 0.9187253699;
band lattice = the MT-kernel zeros, 63 bands in (0, 400], first centre
1.0443, separations 0.980-0.998 mean gaps, non-arithmetic).  Result:

    theta*_paper = 0.995  (same grid point as the T1 window),
    margins roughly 2x the T1 run in relative terms:
      y=0.02: cap 0.000111 vs slack 0.000248
      y=0.10: cap 0.002636 vs slack 0.006208
      y=0.30: cap 0.023905 vs slack 0.056436
      y=0.49: cap 0.091090 vs slack 0.153435
    theta = 0.999 fails at y = 0.49 (margin -0.116), consistent with
    the multiplicity threshold 0.98922 there.

All mandatory controls ran: kernel identity to 2.5e-16, closed-form
derivative pins (one transient differencer-roundoff false alarm,
documented in the control's docstring; the closed form was right),
no-missed-band ratios 328-7154 with off-band allowance exactly 0,
cap divergence at theta = 1, greedy adversary strictly inside the cap,
free-band ratio 0.42-0.45, and a distinctness control showing this is
not a re-run of the T1 numbers.  The task prompt's series coefficient
for s'(u) was wrong (u^3/1920); sympy pinned u^3/960 - the agent caught
it, which is the control doing its job.

**Consequence.**  theta* = 0.995 is now a measurement about the paper's
own window, not a neighbour's.  With the pairing already settled in
favour of g (previous section), the correctly-paired candidate
H + 2 * 0.995 * c_u(g) = 0.6725106958 no longer waits on the field; it
waits on burden (b) (the ramp) and burden (c) (the multiplicative-theta
derivation), which are unchanged.  The reading of record moves to
**0.6725106958, still a candidate**; no proportion is claimed.


## Burden (c), first half: the composition skeleton is now kernel-checked

Instrument: `t3_composition_skeleton.lean` (produced by the Aristotle
theorem-proving service, project 2e5d794d, task 025d9691; Lean 4 +
Mathlib, sorry-free, axioms propext / Classical.choice / Quot.sound
only; the kernel check ran on the service side and the file plus its
`#print axioms` lines are the artifact).

Two theorems, exactly as submitted:

- **result1_exact_skeleton**: for unit vectors u_i, positive integer
  multiplicities m_i with N = sum m_i, P = sum m_i u_i u_i^T, Q an
  arbitrary symmetric matrix, R = sum_{i != j} m_i m_j <u_i, u_j>^2 and
  D = R + 2 tr(PQ) + ||Q||_F^2:

      s >= 2N - ||P + Q||_F^2 + D.

  The route is the exact arithmetic this hunt had been treating as an
  analogy: ||P||_F^2 = sum m_i^2 + R exactly, ||P+Q||_F^2 expands, and
  2m - m^2 <= 1 for positive integers.

- **result2_conditional**: adding ||P+Q||_F^2 <= C*N and D >= theta*R0
  gives s >= (2 - C)*N + theta*R0.

**What this closes.**  The multiplicative entry of theta into the
composed reading is no longer an analogy borrowed from Cheer-Goldston:
IF the chain's measured retention is the statement D >= theta*R0, THEN
s >= (2-C)N + theta*R0 follows by kernel-checked arithmetic.  The
coefficient and the linearity are now theorem-shaped, not calibrated.

**What this does not close.**  Two seams, both named before, now carry
the whole weight:

  (i) the paper's prime side evaluates ||G-tilde||_F^2 = C*N in its own
      units; matching those units to the chain's (LAW D normalisation,
      the aL^2 scaling of (4.4)) is the unit-conversion seam;
 (ii) that the band dual's damage cap IS the statement
      D >= theta*R0 - i.e. that 2 tr(PQ) with the paper's
      transpose-structure pair blocks is exactly the W-field the dual
      bounds, and that ||Q||_F^2's contribution is one-sided - is the
      identification seam.  The `test_mt_W_normalisation` control pins
      a piece of it at the T1 field; the paper-field version is open.

Until (i) and (ii) are discharged the reading stays a candidate.


## Burden (a) hardened: the ball-arithmetic pass at the paper field

Instrument: `hardened_paper.py` (agent build, coordinator-reviewed);
controls in `test_hardened_paper.py` (9 tests, plus the discipline
suite).

The paper-field band dual survives hardening at **theta = 0.995**, the
same grid point as the float pass, with both sides enclosed (slack
lower endpoint vs cap upper endpoint; sigma2 radii ~2.5e-38 at prec
128).  Margins at theta = 0.995: +1.44e-4 / +3.61e-3 / +3.26e-2 /
+6.27e-2 at y = 0.02 / 0.1 / 0.3 / 0.49.  Unlike the T1 field, 0.9988
does NOT survive here: the boundary is the multiplicity threshold at
y = 0.49 (double occupancy pays above theta = 0.989249, hardened), and
0.9988 fails by -7.6e-2.  The two-term field is even more
interval-friendly than the T1 three-term form (amplification 0.25 down
to 0.002 across the band range, no mean-value form needed); the
hardened caps are TIGHTER than float everywhere (ratios 0.94-0.996),
the same removed-blanket mechanism as the T1 hardening.  The
singular-branch series carries explicit remainder bounds, pinned
against an mpmath oracle that itself needed 45 guard digits (the s''
closed form cancels ~24 digits near u = 1e-8 - an oracle trap recorded
in the module).

One inherited-prose defect found: the T1 modules' multiplicity print
states the profitable side of the threshold backwards (their own
numbers show occupancy paying ABOVE 1 - F/(2K)).  The new module
states the correct direction; the T1 print is left as-is and recorded
here.

**Where the reading stands.**  theta* = 0.995 at the paper field is now
float-and-ball agreed, single-pair.  The candidate 0.6725106958 waits
on: the joint layer at the paper field (running), the ramp (burden b),
and the two seams of burden (c) above.  No proportion is claimed.


## The joint layer at the paper field: theta_full = 0.995

Instrument: `paper_joint.py` (agent build, coordinator-reviewed);
controls in `test_paper_joint.py` (10 tests).

The multi-pair sweep at the paper field lands on the same grid point as
the single-pair dual: **theta_full = 0.995** (0.999 fails at the
nu = 0.5 lattice, y = 0.49, by a factor -1.29 relative).  The binding
configuration at 0.995 is that same sparse lattice (+0.33 relative);
the isolated pair binds only at lower thetas.  The soft-window density
was re-derived from this field's own band geometry, nu_p = 0.9576
(first damage-band centre 1.0443 mean gaps), distinct from both the T1
value 0.97 and the bare kernel-zero reciprocal 0.9458, and at it the
joint shielding leaves only 4 residual band cells (cap 0.0746 against
an isolated-pair 0.0947).  Dense lattices cap at exactly 0 with
positive budget, and the positive-part discipline control shows the
clipping order has measured power (per-pair clipping is strictly
larger).  Distinctness against the T1 joint at a matched configuration:
caps 26% apart, not a re-run.

**Consequence.**  theta_full = 0.995 is now a statement about the
paper's own window across the swept configuration families, float
grade, with the single-pair skeleton ball-agreed.  Remaining before the
candidate 0.6725106958 can be called a reading: the ramp (burden b),
the two burden-(c) seams (units; the dual's cap as D >= theta*R0), and
hardening of the joint sweep if wanted.  One-sided/measured grade
throughout; grid thetas only; the no-bands branch reports cap 0 without
the beyond-window tail (mirrors mt_joint, noted in code).  No
proportion is claimed.


## Burden (b) discharged: the ramp does not move theta*

Instrument: `ramped_field.py` (agent build, coordinator-reviewed);
controls in `test_ramped_field.py` (14 tests).

The retention scan was re-run with the paper's ramp mollification in
place: taper Psi((1/2 - |u|)/eps) with Psi the C^3 degree-7 smoothstep
(endpoint derivatives pinned by sympy), squared taper on phi^2, field
by error-pinned mpmath quadrature (ladder + dps-30 oracle; one-sided
quadrature pins ADDED to every margin), band lattice recomputed from
each ramped field's own zeros.  Result:

    theta*(1/8)  = 0.995   (worst allowed ramp)
    theta*(1/16) = 0.995
    theta*(1/32) = 0.995
    theta*(0)    = 0.995   (box reference)

Stable at 0.995 across the entire allowed ramp range; caps and slacks
converge monotonically to the box values as eps -> 0, with the measured
field defect cleanly O(eps) (constant 0.877 against a derived bound
1.226 via c_psi = int(1 - Psi^2) = 0.595183).  The thinnest margin
anywhere is y = 0.02 at eps = 1/8 (+1.05e-4, ~57% of the box margin).
Multiplicity thresholds at y = 0.49 sit at 0.9899-0.9920, below 0.995,
and 0.999 fails at every eps.  A one-point shape-dependence check
(degree-9 smoothstep) moves the binding cap by 1.6% without changing
any verdict; recorded as a caveat-measurer, not a supremum over shapes.

**Where the reading stands.**  Burdens (a) and (b) are both discharged:
theta* = 0.995 is measured at the paper's own window, box and ramped,
float and (for the box) ball-agreed, single-pair and joint.  The
candidate 0.6725106958 now rests on exactly the two burden-(c) seams:
the unit conversion (LAW D exactness is on the formal bench) and the
identification of the dual's cap with D >= theta*R0.  No proportion is
claimed.


## Seam (i), core: LAW D exactness is kernel-checked

Instrument: `law_d_incidence.lean` (Aristotle service, project c6519a2a;
Lean 4 + Mathlib, sorry-free, axioms propext / Classical.choice /
Quot.sound only; service-side kernel check, artifact in-tree with its
#print axioms lines).

What is now theorem-shaped, for phihat(x) = int phi(u) e^{ixu} du:

- **hasSum_phihat_mul_phihat**: for phi measurable, bounded, supported
  in [-1/2, 1/2], no continuity, no decay, no smoothness, the grid
  family n |-> phihat(x-n) phihat(y-n) is SUMMABLE over Z with sum
  2 pi * int phi(u) phi(-u) e^{i(x-y)u} du (the autocorrelation form).
- **tsum_phihat_mul_phihat_even**: with evenness added, the sum equals
  2 pi * FT(phi^2)(x - y): LAW D as the chain uses it.
- The three windows of this hunt are handled as explicit theorems, not
  prose: `tsum_phihat_windowA` (cos(sqrt2 u) box, jumps at the edges),
  `tsum_phihat_windowB` (sqrt(cos(sqrt2 u)) box, the paper's Theorem D
  profile), `tsum_phihat_of_continuous` (any continuous even window,
  covering every C^3 ramp mollification; boundedness derived).

**A defect in our own submission, caught by the prover.**  The phi^2
form as we stated it is FALSE without evenness: the file contains
`grid_incidence_needs_even`, exhibiting the indicator of (0, 1/2] with
grid sum 0 against 2 pi int phi^2 = pi.  Every window this hunt uses is
even, so the intended applications are unaffected, but the submission
had not said "even", and a prover that silently added the hypothesis
would have hidden that.  Logged with the session's other caught defects.

**Method note.**  The proof does not use Poisson summation at all: with
support in an interval of length 1 < 2 pi, phihat(x - n) are (2 pi
times) Fourier coefficients of the modulated window on R / 2 pi Z, and
the identity is a polarised Parseval (built from Mathlib's fourierBasis,
which only ships the norm-squared form).  That is why bounded
measurable suffices, strictly weaker hypotheses than the BV/decay
route the submission sketched, and one-sided in exactly the right way:
the aliasing question for the truncated grid sums (the measured ~1/K
truncation defect of `mt_law_d`) is now the ONLY gap between the
chain's finite sums and the exact identity.

**Where the seams stand.**  Seam (i)'s analytic core is closed; what
remains of it is bookkeeping (the paper's aL^2 units of (4.4) against
the chain's 2 pi Phi2(0) normalisation, plus the finite-truncation
accounting already measured).  Seam (ii), the dual's cap as the
statement D >= theta * R0, is unchanged and is the next piece of work.
No proportion is claimed.


## Seam (ii): the identification, derived and measured

Instrument: `identification_seam.py` (coordinator-built); controls
appended to `test_transplant_lemma.py` (4 tests).

The dictionary between the band dual and the kernel-checked composition
hypothesis D >= theta*R0, term by term, each measured on explicit
truncated-grid matrices at the paper field (never dense - all low-rank
inner products):

1. **Gram = omega.**  With LAW D normalisation (unit norms via
   2 pi A), <u_i, u_j> = Phi2(dx)/A: defect 4.4e-4 at K = 1200,
   shrinking 1/K.  So R = sum m_i m_j omega^2 - the chain's retained
   mass in the chain's kernel.
2. **The pair trace is the W field.**  u^T Q_p u = W(x - t, y) to
   5.4e-5: the dual's damage field IS -2 tr(PQ) per unit multiplicity.
3. **The pair surplus is slack(y).**  ||Q_p||_F^2 - (4 tr Q_p - 4 b_p)
   = 8 sigma^2 + 8 sigma^4 to 2e-6..6e-4 (truncation), with tr Q_p =
   1.9982 ~ 2 and b_p = 1 measured, not assumed.
4. **Cross terms are NEGATIVE - measured, and covered.**  tr(Q_p Q_p')
   summed over p != p' is negative in every multi-pair configuration
   (-0.066 to -0.342).  This was the last place a hole could hide: the
   composition needs ||Q||_F^2 whole, and the per-pair budget does not
   include cross terms.  They are covered - by orders - by the
   4 tr Q_p - 4 b_p = 4-per-pair cushion that the composition keeps and
   the paper's (L) would have consumed.  Recorded, not waved at.

End-to-end, gross and sharp, at theta = 0.995 over the binding families
plus adversarial placements derived from the field itself (on-line
points AT the damage minima, where total damage is positive and the
inequality actually bites): D >= theta*R holds everywhere, and the
sharp form damage <= (1-theta)R + sum slack_p holds everywhere, with
the worst adversarial damage +0.0796 (double zeros at the first
minimum) against budget 0.1534 - coherent with the hardened dual's cap
0.0907 at the same depth, which sits between the measured adversary and
the budget exactly as a one-sided cap should.

The module's own first run had a defect, kept as a control: fixed-order
Gauss-Legendre cannot resolve e^{ixu} beyond |x| ~ 150, and the
truncation ladder ran BACKWARDS.  The argument-sized rule restores the
1/K law; `quadrature_order_control` measures both.

**What the identification does and does not close.**  The dual's
verdict now translates, through measured identities, into exactly the
hypothesis the kernel-checked corollary consumes, over the dual's
swept families and with the joint layer's one-sided completeness.
Remaining, named: the R >= R0 census step (the CG-LP floor under the
gap constraints, instrumented in `kernel_pairing.py`; its nu input at
the paper window is the standing census conversion), the asymptotic
o(N) bookkeeping of the paper's (P) side against these finite-grid
units, and T4's taper/truncation one-sidedness.  The candidate
0.6725106958 stays a candidate; the seam list is now bookkeeping-grade
rather than derivation-grade.  No proportion is claimed.


## Closing the bookkeeping: census, units, T4

Instrument: `closing_bookkeeping.py`; 4 controls appended to
`test_transplant_lemma.py`.

**Census (R >= R0).**  The LP floor is measured NONDECREASING in nu at
fixed edges (0 at nu = 0.5 rising to 1.26e-4 at CG's 0.83625), so the
reading's nu = H_pinned - a lower bound on the true distinct-gap
density via the paper's Theorem B - can only under-state the floor.
Under-reporting nu is one-sided in the safe direction.  A grade note
surfaced on the way: the discovery-grade kernel table would put the
fixed-edge floor near 8e-6 where the reading carries the
hardened-table 5.021179e-6 - the reading already sits on the
conservative side of its own instrument ladder.

**Units.**  On growing nu = 1 lattices, R/N converges to the
translation-invariant reference sum_{k != 0} omega^2(2 pi k) =
0.00612719 (defects 4e-4 / 1.5e-5 / 2.7e-4 at N = 9 / 17 / 33, the
residue being the assembly's own ~1/K truncation), and per-pair damage
is N-stable.  The finite-N identities survive the per-N normalisation
with 1/N edge defects - the shape the paper's o(N) absorbs.

**T4 (truncation directions).**  The beyond-window tail: the 64 real
bands in (G, 2G] carry 5.0e-5 / 1.3e-4 (y = 0.3 / 0.49) of band maxima
against the closed-form allowance 6.6e-4 / 1.8e-3 the cap already
charges - covered with an order to spare.  The LAW D grid truncation is
the assembly ladder's measured ~1/K.  And one more of this session's
defects, caught by its own control: the module's first draft claimed
the truncated assembly under-reports R; it OVER-reports (the dropped
squares live in the norms, inflating the normalised inner products).
The reading is unaffected - its floor uses the exact closed-form
kernel, never truncated grids - and the refuted claim is kept in the
module as the standing lesson.

**What is cited, not re-derived** - the boundary of this laboratory's
remit, stated plainly: the paper's (P)-side prime evaluation of tr and
tr^2, the Theorem B simple-zero density feeding the census, and the
D0-window edge accounting.  Those are the source paper's theorems.
Everything on this side of that boundary is measured, hardened, or
kernel-checked, and every step's grade is in this ledger.

**Final state of the hunt.**  Candidate reading 0.6725106958 =
H_pinned + 2 * 0.995 * 5.021179e-6, with: the window pinned from the
source; the kernel pairing settled by construction at that window;
theta* = 0.995 measured at the paper field (float + ball, single-pair
+ joint, box + ramped); the composition and LAW D kernel-checked
sorry-free; the dual-to-hypothesis dictionary measured term by term
with its last hole-candidate (negative cross traces) found and
covered; and the bookkeeping items closed above.  The word for what
remains between this and "the proportion moved" is the cited (P)-side
- the paper's own asymptotics - plus review.  Per the honest-scope
rule this tree does not claim it; the ledger is the deliverable.  The
session's caught-defect count stands at nine, every one found by a
control or an independent route, none by inspection - which is the
argument for the controls, and the argument for reading this ledger
before believing any number in it.
