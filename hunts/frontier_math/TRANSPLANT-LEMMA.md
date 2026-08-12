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
| MT (phi = cos(sqrt2 t), width-1 box) | 1 : 1.9201 : 2.8566 : 3.7977 | **ALIVE** (CG 1993; c_u one-sided = 5.02e-6 at nu_on) | alias defect 5.3e-3 (box aliases at +-2pi; carry one-sidedly) | minW/sigma^2 = **-0.43**, band at 1.10-1.12 mean gaps |

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
  occupy).  One new burden: the box window's grid form has a measured
  0.53% alias defect, so the law hierarchy must carry an explicit alias
  term one-sidedly.  Expected outcome: theta_full^MT >= the hunt's 0.02,
  plausibly much larger.
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
