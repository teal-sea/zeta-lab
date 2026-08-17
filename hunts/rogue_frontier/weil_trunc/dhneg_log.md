# dhneg: progress log

Goal: first (c, N) where the DH truncated Weil form acquires a negative
eigenvalue, enclosure-checked, with zeta control and localization evidence.
Data: `dhneg_scan.json` (checkpointed per point). Drivers: `dhneg_scan.py`,
`dhneg_confirm.py`, `dhneg_localize.py`.

## Session 2026-08-17

### Groundwork (before any scan)

Off-line pair (zeta.epstein, pinned): rho = 0.80851718245663738555 +
85.69934848537759217193 i, so delta = beta - 1/2 = 0.30851718..., gamma_off =
85.699348... The quadruple {rho, 1-rho, conj} enters the zero-side dictionary
as 4 Re g_v(gamma_off - i delta).

On-line landscape (data/dh_zeros_online_T120.json, 64 zeros to T=120):

- 43 on-line ordinates below 85.699.
- Local spacing near t=85.7 is ~1.5 (mean density (1/2pi) log(5t/2pi) =
  0.672/unit at t=85.7), EXCEPT a 4.54-wide gap between 83.109 and 87.647.
  The off-line ordinate sits inside that gap. So a band-limited beam of
  width ~2pi/L placed in the gap touches no on-line zero within +-2.2.

### Regime reasoning (what (c, N) should first expose the pair)

Three requirements interact:

1. Band reach: the even-sector test functions F_v have resonances at
   z = 2 pi k / L, k <= N; to place mass at gamma_off the band edge
   2 pi N / L must exceed 85.7. That gives N > 13.64 L: N > 35 (c=13),
   N > 46 (c=29), N > 52.5 (c=47). The whole existing positive grid
   (N <= 32, c <= 47) has band edge <= 52.2 < 85.7: it never reached the
   off-line ordinate at all. The N=32 truncation was indeed too coarse.
2. Amplification: the quadruple term carries the analytic-continuation
   factor ~ e^{delta L} = c^{0.3085} (|sin(zL/2)| ~ e^{delta L/2}/2 off the
   axis). Small: 2.2 at c=13, 3.3 at c=47. So negativity is not free; the
   on-line positive terms near the beam must be suppressed.
3. Suppression capacity: a positive-type band-limited g (hat g >= 0 on R,
   type L) can vanish on reals only at density L/(2pi) per unit (real zeros
   come doubled), vs on-line density 0.672/unit near t=85.7; equality at
   L = 4.22, c ~ 68. BUT the 4.5-wide gap at 85.7 relaxes this: the beam
   needs to null neighbors only outside the gap, so the practical threshold
   should sit well below c=68. Expect first negativity at moderate c once
   N crosses the band-reach line ~ 13.64 L with some margin for beam
   shaping.

Probe first: N-ladders (pivot-sign LDL in balls: one factorization at Nmax
gives n_neg for every principal N at once) at c in {13, 19, 29, 37, 47},
Nmax = 96; then bisect c downward.

### First timing probe (before the systematic scan)

c=47, N=96, prec=600: assembly 0.2 s, even LDL 0.1 s, inertia (95, 2)
conclusive: TWO negative eigenvalues. eig on the N=64 principal submatrix:
lam_min ~ -0.316 (not small). So the transition is somewhere at N <= 64 for
c=47, and the negative value is O(0.1), far above the 1e-38 positive floor
at N=32. A float scout cross-check (independent mpmath route) is mandatory
before believing this; scheduled next.

Float scout agreed to all printed digits: mpmath eigsy at (47, 64), dps 40,
gives lam_min = -0.316302853076, one negative eigenvalue, next eigenvalue
+1.5e-41. Ball route trusted; systematic scan started.

### The scan (dhneg_scan.py; all points in dhneg_scan.json)

Method observation that made the scan cheap: ONE ball LDL^T factorization
at Nmax gives the inertia of EVERY leading principal submatrix (the number
of negative eigenvalues at band N = number of negative pivots among the
first N+1), so first_neg_N(c) is one factorization per c per sector,
~1 s per c at Nmax = 128, prec 600. Full integer sweep c = 6..60 done.

Transition curve (even sector; odd tracks it 0..1 steps later):

- c <= 30: NO negativity to N = 128; deep probes c = 29, 30 stay positive
  to N = 256 conclusively (band edge ~470 >> 85.7, so it is not a reach
  limit; the bandwidth L = log c is genuinely too small to build the
  negative functional).
- c = 31: first negativity, even sector, exactly at N = 60; odd sector
  still positive at N = 192. Crossing pinned by float scout (mpmath,
  independent route): lam_min(31, 59) = +8.365e-31,
  lam_min(31, 60) = -1.874e-31, lam_min(31, 64) = -3.81e-30.
- c = 32..60: first_neg_N between 48 and 54, with the band edge
  2 pi N / L at the crossing hugging 84 +- 5, i.e. the off-line ordinate
  85.699 (the crossing happens as soon as the band reaches the off-line
  pair, plus a small beam-shaping margin; at c = 31 the margin is larger,
  N = 60 vs reach 47, because the amplification e^{delta L} ~ 2.9 is
  minimal there).
- c >= 44: a SECOND negative eigenvalue appears by N = 128, at band edge
  ~114-138. The on-line cache shows a second zero gap 112.38..116.72, and
  an argument-principle box-vs-line count on 112 < t < 117 gives
  box = 4 vs line = 2: a second off-line pair sits there. Its negativity
  onset tracks its own gap exactly as the first pair's did.

Saturated negativity depth vs c (N = 128 slice, even):
c = 28: +6.4e-28, 29: +6.6e-28, 30: +9.5e-29 (all positive);
c = 31: -7.5e-30, 32: -8.4e-28, 33: -2.0e-23, 37: -2.7e-07, 41: -3.4e-02,
43: -0.175, 45: -0.288, 47: -0.333, 53: -0.663. The depth climbs ~28
orders of magnitude over 31 <= c <= 41: the threshold is sharp.

### Confirmation package at (31, 60), prec 700 (dhneg_confirm.py)

- even inertia at 0: (60 pos, 1 neg), conclusive; odd: (60, 0) conclusive.
- Rayleigh upper bound from a recorded exact-dyadic vector (dps-60
  eigenvector snapshot, mantissa/exponent pairs in the JSON): upper ball
  endpoint -1.8693e-31 < 0. This alone is a rigorous negativity witness.
- Rump eig enclosure: lam_min = -1.8739356885701883864888e-31 with ball
  radius ~1e-241; next eigenvalue +3.56e-31.
- mpmath float scout agrees to all displayed digits.

### Zeta control at (31, 60)

Same assembly, zeta data, prec 2400 (prec 700 was inconclusive: zeta's
floor here is ~5e-100, LDL elimination entries reach ~1e100 and square
into the pivot radii, so ~200 digits of cascade error need headroom):
even inertia (61, 0) conclusive, odd (60, 0) conclusive,
lam_min(zeta, 31, 60) = 4.8216e-100 > 0. The SAME truncation, same cell,
stays positive for zeta and goes negative only for the RH-violating
input.

### Localization

- Deep cell (47, 64): eigenvector of lam_min = -0.3163 is a textbook
  beam: peak mode k = 52 (frequency 2 pi k/L = 84.86; the off-line
  ordinate predicts k_off = 52.5), 95.6% of the mass within +-6 of
  85.699, |F_v| maximal at z = 84.5, inside the on-line gap 83.11..87.65
  that contains the off-line ordinate.
- Marginal cell (31, 60): the eigenvector is bulk low-frequency (the
  usual quasi-ground-state shape) with a whisper of the 85.7 beam
  (mass fraction 7.8e-29 near the target vs |lam| = 1.9e-31); at the
  threshold the negativity rides on a tiny admixture, so the
  identification burden falls on the dictionary decomposition
  (running: quadruple term 4 Re g_v(gamma_off - i delta) vs lam).
- Second negative at (47, 128) is its own marginal crossing
  (-4.4e-33), same whisper pattern aimed at the second gap.

### Dictionary attribution at (31, 60) (the mechanism check)

Zero-side decomposition of lam = <v0, Q v0> per the ported G2 Thm 2.5
dictionary (all terms computed with galerkin.g_even at dps 60; top-24
on-line ordinates refined by Z_dh bisection at dps 50):

    lam                      = -1.8739e-31
    off-line quadruple term  = -6.7350e-29   (= 4 Re g_v(85.699... - 0.30852 i))
    on-line partial sum T<=120 = +5.9537e-29   (64 terms, every one >= 0)
    lam - quad               = +6.7162e-29   POSITIVE
    residual (lam - quad - online) = +7.6e-30
    tail model (mean density, T>120) = +3.0e-30
    second-pair quadruple    = +7.6e-32   (rho2 located: 0.650830 + 114.163343 i,
                                           |f(rho2)| ~ 4e-42, box-window seeded)
    unexplained bookkeeping  = ~4.7e-30 (7% of |quad|; float cache ordinates
                                          for the 40 unrefined zeros + crude
                                          density tail; sign conclusions
                                          unaffected, margin factor ~14)

So: the off-line quadruple's dictionary term is 359x the eigenvalue and is
the only negative entry; removing it flips the form value positive. The
negativity is the off-line pair speaking, quantitatively.

Largest single on-line term sits at gamma = 89.44, the nearest zero
beyond the gap edge: the positive leakage lands exactly where the
beam-in-gap picture says it must.

### Second lab defect note (recorded, none found this session)

The two independent routes (mpmath galerkin vs Arb enclosures) agreed at
every cross-checked cell to all displayed digits; no oracle or precision
defect surfaced in this study. The prec-700 zeta-control inconclusiveness
was a precision-budget effect (pivot cascade), not a defect; prec 2400
resolved it conclusively.
