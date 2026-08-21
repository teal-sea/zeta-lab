# RESULTS: replication + rigorization of the CvS/CCM truncated Weil form

Study of 2026-08-17, `hunts/rogue_frontier/weil_trunc/`. Sources, exact
construction and claim inventory: `SOURCE.md`. Everything below is graded
**measured** or **hardened** per the repository ladder; nothing here bears on
RH (docs/08 discipline), and nothing in `hunts/` is a result until it
survives a battery it did not write. Raw numbers live in the JSON files
beside this document; reproduction commands are at the end.

## 0. Source verification (the survey vs the record)

Both arXiv IDs the survey cited exist and are current work; the survey's
attributions were scrambled (details in `SOURCE.md` s1). Correct picture:
arXiv:2605.20224 and arXiv:2607.02828 are both by Akiva Groskin (May and
July 2026, both revised 2026-08-14); the construction they implement and
extend is Connes-van Suijlekom (arXiv:2511.23257, Prop 4.1) and
Connes-Consani-Moscovici (arXiv:2511.22755); the open convergence question
is Connes arXiv:2602.04022 s6 (Feb 2026). The headline numbers the survey
quoted (2e-55 at c=13, 1.5e-168 at c=67, both at N=100) are real and sit in
2605.20224 Tables 3/20, not in 2607.02828. Survey verdict: not a
hallucination, but sloppy provenance; every load-bearing fact checked out
against the primary record.

## 1. Replication (independent implementation, no code consulted)

`galerkin.py` implements the truncation from the papers' definitions alone,
via the CCM closed-form assembly Q = W02 - WR - Wp on the Fourier basis of
L^2([0, L]), L = log c, with the archimedean entries re-derived from CCM
(3.15) as digamma/trigamma closed forms plus geometric series in e^{-2L}
(`SOURCE.md` s2). Validation gates, all passing (`run_replication.py`,
`replication.json`):

| gate | what | printed | ours | verdict |
|---|---|---|---|---|
| A | closed forms vs direct quadrature (zeta+DH, off-diag and zeta diag) | -- | agree to 2e-40 | pass |
| B | G2 s2.3 worked example <v,Qv> at (13,4) | 0.049968414571096979730 | 0.0499684145710969797302899 | dev 2.9e-22 |
| B | lambda_min^even(13,4) (G2 Fig 2) | 9.7e-15 | 9.6793e-15 | pass |
| B | pole identity 2 g_v(i/2) = <v,W02 v> | -- | dev 2.1e-50 | pass |
| C | finite-T flow (13,4), T=11/14/18 (G2 Fig 2 inset) | -1.9e-2 / -5.3e-7 / -3.9e-10 | -1.867e-2 / -5.328e-7 / -3.908e-10 | pass |
| D | zero-side dictionary partial sums, M=32..512 (G2 Table 1) | residuals -9.1e-7 .. -4.7e-11 | -9.05e-7 .. -4.66e-11 | pass |
| E | T-route + analytic tail = closed form (zeta (29,6), DH (13,3)) | -- | within remainder bound | pass |
| F | DH kappa closed form vs lab-derived kappa | KAPPA_REF | dev 1.2e-41 | pass |
| G | diagonals from the r-space integral (zeta control + DH) | -- | dev ~1e-3, inside tail bound | pass |
| H | DH diagonal vs zeta diagonal + log 5 + difference-kernel integral | -- | dev 6.7e-31 (n=0), 0.0 (n=1) at dps 30 | pass |

Gate H matters most: a uniform error eps in the DH diagonal constant would
shift every DH eigenvalue by exactly eps (Weyl), and the DH floors reported
in s4 are ~1e-10; the gate validates that constant to ~1e-30, twenty
orders below the smallest floor, via an identity whose integrand decays
like r^-4 (so the window integral genuinely converges).

Headline cells (`run_headline.py`, `headline.json`), ours cutoff-free
(T = infinity) vs the published T = 800 values:

| cell | published lambda_min (T=800) | ours (cutoff-free) | published gamma_1 err | ours |
|---|---|---|---|---|
| (13, 100) | 2.865e-59 [G1 Table 3] | 3.7209e-59 | 2.005e-55 [G1]; 2.44e-55 [CCM, N=120]; ~2.6e-55 [Connes] | 2.6018e-55 |
| (14, 100) | 4.835e-65 [G1 Table 3] | 1.6421e-64 | 3.541e-61 [G1]; ~1.07e-60 [CCM] | 1.1981e-60 |

Both lambda_min values land ABOVE the published finite-T numbers, which is
not a discrepancy but the direction G2's tail-order theorem (Thm 3.2:
lambda_j strictly increasing in T) requires; the gamma_1 errors land inside
the published cluster for both cutoffs. **Replication verdict: full.** No
defect was located in either posting's numbers at the cells we can reach;
the only source blemishes found are two display-level constant slips in CCM
eq. (4.4)/(4.14) that cancel in their own Prop 4.3 table (`SOURCE.md` s2),
caught because we re-derived the entries from (3.15) instead of copying
the table.

## 2. Enclosure-checked smallest eigenvalues (the rigorization)

`enclosures.py` mirrors the assembly in Arb ball arithmetic (python-flint,
the same backend `zeta.rigor` standardizes on): rigorous special-function
balls, geometric-series tails added as explicit ball radii, then three
independent rigorous statements per cell: ball LDL^T inertia at shift 0, a
[LDL-shift, Rayleigh] bracket, and python-flint acb_mat.eig (Rump)
enclosures. All three agreed at every cell (`enclosures.json`).

Zeta, even sector (odd sector inertia also computed, all positive):

| c | N | lambda_min enclosure (mid +/- rad) | inertia at 0 (pos, neg) |
|---|---|---|---|
| 6 | 32 | 1.0617697979925590e-22 +/- 1.7e-101 | (33, 0) conclusive |
| 9 | 32 | 1.9314511727773929e-37 +/- 2.9e-116 | (33, 0) conclusive |
| 13 | 4 | 9.6792618605069722e-15 +/- 1.5e-93 | (5, 0) conclusive |
| 13 | 8 | 7.6743925563601896e-23 +/- 9.1e-102 | (9, 0) conclusive |
| 13 | 16 | 8.5686274780724443e-35 +/- 1.1e-113 | (17, 0) conclusive |
| 13 | 32 | 2.2589311905740534e-49 +/- 1.4e-128 | (33, 0) conclusive |
| 19 | 32 | 3.7533453979020384e-59 +/- 2.0e-138 | (33, 0) conclusive |
| 29 | 32 | 9.3053985193016620e-68 +/- 2.8e-147 | (33, 0) conclusive |

(20 zeta cells total over c in {6,9,13,19,29} x N in {4,8,16,32}; every
cell conclusive, every eigenvalue of both parity sectors strictly positive,
ball radii 1e-91 .. 1e-147.) The signs and magnitudes of lambda_min on this
grid are therefore **hardened**: enclosure-carrying, two independent
rigorous routes agreeing, on top of exact cited entry formulas. The G2
flagship-style statement "n_minus = 0 for the cutoff-free matrix" is
reproduced here at every grid cell by the same LDL^T-in-balls method that
paper reports at (100, 200).

## 3. The measured convergence law (`grid.json`, `rates.json`)

Grid: c in {6,7,9,11,13,17,19,23,29,31,37}, N in {4,8,16,24,32}, plus an
N-ladder at c=13 up to N=64, cutoff-free entries, float eigensolver at
cell-adaptive dps with a dps-130 `mpmath.zetazero` oracle.

**N-law at fixed c (the Galerkin regime).** At c = 13 the local log-log
exponent p(N) = d log10 err_gamma1 / d log10 N is

    N:      8      12     16     20     24     32     40     48     64
    p:   -40.7  -42.8  -46.3  -51.0  -48.2  -50.0  -45.7  -36.8  -18.4

i.e. err ~ N^p with p stabilizing near -49 +/- 3 on 16 <= N <= 40, then
saturation toward the c = 13 floor (err 4.4e-55, lambda_min 6.3e-59 at
N = 64, approaching our N = 100 values 2.6e-55 / 3.7e-59). Falsifiable
statement: at c = 13 with cutoff-free entries, err_gamma1(N) on
16 <= N <= 40 is a power law with exponent -49 +/- 3; the same measurement
at c = 19 or c = 29 (not yet saturated at N = 32) should show the same
shape with a deeper floor. This complements G1: their s(c) exponents were
measured near saturation at N in {40..100} with finite-T entries and their
proposed Paley-Wiener mechanism for them is withdrawn in their v4; our
window is the pre-saturation regime, where the exponent is far larger than
their near-saturation values.

**c-law.** On the N = 32 row (which mixes N-limited and saturated cells),
all five two-parameter smooth models we tried (power law in c, linear c,
c/log c, sqrt(c) log c, log^2 c) fail with rms 3.3-5.8 log10 units, and a
held-out fit misses the c = 37 cell by 7-13 orders. This echoes G1 s5.3,
where all eight pre-registered smooth models fail at N = 100 over
c in [13, 67]. The convergence law in c resists cheap parametrization in
both datasets; that agreement is itself a replication datum.

**The error/eigenvalue ratio** err_gamma1 / lambda_min at N = 32 grows
smoothly 3.4e3 -> 5.5e4 over c = 6 -> 37 (G1 report 7.0e3 -> 1.8e4 over
c = 13 -> 67 at N = 100); same direction, same order.

## 4. The DH control (battery discipline; `dh_control.json`)

The construction ports to Davenport-Heilbronn with three structural
changes, each dictated by the explicit formula (SOURCE.md s4): coefficient
measure Lambda_f(n) on ALL n >= 2 (no Euler product; computed by the
log-derivative recursion with kappa in closed form, validated against the
lab's derived kappa to 1e-41), no pole block (f entire), and archimedean
kernel a = 3/4 with conductor constant log(pi/5) (same shift Groskin's own
chi_3 port uses, corroborating the port design). So the truncation does
NOT structurally reject an RH-violating input; it runs happily on one.

Measured outcome, DH grid c in {6,9,13,19,29,37,47}, N in {4,8,16,32}:

1. **Every DH cell is positive too** , and at N = 32 this is
   enclosure-checked: inertia (33, 0) conclusive at every c, e.g.
   lambda_min(DH, 13, 32) = 1.0205115394980095e-10 +/- 8.9e-90. A
   finite window on Weil positivity does not see DH's RH-violation
   anywhere on this grid.
2. **The DH ground state approximates DH's on-line zeros** the way zeta's
   approximates gamma_k: at (29, 32), err(gamma_1^DH) = 7.3e-26; at
   (47, 32), 1.7e-36 (oracle: `zeta.epstein.Z_dh` bisection at dps 60,
   first ordinate 5.09415984457109492569879551708). The qualitative signature
   "truncated Weil form is positive and its ground state locates the
   zeros" is therefore NOT a zeta-specific behavior at these windows. By
   the battery rule (docs/09 gate #3), that qualitative signature alone
   distinguishes nothing.
3. **What does differ is quantitative and large**: where the N-saturated
   floor is reachable, DH's floor is dozens of orders of magnitude higher
   than zeta's at the same c:

   | c | zeta floor (even) | DH floor (even) | gap |
   |---|---|---|---|
   | 6 | ~1.1e-22 | 7.256383168508e-4 | 19 OOM |
   | 9 | <= 1.9e-37 (not saturated) | 7.790893410286e-7 | >= 30 OOM |
   | 13 | ~3.7e-59 (N=100) | 1.020511539498e-10 | ~49 OOM |

   (DH floors saturate by N = 16..32: the N = 16 -> 32 change is < 15%.
   All DH floor values are enclosure-checked at N = 32.) At c >= 19 the
   DH minimum has not yet saturated by N = 32 (4.9e-17 at 19, 7.5e-38 at
   47, still falling), so only upper bounds are claimed there.
4. **Attribution caveat, stated plainly**: DH differs from zeta in three
   ways at once (RH-violation, no Euler product, no pole), so this
   experiment does NOT identify which property the floor gap tracks. It
   is the detector-strength confound of docs/22 / issue #21 in a new
   instrument. G1's chi_3 port (GRH-true, Euler product, no pole, odd
   character like DH) reaches 28-digit convergence, which weakly points
   away from "no pole" as the driver, but chi_3 vs DH still differs in
   two properties at once.
5. **Thread raised, not pursued** (mission scope): since Weil positivity
   is false for DH, the cutoff-free DH band minimum must go negative for
   some finite c (the band-limited family is asymptotically dense in the
   admissible class); our data say that c > 47 at N <= 32. Where the
   first negative appears, and whether the floor's decay accelerates as
   the band reaches DH's first off-line ordinate (t ~ 85.7), is a sharp,
   well-posed computational question this battery run surfaces. It
   belongs in an issue, not in this hunt.

## 5. Grading summary

- lambda_min signs and magnitudes on both grids (s2, s4 item 1/3):
  **hardened** (enclosure-carrying, independent rigorous routes agreeing).
- Replication matches (s1), rate measurements (s3), DH comparisons (s4):
  **measured** (float arithmetic under precision policies, high-precision
  oracles, printed-value cross-checks).
- Nothing here is kernel-checked; nothing here uses the reserved word,
  which belongs to `zeta/rigor.py`.

## 6. Caveats and incidents (recorded, not buried)

- Two oracle-precision defects were caught during the runs by the
  "identical floor across unrelated cells = artifact" reflex: (i) gamma
  errors floored at 7.7e-31 because the repo's dps-30 zero cache was used
  as oracle; (ii) after switching to a dps-130 oracle, errors floored at
  9.71e-48 because the reference strings were parsed at the ambient dps of
  the first grid cell (47). Both fixed (`run_grid.py` parses inside
  `mp.workdps(135)`); the incident is why every floor in this document was
  re-derived after the fix and why the DH floors were additionally checked
  for c-dependence (a uniform-shift artifact cannot produce c-dependent
  floors).
- The published lambda_min values are finite-T (T = 800); ours are
  cutoff-free. They are different numbers by design and are compared only
  directionally (ours must sit above, and do).
- Zero-location errors use float eigenvectors (mpmath eigsy); only the
  eigenvalue statements carry enclosures. Extraction noise is bounded well
  below every reported error by the cell dps policy.
- The DH floor interpretation carries the attribution confound of s4
  item 4, and DH floor values at c >= 19 are upper bounds only.
- The c = 13 N-ladder exponent p ~ -49 is a cutoff-free, pre-saturation
  measurement; it is not comparable 1:1 with G1's near-saturation
  finite-T s(c) values, and neither settles a mechanism (theirs is
  explicitly withdrawn in their v4).

## 7. Reproduction

From the repo root, in order (total ~25 min on this machine):

    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_replication.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_grid.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_enclosures.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_dh.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_headline.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/fit_rates.py

Requires: the repo venv (mpmath, numpy, python-flint), network access NOT
required, writes only inside this directory. `gammas_dps130.json` is
regenerated by twelve `mpmath.zetazero` calls at dps 130 if deleted.

## 8. Where DH's Weil-positivity failure first becomes visible (s4 item 5, pursued)

Follow-up study of 2026-08-17, run as its own tasked session; drivers
`dhneg_scan.py` / `dhneg_confirm.py` / `dhneg_localize.py`, every data point
in `dhneg_scan.json`, session log in `dhneg_log.md`. Question (raised in s4
item 5 and left there as a thread): Weil positivity is FALSE for DH, so the
cutoff-free truncated form must eventually acquire a negative eigenvalue;
where is the first (c, N)? The off-line pair is at
rho = 0.80851718245663738555 + 85.69934848537759217193 i
(`zeta.epstein`, pinned), delta = beta - 1/2 = 0.30851718...

### 8.1 The answer

**The first negative cell on the integer lattice is (c*, N*) = (31, 60),
even sector**, and the sign statements below are **hardened** (enclosure-
carrying, three independent rigorous routes, plus the independent-code
mpmath scout):

| statement | route | value |
|---|---|---|
| lam_min(DH, 31, 60) < 0 | ball LDL^T inertia at 0, prec 700 | even inertia (60 pos, 1 neg), conclusive |
| same | Rayleigh quotient of a recorded exact-dyadic vector, ball upper endpoint | -1.8693e-31 < 0 |
| same | acb_mat.eig Rump enclosure | -1.87393568857018838649e-31, radius ~1e-241 |
| float scout (independent implementation) | mpmath eigsy, dps 60 | -1.8739356885701883865e-31 |
| one step earlier: lam_min(DH, 31, 59) > 0 | ladder pivots + scout | +8.3650456617028903377e-31 |
| odd sector at (31, 60) | ball LDL^T | (60, 0) conclusive, positive |
| **zeta control at the same cell** | ball LDL^T at prec 2400 + eig enclosure | even (61, 0), odd (60, 0), conclusive; lam_min = +4.8216e-100 |

The zeta control is the discrimination statement: the SAME truncation, at
the SAME (c, N), is positive for zeta by a hundred orders of magnitude and
negative for the structure-matched RH-violating rival. This is the first
quantitative positivity-failure height for the 2026 truncated-form
programme (CvS Prop 4.1 / CCM (3.10) / G1, G2) on an input that violates
the RH analogue: the finite window stops being blind to DH's off-line
zeros at c = 31, N = 60.

### 8.2 The transition curve (one factorization per c gives the whole N-ladder)

Method dividend that made the sweep cheap: the (N+1)-band even matrix is
the leading principal submatrix of the Nmax-band one, and LDL^T pivots
give the inertia of every leading principal submatrix at once (number of
negative eigenvalues at band N = negative pivots among the first N+1).
One conclusive ball factorization at Nmax = 128 per integer c in 6..60,
prec 600, ~1 s each (`dhneg_scan.json` "ladders"):

- **c <= 30: no negative eigenvalue at any N <= 128**, either sector;
  c = 29 and c = 30 probed to N = 256, still conclusively positive. The
  band edge 2 pi N / L at those probes is ~470 >> 85.7, so this is NOT a
  reach limit: below c* the bandwidth L = log c is what is insufficient.
- **c = 31: first negativity, N = 60** (band edge 109.8; odd sector still
  positive at N = 192; n_neg stays 1 through N = 192).
- **c = 32..60: first_neg_N in 48..54**, and the band edge at the
  crossing is 83.6 +- 2.5, i.e. the crossing happens as soon as the band
  reaches the off-line ordinate 85.699 (plus beam-shaping margin; at
  c = 31 the margin is largest, N* = 60 vs reach N = 47, where the
  analytic-continuation amplification e^{delta L} = c^0.3085 ~ 2.9 is
  weakest).
- **c >= 44: a second negative eigenvalue** appears by N = 128, at band
  edge ~114-138. The on-line cache has a second spacing gap
  112.38..116.72, an argument-principle box-vs-line count on
  112 < t < 117 gives box 4 vs line 2 (one more off-line pair), and a
  findroot polish inside that window lands on
  rho_2 = 0.6508300806 + 114.1633427308 i with |f(rho_2)| ~ 4e-42
  (measured; delta_2 = 0.1508, weaker amplification, which is consistent
  with its higher c threshold).

Approach to negativity at c = 31 (even lam_min, enclosure mids; full
trajectories for c in {13, 19, 29, 31, 32, 33, 37, 41, 43, 45, 47, 53}
are in `dhneg_scan.json` "trajectories"):

    N:     40        48        56        59        60         64         96        128       192
    lam: +1.7e-29  +8.1e-30  +2.5e-30  +8.4e-31  -1.9e-31  -3.8e-30  -6.6e-30  -7.5e-30  -7.8e-30

Saturated depth vs c (N = 128 slice): +9.5e-29 (c=30), -7.5e-30 (31),
-8.4e-28 (32), -2.0e-23 (33), -2.7e-7 (37), -3.4e-2 (41), -0.175 (43),
-0.288 (45), -0.333 (47), -0.663 (53). The depth climbs ~28 orders of
magnitude over 31 <= c <= 41: the threshold is sharp in c, and for
c <= 30 the still-positive floors (e.g. 6.6e-28 at c = 29, N = 256) are
falling only slowly in N.

### 8.3 Localization: the negativity is the off-line pair speaking

Three measured lines of evidence (float route, dps 40-60):

1. **Deep cell (47, 64), lam_min = -0.3163**: the eigenvector is a beam
   at the off-line ordinate. Peak mode k = 52 vs k_off = gamma_off L /
   (2 pi) = 52.5; 95.6% of the coefficient mass within +-6 of 85.699;
   |F_v| maximal at z = 84.5, inside the on-line gap 83.109..87.647 that
   contains the off-line ordinate. (That 4.5-wide gap, where DH's two
   would-be line zeros went off the line, is what a bandwidth-3.85 beam
   can thread; the mean on-line spacing there is 1.49.) The zeta control
   at this deep cell is also positive and conclusive: even inertia
   (65, 0) at prec 4200, lam_min(zeta, 47, 64) = +6.6006e-119, against
   DH's -0.3163 at the same cell.
2. **Dictionary decomposition at the marginal cell (31, 60)** (ported
   G2 Thm 2.5 zero-side sum; on-line ordinates from the lab cache, the
   24 largest terms re-bisected with `zeta.epstein.Z_dh` at dps 50):

       lam                        = -1.8739e-31
       off-line quadruple 4 Re g_v(gamma_off - i delta) = -6.7350e-29
       on-line partial sum (T <= 120, 64 terms, all >= 0) = +5.9537e-29
       lam - quadruple            = +6.7162e-29  (POSITIVE)
       tail model T > 120 (mean density) = +3.0e-30
       second-pair quadruple      = +7.6e-32
       unexplained bookkeeping    = ~4.7e-30 (7% of |quad|)

   The quadruple term is 359x the eigenvalue and is the only negative
   entry in the decomposition: removing it flips the form value positive
   with a margin factor of ~14 over the bookkeeping slop. The largest
   single on-line term sits at gamma = 89.44, the nearest zero beyond the
   gap edge, exactly where beam leakage must land.
   The same decomposition at the deep cell (47, 64), dps 50:
   lam = -0.31630285, quadruple = -0.83065725 (again the only negative
   entry, 2.6x lam), on-line sum = +0.49306094, lam - quadruple =
   +0.51435440, bookkeeping closes to 2.2% (tail model 0.0098, residual
   0.0213). Largest on-line term at gamma = 87.647, the other gap edge.
3. **The marginal-cell shape**: at (31, 60) the eigenvector is bulk
   low-frequency (quasi-ground-state) with a whisper of the 85.7 beam
   (coefficient mass 7.8e-29 near the target vs |lam| = 1.9e-31), which
   is why the dictionary, not the coefficient profile, carries the
   identification there; the second negative direction at (47, 128),
   itself a fresh marginal crossing at -4.4e-33, shows the same pattern
   aimed at the second gap.

### 8.4 Grading and caveats

- **Hardened**: every sign statement in 8.1; the transition curve
  first_neg_N(c) for c in 6..60 (each cell a conclusive-pivot ball
  factorization); the deep probes at c = 29, 30, 31; the trajectory
  values (eig enclosure mids with recorded radii, 1e-160s and below).
- **Measured**: the localization profiles, the dictionary decomposition
  (float cache ordinates for the 40 unrefined on-line zeros, a
  mean-density tail model, and the ported-dictionary assumption itself,
  corroborated here by the decomposition closing to 7%), rho_2, and the
  mechanism reading "the negativity is the first off-line pair". The
  composite claim takes this measured grade; the negativity itself does
  not depend on it.
- **"First" is a lattice claim**: first on integer c with N <= 128
  (N <= 256 at c = 29, 30; N <= 192 at c = 31). The N -> infinity limit
  at fixed c <= 30 (the bandwidth-L Weil form) is not settled by these
  probes: lam_min was still slowly decreasing at the ceilings. What is
  settled is that the detector's first firing on the searched lattice is
  (31, 60), and that it fires there for the RH-violating input only.
- s4's grid statement "positive everywhere at N <= 32, c <= 47" stands;
  those windows never reached the off-line ordinate (band edge <= 52.2 <
  85.7). The s4 item 4 attribution confound (DH differs from zeta in
  three properties at once) does not touch the negativity itself, which
  is a property of the form, but it also does not arise for the
  mechanism claim here: the dictionary term that flips the sign is
  computed at the off-line zero's own coordinates.

### 8.5 Reproduction

From the repo root (total ~45 min, writes only inside this directory):

    .venv/bin/python hunts/rogue_frontier/weil_trunc/dhneg_scan.py           # c-sweep 6..60, Nmax 128
    .venv/bin/python hunts/rogue_frontier/weil_trunc/dhneg_confirm.py        # deep probes, scouts, enclosure package, zeta control
    .venv/bin/python hunts/rogue_frontier/weil_trunc/dhneg_localize.py       # localization + dictionary attribution
