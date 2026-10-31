# RESULTS: ghost zeros of the DH ground-state transform (lane ghost-zeros)

1. **P is confirmed, with a wide margin (hardened, band N = 128).** At each of the seven preregistered windows, c = 29, 30, 61/2, 245/8 before the N = 128 even crossing c*_128 in (30.646484375, 30.6474609375] and c = 31, 63/2, 47 after it, DH's even ground-state transform F_v has exactly one zero in the gap rectangle [83.109, 87.647] x [-1/2, 1/2] around the off-line ordinate gamma_1 = 85.69934848 (counted on that nominal rectangle through R_ctx, s1). That zero is real and simple, and lies between 85.7179 and 85.7344, so 0.019 to 0.035 above gamma_1. An exploratory scan below 29 finds a zero within 0.3 of gamma_1 at every scan window from c = 15 on (15, 16, 17, 18, 22, 25, 27, 28), where the even form is still positive.
2. **The lesion ties the ghost to the off-line quadruple.** Subtracting that quadruple's term (4/L) Re(a(z_1) a(z_1)^T) removes the ghost at all seven windows: no zero is left within 0.3 of gamma_1, and the lesioned transform's zeros move to within 0.022 of DH's own on-line zeros for c >= 30 (at c = 47 they read 81.9254, 83.1088, 87.6475, 89.4392, DH's zeros to four decimals). Subtracting an on-line term of the same kind (at the DH zero 89.4392) keeps the ghost at all seven windows, moved to 85.7061 to 85.7073. To first order Q1 = (4/L) F_v'(x_g)^2 [(gamma_1 - x_g)^2 - delta_1^2], with x_g the ghost; the measured Q1 is 1.063 to 1.100 times that value at every preregistered window (S2 holds).
3. **Controls.** zeta, at the same N and c, has no zero in its gap rectangle [gamma_23 + 0.01, gamma_24 - 0.01] x [-1/2, 1/2] at any of the seven windows. Its four zeros in [80.5, 90.5] each lie inside a zero bracket of F_v no wider than 2.4e-38, and F_v has no other zero in R_ctx (s4). Epstein (1,1,6), the rival with its own off-line zero, behaves like DH: exactly one zero in its on-line gap (14.6305, 18.8285) at each window, real, at 16.200 to 16.236, which is 0.055 to 0.090 below its off-line ordinate 16.2902. The Dedekind zeta of Q(sqrt(-23)) has no ghost at any window. S5 still fails as preregistered, because at that height its transform does not follow zeta_K's on-line zeros, so that negative control is weak there (s4).
4. **CvS hypotheses, band-N matrix.** H1 (simple) and H3 (isolated) hold at every (kind, c). H2 (the lowest eigenvector of the whole form is even) fails for DH at c = 63/2 and 47, and for Epstein at c = 29 and 47: there the odd sector dips below the even bottom. A derivation written before computing (PREREG s3; ordinary argument, unreviewed) says that in the band-N even space a simple lowest eigenvalue alone forces every zero of F_v to be real or purely imaginary. All 264 rectangles counted, every one with H1, had as many zeros as real sign changes (S1).
5. **Not claimed.** These are statements about the band-N matrix that `../../rogue_frontier/weil_trunc` assembles, at the listed windows. There is no statement about the continuum minimiser and no claim of convergence in N; the exploratory basis-size response moves the ghost by at most 6.2e-04 between N = 64 and N = 256 at c = 29, 31, 47. Nothing here bears on RH. The result is original to this lane. No literature search was run for it beyond the sources the theory worker engaged (CCM, CvS).

Lane "ghost-zeros" of hunt `weil_propagation`, branch `hunt/weil-ghost-zeros`,
2026-10-21. The prediction and every rule below were fixed in `PREREG.md`,
committed as 2851018e9 before any ground state of this lane existed. Code:
`ghost.py`; pins: `test_ghost.py`; raw record: `ghost_table.json` (merged from
`units/` by `ghost.py summary`); run log: `RUNS.md`. Grades follow the ladder
in `AGENTS.md`. Here *hardened* means that every step of a count carries an Arb
enclosure and that the count was repeated at a second precision and by a float
route written separately (s0 lists what the two routes share).

## 0. What was run, and the deviations from PREREG

As preregistered: four kinds (dh, zeta, epstein (1,1,6), dedekind Q(sqrt(-23)))
at c in {29, 30, 61/2, 245/8, 31, 63/2, 47}, band N = 128, even sector. H1 to
H3 come from ball LDL^T. The Davis-Kahan eigenvector radius eta comes from the
ball residual and the gap proved by H1's shift. Zeros are counted by an Arb
argument principle (Taylor models with a Cauchy remainder, vertical sides at
least 1/32 from every omega_k) and by enclosure-carrying sign changes at step
1/512. Everything was repeated at a second precision (640 bits; for zeta, 1300
bits with the LDL steps at 3200) and by the mpmath float route. The Q1 lesion
and the on-line sham lesion were run, and so was the exploratory scan at
c in {14, 18, 22, 25, 27, 28}.

Deviations, each decided before the numbers it affects existed:

- **Control windows from PARI.** One `zeta.epstein.Z_epstein` evaluation took
  about 10 s on the loaded box, so the preregistered Z_epstein scan at step
  1/100 would have taken hours. Epstein's on-line zeros in [12, 21] therefore
  come from PARI `lfunzeros(lfunqf([2,1;1,12]))`, each confirmed by a sign
  change of Z_epstein at +-0.01. zeta_K's come from PARI
  `lfunzeros(lfuncreate(x^2+x+6))`; they agree to 1e-8 with the mpmath list
  (zetazero plus sign changes of the completed L(1/2 + it, chi_-23)), and each
  is confirmed by a sign change of Z_(1,1,6) + 2 Z_(2,1,3).
- **Bisection depth.** Zero brackets are bisected to 2^-70 (dh, epstein,
  dedekind) and 2^-136 (zeta), so that S7's location tolerances (1e-20, 1e-40)
  can be read. PREREG s4 said 2^-40.

The finer scan c in {15, 16, 17}, S2 on the scan windows, and everything in s9
were added after the primary numbers and are exploratory. So was the reading of
counts on the nominal rectangles through R_ctx (s1); it is bookkeeping on the
same enclosures, and adds no computation.

**What the float route shares with the Arb route.** It is a second
implementation of the same assembly formulas (`galerkin.Truncation` is the
mpmath original of which `enclosures.BallTruncation` is the ball twin), so it
checks the code, not the derivation of those formulas. The two routes also
share the prime-power sieve `galerkin.prime_powers_upto` (imported by the Arb
assembly) and, for Epstein and Dedekind, the integer representation counts of
`zeta.epstein.epstein_representation_count`. The inverse iteration, the
inertia, the transform (sinc form against the partial-fraction form), the zero
scan and the winding number are separate code.

**The counter's place among the lab's instruments.** The Arb argument
principle here is a sibling of the chord-tube segment winding count indexed in
`docs/37-methods.md` (`hunts/lambda_dh_bounds/`). Both accept a boundary segment
only when the image provably stays in a half-plane and otherwise bisect or
refuse; this one bounds the image by a Taylor model with a Cauchy remainder
instead of a second-derivative tube. It was built before that index entry was
consulted, and the lane does not add itself to the index (its mission confines
it to `hunts/weil_propagation/`).

**One void launch** (`RUNS.md`). The first DH launch voided c = 31 and 63/2. A
residual at rounding level made the square root of the residual's ball NaN,
so eta and every sign were undecided. `ghost.residual_upper` fixes it, pinned
by `test_residual_bound_is_finite_at_rounding_level`, and the DH run was
repeated from scratch.

**Eigenvector radius limited by iterations, not precision.** Where inverse
iteration at shift 0 was used (positive definite even forms), eight iterations
leave a component along the second eigenvector, and eta is the same at both
precisions. It stays a valid bound, and it caps the bisection: Epstein at
c = 29 has eta 7.0e-15 and zero brackets up to 1.2e-10 wide, and
zeta has brackets up to 2.4e-38 wide. No count and no decision depends
on this.

## 1. DH: the ghost at the preregistered windows

| c | lambda_1 (ball RQ) | lambda_2 (est.) | H1 simple | H2 even | eta | Q1 | zeros in R_gap | ghost x | x - gamma_1 |
|---|---|---|---|---|---|---|---|---|---|
| 29 | 6.575e-28 | 2.1e-20 | yes | yes | 6.6e-61 | -1.297e-27 | 1 | 85.729815 | +0.0305 |
| 30 | 9.548e-29 | 1.3e-21 | yes | yes | 5.3e-58 | -2.759e-29 | 1 | 85.734417 | +0.0351 |
| 61/2 | 9.575e-30 | 6.0e-22 | yes | yes | 4.0e-63 | -1.276e-28 | 1 | 85.731484 | +0.0321 |
| 245/8 | 1.099e-30 | 5.1e-22 | yes | yes | 4.8e-70 | -1.284e-28 | 1 | 85.731337 | +0.0320 |
| 31 | -7.529e-30 | 3.2e-22 | yes | yes | 2.4e-95 | -1.054e-28 | 1 | 85.731180 | +0.0318 |
| 63/2 | -8.323e-30 | 1.1e-22 | yes | no | 6.8e-95 | -9.985e-29 | 1 | 85.731163 | +0.0318 |
| 47 | -3.325e-01 | -4.4e-33 | yes | no | 2.9e-115 | -8.309e-01 | 1 | 85.717910 | +0.0186 |

lambda_1 is the ball Rayleigh quotient of the inverse-iteration vector (its
Temple bracket is in the JSON); lambda_2 is the estimate that placed the LDL
shift. At every c <= 63/2, lambda_1, Q1 and the first six coefficients agree
with `../numerics/grid_dh_N128.json` (`test_table_reuses_the_grid_where_it_applies`).
The ghost is the only zero in R_gap at every c. DH's on-line neighbours
83.1088 and 87.6475 have no approximant inside the gap, and in R_ctx =
[80.5, 90.5] the other real zeros of F_v sit 0.12 to 0.57
from DH's on-line zeros. The ghost's distance from gamma_1 stays put although
lambda_1 changes sign and Q1 runs from -2.759e-29 (c = 30) to -8.309e-01
(c = 47).

**Sides, and the nominal rectangles.** As PREREG s4 allows, the argument
principle moved a vertical side inward where it came within 1/32 of some
omega_k or where a segment did not close; the largest move in a primary DH
rectangle is 0.053 (the left side of R_gap at c = 30, moved off omega_45). The
sides used are in the JSON (`rects.*.AP.a`, `b`). The counts in the tables are
on those rectangles. The counts on the nominal rectangles follow from R_ctx:
wherever R_ctx's count closed and equalled its sign changes (S1), every zero of
F_v in R_ctx is real, simple and alone in one sign bracket, so a nominal
rectangle inside R_ctx holds exactly the brackets inside it (`nominal_count` in
`ghost.py`, the `nominal_counts` block of the table). Read that way, DH's
nominal R_gap and R_ghost hold exactly one zero at every c, zeta's none, and
Epstein's one.

## 2. Below c = 29 (exploratory scan)

| c | lambda_1 | H1 | zeros in R_gap | ghost x | x - gamma_1 | Q1 |
|---|---|---|---|---|---|---|
| 14 | 6.279e-12 | yes | 2 | none | n/a | 1.119e-14 |
| 15 | 3.920e-13 | yes | 1 | 85.661572 | -0.0378 | -3.871e-15 |
| 16 | 3.522e-14 | yes | 1 | 85.748487 | +0.0491 | -5.225e-16 |
| 17 | 4.085e-15 | yes | 2 | 85.854219 | +0.1549 | -2.348e-17 |
| 18 | 4.309e-16 | yes | 2 | 85.475904 | -0.2234 | 4.080e-19 |
| 22 | 2.753e-20 | yes | 2 | 85.793971 | +0.0946 | -5.406e-22 |
| 25 | 1.411e-23 | yes | 1 | 85.734771 | +0.0354 | -5.276e-24 |
| 27 | 1.188e-25 | yes | 1 | 85.744303 | +0.0450 | -2.132e-26 |
| 28 | 6.448e-27 | yes | 1 | 85.732374 | +0.0330 | -9.296e-27 |

At c = 14 the gap holds two zeros; the nearer, 85.360095, is 0.3393 below
gamma_1, outside the 0.3 radius, and Q1 > 0 there. From c = 15 on
there is a zero within 0.3 of gamma_1 at every scan window. At 15 and 16 it is
alone in the gap. At 17, 18 and 22 a second zero shares the gap, and the near
one sits at +0.1549, -0.2234 and +0.0946 (at most 0.2234 from
gamma_1 below c = 25). Q1 is negative at every scan window except 14 and 18.
At every grid window from c = 25 on (scan and preregistered) the gap holds a
single zero, at 85.717910 to 85.744303 (at most 0.045 from gamma_1). The even
form is positive at every scan window and at c = 29 to 245/8 (conclusive ball
LDL^T at shift 0), and the N = 128 crossing bracket is c*_128 in
(30.646484375, 30.6474609375]. So on this grid a zero within 0.3 of gamma_1 is
present at every window from c = 15 on, and it appears while the form is still
positive, well before the sign flip.

## 3. The first-order link between the ghost and Q1 (S2)

| c | window set | x_g | x_g - gamma_1 | Q1 | first-order value | ratio | sign rule applies | holds |
|---|---|---|---|---|---|---|---|---|
| 14 | scan | 85.360095 | -0.3393 | 1.119e-14 | 2.862e-15 | 3.911 | no | yes |
| 15 | scan | 85.661572 | -0.0378 | -3.871e-15 | -3.987e-15 | 0.971 | yes | yes |
| 16 | scan | 85.748487 | +0.0491 | -5.225e-16 | -4.784e-16 | 1.092 | yes | yes |
| 17 | scan | 85.854219 | +0.1549 | -2.348e-17 | -2.565e-17 | 0.916 | yes | yes |
| 18 | scan | 85.475904 | -0.2234 | 4.080e-19 | -8.607e-19 | -0.474 | yes | no |
| 22 | scan | 85.793971 | +0.0946 | -5.406e-22 | -5.617e-22 | 0.963 | yes | yes |
| 25 | scan | 85.734771 | +0.0354 | -5.276e-24 | -4.835e-24 | 1.091 | yes | yes |
| 27 | scan | 85.744303 | +0.0450 | -2.132e-26 | -2.010e-26 | 1.061 | yes | yes |
| 28 | scan | 85.732374 | +0.0330 | -9.296e-27 | -8.499e-27 | 1.094 | yes | yes |
| 29 | C | 85.729815 | +0.0305 | -1.297e-27 | -1.178e-27 | 1.100 | yes | yes |
| 30 | C | 85.734417 | +0.0351 | -2.759e-29 | -2.595e-29 | 1.063 | yes | yes |
| 61/2 | C | 85.731484 | +0.0321 | -1.276e-28 | -1.171e-28 | 1.090 | yes | yes |
| 245/8 | C | 85.731337 | +0.0320 | -1.284e-28 | -1.176e-28 | 1.092 | yes | yes |
| 31 | C | 85.731180 | +0.0318 | -1.054e-28 | -9.637e-29 | 1.093 | yes | yes |
| 63/2 | C | 85.731163 | +0.0318 | -9.985e-29 | -9.132e-29 | 1.093 | yes | yes |
| 47 | C | 85.717910 | +0.0186 | -8.309e-01 | -7.658e-01 | 1.085 | yes | yes |

Q1 = (4/L) Re F_v(z_1)^2 with z_1 = gamma_1 - i delta_1. Expanding F_v at its
real zero x_g gives F_v(z_1) = F_v'(x_g)(gamma_1 - x_g - i delta_1) + O(F_v'' delta_1^2),
hence the first-order value (4/L) F_v'(x_g)^2 [(gamma_1 - x_g)^2 - delta_1^2],
with F_v normalised by ||x||. At every preregistered window the ratio lies
between 1.063 and 1.100 and the sign rule holds; the
ghost sits well inside the radius delta_1 = 0.3085 at which Q1 changes sign.
In the scan the rule fails once, at c = 18, where two zeros 1.42 apart
share the gap and the single-zero expansion does not apply (ratio -0.474). To this
order, a real zero within delta_1 of gamma_1 is what makes the off-line term
negative.

## 4. Controls at the same N and c

| kind | c | lambda_1 | H1 | H2 | n_AP(R_gap) | n_AP(R_ghost) | ghost | zeros in R_ctx | on-line zeros in R_ctx | accounted within 0.15 |
|---|---|---|---|---|---|---|---|---|---|---|
| zeta | 29 | 4.733e-135 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 30 | 2.146e-138 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 61/2 | 8.026e-140 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 245/8 | 3.292e-140 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 31 | 2.856e-141 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 63/2 | 1.015e-142 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| zeta | 47 | 3.367e-175 | yes | yes | 0 | 0 | none | 4 | 4 | 4 |
| epstein | 29 | 5.523e-04 | yes | no | 1 | 1 | 16.199840 | 5 | 5 | 1 |
| epstein | 30 | -7.895e-02 | yes | yes | 1 | 1 | 16.202805 | 5 | 5 | 1 |
| epstein | 61/2 | -1.166e-01 | yes | yes | 1 | 1 | 16.204256 | 5 | 5 | 1 |
| epstein | 245/8 | -1.240e-01 | yes | yes | 1 | 1 | 16.204525 | 5 | 5 | 1 |
| epstein | 31 | -1.422e-01 | yes | yes | 1 | 1 | 16.205161 | 5 | 5 | 1 |
| epstein | 63/2 | -1.581e-01 | yes | yes | 1 | 1 | 16.205684 | 5 | 5 | 1 |
| epstein | 47 | -8.916e-01 | yes | no | 1 | 1 | 16.235623 | 5 | 5 | 1 |
| dedekind | 29 | 7.246e-05 | yes | yes | n/a | 0 | none | 5 | 7 | 2 |
| dedekind | 30 | 4.605e-05 | yes | yes | n/a | 0 | none | 5 | 7 | 2 |
| dedekind | 61/2 | 3.728e-05 | yes | yes | n/a | 0 | none | 5 | 7 | 2 |
| dedekind | 245/8 | 3.556e-05 | yes | yes | n/a | 0 | none | 5 | 7 | 2 |
| dedekind | 31 | 3.147e-05 | yes | yes | n/a | 0 | none | 6 | 7 | 1 |
| dedekind | 63/2 | 2.636e-05 | yes | yes | n/a | 0 | none | 6 | 7 | 1 |
| dedekind | 47 | 1.062e-07 | yes | yes | n/a | 0 | none | 6 | 7 | 3 |

- **zeta (S3, holds).** No zero in [gamma_23 + 0.01, gamma_24 - 0.01] x
  [-1/2, 1/2] and none within 0.3 of gamma_1, at every c. In R_ctx F_v has
  exactly four zeros, one at each of zeta's 82.91038, 84.73549, 87.42527 and
  88.80911: each ordinate (`mpmath.zetazero` at 60 digits) lies inside an F_v
  bracket no wider than 2.4e-38 (`test_zeta_ordinates_lie_inside_their_brackets`).
  Here F_v follows zeta's zeros, and nothing extra sits in the gap.
- **Epstein (1,1,6) (S4, holds).** H1 holds at every c. The even lambda_1 is
  negative for c >= 30 and positive at 29, where the odd sector is lower (H2
  fails, as at 47). At every c, including 29, the on-line gap (14.6305,
  18.8285) holds exactly one zero, real, at 16.200 to 16.236: below
  the off-line ordinate 16.2902 by 0.055 to 0.090, well
  inside its delta = 0.4533. So the ghost is not peculiar to DH; a second
  function with its own off-line zero shows it at its own ordinate.
- **Dedekind zeta of Q(sqrt(-23)) (S5, fails as preregistered).** No real zero
  of F_v lies within 0.3 of 16.2902 at any c; the closest is 0.47
  away. But S5 also required every real zero of F_v in [12, 21] to be accounted
  for by an on-line zero of zeta_K within 0.15, and that fails at every c:
  F_v has 5 to 6 real zeros there against zeta_K's 7, and only
  1 to 3 of them are accounted for. At this height the band-128 transform
  does not follow zeta_K's zeros at all (s9), so the absence of a ghost is weak
  evidence. A negative control at matched zero density (for example the real
  character mod 5, conductor 5 like DH) was not run.

## 5. Lesions (S6, holds)

| c | unlesioned ghost x | Q1 lesion: lambda_1 | Q1 lesion: zeros within 0.3 of gamma_1 | Q1 lesion: nearest zero | sham lesion: ghost x |
|---|---|---|---|---|---|
| 29 | 85.729815 | 7.121e-28 | 0 | 87.652139 | 85.706122 |
| 30 | 85.734417 | 3.472e-29 | 0 | 87.649000 | 85.706108 |
| 61/2 | 85.731484 | 7.705e-30 | 0 | 87.648373 | 85.706316 |
| 245/8 | 85.731337 | 5.117e-30 | 0 | 87.648250 | 85.706372 |
| 31 | 85.731180 | 1.622e-30 | 0 | 87.647990 | 85.706455 |
| 63/2 | 85.731163 | 3.783e-31 | 0 | 87.647786 | 85.706469 |
| 47 | 85.717910 | -1.691e-18 | 0 | 87.647476 | 85.707272 |

With the Q1 term removed, no zero lies within 0.3 of gamma_1 at any c; the zero
nearest gamma_1 is the approximant of DH's on-line zero 87.6475. The lesioned
transform's other zeros in R_ctx sit within 0.022 of DH's
on-line zeros for c >= 30 (within 0.23 at c = 29), where the
unlesioned ones sat 0.12 to 0.57 away. One of them, the
approximant of DH's on-line zero 83.10884, sits 0.0004 to 0.018 above it at
c <= 63/2, just inside the nominal left side 83.109 of R_gap; that is why the
lesioned units' nominal R_gap count (1) differs from the count on the moved
sides (0) at c = 30 and 63/2. It is accounted for by an on-line zero, so it is
not a ghost. The lesioned form is positive for c <= 63/2 (conclusive ball
LDL^T at shift 0). The sham lesion removes an on-line term at 89.4392,
releases the zero that approximated it, and keeps the ghost, at 85.7061
to 85.7073. So the ghost belongs to the off-line term, not to having
removed some term.

## 6. Precision response and the float route (S7, holds)

| kind | c | second precision: counts | its brackets | float route: counts | its locations (float64) | its lambda_1, relative difference |
|---|---|---|---|---|---|---|
| dh | 29 | same | identical | same | equal | 0e+00 |
| dh | 30 | same | identical | same | equal | 1e-16 |
| dh | 61/2 | same | identical | same | equal | 1e-16 |
| dh | 245/8 | same | identical | same | equal | 6e-16 |
| dh | 31 | same | identical | same | equal | 6e-16 |
| dh | 63/2 | same | identical | same | equal | 5e-16 |
| dh | 47 | same | identical | same | equal | 1e-15 |
| zeta | 29 | same | identical | same | equal | 1e-15 |
| zeta | 30 | same | identical | same | equal | 2e-15 |
| zeta | 61/2 | same | identical | same | equal | 5e-16 |
| zeta | 245/8 | same | identical | same | equal | 1e-15 |
| zeta | 31 | same | identical | same | equal | 1e-15 |
| zeta | 63/2 | same | identical | same | equal | 2e-15 |
| zeta | 47 | same | identical | same | equal | 8e-16 |
| epstein | 29 | same | identical | same | 3.5e-12 apart | 2e-16 |
| epstein | 30 | same | identical | same | equal | 7e-16 |
| epstein | 61/2 | same | identical | same | equal | 5e-16 |
| epstein | 245/8 | same | identical | same | equal | 2e-15 |
| epstein | 31 | same | identical | same | equal | 6e-16 |
| epstein | 63/2 | same | identical | same | equal | 7e-16 |
| epstein | 47 | same | identical | same | equal | 2e-16 |
| dedekind | 29 | same | identical | same | equal | 4e-16 |
| dedekind | 30 | same | identical | same | equal | 1e-16 |
| dedekind | 61/2 | same | identical | same | equal | 1e-15 |
| dedekind | 245/8 | same | identical | same | equal | 0e+00 |
| dedekind | 31 | same | identical | same | equal | 4e-16 |
| dedekind | 63/2 | same | identical | same | equal | 6e-16 |
| dedekind | 47 | same | identical | same | equal | 4e-15 |

All 28 preregistered units were repeated at the second precision and by the
float route, and S7 holds in every one. "identical" means that the
second-precision run produced the same exact dyadic zero brackets, so no sign
decision changed with precision, and the location differences are 0 (S7 asked
for 1e-20 and 1e-40). The float route (mpmath assembly, eigenvector, sinc-form
transform, sampled winding with an integrality guard) found the same counts in
every rectangle and the same real zeros. "equal" means its zero locations and
the Arb bracket midpoints are the same float64 number (S7 asked for 1e-8); at
Epstein c = 29 they differ by up to 3.5e-12, where that unit's Arb brackets are
up to 1.2e-10 wide (s0). Each of the float route's real zeros lies inside its
Arb bracket, widened by two float64 ulps (`test_float_route_zeros_lie_in_the_arb_brackets`).
Its lambda_1 agrees with the ball Rayleigh quotient to the 15 significant
digits it stores, which is all the last column can show. Every winding number
of the float route came out within 1e-50 of an integer.

## 7. The counter against planted zeros

`test_planted_counter_arb_route` and `test_planted_counter_float_route` build an
element of the band-64 space at L = log 29 from a polynomial p with known
roots: real zeros at 84.2 and omega_46 + 0.015, and non-real pairs at
85.1993484 +- 0.3i and 85.6993484 +- 0.3i. Both counters return 6 in
[83.109, 87.647] x [-1/2, 1/2], with 2 real sign changes at the planted
places. The Arb route returns 3 in R_ghost (the pair at gamma_1 +- 0.3i and
the zero near omega_46), 2 with h = 1/4 (the pairs excluded), and 0 after a
side asked to sit 0.01 from omega_46 is moved clear of it. A counter that only
counted real sign changes, or that missed non-real zeros, would fail these
tests.

## 8. The band-N reality statement (S1, holds)

The derivation of PREREG s3 (ordinary argument, unreviewed) needs only that
the lowest even-sector eigenvalue of the band-N matrix is simple. Its
algebraic step, F_v = 2 sin(zL/2) p(z^2)/(z q(z^2)) with deg p <= N, is
checked numerically by `test_band_n_representation_of_prereg_s3`. It is CvS's
multiplier argument; it goes through in V_N because multiplying by
(z^2 - conj(w_0))/(z^2 - w_0) does not raise deg p. It does not need H2, which
fails for DH at 63/2 and 47 and for Epstein at 29 and 47. Every one of the
264 rectangles in which H1 held had as many zeros as real sign changes,
including the lesioned, sham, scan, basis-size and second-gap runs.

## 9. Exploratory, chosen after the numbers

**Basis size.**

| c | N | band edge | lambda_1 | H1 | zeros in R_gap | ghost x | x - gamma_1 |
|---|---|---|---|---|---|---|---|
| 29 | 64 | 119.4 | 7.169e-28 | yes | 1 | 85.729951 | +0.0306 |
| 29 | 128 | 238.8 | 6.575e-28 | yes | 1 | 85.729815 | +0.0305 |
| 29 | 192 | 358.3 | 6.455e-28 | yes | 1 | 85.729792 | +0.0304 |
| 29 | 256 | 477.7 | 6.326e-28 | yes | 1 | 85.729767 | +0.0304 |
| 30 | 128 | 236.5 | 9.548e-29 | yes | 1 | 85.734417 | +0.0351 |
| 61/2 | 128 | 235.3 | 9.575e-30 | yes | 1 | 85.731484 | +0.0321 |
| 245/8 | 128 | 235.0 | 1.099e-30 | yes | 1 | 85.731337 | +0.0320 |
| 31 | 64 | 117.1 | -3.810e-30 | yes | 1 | 85.731313 | +0.0320 |
| 31 | 128 | 234.2 | -7.529e-30 | yes | 1 | 85.731180 | +0.0318 |
| 31 | 192 | 351.3 | -7.792e-30 | yes | 1 | 85.731174 | +0.0318 |
| 31 | 256 | 468.4 | -7.842e-30 | yes | 1 | 85.731173 | +0.0318 |
| 63/2 | 128 | 233.1 | -8.323e-30 | yes | 1 | 85.731163 | +0.0318 |
| 47 | 64 | 104.4 | -3.163e-01 | yes | 1 | 85.718471 | +0.0191 |
| 47 | 128 | 208.9 | -3.325e-01 | yes | 1 | 85.717910 | +0.0186 |
| 47 | 192 | 313.3 | -3.341e-01 | yes | 1 | 85.717860 | +0.0185 |
| 47 | 256 | 417.8 | -3.344e-01 | yes | 1 | 85.717851 | +0.0185 |

From N = 64 to N = 256 the ghost moves by at most 6.2e-04, while
lambda_1 changes with N; at each of these N it is the only zero in R_gap.

**The second off-line pair.** DH's second off-line zero is at
z_2 = 114.1633427308 - 0.1508300806 i, in the on-line gap (112.37639,
116.72151). The same enclosure chain (`ghost.py gap2`) finds a real zero of
F_v within 0.3 of gamma_2 at all seven windows. The closest approach is
5.3e-04 (c = 30) and the farthest 0.047; at c = 29 and 47 the gap
holds a second zero. Both off-line pairs this tree records below 120
(`GAMMA_OFF`, `GAMMA_OFF2` in `../numerics/wp_common.py`; their completeness is
not checked here) thus have a ghost at their ordinate.

**Tracking of on-line zeros against height** (`ghost.py resolution`).

At c = 30, by sign changes only (no argument principle): DH's F_v follows
every DH on-line zero below t_res = 37.7 to within 1e-11.
The comparison itself resolves about 1e-12 (brackets of width 2^-40 against a
float64 zero list). t_res = 2 pi c / 5 is the height at which DH's mean zero
density (1/2 pi) log(5t / 2 pi) reaches L/(2 pi), the mean real-zero density
of an entire function of type L/2. Above t_res the agreement decays
smoothly: 1e-09 at the first zero above 40, and 0.045 to 0.86
above 68. Between 68 and 120, two of the zeros of F_v that no on-line zero
accounts for sit at the two off-line ordinates: the ghost of s1 and the ghost
of the second gap. Removing Q1 sharpens the agreement near gamma_1 (at
87.6475: 2e-03 instead of 0.24). Removing both
quadruples also removes the second ghost, but the decay with height stays
(0.1 to 0.7 between 92 and 110). zeta at the same c follows all
38 of its zeros in [10, 120] to within 4e-13, which is the resolution of this
comparison (in [80.5, 90.5] the brackets of s4 contain zeta's ordinates); its
t_res is 188.5. zeta_K and Epstein have degree 2 and conductor 23, so
t_res = 2 pi sqrt(c/23) = 7.2. Below it their zeros are followed to
within 2e-03 and 1e-02; above 12 the offsets are only
0.11 to 0.51 and 0.12 to 0.68. So at c = 30, for these four functions, the
band-128 transform is a sharp approximant of the function's zero set below
t_res and a distorted one above it (measured). DH's ghost sits far above DH's t_res, yet stays within 0.035
of gamma_1, while the Dedekind control at 16.29 sits above zeta_K's t_res,
where nothing is followed.

## 10. Grades

| statement | grade |
|---|---|
| zero counts, real-zero brackets, H1, H3, eta, at each listed (kind, c, variant) | hardened: every step enclosure-carrying (Arb), repeated at a second precision and by the mpmath float route, a second implementation of the same assembly formulas (s0) (preregistered runs; the exploratory runs are enclosure-carrying but not repeated) |
| counts on the nominal rectangles | hardened, read from the R_ctx enclosures (s1); no separate computation |
| that these concern DH's band-128 Weil matrix | the assembly is `../../rogue_frontier/weil_trunc`'s (validated there against an independent mpmath assembly); Fact A of `../numerics/RESULTS.md` s0 (ordinary argument) identifies it with the restriction of DH's Weil form |
| H2 (global evenness) | hardened where decided (ball LDL^T of the odd sector) |
| the band-N reality statement | ordinary argument, unreviewed; numerically consistent in every rectangle (S1) |
| "the ghost is the off-line quadruple's" | measured: lesion, sham, S2 and the second gap on the band-128 matrix; the lesion uses the 50-digit z_1 and the DH explicit-formula dictionary (ordinary argument, internally reviewed) |
| the controls' on-line zeros | measured, two routes each (PARI plus the lab's or mpmath's) |
| basis-size response, second gap, tracking diagnostic, scan | measured, exploratory |

## 11. The doors

This is not a ceiling hunt. The section records the objects frozen here,
because those are what a follow-up would unfreeze.

1. **What binds the ghost's position.** The off-line term Q1 rewards, to first
   order, a real zero within delta_1 of gamma_1 (s3). The on-line terms hold
   the ghost 0.019 to 0.035 above gamma_1 and push its
   neighbours off DH's on-line zeros. Without Q1 the neighbours return to
   DH's zeros (s5).
2. **Frozen constants.** N = 128 (exploratory response in s9). The ghost
   radius 0.3 is the prediction's; the observed distances are at most
   0.045 for c >= 25. The sector is even; at 63/2 and 47 DH's lowest eigenvector is
   odd, and that transform was not examined. The lesion strength is all of
   Q1; a partial lesion t M_Q1 would locate the t at which the ghost leaves
   the gap, trading lesion size for a threshold. The window grid is fixed.
3. **Information class.** Every count reads only the band-N form on one
   window, built from the prime side of the explicit formula: DH's Dirichlet
   coefficients up to c and its gamma factor. z_1 enters only the lesion and
   S2. So the ghost locates the off-line ordinate gamma_1 without reading any
   zero: within 0.3 at every scan window from c = 15 on, within 0.045 at every
   grid window from c = 25 on, and gamma_2 within 0.047 at the preregistered
   windows (measured, band 128). delta_1 is not read, since the zeros are real.
   Whether delta can be read from the shape of F_v near the ghost is open.

## 12. Reproduction

From the repository root (`RUNS.md` has the unit costs):

    export PYTHONPATH=$PWD; P=.venv/bin/python; G=hunts/weil_propagation/ghost_zeros/ghost.py
    $P $G windows
    for k in dh zeta epstein dedekind; do $P $G arb $k; $P $G arb $k --variant=prec2; $P $G float $k; done
    $P $G arb dh --variant=q1; $P $G arb dh --variant=sham; $P $G arb dh --variant=scan
    $P $G arb dh 15 16 17 --variant=scanfine
    for n in 64 192 256; do $P $G arb dh 29 31 47 --variant=N$n; done
    $P $G s2; $P $G s2 14 15 16 17 18 22 25 27 28; $P $G gap2
    $P $G resolution dh:30:3:120 zeta:30:10:120 dh:30:3:120:q1 dh:30:3:120:q12 dedekind:30:1:21 epstein:30:1:21
    $P $G summary
    $P -m pytest -q -n0 hunts/weil_propagation/ghost_zeros
