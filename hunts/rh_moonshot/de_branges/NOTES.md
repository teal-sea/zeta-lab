# de_branges: a Hermite-Biehler structure function built from xi

**Hunt #150 (`rh_moonshot`), mechanism 2. Built 2026-10-26. Status: constructed, measured
and pushed to a located obstruction; not challenged yet; unreviewed by any person.**
Nothing here is a result until the case log in `hunts/README.md` says how this hunt ended.
Files: `dbr_common.py` (the completed functions by two routes, the defect, the local
factor, Conrey and Li's numbers), `dbr_grid.py` (the grid), `test_de_branges.py` (the pins),
`data/` (every number below), `RUNS.md`, this page.

Grades are the hunt's (`MISSION.md`, top): *measured*, *hardened*, *derived* with its review
status, *kernel-checked*; *cited* marks a statement read in a primary source at the stated
place; *quoted* marks one taken from a secondary source and not checked. A sign read from an
Arb ball that excludes 0 is ball-carried, and with the mpmath route agreeing it is
hardened. Nothing here is kernel-checked. A composite claim takes the grade of its weakest
step.

## 1. Sources, read at section, and the search

Searched on 2026-10-26: three web searches (Conrey-Li's title; Lagarias "Hilbert spaces of
entire functions and Dirichlet L-functions"; Lagarias "Zero spacing distributions for
differenced L-functions"), then the arXiv TeX sources were fetched into the session scratch
directory and read as data:

- **Conrey and Li**, "A note on some positivity conditions related to zeta and
  L-functions", *Internat. Math. Res. Notices* 2000, no. 18, 929-940; arXiv math/9812166
  (e-print SHA-256 `c458dcc9b7eb8a93f78d7d76b8f5a4687e9a9aea49d464cfd7c424ca863ba29f`).
  *Cited.* Section 2, Theorem 1 (de Branges's condition): for E with no real zeros,
  |E(conj z)| < |E(z)| on Im z > 0, conj E(conj z) = eps E(z - i) and |E(x + iy)| increasing
  in y > 0, if Re <F(z), F(z + i)>_{H(E)} >= 0 for every F in H(E) with F(z + i) in H(E),
  then the zeros of E lie on Im z = -1/2. Theorem 2 is the companion condition on a space
  F(W). Section 3.1 takes **E(z) = xi(1 - iz)** with xi(s) = s(s-1) pi^{-s/2} Gamma(s/2)
  zeta(s) (no factor 1/2), proves it Hermite-Biehler from 0 < Re rho < 1, and refutes
  condition (3.1) by -Re{xi'(rho) xi(1 + rho)} = -5.389100507182945e-69 at the 34th zero
  rho = 1/2 + 111.0295...i, and condition (3.3) by Re{xi(1 + 282i)/xi(2 + 282i)} =
  -0.000131957; section 3.2 does the same for L(s, chi_4); the closing remark records
  Sarnak's computation-free proof that (3.3) fails. Both printed numbers are reproduced
  here by two routes (`test_conrey_li_numbers_two_routes`).
- **de Branges**, "The Riemann hypothesis for Hilbert spaces of entire functions", *Bull.
  AMS* 15 (1986) 1-17; "The convergence of Euler products", *J. Funct. Anal.* 107 (1992)
  122-210; "A conjecture which implies the Riemann hypothesis", *J. Funct. Anal.* 121
  (1994) 117-184. *Quoted* (titles and places from the two bibliographies above; not read).
- **Lagarias**, "Zero spacing distributions for differenced L-functions", *Acta Arith.*
  120 (2005) 159-184; arXiv math/0601653 (e-print SHA-256
  `7f648d2824d17e24b4c1a4fce249dde77744f0d70d9fcb7e163e6d5eb74de4d5`). *Cited.* Lemma 2.1:
  (1) for h >= 1/2, |xi(h + s)| > |xi(h + 1 - conj s)| when Re s > 1/2; (2) under RH the
  same for each h > 0; proved factor by factor on the Hadamard product. Lemma 2.2 (de
  Branges 1959, Lemma 5): such an E has A = (E + E^#)/2 and B with only real, interlacing
  zeros. Theorem 2.1: so A_h and B_h have only simple zeros on the critical line for
  |h| >= 1/2, and for all h != 0 under RH. Section 6 restates Lemma 2.1 as: **E_h(z) =
  xi(1/2 + h - iz) is a de Branges structure function** for h >= 1/2, and for all h != 0
  under RH; h = 1/2 is de Branges's E(z) = xi(1 - iz). The same section cites Conrey and Li
  as showing de Branges's hypotheses fail for H(xi_chi(1 - iz)), chi trivial or chi_{-4}.
- **Lagarias**, "Hilbert spaces of entire functions and Dirichlet L-functions", in
  *Frontiers in Number Theory, Physics, and Geometry I*, Springer 2006. *Quoted* from the
  2005 paper's section 6: a de Branges space attached to L(s, chi) exists if and only if
  RH holds for it. Not read.

**A citation in this tree is wrong.** `hunts/rogue_frontier/FRONTIER_MAP.md` (territory F,
"de Branges / canonical-system route") says "Lagarias (2006) proved RH holds iff E = A - iB
built from xi is a Hermite-Biehler function", gives the title as "Hilbert spaces of entire
functions and the Riemann zeta function" (2006), and dates the work "(2025)". The checked
record: the 2006 chapter's title ends "and Dirichlet L-functions"; the Hermite-Biehler
family is in the 2005 *Acta Arith.* paper, which proves the property for h >= 1/2
unconditionally and for every h != 0 under RH, and does not state the converse (section 3
below supplies it in one line); no 2025 item by Lagarias on this was found. That file is
outside this hunt's write scope, so the correction is recorded here for the operator.

## 2. Target

The structure function, for any entire Lambda with Lambda(1 - s) = Lambda(s) and
Lambda(conj s) = conj Lambda(s):

    E_h(z) = Lambda(1/2 + h - i z),   h > 0,

so for z = x + iy, E_h(z) = Lambda(1/2 + h + y - ix) and E_h(conj z) = Lambda(1/2 + h - y - ix).
The Hermite-Biehler defect is D_h(z) = log|E_h(conj z)| - log|E_h(z)|; E_h is
Hermite-Biehler when D_h < 0 on Im z > 0. For Lambda = xi:

- if E_h is Hermite-Biehler, A_h = (E_h + E_h^#)/2, which on the line is
  Re xi(1/2 + h + it), has only real zeros (Lagarias, Lemma 2.2 and Theorem 2.1);
- if E_h is Hermite-Biehler for every h in (0, 1/2], A_h -> xi(1/2 - iz) = Xi(z) locally
  uniformly as h -> 0, and Hurwitz's theorem gives RH.

**The named arithmetic input** is the zero-free half-plane that the Euler product supplies:
zeta(s) != 0 on Re s >= 1 (Hadamard and de la Vallee Poussin, from the Euler product)
gives h >= 1/2, which is Lagarias's Lemma 2.1(1); the strip Re s > 7/8 (OpenAI 2026,
kernel-checked here on two kernels, pending human review of its argument, `docs/08`
section 1.1) gives h > 3/8 (section 3).

**How this differs from what Conrey and Li refuted.** They take the one structure function
E_{1/2}(z) = xi(1 - iz), which is Hermite-Biehler unconditionally, and refute de Branges's
*positivity conditions on its space*: (3.1) Re <F(z), F(z + i)> >= 0 on H(E), and (3.3) on
F(1/xi(1 - iz)). The form here asks instead for the Hermite-Biehler property of E_h itself
at h < 1/2, a condition on the structure function and not an inner-product positivity on a
space. Conrey and Li do not cover it. Section 3 shows what does.

## 3. Construction: what the Hermite-Biehler property of E_h is (derived, self-reviewed)

**(a) It is a zero-free half-plane, exactly.** For Lambda as above with a Hadamard product
pairing rho with 1 - rho and no exponential factor left over (Lagarias's B* = 0 for xi;
assumed, not checked, for the three rivals with the functional equation) and h > 0:

> E_h is Hermite-Biehler if and only if Lambda has no zero with Re rho > 1/2 + h.

If: Lagarias's factor-by-factor proof of Lemma 2.1(1) uses only beta - h - 1/2 < 0 for every
zero, which is this hypothesis with the functional equation (a zero exactly on
Re rho = 1/2 + h gives equality in its own factor and leaves the others strict). Only if: a
zero rho = 1/2 + delta + i gamma with delta > h makes E_h vanish at z = -gamma + i(delta - h)
in the upper half-plane, where |E_h(conj z)| < |E_h(z)| = 0 is impossible. So
"E_h Hermite-Biehler for every h > 0" is RH, and "for a given h" is the quasi-Riemann
hypothesis with abscissa 1/2 + h.

**(b) The furthest statement the arithmetic input reaches.** With Re s > 7/8 zero-free,
every zero has Re rho <= 7/8 < 1/2 + h for h > 3/8, so E_h is Hermite-Biehler for every
h > 3/8, and Lagarias's proof of Theorem 2.1 then gives: for h > 3/8 and every theta,
A_{h,theta} and B_{h,theta} have only simple zeros, all on the critical line, interlacing
(the simplicity step needs a zero with real part 1/2 + h > 7/8, which does not exist).
Grade: derived, self-reviewed, conditional on the 7/8 strip (kernel-checked, pending human
review), so it extends Lagarias's unconditional range h >= 1/2 to h > 3/8. Novelty: not
searched beyond the two papers read.

**(c) The Euler product is not Hermite-Biehler factor by factor.** For one local factor
E_p(z) = (1 - p^{-(1/2 + h - iz)})^{-1}, with r_{+-} = p^{-(1/2 + h +- y)},
|E_p(conj z)| / |E_p(z)| = sqrt(f(r_+)/f(r_-)), f(r) = 1 - 2r cos(x log p) + r^2, which
exceeds 1 exactly when cos(x log p) > (r_+ + r_-)/2. Since r_{+-} < 1, every p violates the
inequality on a set of x of positive density. So the property of E_h does not come from the
Euler product locally: it comes only from where the zeros are, through the Hadamard
product (pinned by `test_local_euler_factor_is_not_hermite_biehler`).

## 4. Tests run and measurements

Grid (`dbr_grid.py`): h in {1/2, 3/8, 3/10, 1/4, 1/5, 1/10, 1/20}, y in {1/20, 1/5}, x on
[0, 100] in steps of 1/2 plus 14.1347 and the rival's off-line ordinate (Epstein: x <= 40),
both routes at every point (Epstein's mpmath lattice route on 16 points per h, at 12 to 18 s
each), and an Arb column at x = gamma, y = 0.01 .. 0.60. `test_de_branges.py`: Conrey and
Li's numbers, route agreement and the functional equation for each function, the defect's
sign at chosen points, the local-factor criterion, and every grid number below.

| function | hypotheses of (a) | h where the grid shows D > 0 | where | routes agree to |
|---|---|---|---|---|
| zeta | all; Euler product | none, at any h (2828 points, 0 positive) | | 4.3e-11 |
| DH | functional equation, real, no Euler product | h <= 3/10 | x = 85.699 (and 85.5 for h <= 1/5); positive for y in [0.01, 0.06] at h = 3/10, [0.01, 0.17] at 1/4, [0.01, 0.30] at 1/20 | 5.0e-12 |
| Epstein (1,1,6) | functional equation, real, no Euler product | h <= 3/8 at x = 16.290, and h <= 1/4 also at x = 29.5 | x = 16.290 (and 16.0, 16.5), 29.5 | 4.7e-12 (112 points) |
| W_{1/4} | functional equation, real, Euler product with local roots p^{+-1/4} | h <= 1/5 (none at h = 1/4) | at zeta's ordinates (14.13, 21.0, 25.0, ...), 19 to 49 of 406 points | 1.4e-11 |
| zeta(s - 1/5) | no s -> 1 - s functional equation | h <= 1/10, at every point; D = -5.1e-20 at h = 1/5 | everywhere | 1.6e-11 |

**A second off-line zero of Epstein (1,1,6).** The grid's failure at x = 29.5 for h <= 1/4
but not at 3/10 pointed at a zero of offset between 1/4 and 3/10, and Newton's method on
the Arb route found it at **0.7979971571787 + 29.5517610986291i** (offset 0.2980); the
lattice route gives |s(s-1)Lambda_Q| = 9e-47 there against 1.3e-18 at distance 0.01
(`test_epstein_second_offline_zero`). Measured, by two routes; the record of this tree
pinned only the zero at height 16.29; whether this one is in the literature was not
searched.

Every positive region sits where (a) puts it: E_h^DH vanishes at y = delta - h with
delta = 0.3085 (0.0085 at h = 3/10, 0.0585 at h = 1/4), Epstein's delta is 0.4533, W's 1/4
(boundary case h = 1/4 passes), and zeta(s - 1/5) is symmetric about 1/2 + 1/5, so its
defect changes sign at h = 1/5 identically in x. The Arb undecided points are removable
points the Arb routes evaluate literally: s = 1 (zeta, DH and Epstein at h = 3/10 or 1/5,
y = 1/5, x = 0) and, for Epstein's Fourier-Bessel route, s = 1/2 (h = 1/20, y = 1/20,
x = 0, which also makes that h's recorded maximum NaN). The mpmath route handles both
(Epstein's lattice route by a circle mean at s = 0 and 1); its values there are negative.

## 5. The distinguishing step and the rival gate

The step that separates zeta from the rivals is the zero-free half-plane Re s > 1/2 + h,
and nothing else: by (a) the defect reads only the real parts of the zeros. The rivals'
results on complete hypotheses:

- **DH** meets every hypothesis of (a) and is not a counterexample to it: (a) predicts its
  E_h fails exactly for h < 0.3085 at its pinned zero, and the grid shows that. It does not
  meet the construction's conclusion-producing hypothesis (Hermite-Biehler), so the kill
  "the DH analogue meets the complete hypotheses" is not triggered. The grid passes DH at
  h = 3/8 and 1/2, but only on |x| <= 100: DH has zeros in Re s > 1 (Davenport and
  Heilbronn 1936, *quoted*, not verified here; `li_dh_onset` found none in
  [1, 4] x [0, 120]), which by (a) make E_{1/2}^DH fail somewhere higher. A finite grid
  stands in here for the whole half-plane, and says nothing above x = 100.
- **Epstein (1,1,6)**, likewise, fails for h below its offsets 0.4533 and 0.2980, each at its own zero.
- **W_{1/4}** has a scalar Euler product, nonnegative coefficients and the functional
  equation, and fails for h < 1/4 at every zeta ordinate on the grid: an Euler product alone
  does not supply the input; its non-unitary local roots move the zeros, as in
  `ccm_arithmetic` and `li_arithmetic`.
- **zeta(s - delta)** lacks the s -> 1 - s functional equation, so (a) does not apply; its
  defect sees its symmetry centre directly.

## 6. Known obstructions

- **Conrey and Li** cover de Branges's positivity conditions on H(xi(1 - iz)); they do not
  cover the form here (section 2).
- **Reformulation (kill condition 3 of `MISSION.md`).** By (a), "E_h Hermite-Biehler for all
  h > 0" is RH restated as a family of zero-free half-planes, and the arithmetic input
  enters only as such a half-plane. The form adds no estimate: every h it reaches is a
  zero-free strip proved some other way (h >= 1/2 classically, h > 3/8 from the 7/8 strip).
  It does not reduce to Weil positivity; it reduces to quasi-RH.
- **Zero-configuration only.** The defect reads the zero locus and nothing about primes
  (c); it is the de Branges analogue of `MISSION.md`'s dead route "mechanisms that read only
  the zero configuration".
- **Finite grid.** No measurement here bears on |x| > 100 (section 5).

## 7. Disposition (proposed by the builder; the challengers decide)

**Recorded as a reformulation under kill condition 3, with a located obstruction:** for the
Lagarias family E_h, the Hermite-Biehler inequality is exactly the zero-free half-plane
Re s > 1/2 + h, so it can deliver nothing beyond the zero-free strips it is given. On
`ALIGNMENT.md` section 5's scale the route to RH through this family is *unresolved*
(it is as hard as quasi-RH for every abscissa above 1/2) and adds no estimate. Conrey and
Li's refutation does not apply to it.

## 8. Furthest true statement, with its grade

For every h > 3/8, E_h(z) = xi(1/2 + h - iz) is a de Branges structure function, and
A_{h,theta}, B_{h,theta} have only simple, interlacing zeros on the critical line: **derived,
self-reviewed, conditional on the 7/8 strip** (kernel-checked here, pending human review);
unconditional for h >= 1/2 (Lagarias 2005, cited). On the grid, zeta's defect is negative at
all 2828 points for h from 1/20 to 1/2 with |x| <= 100 (**hardened**: Arb ball signs with the
mpmath route agreeing to 4.3e-11), and each rival's defect turns positive exactly at its
off-line zero (**hardened** at the points listed).

## 9. Next step

Nothing further along this family: (a) exhausts it. A structure function whose
Hermite-Biehler property is not decided by the zero locus alone would be a different
construction: Suzuki's de Branges space of the Weil form (arXiv:2301.00421, which assumes
RH) or his screw-function form (arXiv:2606.09096) are the candidates the record names,
and either would first have to say which inequality on the screw function would be new.
The h-range itself moves only with a new zero-free strip (`probe_tower`, hunt #136).

## Correction (2026-10-26, synthesis session)

Added by the synthesis session of hunt #150, which did not build this mechanism; the text
above is left as written. The circularity challenge (`challenge/CHALLENGE_circularity.md`,
findings B2 and B5) shows that two statements above are about the sample, not about the
functions:

- **Epstein (1,1,6) has more off-line zeros than section 4's table row and section 5's
  Epstein bullet list.** An argument-principle census of [0.55, 1.6] x [0.5, 60.5] on an
  independent Chowla-Selberg route finds five, not two: besides 0.953260 + 16.290216i and
  0.797997 + 29.551761i, also 0.663652 + 33.650101i, 0.809992 + 43.858664i and
  0.782379 + 46.960994i (offsets 0.1637, 0.3100, 0.2824), each measured by two routes and
  a winding count, none enclosed. The zero at 33.650 lies inside this page's grid
  (x <= 40); the grid's step of 1/2 in x missed its failure region (defect +0.457 at
  x = 33.6501, negative at the grid points 33.5 and 34.0, h = 1/20, y = 1/20). So the
  table's "h <= 3/8 at x = 16.290, and h <= 1/4 also at x = 29.5" and section 5's "fails
  for h below its offsets 0.4533 and 0.2980" should read: by (a), E_h fails below each of
  the offsets 0.4533, 0.3100, 0.2980, 0.2824 and 0.1637 (and below any offset of a zero
  outside the census box); the grid sampled two of them. Statement (a) is unaffected.
- **DH fails for every h <= 1/2, not only h <= 3/10.** By Saias and Weingartner (Acta
  Arith. 140 (2009), abstract), DH has zeros with real part in (1, 1 + eta), so by (a)
  E_h^DH is not Hermite-Biehler for any h <= 1/2. Section 5's "the grid passes DH at
  h = 3/8 and 1/2" is a finite stand-in that the theorem overrides.

The Epstein zeros are recorded in `../RESULTS.md` section 9 with their grade.
