# RESULTS: `rh_moonshot`, six RH-direct mechanisms (hunt #150, first wave)

**Synthesis, 2026-10-26.** Written by the synthesis session, which built none of the six
constructions and ran none of the challenges. Inputs: the six `NOTES.md` on
`hunt/rh-moonshot`; the rival-gate challenges (branch `hunt/rh-moonshot-challenge-rival`,
head `7c3523396`, files `*/challenge/CHALLENGE_RIVAL.md` and `CHALLENGE_RIVAL_STATUS.md`);
the circularity challenges (branch `hunt/rh-moonshot-challenge-circularity`, head
`264a74658`, files `*/challenge/CHALLENGE_circularity.md`). Both branches were merged into
`hunt/rh-moonshot` without conflict. Nothing here is reviewed by any person.

Grades are those of `MISSION.md`: *measured*, *hardened*, *derived* (with its review
status), *kernel-checked*; *cited* (read in a primary source at the stated place) and
*inferred* (a reading no computation checks) as the mechanisms use them. Nothing in this
hunt is kernel-checked. A composite claim takes the grade of its weakest step.
Dispositions are `ALIGNMENT.md` section 5's four (refuted, restricted class obstructed,
unresolved, paused by allocation) plus *alive*: a stated next step and no located failure.

## The answer, in the scope of this hunt

**No route to RH was established in the searched set under the stated inputs.** This is
the bounded fact `ALIGNMENT.md` section 5.1 asks for, about six specific constructions at
their stated parameters, and it is not a statement that no route exists. Sorted by
section 5.1's four headings:

- **(a) Refuted, at stated parameters.** Two absolute-value bounds on Li's arithmetic part
  (`li_arithmetic`); the implication "scalar Euler product, nonnegative log-derivative
  coefficients and the functional equation give lambda_n >= 0", by W_{1/4} at n = 8260
  (`li_arithmetic`, hardened); the same package as a source of the Hermite-Biehler
  property, by W_{1/4} at h = 1/5 (`de_branges`, measured); a function-field
  implication, by the golden fake (`positivity_geometry`, derived, self-reviewed); the
  tower premise that sigma_0(k) falls to 1/2, inside the order-k template
  (`probe_tower`); and self-adjointness as a discriminator, by DH (`spectral_operator`).
- **(b) Restricted classes with proved obstructions.** The order-k power-residue template
  of the 7/8 assembly (`probe_tower`; its transfer to actual order-k theta systems is
  inferred); the CCM operator's self-adjointness step, by Connes and van Suijlekom's
  theorem for every even-simple real distribution (`spectral_operator`).
- **(c) Unresolved or alive.** `ccm_arithmetic` (alive), `li_arithmetic`,
  `positivity_geometry`, `de_branges` (unresolved; the last recorded as a reformulation
  with nothing left in its family), and `spectral_operator`'s link (3), which is
  `ccm_arithmetic`'s open step in operator language.
- **(d) Not searched here.** Every construction outside these six, among them Suzuki's
  de Branges space of the Weil form, Bombieri-Stepanov's surface-free route, Berry-Keating
  and Sierra operators, and probes whose principal frequencies have density above 1/2.

| mechanism | builder proposed | rival gate | circularity | this synthesis | composite grade of the furthest statement |
|---|---|---|---|---|---|
| `ccm_arithmetic` | unresolved | unresolved | unresolved | **alive** | measured |
| `de_branges` | reformulation; unresolved | unresolved | reformulation; unresolved | **unresolved** (reformulation, family exhausted) | derived, self-reviewed, conditional on the 7/8 strip |
| `li_arithmetic` | unresolved, two sub-routes refuted | unresolved | unresolved; target a reformulation | **unresolved** (target a reformulation; sub-routes refuted) | measured |
| `positivity_geometry` | unresolved, restricted class obstructed | unresolved, narrower obstruction | unresolved; label withdrawn to a refutation | **unresolved**, golden fake a **refutation** of one function-field implication | derived, self-reviewed |
| `spectral_operator` | reformulation for self-adjointness; link (3) unresolved | unresolved; self-adjointness refuted as discriminator | restricted class obstructed (self-adjointness); unresolved | **restricted class obstructed** (self-adjointness); link (3) **unresolved**, merged with `ccm_arithmetic` | measured |
| `probe_tower` | restricted class obstructed | restricted class obstructed | restricted class obstructed | **restricted class obstructed** | inferred |

## 1. `ccm_arithmetic`: CCM step 2, the ground-state transform converging to Xi

**The construction** (`ccm_arithmetic/NOTES.md`). The even-sector truncated Weil form
Q_c on [0, log c] in a band of N cosines, assembled in Arb balls from the archimedean
place, the pole and Lambda(n), n <= c. Its ground state v_1 is compared with the radical
vector of Xi (a diagnostic that reads Xi values, never zeros, and never enters the form).
The chain: (1) the ground state is simple and even for every c; (2) capture of v_c by
Xi times even polynomials, with F_v -> Xi locally uniformly on a neighbourhood of
|Im z| < 1/2; (3) Prop. 4.1 of Connes and van Suijlekom plus Hurwitz give RH. Link (2) is
the distinguishing one.

**Builder: unresolved.** On c <= 60, N <= 128, zeta's ground state is captured
(dist^2 to R_4 at most 8.3e-11), its transform's real zeros match Xi's below 100 to
7.8e-16, and the approach rate kappa is near 0.8. DH, Epstein (1,1,6) and W_{1/4} each
lose capture at a located window (31 to 33; 29 to 59/2; 2 to 3) where the form goes
negative; the Dedekind zeta of Q(sqrt -23) keeps it to c = 60. The perturbative capture
bound is vacuous at m = 2 and m = 4.

**Rival gate: unresolved.** An independent 70-digit Galerkin assembly reproduced the
transitions: DH at c = 31 has lowest value -3.81e-30 and misfit 1.1e-4 (still captured),
at c = 33 misfit 0.9999; Epstein changes sign between 29 and 29.5; W_{1/4} at c = 2 has
misfit 0.19, at c = 3 misfit 0.999. zeta(s - 0.1) fails the fixed-half even sector
(evenness defect 0.0099 at the first node); recentred at 0.6 its matrix is zeta's to
1e-50, so it meets the conclusion and is not a counterexample.

**Circularity: unresolved, with one grade lowered (C1).** No zero or RH input in the form,
checked by hand at `ccm_common.py` lines 171-229. But "lambda_1 > 0" is not
ball-carried positivity: a positive Rayleigh ball bounds the lowest eigenvalue from above
only, and the band-N matrix is a principal submatrix of every larger band, so lambda_1(N)
is an upper bound on the window infimum. It falls monotonically in N on every window of
zeta, Dedekind and DH, by 112 orders from N = 32 to 128 at c = 60. So zeta's positivity
and simplicity are band-level and measured; the rivals' negative values stand. C2: capture
co-locates with positivity on this grid, so a proof of link (2) may have to deliver
all-window Weil positivity (kill condition 3), undecided. Prior art: CCM's own abstract
says a proof of this convergence would establish RH; Zhu (arXiv:2608.24827) finds the
window infimum positive but falling doubly exponentially, which agrees with C1; no
published rival test of step 2 was found.

**Synthesis: alive.** The challengers' "unresolved" and this "alive" do not conflict:
both say the chain is unproved for any infinite family of c, and `MISSION.md` reserves
*alive* for a construction with a stated next step and no located failure, which is this
one's state. No step fails for zeta on the grid; each rival tested fails at link (2) where
it lacks a named hypothesis (DH and Epstein the Euler product, W_{1/4} unitary local
roots); and the next steps (section 8) are concrete. C1 is accepted: wherever this page or
the NOTES say zeta's form is positive, read "the band-N lowest eigenvalue is positive,
measured". One datum bears on C2 and is shared by builder and rival challenger: DH at
c = 31, N = 64 is still captured while its form already takes a negative value, so on that
cell capture is not the same event as positivity. One cell does not decide C2; the fine
grid of section 8 does.

Grades: link (1) measured, band-level; link (2) measured on c <= 60, N <= 128, with the
relative error on Im z = 0.45 at best 7.3e-2 and no established decay; link (3) cited
(Prop. 4.1, Commun. Math. Phys. 406 (2025) 312) plus classical Hurwitz; rival negative
values ball-carried for stated vectors, W_{1/4}'s sign change hardened. Composite:
measured.

## 2. `de_branges`: the Lagarias structure functions E_h

**The construction** (`de_branges/NOTES.md`). E_h(z) = xi(1/2 + h - iz), h > 0, with the
Hermite-Biehler defect D_h measured by an Arb route and an mpmath route. (a) E_h is
Hermite-Biehler if and only if xi has no zero with Re rho > 1/2 + h (derived,
self-reviewed); (b) from the 7/8 strip, E_h is Hermite-Biehler for every h > 3/8 and A_h,
B_h have only simple interlacing zeros on the line (derived, conditional on the strip,
which is kernel-checked here and pending human review); (c) no single Euler factor is
Hermite-Biehler. The form differs from what Conrey and Li refuted (positivity conditions
on the space H(xi(1 - iz)), not the property of E_h at h < 1/2).

**Builder: a reformulation under kill condition 3, unresolved as a route.** By (a) the
property is exactly a zero-free half-plane, so the family delivers only the strips it is
given and reads only the zero locus.

**Rival gate: unresolved.** Independent defects at a failure point and a control point
per rival: DH flips at h between 0.25 and 0.375 at its zero, Epstein between 0.375 and
0.5, W_{1/4} between 0.2 and 0.3 (so the scalar Euler product with nonnegative
coefficients and the functional equation does not give the property), zeta(s - 0.1) lacks
the fixed functional equation. The challenger declined to upgrade the reformulation to a
restricted-class impossibility.

**Circularity: the builder's disposition stands.** B1: statement (a) is close to
Sondow-Dumitrescu (|xi| increasing along horizontal half-lines in a zero-free right
half-plane, Period. Math. Hungar. 60 (2010)) and to Lagarias's 2006 chapter (a de Branges
space for L exists if and only if RH holds for L); the exact form at given h was not found
in print. B2: by Saias and Weingartner (Acta Arith. 140 (2009), abstract re-read), DH has
zeros with real part in (1, 1 + eta), so by (a) **E_h^DH fails for every h <= 1/2**; the
grid's passes at h = 3/8 and 1/2 are a finite stand-in that the theorem overrides. B5: a
Chowla-Selberg census of the Epstein zeta in [0.55, 1.6] x [0.5, 60.5] finds five
off-line zeros, not the NOTES' two; the one at 33.650 lies inside the builder's grid
(x <= 40), whose step of 1/2 missed it (defect +0.457 at x = 33.6501, negative at the grid
points 33.5 and 34.0). A run-time trap around the builder's defect records no zero read.

**Synthesis: unresolved, recorded as a reformulation; the family is exhausted.** All
three sessions agree, and the evidence that decides it is the exact equivalence (a),
whose converse the circularity challenger rechecked: nothing in this family is weaker
than quasi-RH at the matching abscissa. Not *alive*, because no next step is left in the
family; not *restricted class obstructed*, because (a) is an equivalence, not a theorem
that rules a class out. B2 and B5 are accepted. The NOTES' Epstein failure list is
corrected by a dated note at the end of `de_branges/NOTES.md`.

Grades: (a) derived, reviewed by a second session (the circularity challenger rechecked
the converse); (b) derived, self-reviewed, conditional on the 7/8 strip; zeta's 2828
grid points hardened at the points, a sampled statement; B2 cited from an abstract.
Composite: derived, conditional on the 7/8 strip.

## 3. `li_arithmetic`: a uniform bound on Li's arithmetic part

**The construction** (`li_arithmetic/NOTES.md`). lambda_n = A(n) + T(n) (archimedean and
arithmetic parts, identity defect 8.1e-28), and the prime-side form lambda_n >= 0 if and
only if P_n <= M(n), with P_n = int_2^oo (psi(x) - x) L_{n-1}^{(2)}(log x) dx / x^2.
Measured for n <= 5000: |T(n)| <= 13.6 (zeta), 19.2 (DH), against A(n) up to 1.6e4.

**Builder: unresolved, two sub-routes refuted.** The pointwise bound by |E| exceeds M(n)
at every n <= 5000 where M(n) > 0 (least ratio 11.5), even with Schoenfeld's RH envelope;
the mean-square bound fails outside n in [32, 1258]. W_{1/4} has lambda_8260 = -122.32
with the failure in its arithmetic part.

**Rival gate: unresolved.** An independent recurrence finds DH's first negative
log-derivative coefficient at 3 and off-support at 6, Epstein's at 48 and 6, none for
zeta, W_{1/4} or zeta(s - 0.1) through 60; an independent zero-side sum gives
lambda_8260(W_{1/4}) = -122.315821669551207. W_{1/4} refutes the coarse package;
a theorem that adds unitary local roots is unformulated.

**Circularity: unresolved, the target a reformulation.** L1: the RH-conditional inputs
(Schoenfeld, Cramer's constant) sit only in the refuted routes; the positive half of the
mean-square bullet ("at most M(n) on [32, 1258]") is conditional and is no evidence. L2:
the artifact's P_n is M(n) - lambda_n with lambda_n from the xi side, so "P_n <= M(n) for
n <= 5000" is lambda_n >= 0 restated; an independent prime-side integral to 10^8 matches
it within 0.04 for n <= 1000 (measured, the tail beyond 10^8 unbounded). L3: W_{1/4}'s
zero-side cross-check assumes on-line zeros above height about 1419 (verified to 3e12).
L4: that DH has some negative lambda_n is a theorem (Bombieri-Lagarias multiset theorem);
only the index 328997 is extrapolated. Computed new: zeta(s - delta), delta = 1/4, has
lambda_n > 0 for every n (derived, self-reviewed by that session; measured for n <= 30)
and violates RH. Prior art: Voros's sharpening (arXiv math/0506326) is the published form
of the builder's onset heuristic; Johansson has lambda_n with interval values to
n = 100000.

**Synthesis: unresolved; the target is recorded as a reformulation until an estimate is
offered; the two absolute-value sub-routes and the coarse-package implication are
refuted at their stated parameters.** The challengers agree with each other and with the
builder; L2 lowers the builder's "prime integral satisfies P_n <= M(n)" to the xi-side
statement above n = 1000. The zeta(s - delta) result sharpens the target: Li positivity
implies RH only through the functional equation, which in this split enters through A(n),
so a proof of P_n <= M(n) must use the functional equation as well as psi.

Grades: split derived, self-reviewed, identity measured; Laguerre identity derived,
measured by a second route for n <= 1000; W_{1/4}'s sign hardened (two Cauchy radii plus
the zero route, reproduced by the rival challenger); onset heuristic inferred, published
in Voros's form. Composite: measured.

## 4. `positivity_geometry`: Weil's proof for curves, carried over

**The construction** (`positivity_geometry/NOTES.md`). The finite-field shadow (Gram
matrix of {F1, F2, Frobenius graphs} on C x C from brute-force counts, exact inertia, 8
curves of genus 1 and 2: one positive eigenvalue, every fake two); the number-field
target H_Q, equivalent to Weil positivity; the window-2g lemma (in the shadow, positivity
on the first 2g Frobenius powers is RH for C, sharp in genus 2 and 3); the golden fake
Z(T) = (1 - 5T + 5T^2)/((1 - T)(1 - 5T)) over F_5, with rationality, the curve functional
equation and poles, nonnegative closed-point counts in every degree and a
quadratic-character Euler product of conductor 4, whose Frobenius moduli are
sqrt 5 phi^(+-1). Euler-product step: G1 (nonnegative prime-power intersections), plus G2
(one pole plane); the engine G3 (Hodge index on an ambient surface) uses no Euler
product and is missing for zeta.

**Builder: unresolved, with a restricted-class obstruction** for arguments confined to
G1, G2, the functional equation and finiteness of rationality type that "transfer
verbatim" to function fields.

**Rival gate: unresolved, the obstruction narrower.** Independent exact recomputation of
the golden fake (counts, closed points to degree 80, moduli to 30 digits, margin -5) and
of the G1 table; W_{1/4} and zeta(s - 0.1) pass G1, so G1 is a precondition. The
restricted-class obstruction stays at the builder's review grade.

**Circularity: unresolved; the restricted-class label withdrawn to a refutation (D2).**
D1: the claim that no degree-1 Q-analogue of the golden fake exists is conditional on GRH
for Dirichlet L-functions. D2: "transfers verbatim" defines no class; what the golden fake
establishes is a counterexample to one function-field implication, {rationality, curve
functional equation, curve pole structure, nonnegative integer closed-point counts in
every degree, a +-1 local factor per place of F_5(t) with conductor 4} does not give RH.
D3: Ihara zeta functions of non-Ramanujan regular graphs (and Weng's non-abelian zeta
functions) are published neighbours, not the exact form. H_Q as a reformulation is in
print (Connes 1999; Connes, Consani and Marcolli, arXiv math/0703392). The window-2g
lemma is adjacent to Caratheodory-Fejer, not shown to follow from it. Recomputed golden
fake to degree 300; window lemma checked on 120 arbitrary closed multisets.

**Synthesis: unresolved for the mechanism; the golden fake recorded as a refutation of
the function-field implication D2 lists.** The builder and the rival challenger disagree
with the circularity challenger only about the label. `ALIGNMENT.md` section 5, item 2,
decides it: a restricted-class obstruction needs an explicitly defined class and a
theorem whose hypotheses are shown to apply, and "arguments that transfer verbatim" is
not an explicit class. The golden fake does fully support disposition 1 for the stated
implication. D1 is accepted: the scope boundary over Q is conditional on GRH. Over Q,
zeta(s - delta) passes G1 and G2 and violates RH while lacking the centred functional
equation, which supports the builder's "preconditions, not engine" without the
function-field detour.

Grades: shadow on 8 curves hardened (exact integers, two inertia routes); window-2g lemma
derived, reviewed by a second session, with measured checks; golden fake in every degree
derived, self-reviewed, its finite part recomputed exactly by both challengers; H_Q
equivalent to RH cited. Composite of the refutation: derived, self-reviewed.

## 5. `spectral_operator`: the CCM zeta spectral triple

**The construction** (`spectral_operator/NOTES.md`). CCM's operator D'' on
E_N / C xi, self-adjoint for W = T - eps_N when T is even-simple (CCM Lemma "key",
Theorem "finmain"), built from the same prime, pole and archimedean data. Even-simplicity
hardened by Arb LDL^T inertia on 7 cells; spectrum by two routes agreeing to 2e-26.
For zeta at (60, 100) all 46 zeros below 138 are matched to 4.6e-40, far beyond the
Gram-point control (median distance 0.76). For DH, at (60, 100) its form has negative
directions, yet the operator is self-adjoint with real eigenvalues inside the gap of its
off-line pair.

**Builder: a located obstruction, recorded as a reformulation for the self-adjointness
step;** the RH content is link (3), the convergence, which is `ccm_arithmetic`'s step 2.

**Rival gate: unresolved; self-adjointness refuted as a discriminator.** Independent
assembly and operator for DH (13, 40), Epstein (13, 20), W_{1/4} (2, 8): commutator
defects 6e-60 to 2e-55, real spectra, nearest eigenvalues at distance 0.46, 0.67 and 0.34
from the off-line zeros. Recentred zeta(s - 0.1) is zeta. One small cell each, measured.

**Circularity: restricted class obstructed for the self-adjointness step; unresolved for
the mechanism.** P1: provenance verified at run time, which is stronger than the
builder's text scan: traps on every zero routine of mpmath, Arb, `zeta.zeros` and the xi
and theta functions, every zero-like module constant on the definition path poisoned
(including DH's off-line ordinates, which `wp_common` carries), every file open logged.
Nothing fired, nothing was touched, no file was opened, for zeta and for DH; both
planted controls were caught. The 4e-41 match is therefore an output, not imported zeros.
P2: self-adjointness is Connes and van Suijlekom's theorem with no arithmetic input.
P3: a second eigensolver agrees.

**Synthesis: restricted class obstructed for the self-adjointness step; link (3)
unresolved and merged with `ccm_arithmetic`.** The two challengers differ only in the
label for the same fact, and the circularity challenger's label is the one the evidence
supports: there is a primary-source theorem (Connes and van Suijlekom, Prop. 4.1, with
CCM's Lemma "key") for an explicit class (every real distribution whose truncated form is
even-simple), and its hypotheses are shown to apply to DH on three hardened cells. The
rival challenger's "refuted as a discriminator" is the instance of that theorem on DH.
The mechanism is not ranked separately below, because its only open step is
`ccm_arithmetic`'s link (2) read through the operator.

Grades: even-simplicity hardened, band-level (the C1 caveat applies); self-adjointness
cited, checked numerically to 1e-60; spectrum against zeros measured (float-grade
eigenvector, 42-digit targets); provenance clean by three methods. Composite: measured.

## 6. `probe_tower`: probes of growing degree in the 7/8 assembly

**The construction** (`probe_tower/NOTES.md`). Reading each 6 of OpenAI's 7/8 paper as
the character order k gives sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k), strictly increasing
in k and tending to 1; LP walls 1 - 2/k (dual length) and 1 - 4/(5k) (floor rows), so the
best order is k = 2 at 3/5, for which no system exists; the formal k = 1 is Littlewood's
RH-equivalent Moebius bound. The Euler-product step (E_k) is k-independent; DH and
Epstein fail it at their zeros, DH for every finite deletion set by Saias-Weingartner;
W_a passes it and is held off by unitarity, a shift of exactly 1/4.

**Builder, rival gate and circularity: restricted class obstructed.** The rival
challenger rebuilt the formulas and the dual identity in exact rationals (1,080 identity
instances) and the rival rows; the circularity challenger rebuilt the walls by exact
vertex enumeration and DH's correction at its zero by a Hurwitz route. P1: every wall
rests on the inferred k-reading, and the agreement with hunt #136's probe lane checks
algebra, not the reading. P2: some cited sources were uncommitted when cited; hunt #136's
checkpoint `57c7024c1` was local only when checked. New: zeta(s - delta) passes (E_k)
exactly and every wall rises by delta, the cleanest unitarity rival. Prior art: Liu
(arXiv 2610.12234) proves optimality of about 0.874957 within an explicitly specified
exponent system; no published order-k tower was found.

**Synthesis: restricted class obstructed**, with the class as `probe_tower/NOTES.md`
section 9 defines it, the tower premise refuted inside it, and the transfer to actual
order-k theta systems inferred. All three sessions agree. Its hand-off is a half-plane
step below 13/15 that belongs to hunt #136, not an RH step.

Grades: walls derived, symbolic in k, rechecked by two independent routes; k-reading
inferred; rival rows measured; Saias-Weingartner cited from its abstract. Composite:
inferred.

## 7. Ranking of the survivors by distance to a proof of RH

The survivors are the constructions not obstructed in their RH form: `ccm_arithmetic`
(with `spectral_operator`'s link (3)), `li_arithmetic`, `positivity_geometry` and
`de_branges`. All four are far from a proof. The ranking is by what is missing and
whether the missing step is known to be as hard as RH.

1. **`ccm_arithmetic`.** The missing step is one convergence statement. It is not known
   to be equivalent to RH (C2 is open), it is measured to hold for zeta on every cell to
   c = 60, and it separates at located windows all three rivals the hunt names while a
   second Euler product (Dedekind) passes. It is also the only mechanism whose
   discriminating step the hunt located by computation on every rival rather than by an
   equivalence. Against it: C1 (positivity is band-level and falling in N), the vacuous
   perturbative bounds, and the risk that capture is Weil positivity in disguise.
2. **`li_arithmetic`.** The target is RH-equivalent by construction, and every
   absolute-value route fails by factors from 11.5 to 1.6e4 on the measured range. What
   is missing is a signed cancellation estimate that uses unitarity and the functional
   equation (zeta(s - delta) and W_{1/4} show both are needed), of the depth of RH
   itself. It ranks above the next two because the missing inequality is explicit and
   each candidate can be tested cheaply against W_{1/4}'s failure at n = 8260.
3. **`positivity_geometry`.** The target is RH-equivalent and the ingredient that proves
   it in the shadow, an ambient surface with Riemann-Roch, does not exist for Spec Z. Its
   first next step is cheap and decisive for one candidate (the pairing of two scaling
   correspondences against Lambda(n) n^(-1/2)), but a match would only move the problem
   to Riemann-Roch on the square.
4. **`de_branges`.** In the Lagarias family the property is quasi-RH at each abscissa, so
   the family adds nothing to RH; a different structure function (Suzuki's space, which
   assumes RH, or his screw-function form) would be a new construction, not this one.

## 8. The next construction step for the top two, and what decides it

**`ccm_arithmetic`: the fine DH grid on c in (30.6, 33) at N = 64 and N = 128** (NOTES
section 9, step 2). Measure, on one grid, the sign change of the band-N form, the window
where capture is lost (misfit against DH's own radical), and the gap scale
(lambda_2 - lambda_1)/||dA/dy||. What decides it: if capture is lost at a c that stays
above the sign change by a margin that does not shrink as N grows (c = 31 already shows
capture with a negative value at N = 64), capture is strictly weaker than window
positivity and the target is not Weil's criterion restated; if the loss of capture
converges onto the sign change as N grows, C2 holds on this evidence and link (2) is
recorded as a reformulation (kill condition 3). Either outcome is a disposition change.
Under C1 the grid must also report lambda_1 against N, so that a sign is read only where
it is stable in N. The step after it, whichever way this goes: test the semilocal unitary
decomposition (U-S) on v_c for zeta and Dedekind against W_a at its threshold c_a, the
arithmetic input the unitarity dial points to.

**`li_arithmetic`: a mean-value bound on the kernel-weighted prime sum** (NOTES section
9, step 1, its arithmetic alternative): bound
sum_m Lambda(m) m^(-1/2) e^(i t log m) weighted by the Laguerre kernel's phase
2 sqrt(n u), by a large-sieve or mean-value inequality, and compare with M(n). What
decides it: the bound must beat M(n) on 1259 <= n <= 5000, where the mean-square route
fails, and its W_{1/4} analogue must fail at or before n = 8260; a bound whose W_{1/4}
analogue still holds at 8260 uses only the coarse package that W_{1/4} refutes, and is
refuted with it before any zeta computation.

## 9. What the record keeps regardless of RH

These are outputs of the hunt that stand whatever happens to the mechanisms. None is
kernel-checked, and none is claimed novel in the literature unless a search is stated.

1. **Five off-line zeros of the Epstein zeta of x^2 + xy + 6y^2 (discriminant -23)** in
   [0.55, 1.6] x [0.5, 60.5], counted by the circularity challenger's argument-principle
   census (windows of height 10 from 0.5: 0, 1, 1, 1, 2, 0; `de_branges/challenge/`):

   | zero | offset from 1/2 | found by | grade |
   |---|---|---|---|
   | 0.953260 + 16.290216i | 0.4533 | already in the record (`weil_propagation`; hunt #120) | as recorded there |
   | 0.7979971571787 + 29.5517610986291i | 0.2980 | `de_branges` builder | measured, three routes and a winding count |
   | 0.66365167885960 + 33.65010058252734i | 0.1637 | circularity challenger | measured, two routes and a winding count |
   | 0.80999153149713 + 43.85866436500448i | 0.3100 | circularity challenger | measured, two routes and a winding count |
   | 0.78237857667773 + 46.96099366990747i | 0.2824 | circularity challenger | measured, two routes and a winding count |

   The four below the first are **new to this tree**: absent from hunt #120's census
   (which covered Re s >= 0.8751 only), from `plocal_rivals`, `zeta.epstein` and
   `docs/23`. **None is enclosed**: the evidence is Newton roots with small values and
   winding counts, and no in-tree route evaluates this function on segment balls (hunt
   #120's ball route inflates an input radius of 1e-4 to an output radius of 1e67 at
   height 15). No literature novelty is claimed: one search was run for the zero at
   29.55 (Hejhal's ICM 1986 survey and five papers on other forms, none listing it) and
   none for the other three.
2. **W_{1/4} = zeta(s + 1/4) zeta(s - 1/4) has its first negative Li coefficient at
   n = 8260**, lambda_8260 = -122.32 (215 negative values to n = 9000, least -87409.5 at
   n = 8977). Hardened: Cauchy routes at two radii agree to 2.6e-48 relative, and a
   zero-side route (which assumes on-line zeros above height about 1419) gives
   -122.3158; the rival challenger reproduced -122.315821669551207 without mechanism
   code. The failure is in the arithmetic part, abruptly (T_W(8260) = -55949 against
   A_W(8260) = 55827).
3. **zeta(s - delta) keeps every lambda_n > 0 while violating RH.** Its completion's
   zeros all lie on Re s = 1/2 + delta, so |1 - 1/rho| < 1 for each and every
   lambda_n = sum_rho [1 - (1 - 1/rho)^n] is positive (derived, self-reviewed by the
   circularity challenger; measured for n <= 30 at delta = 1/4). It lacks the centred
   functional equation, so it is not a counterexample to Li's criterion; it shows the
   criterion carries RH only through that functional equation. The same function passes
   G1 and G2 (`positivity_geometry`) and the Euler step (E_k) (`probe_tower`), which makes
   it the cleanest one-factor rival for the unitarity hypothesis.
4. **The golden fake** over F_5: rational, with the curve functional equation and poles,
   nonnegative closed-point counts in every degree and a +-1 local factor per place of
   F_5(t) of conductor 4, and Frobenius moduli sqrt 5 phi^(+-1). Derived for all
   degrees, self-reviewed; recomputed exactly to degree 300 by a second session.
   Original to this hunt; published neighbours (Ihara, Weng) are not the exact form.
5. **The window-2g lemma** for curves: positivity of the projected Toeplitz form on the
   first 2g Frobenius powers is equivalent to RH for C, and 2g is sharp in genus 2 and 3.
   Derived, reviewed by a second session; adjacent to Caratheodory-Fejer.
6. **The W_a unitarity dial** (`ccm_arithmetic`): W_a's truncated Weil form first goes
   negative at c_a in (2.3887, 2.3906) for a = 1/4, moving by about +0.15 per halving of
   a, with W_0 = 2 Q_zeta to 3.9e-180. Hardened (Arb LDL^T).
7. **DH meets no Hermite-Biehler structure of the Lagarias family for any h <= 1/2**, by
   Saias-Weingartner and statement (a) (cited plus derived).
8. **The CCM operator's provenance is clean by three methods**, including run-time traps
   with poisoned constants, so its 4e-41 agreement with zeta's first zero (and 4.6e-40 for
   46 zeros below 138 at (60, 100)) is an output of primes up to c, the pole and the
   archimedean place. Measured; a reproduction of CCM, no novelty claimed.
9. **A citation in this tree is wrong** (`de_branges/NOTES.md` section 1, confirmed by the
   circularity challenger): `hunts/rogue_frontier/FRONTIER_MAP.md`, territory F, gives
   Lagarias's 2006 chapter a wrong title and an equivalence it does not state. That file
   is outside this hunt's scope; the operator holds the correction.

## The doors

This hunt measured where six constructions stop, so it owes the door analysis. Candidate
status: every stopping point below is a measured or derived wall of a specific
construction at its stated parameters, not a proved ceiling on RH; information class is
given per door; proof status as graded in sections 1 to 6. The latest door gets no
automatic priority: allocation is the owner's.

### Active constraints at the optimum

Ranked by how directly each binds a survivor's open step:

1. **The uniform step (all windows, all n, all h, all k).** Every survivor stops at a
   finite range: c <= 60 and N <= 128 (`ccm_arithmetic`), n <= 5000 and x <= 10^8
   (`li_arithmetic`), |x| <= 100 (`de_branges`), seven (c, N) cells (`spectral_operator`).
   It binds everywhere and no measurement relaxes it.
2. **Capture co-located with positivity** (`ccm_arithmetic`). The perturbative bound
   eta / (mu - lambda_1) is at least 2.8e4 because mu, the bottom of the form off R_m, is
   itself exponentially small (lambda_2's eigenvector is also radical times a
   polynomial); the leakage eta, about 1e-35, is not what binds. Rigidity shows any proof
   of capture must read the prime powers exactly, at a scale shrinking exponentially in
   c.
3. **Band-level positivity** (C1). lambda_1(N) is an upper bound on the window infimum
   and still falling at N = 128, so no window sign for zeta is read from this grid.
4. **Absolute value against oscillation** (`li_arithmetic`). The true P_n is small by
   cancellation of the Laguerre kernel against psi(x) - x; pointwise bounds exceed M(n)
   by at least 11.5, the mean-square tail (3.99e4 against 7.7e3 at n = 5000) binds from
   n = 1259.
5. **The zero-free abscissa** (`de_branges`). The family reaches h > 3/8 only because the
   7/8 strip exists; its slope is one for one, h = sigma - 1/2.
6. **The missing ambient surface** (`positivity_geometry`, G3) and **the comparison pole
   1/k** (`probe_tower`, shadow price -3/4 at the paper's geometry), both outside the
   survivors' data.

### The frozen-constant inventory

| constant | value | what relaxing it trades | trade shape |
|---|---|---|---|
| window range (`ccm_arithmetic`) | c <= 60 | cost grows with c and needs N to grow with it | genuine: the fine DH grid needs c only to 33 |
| band (`ccm_arithmetic`, `spectral_operator`) | N <= 128; N <= 200 | lambda_1 falls by orders with N; time grows (890 s at (13, 200)) | genuine: C1 needs a saturation curve in N |
| capture subspace degree | m = 2, 4 | raising m raised mu by 13 orders and left the bound vacuous | none at small m; the door is a direct leakage bound |
| off-axis line | Im z = 0.45 | Hurwitz needs the whole strip neighbourhood | genuine, unmeasured beyond one line |
| Li range and prime cutoff | n <= 5000, x0 = 10^8 | cost grows with n (work digits like n log10(1/r)); DH's onset is near 3.3e5 | genuine; Johansson's range is 1e5 |
| conditional envelopes | Schoenfeld above 10^8, Cramer's constant | refuted routes only; unconditional envelopes are larger | none: the routes fail a fortiori |
| Epstein grid (`de_branges`) | x step 1/2, x <= 40 | missed the zero at 33.65; a finer step costs 12 to 18 s per mpmath point | genuine |
| Epstein census box | [0.55, 1.6] x [0.5, 60.5] | zeros above 60.5 and left of 0.55 unknown | genuine |
| rival shifts | a = 1/4; delta = 0.1, 1/5, 1/4 | one value each; the dial shows a matters smoothly | genuine for the unitarity reading |
| order and floor bin (`probe_tower`) | k = 6; delta_0 = 1/50 | see `probe_tower/NOTES.md`, its own doors | as recorded there |
| target zeros | 42 digits | floors the operator residuals near 1e-41 | none for the conclusions |

### The information class

- **Inside the data the families already read.** The fine DH grid and the saturation in
  N (primes up to c, the pole, the archimedean place); the U-S test on v_c (local
  factors, the same data); a mean-value bound on the kernel-weighted prime sum (prime
  powers only); the operator run on Epstein (1,1,6), W_{1/4} and zeta(s - delta) below
  and above their capture-loss windows, of which the rival challenger ran one small cell
  each (DH (13, 40), Epstein (13, 20), W_{1/4} (2, 8), recentred zeta(s - 0.1) (13, 16))
  but not the comparison across the windows; the census of the Epstein zeta above height
  60.5.
- **Reading more.** Enclosures of the Epstein zeros, which need a route that evaluates
  the D = -23 function on segment balls, which this tree does not have; a signed bound on
  P_n zero by zero, which reads the zeros and is a different information class from the
  prime side; any move of `de_branges`'s h-range, which needs a new zero-free strip;
  `positivity_geometry`'s ambient surface, an object no current data supplies; and the
  half-plane step below 13/15, which belongs to hunt #136.
- **Not done, named by the challengers.** Enclosures of the five Epstein zeros, a census
  above height 60.5, and the Epstein, W_{1/4} and zeta(s - delta) rivals through the
  spectral operator across their capture-loss windows. Each is in the first class except
  the enclosures.

## Run record

```runmanifest
id: rh_moonshot-synthesis-2026-10-26
hunt: rh_moonshot
started: 2026-10-26T16:14+00:00
finished: 2026-10-26T16:24+00:00
ran:
  - git merge --no-edit origin/hunt/rh-moonshot-challenge-rival (no conflict)
  - git merge --no-edit origin/hunt/rh-moonshot-challenge-circularity (no conflict)
  - nice -n 10 .venv/bin/python -m pytest -q -n0 on each of the six */challenge directories and each mechanism's own test_*.py files, one process per directory (12 processes in sequence)
  - .venv/bin/python -m pytest -q -n0 tests/test_hunt_doors.py tests/test_hunt_probe_discipline.py tests/test_huntspec.py tests/test_docs_numbering.py
  - .venv/bin/python scripts/make_context.py --check
outcome: both challenges merged; every challenge directory (80 tests) and every mechanism's own tests (166) pass with -n0, plus the repo checks test_hunt_doors, test_hunt_probe_discipline, test_huntspec, test_docs_numbering and make_context --check; six dispositions recorded (ccm_arithmetic alive; de_branges, li_arithmetic, positivity_geometry unresolved; spectral_operator self-adjointness restricted class obstructed with link (3) unresolved; probe_tower restricted class obstructed); no route established in the searched set
artifacts:
  - hunts/rh_moonshot/RESULTS.md
  - hunts/rh_moonshot/de_branges/NOTES.md (dated correction appended)
```
