# Assembly lane: an exact model of OpenAI's Part II final assembly

**Hunt #136, lane "assembly", 2026-10-21. Status: lane output, revised after verifier round 1,
unreviewed by any person. Nothing here is a result until the case log in `hunts/README.md`
says how the hunt ended.** Files: `assembly.py` (the model and its solvers) and
`test_assembly.py`. The tests pin the numbers on this page: every decimal and fraction in the
text is checked, sign included, against a whitelist in `test_assembly.py` whose entries are
asserted by its tests (or are cited constants of the paper, input values and external
reference lines, each marked as such where it appears), and the three
tables of sections 4 to 6 are checked cell by cell against the computed values. For prose
numbers the check is a whitelist, so it catches an unpinned or mistyped number, not two pinned
numbers swapped in a sentence.

Grades as in `MISSION.md`: *cited* (a line of the pinned `paper.tex`, sha256 `42a5ee0f...c6a3`,
checked by `assembly.verify_citations`), *derived* (exact arithmetic here, pinned by a test),
*inferred* (a reading no computation checks), *measured* (float output). A composite claim
takes the grade of its weakest step. Nothing on this page is about real part 1/2 or RH, and
no improvement of the half-plane is claimed: every abscissa below is a statement about this
one assembly with stated inputs, and the lemmas that supply those inputs are not checked here.

**Two readings carry every abscissa below 7/8 on this page.** Both are inferred, and a
sub-7/8 number is graded "conditional on R1 and R2" wherever it appears.

- **R1, total accounting** (hunt #134): only the unrescaled summand of the low estimate must
  be lossless (Lemma probe-row-norm, lines 8306 and 8325). Under the paper's own per-summand
  bookkeeping the best abscissa is exactly 7/8 (section 2).
- **R2, the shared lemmas below their range.** Every high row of the model is the exponent of
  Lemma bin-contour-accounting (line 6090), and the floor, small and large rows come from
  Lemma fixed-bin-contour, the principal-signal lemma and Lemma outer-row-tails. All four are
  stated only for `sigma_0 in [7/8, 1)` with `beta_* > sigma_0` (lines 5811, 6024, 6178, 6345),
  and the paper invokes them at `sigma_0 = 7/8` (lines 15532, 15823). Using them at a target
  near 0.87496, or lower, is the bootstrap clause of MISSION dead route 1. The Euler-region
  inputs that plug in 7/8 are in the same position; hunt #134 (RESULTS section 7) read them
  as harmless for targets above about 2/3, also inferred. This lane does not check that any
  of these proofs survive a lower target.

## Summary

1. **The model.** The final section (lines 15495 to 16463) and the lemmas it cites are
   rewritten with seven exponents as symbols: the marked capacity slope `c_M` (paper 1/2), the
   plain capacity slope `c_P` (2/9), the amplification slope `alpha` (5/6), the floor-bin
   count `R_fl` (1), the Gram exponent `g` behind `P_a^{1/12}` (1/6), the sextic pole `z_p`
   (1/6), and, though it is not a row count, the pointwise reflected-numerator cost `n` of
   `U^{n delta}` (1/2, line 15801), the factor this hunt's `FOLLOWUPS.md` reports the public
   follow-ups changed. With the geometry (ell, M, b) free, every high exponent is affine in
   the geometry once the bin data (delta, x) are fixed, so the best abscissa of the assembly
   is a semi-infinite linear program in three variables. 72 reproduction checks (printed
   constants and printed identities, rebuilt from the general formulas) agree, and 123
   citations sit on their stated lines of the pinned file (derived, cited).
2. **The controls reproduce exactly.** 7/8 is the target at the paper's geometry and is
   exactly the best abscissa under the paper's own row-norm bookkeeping (a dual witness
   gives 7/8 from below, the paper's geometry gives it from above). Also 49/440640 with its
   completed square, the worst point 7/30672, #134's one-witness bound
   5655673/6464057 (0.8749417) and its Gram-limited 44117/50422, #134's scan 0.874958 (the
   optimum with b held at 3/25 is 0.8749576643), and the perfect-count ceiling 13/15
   (derived; the sub-7/8 ones conditional on R1 and R2).
3. **The re-optimized assembly has a closed-form optimum.** With the paper's inputs the best
   abscissa is `sigma_* = (1507 - 2 sqrt 921)/1653 = 0.8749570698`, at
   `delta_* = (49 - sqrt 921)/48`, ell = 0.1668383875, b = 0.1234054370, M = 1 - ell
   (derived, conditional on R1 and R2). The KKT multipliers form an exact dual witness in
   Q(sqrt 921) whose bound is sigma_* itself; a rational geometry checked exactly on the whole
   (delta, x) rectangle lies less than 2 parts in 10^14 above it; an LP proposed from a float
   cut set and decided exactly brackets it within 2 parts in 10^8. #134's 0.8749417 is a lower
   bound with slack, and its scan value sits at b = 3/25.
4. **Guo's number matches this re-optimization with the plain capacity tied to the target.**
   Setting `c_P = 1/(6 (2 sigma - 1))` (the dynamic kappa of line 15100 carried below 3/4)
   and solving the fixed point gives 0.87495701942 (exact bracket of width below 10^-18),
   which agrees with Guo's 0.8749570194 in all ten printed digits. Measured agreement; that
   Guo's improvement is exactly this is inferred, since his paper was not read here. Beyond
   R1 and R2 it uses Lemma plain below its stated range kappa >= 3/4 (line 12532).
5. **Shadow prices (derived, exact in Q(sqrt 921); conditional on R1 and R2).** Per unit of
   each input at the optimum: `z_p` -0.8119602997, `n` +0.0591792953, `g` +0.0501294854,
   `c_M` -0.0095710837, `alpha` +0.0047006135, `c_P` -0.0019776984, `R_fl` 0 (the floor is
   slack). Ranked by size: z_p, n, g, c_M, alpha, c_P, R_fl, and the elasticities rank the
   same. Of the three row-count inputs the marked capacity leads, but the numerator cost is
   worth about six times more per unit (ratio 6.18). Finite differences of the closed form agree.
6. **To beat Xu and Sang (0.8748867)** one input alone must move by z_p +0.0000866553,
   n -0.0011898023, g -0.0013738421, c_M +0.0073016702, alpha -0.0146429748 or
   c_P +0.0342796610 (derived, conditional on R1 and R2; each crossing lies in regime A, the
   paper's neighbourhood). **To reach 0.87:** z_p to 0.1727198769, n to 0.3708105098, g to
   between 0.0890072152 and 0.0890074160, or alpha to 0.2946252341; c_M and c_P cannot, alone
   or together, with alpha at 5/6. **To reach 13/15:** z_p to 0.1767414708 or g to 181/4290;
   not n alone (every n >= 0 stays at or above 659/759), and not the row-count inputs, alone or
   together (every value stays at or above 167/192). Each is a candidate about a hypothetically
   stronger input, not a claim that such an input exists.
7. **The reach of the row-count inputs as written is 167/192 = 0.8697916667** (derived, a
   ceiling of the frozen frame, conditional on R1 and R2). The low side, the floor bin
   (line 15847), the dual length and b >= 0 carry an exact dual witness that involves none of
   c_M, c_P, alpha. The bound is attained exactly at every alpha up to 27/100 (checked there;
   the endpoint rows only weaken as alpha falls), and the regime-B closed form reaches it at
   alpha = 0.2757692192. The capacities alone (alpha at 5/6) stop at 0.8740524834, set by
   rows with no prime amplitude (x = 0). #134's 13/15 returns only when the floor bin also
   goes to delta_0 -> 0 (relaxation inferred). These are ceilings of the frame this lane
   froze: the bin ceiling is held at 5/6 with no margin, while the paper's bins satisfy
   delta <= kappa = 2 beta_* - 1 (lines 6825, 15100) and evaluate the intermediate bound at
   5/6 only as a convenience (line 16165).
8. **The constraint that becomes active next** (derived in the model, exact brackets or closed
   forms; the abscissae there are below 7/8, so conditional on R1 and R2):
   along z_p and g, the floor bin (z_p = 0.1751510556, g = 0.1567188215); along c_M, the supply
   hypothesis of Proposition detector-counts (c_M = 0.5361872194); along n, the intermediate
   range (n = 0.4908887159); along alpha, the offset b reaching 0 (alpha = 0.6098049914), then
   the floor bin (alpha = 0.2757692192); along c_P, the binding amplitude ratio leaves x = 1/2
   (c_P = 0.5261221985).

## Corrections after verifier round 1

The first version of this page (the lane run of 2026-10-21 that started at 14:36Z) had three
errors that change claims and several overstatements. Each is corrected in place above and
below; this is the list.

1. **The intermediate row was imposed outside its range** (verifier issue 1). The paper takes
   t = 1 with no slots in `d <= 1/2` only "for delta <= alpha" (line 16146), and Proposition
   detector-counts is stated for `delta <= alpha` (line 15188). Bins with `delta >= alpha` carry
   R = 1 - delta at every d <= h (lines 15458 to 15463, line 16168; inferred for delta > alpha),
   which the endpoint row already holds. The model imposed the intermediate row at delta = 5/6
   for every alpha. It now
   imposes it at delta = min(alpha, 5/6). At the paper's alpha = 5/6 nothing changes. Along the
   alpha axis five statements were false and are withdrawn: that the row-count inputs together
   are capped at 84031/96156; that c_M, c_P and alpha cannot reach 0.87 alone or together;
   that the alpha path meets 84031/96156 and stays; that the intermediate range binds first
   along alpha; and that 84031/96156 is attained at alpha = 1/2. In the corrected model the
   abscissa at alpha = 1/2 is 0.8722266776. What survives of 84031/96156 is the four-row bound
   for alpha >= 5/6 (section 7); `Frozen(intermediate="at_delta_max")` reproduces the old frame.
2. **Sub-7/8 abscissae rested on a second unstated reading** (issue 2): R2 above.
3. **The exact rectangle check had a sampling hole** (issue 3). The sampler skipped a gap
   between two roots whenever sympy's isolating intervals shared an endpoint, so it could pass
   a polynomial negative between two close roots. It now samples every interval endpoint and
   checks each closed cell between samples with a Sturm count, bisecting any cell that holds
   two roots. Every stored upper-end geometry in the tests was re-checked with the repaired
   check and passes (the verifier's own dense grid, in an independent model, also found them
   feasible), so no number moved. The upper ends are derived on the repaired check.
4. **The markdown gate ignored negative numbers** (issue 4) and was described as stronger than
   it was. It now reads signs and checks three tables cell by cell; the header says what it
   cannot catch.
5. **Two planted code faults stayed green** (issue 5). In the repaired sampler soundness rests
   on the Sturm guard alone; the interval endpoints and midpoints only make it fast. So the
   verifier's first fault, gap midpoints removed, is now harmless, and in scratch-copy runs of
   this repair (not tests of the suite) removing the midpoints, the shared endpoints, or both,
   left every test green, as it should. A reconstruction of the 14:36Z sampler (from the
   verifier's description) turned three of the four sampler tests red, and removing the guard
   turned `test_sturm_guard_alone_decides` red. The second
   fault, skipping the bins with delta >= alpha, goes red by the test hook and by deleting the
   branch. A further gap found in the repair: reading the bins delta >= alpha at d = h instead
   of d = d_min inside the check of the rows at d < h stayed green, and now goes red
   (`test_planted_fault_inner_large_delta_rows_go_red`).
6. **The capacity ceiling was called attained at c_M = 9/10** (issue 6) without saying that
   Lemma marked's second width condition (line 9254) fails there. With z = c_M (1 - r) over
   the requested r, whose least value sits at x = 1/2 (or at x = 0, where r = 2/3, once
   c_P > c_M), that condition `2r + 8z <= 3m - c_2` holds only for
   `c_M <= (5 - 4 c_P)/(9 - 8 c_P)` and `c_M <= 5/8`, which is 37/65 at c_P = 2/9 (derived).
   Every regime-A statement along c_M sits below 37/65; the attainment needs a hypothetical
   marked lemma without that condition.
7. **The reduction of every row to d = h assumed n large** (issue 7). The d-slope of each row is
   at least `(1 - z_0) - (1 - n) delta`, nonnegative for every bin once n >= 26/125. Below that the
   rows at d < h are now checked exactly (`inner_rows_ok`), and the n-axis formula is checked
   with them.
8. **The ceilings belong to the frozen frame** (issue 7, second part): item 7 of the summary.

## 1. The model

Everything is in `assembly.py`; every function is exact rational arithmetic and accepts
Fractions, sympy expressions or the quadratic-field numbers `QF`.

| symbol | paper | where it enters | cited at |
|---|---|---|---|
| `c_M` | 1/2 | marked capacity `z_M(r) = c_M (1 - r)`, from `r + 2z <= 1` | 15182, 9254 |
| `c_P` | 2/9 | plain capacity `z_P(m) = c_P (1 - 2m) = (1 - 2m)/(6 kappa)` at kappa = 3/4 | 15175, 15327 |
| `alpha` | 5/6 | amplified count `e(r) = 1 - alpha + alpha r`, from `P = (H/U)^{1/6}` | 15300, 12369 |
| `R_fl` | 1 | count of the floor bin, no zero witness | 15844 |
| `g` | 1/6 | Gram bound `(Q/Y')(1 + P_a^g + P_a^2/Y')`, low bound `P_a^{g/2}`, `P_a = Z^b` | 8353, 8619, 8588 |
| `z_p` | 1/6 | pole of `zeta_F(6z)`: `C(s) = s + l_x/2 - 1 + z_p h`, high exponent `h(z_0 - z_p)` | 5588, 6090 |
| `n` (`n_num`) | 1/2 | pointwise reflected numerator `U^{n delta}` in the d-slope `R + n delta - z_0`; not a row count | 15801, 6090 |

The general forms (derived from the cited displays, checked by reproduction at the paper's
values):

- target: `sigma_0 = 1 - z_p h + (g/2) b`, with `h = 1 + ell - M/2 + b/2`; the row-norm loss
  adds `((1 + 3 ell - 2M)/8)_+` under total accounting (R1), while the paper's own bookkeeping
  requires `M - 2 ell >= 1/2`.
- counts: `D_x = 3 - 2x(c_M + 2 c_P)`, `P_x = (2 - 4 c_P x)(1 - 2 c_M x)`; the crossing of the
  marked and plain counts, `R_short(t) = 1 - delta + (delta P_x/D_x)(3/2 - t)` (independent of
  r, as at line 15417) and `R_* = 1 - delta + K/2` with
  `K = (alpha - delta) delta P_x / ((alpha - delta) D_x + delta P_x)` (line 16019) for
  delta < alpha; `R = 1 - delta` for delta >= alpha (cited at delta = alpha, line 16129; for
  delta > alpha an inferred reading of the remark at lines 15448 to 15467, which the paper
  never needs because its alpha equals its bin ceiling).
- high side, measured against the matched target: the endpoint
  `-E_* = -C_0 + delta(ell + b)/2 - ell x delta - (h/2) K - h delta (n - 1/2)` with
  `C_0 = 1/2 + ell/2 - 3M/4 + b(1/4 - g/2)`; the floor `E(h)` at delta_0 = 1/50 with count
  `R_fl`; the intermediate range at d = 1/2 with the no-slot count `76/75 - 2 delta/3`, for
  delta up to min(alpha, 5/6) only (line 16146); small rows `h(z_0 - z_p) - l_y/2 + 2 d_min`;
  the supply hypothesis that ell/h covers the largest requested capacity (7/37 at the paper's
  values); the Gram condition `b(3 - 2g) <= M - 2 ell`; `M + ell <= 1`; `b >= 0`.
- rows at d < h: each row is affine in d, with slope `R + n delta - z_0` at least
  `(1 - z_0) - (1 - n) delta`, so for n >= 26/125 every row is bounded by its d = h end
  (derived; the paper states the slope at n = 1/2, line 16133). Below 26/125 `inner_rows_ok`
  checks the other ends: the slot rows at d = 1/2, the bins delta >= alpha, the intermediate
  rows and the floor at d = d_min.
- the comparison used at line 16101: `E_actual(h) - Delta <= E_* - (1 - h/4) Delta`, so the
  argument closes for every small Delta > 0 exactly when `E_* <= 0` on every bin.

z_p cancels from every high exponent measured against the target (the signal and the high
side both carry `h z_p`); the small-row bound, measured against `C(beta_*)` and slack, is the
only place it stays. g enters only the low side and the Gram condition.

Four solvers. `regime_A` is the closed form when the only binding high constraint is the
endpoint at x = 1/2 with b > 0: one tangency `K(delta_*) = k_0 + k_1 delta_*` (a quadratic in
delta_*), then two linear equations for (ell, b). `regime_B` is the closed form once b has
reached 0 (section 5). `sandwich` brackets the optimum at any rational inputs: a float LP over
a refined cut set proposes a basis, the lower end is an exact rational dual witness and the
upper end is a rational geometry whose feasibility on the whole rectangle delta in [1/50, 5/6],
x in [0, 1/2] is decided exactly (times J the endpoint is quadratic in delta, so the check is
root isolation in x, with every root-free piece sampled and every cell guarded by a Sturm
count). `lower_bound_from` builds a dual witness from named rows only, which is how the
ceilings below are shown to hold for every value of an input.

## 2. Controls

| control | value here | how | grade |
|---|---|---|---|
| target at (1/6, 5/6, 1/8) | 7/8 | `target`, and 11/12 with no slots | derived |
| best abscissa, paper's bookkeeping | 7/8 | dual witness from below, paper geometry from above | derived |
| endpoint margin floor (line 16068) | 49/440640 | `49/(176256 J)` at J = 5/2, completed square on 101 points | derived |
| worst point delta = 79/204, x = 1/2 | 7/30672 | `neg_E_star` | derived |
| #134 one-witness bound, delta = 223/576 | 5655673/6464057 | `robust_single_point_bound` | derived, R1, R2 |
| #134 Gram-limited bound, delta = 7/18 | 44117/50422 | `gram_limited_single_point_bound` | derived, R1, R2 |
| #134 scan at b = 0.12 | 0.874958 | the b = 3/25 optimum is 0.8749576643 | derived (exact root isolation), R1, R2 |
| perfect counts, floor delta_0 -> 0 | 13/15 | vertex (1/5, 4/5, 0), and a dual witness | derived, R1, R2 |

Planted faults (all go red, `test_planted_*`): a wrong value of any one input (g = 1/12,
z_p = 1/5, alpha = 4/5, c_M = 1/3, c_P = 1/4, R_fl = 99/100, n = 1/3) breaks at least one
reproduction; a wrong exponent changes the optimum; a geometry 10^-6 past the optimum and a
target 10^-10 below sigma_* both fail the exact rectangle check; a geometry with M + ell > 1 or
b < 0 is refused; a perturbed multiplier leaves a nonzero residual; the stored crossing dual
witnesses fail when used at the wrong end; the sampler catches a cubic negative only between
two roots 0.0028 apart, whose isolating intervals share an endpoint, and still catches it with
the interval proposal emptied (the Sturm guard alone), while the guard switched off lets it
through; the rectangle check fails a target violated only in the bins delta >= alpha, and
passes it with that branch switched off; the check of the rows at d < h fails a target
violated among them only by a slot row at d = 1/2 and passes one that only the endpoint
violates (so pointing it at d = h instead goes red); and it fails a target violated among
them only by the bins delta >= alpha at d = d_min (alpha = 2/3, n = 0), so reading those
at d = h goes red too. In scratch-copy runs of this repair (recorded runs, not tests of the
suite): undoing the delta <= alpha restriction of the intermediate row turned 14 tests red
(the alpha axis, regime B, the four-row bound and both inner-row tests), a wrong K_B in
regime B turned 10 red, and dropping the end x = 0 from the second width condition of Lemma
marked turned the marked-width test red.

## 3. The optimum at the paper's inputs

Total accounting (R1), the shared lemmas at the re-optimized target (R2), the paper's inputs,
every frozen choice as printed:

- `sigma_* = (1507 - 2 sqrt 921)/1653 = 0.8749570698`, `delta_* = (49 - sqrt 921)/48`;
  ell = 0.1668383875, b = 0.1234054370, h = 0.8119602997, M - 2 ell = 0.4994848376, which
  is below 1/2: the paper's own bookkeeping forbids this geometry, so every number in
  sections 3 to 7 rests on R1, and every one below 7/8 on R2 as well.
- multipliers: endpoint mu = 0.1875643953, low side 1 - mu, dual length nu = 0.0625214651.
  The dual witness with these weights on the low row, the endpoint row at delta_* and
  M + ell <= 1 has zero residual and bound exactly sigma_*.
- slacks of the other conditions at the optimum: the boundary x = 1/2 (as a d/dx sign)
  0.0091161574, floor 0.0058792912, intermediate 0.0026581589, supply 0.0132242767.
- with the plain capacity tied to the target (fixed point, measured agreement with Guo):
  0.87495701942.

## 4. Shadow prices and ranking

The envelope theorem at the regime-A optimum: for the row inputs the price is
`mu (h/2) dK`, for g it is `(1 - mu) b/2`, for z_p it is `-h` exactly and for the numerator
cost it is `mu h delta_*` (derived, exact in Q(sqrt 921), conditional on R1 and R2; a finite
difference of the closed form at plus and minus 10^-9 agrees to 10^-8).

| rank | input | d sigma / d input | exact | elasticity | change alone to beat 0.8748867 |
|---|---|---|---|---|---|
| 1 | z_p | -0.8119602997 | `-254/551 - 5869 sqrt(921) / 507471` | -0.135327 | +0.0000866553 |
| 2 | n | +0.0591792953 | `66721/1821606 + 623353 sqrt(921) / 838849563` | +0.029590 | -0.0011898023 |
| 3 | g | +0.0501294854 | `-1071/15979 + 56812 sqrt(921) / 14716659` | +0.008355 | -0.0013738421 |
| 4 | c_M | -0.0095710837 | `-12348/303601 + 286552 sqrt(921) / 279616521` | -0.004786 | +0.0073016702 |
| 5 | alpha | +0.0047006135 | `7414/303601 - 181690 sqrt(921) / 279616521` | +0.003917 | -0.0146429748 |
| 6 | c_P | -0.0019776984 | `-5103/607202 + 19737 sqrt(921) / 93205507` | -0.000439 | +0.0342796610 |
| 7 | R_fl | 0 | the floor has slack | 0 | none |

z_p and g are low-side constants of the sextic structure, not row counts: z_p = 1/6 is the
pole of `zeta_F(6z)` and g = 1/6 comes from the sixth-power form of the exceptional Gram
frequencies (`K_R^{1/6}`, line 8541). Neither is a free parameter of the method; their
prices say how much the abscissa leans on them, not that a lemma could move them (inferred).
The numerator cost n = 1/2 is the pointwise size of the reflected L-value at Re w = 1 - a; a
scalar n below 1/2 stands in for a bound averaged over the bin, which is a change of
structure, so its price is the marginal value of such a change, not of a sharper exponent
(inferred).

## 5. The abscissa as a piecewise function of each input

Every abscissa in this section is below 7/8 and conditional on R1 and R2.

**Regime A (the paper's neighbourhood), closed form.** With g = z_p = 1/6 and only the row
inputs moving, put `rho = (3 - c_M - 2 c_P)/((2 - 2 c_P)(1 - c_M))` (37/14 at the paper).
Then delta_* is the root in (0, alpha) of

    (3 - 2 rho) d^2 + (2 rho alpha - alpha - 2/3 + 2 rho/3) d - 2 rho alpha/3 = 0,
    sigma = 11/12 - (5 - 6 delta_*) / (36 (1 + 2 delta_*)),

so c_M and c_P act only through rho (derived). For general g, z_p the tangency is
`K(delta) = k_0 + k_1 delta` with `k_1 = 2 z_p/g`, `k_0 = (2 z_p - 5g + 6 g z_p)/(3g)` (a
numerator cost n other than 1/2 subtracts `2(n - 1/2)` from k_1), and (ell, b) solve two
linear equations (`assembly.regime_A`). Regime A holds from the paper's
value up to the first break:

| input | regime A holds to | what binds there | abscissa there |
|---|---|---|---|
| z_p (raised) | 0.1751510556 | the floor bin | 0.8679871838 |
| n (lowered) | 0.4908887159 | the intermediate range | 0.8744203215 |
| g (lowered) | 0.1567188215 | the floor bin | 0.8743819388 |
| c_M (raised) | 0.5361872194 | the supply hypothesis | 0.8745985237 |
| alpha (lowered) | 0.6098049914 | b reaches 0 | 0.8733861759 |
| c_P (raised) | 0.5261221985 | x leaves 1/2 | 0.8740683460 |

Past the break:

- **z_p** (raised): the optimum is the floor vertex, which involves no z_p, so the abscissa is
  affine: `sigma(z_p) = C - z_p H` with
  `H = (23762198 - 8190 sqrt(22829)) / 27128539` and `C = 83492716/81385617 - 2240 sqrt(22829) / 27128539`,
  at delta = -740/5573 + 35 sqrt(22829) / 11146, until z_p = 0.2735042735 where the endpoint
  multiplier reaches zero (derived). 0.87 is reached inside regime A at z_p = 0.1727198769;
  13/15 at `z_p = 28260493/155678520 - 329 sqrt(22829) / 10378568 = 0.1767414708`, bracketed by
  dual witnesses at 0.1767413646 and 0.1767415654.
- **n** (lowered): (measured, float LP) the endpoint and the intermediate range together, then
  the floor and the intermediate range, where all rows are affine and
  `sigma(n) = (2250 n^2 + 76293 n + 1137725) / (72 (600 n + 18397))` (84031/96156 at n = 1/2);
  b reaches 0 at n = 0.3484739370, and then `sigma(n) = (18 n + 659) / (3 (6 n + 253))`
  (derived formulas). 0.87 is reached at `n = -4301/500 + sqrt(181150489) / 1500 =
  0.3708105098`, bracketed by dual witnesses at 0.3708106102 and 0.3708104095. The last
  formula is the exact optimum at n = 0, 1/10, 1/5, 13/50, 3/10 and 1/3: at each the four-row
  dual witness gives it from below and its vertex geometry passes the rectangle check and the
  rows at d < h with no slack (derived at those six points; in between it is the same vertex,
  inferred). The floor rows weaken as n falls, so the n = 0 dual witness bounds every n >= 0 by
  659/759 = 0.8682476943: n alone cannot reach 13/15.
- **g** (lowered): the floor vertex (now g-dependent) down to 0.0857605178, then the floor and
  the Gram condition: `sigma(g) = (418 g - 1601) / (6 (106 g - 309))` down to g = 4/53, where
  the supply hypothesis binds: `sigma(g) = (12922 g - 11513) / (6 (2650 g - 2221))` (derived).
  0.87 falls in the floor-vertex regime, between g = 0.0890072152 and 0.0890074160; 13/15 at
  g = 181/4290 = 0.0421911422 in the supply regime. Dropping the uniform supply hypothesis
  removes a constraint, so 13/15 would then need a g at least as close to 1/6 (not computed).
- **c_M** (raised): the supply hypothesis of Proposition detector-counts binds: the largest
  capacity it must cover grows with c_M while ell/h cannot. A stronger capacity can always be
  used as a weaker one, so the abscissa is the running minimum of the fixed-capacity optimum;
  on a grid its minimum sits at c_M = 3023/5625 (0.537422, measured), where a checked geometry
  gives 0.8745869525 (derived upper end). With the supply hypothesis dropped entirely, regime A
  runs to 0.5468059250, the binding x then leaves 1/2 and the path flattens toward the capacity
  ceiling 0.8740524834 (path measured, ceiling derived). A per-bin hypothesis, which would only
  need the capacity at t_* (inferred), lies between the two frames and was not computed. The
  regime-A values along c_M and the envelope point lie below 37/65, where Lemma marked's
  second width condition stops holding; the flattening past 0.5468059250 was scanned only in
  float and may cross 37/65, and the ceiling's attainment at c_M = 9/10 lies well past it
  (section 7).
- **alpha** (lowered): regime B, closed form. Once b = 0 the endpoint at x = 1/2 needs
  `ell <= (1 - K)/(5 + 3K)` in every bin, so the binding bin maximises K: at
  `delta_B = alpha (37 - sqrt 518)/23`, `K_B = alpha (714 - 28 sqrt 518)/529`, and
  `sigma = 11/12 - (1 - K_B)/(4 (5 + 3 K_B))` (derived, exact in Q(sqrt 518)). Regime B starts
  at `alpha = 247/573 + 3 sqrt(518)/382 = 0.6098049914` (abscissa
  `18589/20919 - 14 sqrt(518)/20919`), crosses 0.87 at
  `alpha = 85/546 + 5 sqrt(518)/819 = 0.2946252341`, and meets the floor at
  `alpha = 51/350 + sqrt(518)/175 = 0.2757692192`, where the abscissa is 167/192 and stays for
  every smaller alpha. At alpha = 3/5, 1/2, 2/5, 3/10 and 7/25 the regime-B dual witness gives
  the closed form exactly from below and a rational geometry checked on the whole rectangle
  lies within 2 parts in 10^13 above it; the generic vertex solver agrees. The intermediate
  row, now at delta = alpha, does not bind on this axis: its slack, 0.0026581589 at the paper's
  alpha, is larger at every other point checked exactly (three in regime A, five in regime B,
  three in the floor-limited stretch). An independent LP model (the verifier's, built from
  `paper.tex` without this code) gave values within 10^-8 below these at alpha = 4/5, the
  verifier's 0.6076005515, 1/2 and 3/10, as a grid relaxation should (measured agreement).
- **c_P** (raised): the binding amplitude ratio moves inside (0, 1/2) (derived); beyond, the
  capacity ceiling 0.8740524834 bounds the path (derived), which the float LP shows it reaching
  (measured). Lemma marked's second width condition holds along this whole axis: it needs
  c_M <= (5 - 4 c_P)/(9 - 8 c_P) from the amplitude end x = 1/2 and c_M <= 5/8 from x = 0, and
  c_M = 1/2 meets both for every c_P < 1 (derived).

## 6. What each input must reach, alone

| input (paper value) | beat 0.8748867 | reach 0.87 | reach 13/15 |
|---|---|---|---|
| z_p (1/6) | 0.1667533220 | 0.1727198769 | 0.1767414708 |
| n (1/2) | 0.4988101977 | 0.3708105098 | no: every n >= 0 stays at or above 659/759 |
| g (1/6) | 0.1652928246 | 0.0890072152 to 0.0890074160 | 181/4290 |
| c_M (1/2) | 0.5073016702 | no: ceiling 0.8740524834 | no |
| alpha (5/6) | 0.8186903585 | 0.2946252341 | no: every alpha stays at or above 167/192 |
| c_P (2/9) | 0.2565018832 | no: ceiling 0.8740524834 | no |
| R_fl (1) | no (zero price) | no | no |

Every entry is exact: regime-A crossings to 10^-12 from the closed form, the alpha crossing of
0.87 in closed form, the others from a dual witness above the level at one end and a checked
geometry below it at the other. All are conditional on R1 and R2. The improvements in the
first column are candidates about this assembly with a hypothetically stronger input, not
claims that such an input exists.

## 7. Ceilings

All rows of this table are ceilings of the frozen frame (bin ceiling 5/6 with no Delta margin,
the paper's floor bin, contour and supply hypothesis), conditional on R1 and R2.

| frame | ceiling | rows of the dual witness | grade |
|---|---|---|---|
| as written, every (c_M, c_P, alpha) | 167/192 = 0.8697916667 | low side, floor, M + ell <= 1, b >= 0 | derived; attained for alpha up to 27/100 and reached at 0.2757692192 |
| as written, every (c_M, c_P), alpha = 5/6 | 0.8740524834 | low side, endpoint at x = 0, intermediate, M + ell <= 1 | derived; attainment needs a stronger marked lemma |
| as written, alpha >= 5/6, every (c_M, c_P) | 84031/96156 = 0.8739028246 | low side, floor, intermediate at 5/6, M + ell <= 1 | derived; weaker than the row above at alpha = 5/6 |
| the same four rows, bin ceiling 3/4 | 368153/422028 = 0.8723425934 | low side, floor, intermediate at 3/4, M + ell <= 1 | derived (relaxation inferred) |
| intermediate range dropped, floor 1/50 | 167/192 | the rows of the first line | derived (relaxation inferred) |
| also floor delta_0 -> 0 | 13/15 = 0.8666666667 | low side, row-norm loss, floor, M + ell <= 1 | derived (relaxation inferred) |
| as written, every numerator cost n >= 0 | 659/759 = 0.8682476943 | low side, floor at n = 0, M + ell <= 1, b >= 0 | derived |

The first is attained exactly: the geometry (3/16, 13/16, 0) passes every row at the abscissa
167/192 with no slack at alpha = 1/4, 1/5 and 27/100, and fails at alpha = 7/25, just past the
floor point. The second is attained in the float LP at c_M = 9/10 with the supply hypothesis
dropped, and a geometry checked on the whole rectangle confirms it there; but at c_M = 9/10
the second width condition of Lemma marked fails (`2r + 8z - 3 = 215/149`, which must be
negative), so that attainment is a statement about a marked lemma without that condition,
not about Lemma marked.

## 8. Limitations

- The inputs are the lemmas' conclusions at their printed exponents; nothing here checks
  Lemma marked, Lemma plain, the amplification lemma, the Gram bound or the detector.
- Every abscissa below 7/8 rests on R1 and R2, both inferred. Under the paper's own
  bookkeeping the abscissa is exactly 7/8 and every row-input price is zero.
- The general-parameter forms of the supply hypothesis, the intermediate count and the floor
  are readings of displays written at fixed numbers; they reproduce the printed values.
- The model carries only the first width condition of Lemma marked; the second binds above
  c_M = 37/65 (at c_P = 2/9) and is checked only as a separate test.
- The bin ceiling is frozen at 5/6 with no margin. A dynamic treatment, in which a bin with
  delta above 2 sigma_0 - 1 exists only when Delta is large enough and so carries a margin of
  order (1 - h/4) Delta, would relax every large-delta row; it is not modelled here.
- The c_M envelope minimum, the c_P path past its break and the n-axis stretch between regime
  A and the floor-and-intermediate regime are float scans, labelled measured.
- Guo, Liu, and Xu and Sang are reference lines from the campaign's external map; their
  papers were not read in this lane. This hunt's `FOLLOWUPS.md` records a smaller public
  value, 0.8748087 (not checked here); the "beat 0.8748867" column uses MISSION's reference
  line and was not recomputed against it.
- For delta > alpha the count 1 - delta is an inferred reading of the remark at lines 15448 to
  15467; it matters only on the alpha axis below 5/6.

## The doors

Candidate status: the paper's inputs give the exact optimum 0.8749570698 over all geometries
with the frozen choices as printed, conditional on R1 and R2 (both inferred); proof status:
exact arithmetic on transcribed formulas, unreviewed.

### Active constraints at the optimum

1. The endpoint inequality at (delta_*, x = 1/2), weight mu = 0.1875643953. Its inputs'
   prices are the table of section 4: z_p, n and g dominate, then c_M, alpha, c_P.
2. The dual length `M + ell <= 1` (line 8246), price nu = 0.0625214651 per unit of relaxation.
3. Slack, in the order they bind as inputs improve: the floor bin (0.0058792912; first along
   z_p and g, second along alpha), the intermediate range (0.0026581589; first along n), the
   supply hypothesis (0.0132242767; first along c_M), the boundary x = 1/2 (0.0091161574;
   first along c_P). Along alpha the first to bind is b >= 0, which is not a slack of the
   optimum but the sign of b.

### The frozen-constant inventory

| frozen choice | value | binds | what relaxing it trades | trade shape |
|---|---|---|---|---|
| floor bin delta_0 | 1/50 (line 15843) | first along z_p and g, second along alpha; sets 167/192 against 13/15 | rows between the new floor and 51/100 need witnesses (line 4511), and the loss uniformity rests on delta >= 1/50 (line 16076) | genuine |
| intermediate range | t = 1, no slots, d <= 1/2, delta <= alpha (line 16146) | first along n | slots there need a finer mesh, an optimized t needs none (inferred); its slack 0.0026581589 is unused at the optimum | genuine |
| bin ceiling | delta <= 5/6 (line 6825) | through the intermediate range and the large-delta rows, evaluated at 5/6 with no margin | the dynamic value 2 sigma_0 - 1, about 3/4, moves the four-row bound from 84031/96156 to 368153/422028 (relaxation inferred) | genuine |
| supply hypothesis | uniform over t in [1, 3/2] (line 15195) | first along c_M; along g below 4/53 | a per-bin hypothesis only needs the capacity at t_* (inferred) | genuine |
| row-norm bookkeeping | every summand lossless (line 8325) | pins 7/8 exactly | total accounting (R1) moves the optimum to 0.8749570698 | genuine |
| plain capacity kappa | 3/4 (line 15327) | through c_P | tying it to the target gives 0.87495701942, outside the lemma's range (line 12532) | small |
| contour z_0 | 17/50 (line 15742) | never at d = h, where it cancels | none | none |

### The information class

- **Inside the current data:** the geometry and the frozen choices above. The geometry is
  exhausted at 0.8749570698. The intermediate range, the bin ceiling and the supply
  hypothesis are bookkeeping of the final section whose relaxation is a reading, not a new
  lemma; they are the cheapest doors, and the next binding constraints on the row-count path.
- **Inside the current family, better inputs:** c_M, c_P and alpha. Their combined reach as
  written is 167/192, attained through alpha alone; with the floor at delta_0 -> 0 as well,
  13/15. The capacities alone stop at 0.8740524834, because rows with no prime amplitude get
  no help from them. A smaller alpha is a stronger amplification lemma, which this lane does
  not propose.
- **Reading more:** z_p and g are among the largest prices but belong to the sextic
  structure of the probe (the pole of `zeta_F(6z)`, the sixth-power exceptional
  frequencies), which also fixes alpha; moving them is a different probe, not a stronger
  lemma (inferred). The numerator cost n carries the largest price that is not sextic
  structure; lowering it means bounding the reflected L-values on average over a bin instead
  of pointwise, new analytic input of the kind this hunt's `FOLLOWUPS.md` records in the
  public follow-ups. No candidate for such an input is proposed here.
