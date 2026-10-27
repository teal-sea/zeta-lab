# Row counts of the Part II assembly: where they lose, and what each loss is worth

**Hunt #136, lane `rowcounts`, 2026-10-21, repaired after an independent verifier's review
(section 10). A lane report inside an open hunt; no person has reviewed it.** Grades, as in
`MISSION.md`: *cited* (a line of the pinned `paper.tex`, quoted in `rowcounts.CITATIONS` and
checked against the file), *derived* (algebra done here and checked in exact arithmetic by
`test_rowcounts.py`), *inferred* (a reading no computation checks), *measured* (float grids).
A composite claim takes its weakest grade. Nothing here is a statement about RH or about real
part 1/2, and no smaller half-plane is claimed: every abscissa below is a property of one
assembly of the paper's lemmas, taken as inputs at the exponents the paper proves them with.

Source: `github.com/openai/math` at `adc7f124`, `paper.tex`, 16,677 lines, sha256
`42a5ee0f...c6a3` (checked). 98 of 98 quoted snippets sit on their stated lines.

## The answer

1. **None of the recounts tried here recovers anything at the paper's inputs.** Nine places
   where a count could be sharpened are examined in section 3: five recounts die under exact
   enumeration or one line of algebra, three hold but buy exactly nothing there, and one place
   (the floor rows) was not recounted. In particular, using the zero detector at every length
   t at once, instead of one t per bin, gives exactly the paper's count (derived, by an exact
   attaining row type). One of the three that hold, counting the rows d ≤ 1/2 at the
   balancing t instead of at t = 1 (item 14), is slack at the paper's inputs, but the paper's
   count of those rows binds at every perfect-input optimum and already for α on the way to
   0.8748087.
   This is not a claim that no count in the assembly can be improved: `FOLLOWUPS.md` section
   4 reports tracker entries that change counts built on these lemmas (PR 48 and 50, separate
   inverse and plain slot selections; PR 56, a per-fiber detector count; PR 66, saturated
   marked capacities), and whether those need new lemmas was not established here. One
   further loss is real but not a recount: each bin's cardinality multiplies the pointwise
   maximum of the reflected numerator (line 15810). Averaging that numerator over the bin is,
   per `FOLLOWUPS.md`, the change behind Xu and Sang's 0.8748867; it needs a moment of L-values
   the paper does not have, and this lane does not price it.
2. **What the row counts actually consume are four moment-lemma constants.** The
   amplification slope alpha = 5/6 (line 15300); the marked capacity coefficient c_M = 1/2
   in z_M(r) = c_M (1 - r), from the first condition r + 2z < 1 of Lemma marked (lines 9254,
   15182); the plain capacity coefficient c_P = 2/9 in z_P(m) = c_P (1 - 2m) (line 15327); and
   Lemma marked's second condition 2r + 8z < 3, that is z ≤ c_M2 (3/2 - r) with c_M2 = 1/4
   (line 9254), which the paper keeps slack (lines 15182 to 15183, 15376 to 15380). With the
   first three free and the second condition slack, the row count is
   `R_* = 1 - δ + (α - δ)δP_x/(2J)` with `D_x = 3 - 2x c_M - 4x c_P`,
   `P_x = (1 - 2x c_M)(2 - 4x c_P)`, `J = (α - δ)D_x + δP_x` (derived; the paper's 3 - 17x/9 and
   (2 - 8x/9)(1 - x) at the paper's values). The second condition stays slack at every
   inverse row exactly while c_M ≤ 37/65 ≈ 0.5692 at the paper's c_P (derived,
   `marked_second_threshold`); above that the closed form overstates what c_M buys, and the
   measured evaluator imposes the condition.
3. **The exact smallest target of this assembly** (geometry free, the paper's row counts,
   hunt #134's total-accounting reading of the low side) is
   `σ* = (1507 - 2√921)/1653 ≈ 0.87495706979917`, the root of 4959σ² - 9042σ + 4115 = 0,
   reached at ℓ* = 11/551 + 8√921/1653 ≈ 0.16683839 and b* ≈ 0.12340544, binding at the rows
   δ* ≈ 0.38858371, x = 1/2. An exact rational lower bound and an exact rational upper bound
   (feasibility over the whole (δ, x) box checked by Bernstein subdivision in rationals)
   bracket it within 3 × 10^-9 (derived, conditional on the low-side reading, which #134
   inferred and which `FOLLOWUPS.md` reports Liu, Guo, and Xu and Sang claim with proof in
   unrefereed preprints; those proofs are not checked here). This number is not new:
   `FOLLOWUPS.md` records it as Liu's B_alg (arXiv:2610.12234v1) with the same ℓ* and b*, and
   this hunt's assembly lane (`assembly.py`) gets the same closed forms by its own code.
4. **Tying the plain capacity to the target**, c_P = 1/(6(2σ - 1)), turns the optimum into the
   root of 7884σ³ - 18819σ² + 14643σ - 3686 = 0, σ† = 0.8749570194200989..., which agrees with
   Guo's published 0.8749570194 in all ten digits given (derived here; Guo's number is cited
   from the campaign map in `MISSION.md`), and which `FOLLOWUPS.md` identifies with Liu's
   B_new. It uses Lemma plain at κ = 2σ† - 1, about 0.74991, below the stated range κ ≥ 3/4
   (line 12532); the follow-ups extend that range (per `FOLLOWUPS.md`). The tie is worth
   5.04 × 10^-8 and is already public.
5. **Ranking by abscissa bought** (section 5). The two goals are Xu and Sang's 0.8748867
   (`MISSION.md`) and 0.8748087, the best Dirichlet abscissa on record as `FOLLOWUPS.md`
   reports it (tracker PR 68); both are cited, not checked. Perfect values are at the paper's
   floor a = 51/100 and with b ≥ 0. The second column keeps the paper's count of the rows
   d ≤ 1/2; the third recounts those rows at the balancing t (item 14).

   | input | perfect value buys | the same, rows d ≤ 1/2 recounted | to pass 0.8748867 | to pass 0.8748087 | leverage near the paper |
   |---|---|---|---|---|---|
   | amplification slope α | 84031/96156 ≈ 0.8739028 (exact) | 167/192 (exact; 13/15 with the floor pushed to 1/2) | 0.8186904, 1.76 % smaller | 0.8028731, 3.66 % smaller (0.8031897, 3.62 %, recounted) | dσ*/dα = 0.0047006 |
   | marked capacity c_M | about 0.8740525 (measured) | about 0.8734852 (measured; the second marked condition binds) | 0.5073017, 1.46 % larger | 0.5152786, 3.06 % larger | dσ*/dc_M = -0.0095711 |
   | plain capacity c_P | about 0.8740525 (measured) | about 0.8734556 (measured, supply-capped) | 0.2565019, 15.4 % larger | 0.2916823, 31.3 % larger | dσ*/dc_P = -0.0019777 |

   The paper counts the rows d ≤ 1/2 at t = 1 with no selected primes, R = 76/75 - 2δ/3
   (lines 16146 to 16160). Those rows then require ℓ ≤ 188/1593 + 223b/531 (derived), which is
   slack at σ* and at every break-even value except α to 0.8748087, and violated at every
   perfect-input optimum of the third column. Under that count the x = 0 rows, which no
   capacity reaches, stop every capacity improvement at 0.8740525 (derived on the x = 0 slice;
   the measured evaluator agrees for c_M = 1, for c_P = 1 and for both), and α = 0 stops at
   84031/96156, where that line meets the floor (derived). Counting those rows at the
   balancing t instead, still with no selected primes, gives them R_*(δ, 0) =
   1 - δ + (α - δ)δ/(3α - δ) in place of 1 - 2δ/3. That uses only the no-slot counts the paper
   proves for every t (inferred from lines 15438 to 15466 and case z = 0 of Lemma plain, line
   12557), and it leaves those rows slack at every value of the third column (exact sign
   checks).

   Both break-even values of c_M lie below 37/65, where the closed form is exact. Relaxing
   Lemma marked's second condition together with c_M buys about 0.8731593 (measured, rows
   d ≤ 1/2 recounted; the supply then binds). With those rows recounted, both capacities
   perfect stop at the **x = 0 wall** `101/108 - √286/270 ≈ 0.87254987212856` (root of
   10800σ² - 20200σ + 9403 = 0): rows whose prime slots carry no amplitude gain nothing from
   prime slots, so no capacity improvement alone can take this assembly below it (derived).
   Only α, a better count for those rows, or a negative b can. The last needs a Gram estimate
   for P_a < 1, which Prop. probe-gram does not give (it assumes P_a = Y'²/Q ≥ 1, line 8345);
   on the x = 0 slice, b = -1/50 would give 0.8723955 and b = -1/20 would give 0.8722121
   (derived on that slice only).
6. **No new candidate survives from this lane.** Every abscissa below 7/8 it computes is
   either already public (σ* and σ†) or conditional on input values that this lane has not
   seen proved: a smaller α, a larger c_M or c_P, a relaxed second marked condition, or a
   negative b. That describes this lane's reading, not the literature: `FOLLOWUPS.md` sections
   4 and 5 report preprints and tracker entries that move some of these inputs (I3, the
   plain moment: κ ranges [37/50, 1] from Guo and [13/18, 1] from Liu and from Xu and Sang,
   tracker PR 26's prime cost 22/5 in place of 9/2, affine capacities in PR 37 to 68; I5 and
   I6, the no-slot and selected-slot counts), Lean per tracker and not refereed, and no proof
   of them was checked here. For scale only: c_P = 5/22, PR 26's prime cost read as a plain
   capacity used everywhere (inferred reading; per `FOLLOWUPS.md` PR 26 uses it only above
   h - 1/1000), gives 0.8749470 in this lane's model (derived), 1.0 × 10^-5 below σ*; the
   tracker's numbers come with the averaged numerator of item 13 and other changes this
   model does not contain. The loss closest to giving way, by leverage, is the marked
   capacity: a 1.46 % larger c_M would pass 0.8748867 and a 3.06 % larger one would pass
   0.8748087. Its factor two is the mark's full length charged in the row branch of the
   reflected energy (line 9904), which enters the first canonical invariant
   F - M - Q - z_0 ≥ c (line 9808) and becomes r + 2z < 1 at initialization (lines 12208,
   9254); that reading is inferred. Above c_M = 37/65 the second condition 2r + 8z < 3, which
   the second invariant 4F - 3M - 6z_0 ≥ c (line 9809) becomes at initialization (line
   12209), binds as well (derived), so a sharper first invariant alone buys at most down to
   about 0.8734852 (measured, rows d ≤ 1/2 recounted) and the 6z_0 charge of the second
   invariant would also have to give way. Nothing here shows that either charge can be
   reduced; `FOLLOWUPS.md` reports that the follow-ups changed how the marked moment is used,
   not the lemma (its I1).

## 1. What was read

Directly: the row-count proposition and its proof (lines 15095 to 15493), the endpoint
inequality and frequency ranges (15920 to 16189), the order of choices (16189 to 16300), the
zero detector (4201 to 4686), the sextic large sieve and the Part I row envelope (4687 to
5460), the additive Gram bound and the completion of the low bound (8334 to 8651), the full
finite correlations (7042 to 7180), the statements of Lemma marked (9218 to 9269), the
canonical estimate (9282 to 9340), the terminal step of the canonical proof (9783 to 9960),
the initialization of the marked moment (11601 to 12290), the amplification (12343 to
12469), the statement of Lemma plain (12477 to 12601), its prime estimates and induction order
(12831 to 13012), its slot-stripping step (14195 to 14300), the reflected energy lemma and
proof (7657 to 8061), and the probe definitions (3325 to 3486, 3734 to 3850, 6810 to 6918).
The other parts of the two moment-lemma proofs (about 4,000 lines) were not read; the
capacities are taken from the statements and from the steps where they are produced. Also
read, for the public frontier and prior art only: this hunt's `FOLLOWUPS.md`, `PROBE.md` and
`assembly.py`, written by parallel lanes on the same day.

## 2. The row-count algebra with free inputs

Cited: the marked count `1 - δr - 2qz` (line 15235), the plain count `1 - 2δm - 2qz` with two
copies of the plain witness (15238), the capacities `z_M(r) = (1 - r)/2` (15182) and
`z_P(m) = (1 - 2m)/(6κ)`, baseline `2(1 - 2m)/9` at κ = 3/4 (15175, 15327), the two strict
conditions of Lemma marked `r + 2z ≤ m - c_1, 2r + 8z ≤ 3m - c_2` (9254), used at row width
one (15380), the amplified inverse count `1 - α + (α - δ)r` for r ≥ 1 (15289), the detector
constraints r ≤ t, r + m ≥ t, m ≤ 1/2 for every t in [1, 3/2] (4513 to 4535).

Derived (exact, `test_general_inputs_crossing_is_independent_of_r_and_balances`): with
q = xδ, the two counts at r and m = t - r cross at
`r_*(t) = ((2 - 4x c_P)t + 2x(c_P - c_M))/D_x`, the common value is
`R_short(t) = 1 - δ + (δP_x/D_x)(3/2 - t)` whatever the inputs, `r_*(3/2) = 1` always, and the
long branch `L(t) = 1 - δ + (α - δ)(t - 1)` balances it at `t = 1 + δP_x/(2J)`, giving the R_*
above. The inverse count is used only for r ≥ r_*(t) ≥ r_*(1) (line 15370), and the second
marked condition is slack at all such r exactly when
`c_M2(5/2 - x c_M - 4x c_P) - c_M(1 - 2x c_P) ≥ 0` at x = 0 and x = 1/2 (this is D_x times the
slack at r_*(1), affine in x). At the paper's inputs it is 1/8 and 1/16 (the 1/16 is the
paper's margin 9/37 of 2r - 1 at r = 23/37, line 15378, in other units), and it vanishes at
c_M = 37/65 (derived, `marked_second_margin`, `marked_second_threshold`).

39 selected constants of this section are rebuilt from the general formulas at
(α, c_M, c_P) = (5/6, 1/2, 2/9) (`test_every_row_count_constant_is_reproduced`), among them
D_x, P_x, r_*(1) ≥ 23/37, 1/3 ≤ t - r_* ≤ 1/2, 7/37, 2/27, 8/39 - 7/37 = 23/1443, the capacity
comparison ≤ Δ/4, 37/18 ≤ D_x ≤ 3, 7/9 ≤ P_x ≤ 2, 35/54 ≤ J ≤ 5/2, the balance identity, the
endpoint δ = α, 4/25 and 17/12. Ten more, from the endpoint and frequency-range text, are
rebuilt in `endpoint_reproductions`: the actual plain slope -2δ + 4q/(9/2 + 12Δ) < 0 (line
15341), -1/48 - δ/16 at δ = α (15945), -E_* ≥ 49/440640 > 1/10000 on the whole box by Bernstein
subdivision (16000), 51/64 (16101), 1/48 (16123), 2/185 (16126), 76/75 (16151 to 16153),
101/150 - δ/6 (16154), -529/2400 + 25δ/96 and -49/14400 (16159 to 16160). That is still not
every constant printed in the ranges read: among others, the polynomials inside the
proof of the endpoint lemma from line 16012 on are not rebuilt here. One printed constant is loose:
line 16141 states R_* + Δ/4 ≤ 139/96, while 17/12 + Δ/4 with Δ ≤ 1/24 gives 137/96. The looser
139/96 is still a valid bound and the inequality it feeds, 139/96 + 1/2 - 17/50 < 2, holds, so
nothing depends on it.

## 3. The loss inventory

Each place where a count could give something away, with the sharper count tried, the test,
and the verdict.

| # | where (lines) | the paper's count | sharper count tried | test | verdict | buys |
|---|---|---|---|---|---|---|
| 1 | slot selection, 15116 to 15134 | `\|∏Q_i\|² ≥ U^{2qz - δ max w_i}` | `U^{2q(z - max w_i)}`, and the mean q is the exact worst case | exhaustive, 137925 configurations | holds | 0 |
| 2 | one detector length t per bin, 15196 to 15210, 15962 to 15986 | min over t of max(R_short(t), L(t)) | use the witnesses at every t at once | exact attaining type on a 19 × 11 grid | dead | 0 |
| 3 | capacity cuts, 14259, 12873, 15021 | slots only up to z_M, z_P | more slots, paid by the pointwise prime bound | exact grid, 1100 cases | dead | 0 |
| 4 | two copies of S_m, 15242 | `\|S_m\|^4` in Lemma plain | one copy with capacity (1 - m)/(6κ) | exact grid, 2200 cases | dead | 0 |
| 5 | floor rows, 15843 to 15848 | counted in full, R = 1 | none tried | none | slack at the paper's inputs | 0 |
| 6 | conductor in the per-row bound, 4354 to 4367 | conductor ≤ q_u for every row | strata by the powerful part | exact grid, 1260 cases | dead | 0 |
| 7 | Gram exceptional frequencies, 8527 to 8557 | trivial two-column count for k = a^6 e | the ray twist χ_s(b_*)/ξ(s) has mean zero on T-classes | exhaustive in Z[ω] and F_p | dead | 0 |
| 8 | Gram correlation, 7114 to 7130, 8546 | `\|L_C\| ≤ q_C` | `\|L_C\| ≤ φ(C)` | brute force, 392 local sums | holds | 0 |
| 9 | κ in the plain capacity, 12532, 15327 | κ_0 = 3/4 | κ_0 = 2σ - 1 | exact (cubic) | matched by Guo | 5.04 × 10^-8 |
| 10 | sixth-power lift, 12410 to 12455 | sparse lifts bounded by the whole ball | a smaller α | lift count, exhaustive | real, priced | section 5 |
| 11 | marked capacity, 9254, 9808 to 9809, 12208 to 12209, 9904 | r + 2z < 1 and 2r + 8z < 3 | larger c_M | priced; the second condition binds above c_M = 37/65 | real, priced | section 5 |
| 12 | plain capacity, 12561, 14259 | 2m + 6κz ≤ 1 | larger c_P | priced only | real, priced | section 5 |
| 13 | count times pointwise numerator, 15799 to 15810 | U^R times U^{δ/2} for every row | an average of the numerator over the bin | not tested here | real, outside the lemmas | not priced |
| 14 | rows d ≤ 1/2, 16146 to 16160 | t = 1, no primes: R = 76/75 - 2δ/3 | the balancing t, no primes: R_*(δ, 0) | exact sign checks | holds (inferred available) | 0 at σ*; needed by every perfect value |

**1. Slot selection.** The paper fills a requested length z with whole slots in decreasing
order of amplitude and drops the one fractional slot (lines 15118 to 15127). Derived: the
whole prefix has length at least z - max w_i and average amplitude at least the mean q, so
the gain is at least `2q(z - max w_i)`, which implies the paper's `2qz - δ max w_i` since
2q ≤ δ. With all amplitudes equal to q the gain never exceeds 2qz, so no count of the form
2q'z with q' > q holds: the mean is the exact worst case, and the high exponent pays the
amplitude through the same mean q (line 15803). Exhaustive check over 137925 configurations
(three slot lengths, five amplitude levels, up to three slots, every request on a 1/24
grid, three values of δ): both inequalities hold everywhere; the 5364 uniform
configurations never exceed 2qz. Planted fault: filling in increasing order breaks the
paper's inequality in 54 configurations and the sharper one in 6117. The residual loss
δ max w_i tends to zero with the slot mesh, which the paper already takes fine (line 16246),
so this buys nothing.

**2. One detector length per bin.** The detector gives, for every t in [1, 3/2], a pair of
saturated witnesses (lines 4513 to 4535), and the paper picks one t per bin. One could try
to count each row with its witnesses at all t simultaneously. Derived
(`adversary_exact`): for any row type covering every t, the type's count at t = t_* is at
most R_* (if the witness r at t_* is at least 1, the amplified count is at most L(t_*); if
not, the better of the marked and plain counts is at most R_short(t_*)), and the type
A = {r_*(t_*), t_*} with plain length t_* - r_*(t_*) covers every t and attains R_* exactly. So
max-min equals min-max and the refinement gains nothing. The evidence is that attaining
type, checked exactly on a 19 by 11 rational grid of (δ, x). The exhaustive search over all
57337 row types on a 1/12 grid at δ = 7/18, x = 1/2 is only a consistency check: its result
643/972 cannot exceed the paper's grid bound 2687/3996 by the same weak-duality argument, so
it cannot fail, and it sits below R_* = 2363/3546 because the grid misses the attaining type.
Planted fault: dropping the covering constraint lets the search reach 5/6, above every
bound, which shows only that the search code reads that constraint. The derivation uses
only the detector's stated constraints; a correlation between the witnesses at different t,
if the detector's construction implies one, is not used here (inferred: none is visible in
lines 4549 to 4685).

**3. Slots beyond capacity.** A slot of length dz beyond the plain capacity, bounded
pointwise, costs κ dz in the moment exponent (Eq. 3.5 at line 12873; the paper's own exchange
rate at line 14259, where removing a slot of length d frees 6κd and costs κd) and gains
2q dz in the spike. Beyond the marked capacity the pointwise prime bound (line 15021) costs
δ dz. Since q ≤ δ/2 and δ ≤ κ, both nets κ - 2q and δ - 2q are nonnegative (exact grid of
1100 cases, minimum exactly 0). Dead.

**4. Copies of the plain witness.** One copy of S_m with capacity (1 - m)/(6κ) counts worse
than two copies by exactly m δ (1 - x/(3κ)) (derived; exact grid of 2200 cases, minimum
7/4320 > 0). Higher moments of S_m would need a lemma the paper does not have; at the
crossing m lies in [1/3, 1/2] (line 15367), where the fourth moment is already the natural
one (inferred). Dead.

**5. The floor rows.** The floor bin is counted in full, R = 1 (line 15844), and no sharper
count was tried here. Under GRH every row is a floor row, so a count of these rows that
needs no zero witness cannot do better than R = 1 (inferred, structural). At the paper's
inputs the floor is slack: at the exact optimum its value C_0 + (1 + ℓ - M/2)δ_0 is about
-0.0059 with the paper's δ_0 = 1/50, and C_0 itself about -0.0209 (both pinned). It is also
slack at every capacity optimum of section 5. It binds when α = 0: with the paper's count of
the rows d ≤ 1/2 it meets their line at 84031/96156, with those rows recounted at ℓ = 3/16,
b = 0, which gives 167/192 ≈ 0.8697917, and with the floor pushed to a = 1/2 (C_0 ≤ 0) at the
corner 13/15 (all exact; `FOLLOWUPS.md` X8 has the same 167/192). The first version of this
report said the floor binds only at the 13/15 corner; that held only with the floor pushed to
1/2.

**6. Conductor.** Rows whose powerful part has norm U^o number at most U^{1 - o/2} and have
conductor at most U^{1 - o/2}, so their per-row factor is U^{(1 - o/2)δ/2} (line 4361). The
stratum exponent min(1 - o/2, R) + (1 - o/2)δ/2 is largest at o = 0, where it is the paper's
(exact grid of 1260 cases). Dead.

**7. Gram exceptional frequencies.** This is the one candidate that looked worth a
direct-bound improvement. The low exponent l_x/2 + b/12 comes from the term (Q/Y')P_a^{1/6}
of the Gram bound (line 8353), which is the trivial two-column count over the exceptional
frequencies k = a^6 e (lines 8527 to 8557). The coefficient there carries the fixed ray twist
λ(s) = χ_s(b_*)/ξ(s) (line 8366), and when S contains a prime p not over 2 or 3 and ξ_p is not
the sextic residue character itself (the paper suggests the quadratic one, line 3353), λ has
mean zero on every class of T. The k = a^6 terms would then cancel, the low exponent would
lose its b/12, and the target would drop by b/12 at fixed geometry. Dead: frequencies whose
S-part is π^{j-1} times sixth powers (ξ_p = ψ^j) carry the character ψ^{j-1} in χ_m(k), which
cancels λ's p-part and restores a nonzero mean with the same count, of order K^{1/6}. Checked:
(a) the reciprocity factor (π_0/m)_6 / (m/π_0)_6 depends only on m mod 4 for all 74 primary
primes of norm at most 400 against base primes of norms 7, 13 and 19 (12 classes, no
conflict), so χ_m(π_0) is the residue character of m mod π_0 up to a 2-power factor; (b) for
every prime p in {7, 13, 19, 31, 37, 43} and every nonprincipal ξ_p = ψ^j, exactly one
exponent e = j - 1 (mod 6) gives a nonzero complete mean (30 cases); planted fault:
expecting e = j fails. Check (b) is only the orthogonality of the characters of F_p^×: it
confirms the bookkeeping e = j - 1 and adds no evidence for the identifications λ_p = ψ^{1-j}
and κ_e = ψ^e, which are the inferred part; (a) is the only enumeration that bears on them,
through the reciprocity step. The b/12 is therefore a genuine main term of this mean square
(inferred from (a) and the structure of lines 8366 to 8557).

**8. Gram correlation factor.** The bound |L_C| ≤ q_C (line 7130) is lossy, but only by the
factor φ(C)/q_C. Brute force of L_{p^c} over 392 local sums ((p, c) = (7, 1), (13, 1), (19, 1),
(7, 2), (13, 2), (7, 6), each with n1 in {1, 2, 3, p, 2p}, n2 in {1, 5, p} and k in
{0, 1, 2, p, 2p}, pairs with p dividing both left out, plus two sums at (13, 6)) matches the
paper's local formula (lines 7114 to 7123) in every case, including p dividing one of n1, n2.
So |L_{p^c}| ≤ φ(p^c) = P^{c-1}(P - 1), which is attained when p divides k (p not dividing
n1 n2) and when p divides one of n1, n2 with 6 | c and p not dividing k (123 of the 392 sums
attain it); the smaller values P^{c-1}(P - 2) (6 | c) and P^{c-1} (6 not dividing c) occur
only when p divides none of k, n1, n2. **Withdrawn:** the first version of this report
stated |L_{p^c}| ≤ P^{c-1}(P - 2) whenever 6 | c and p does not divide k, without the
condition that p divide neither n1 nor n2. That is false: at (p, c, n1, n2, k) =
(7, 6, 7, 1, 1), the sum is 100842 = 7^5 · 6 against the claimed 84035 = 7^5 · 5, and at
(13, 6, 13, 1, 1) it is 4455516 against 4084223. The enumeration now finds 15 such sums, all
in that case; the first enumeration had skipped p | n1 at c = 6, and the verifier found the
counterexample.
Planted fault: dropping the sign of the case p not dividing k, 6 not dividing c gives 60
mismatches. The verdict is unchanged: this buys nothing, because the C = 1 term carries the
whole P_a^{1/6} (derived from the dyadic sums at lines 8551 to 8553).

**9. κ tied to the target.** See answer 4: 5.04 × 10^-8, Guo's value, and it needs Lemma
plain below its stated range.

**10. The sixth-power lift.** The amplified moment (line 12375) lifts each row u to the
rows u a^6 with q_a ≤ P = (H/U)^{1/6} and bounds the lifted rows by the whole ball q_v ≤ H
(line 12449). The lift count is sharp and the map is injective; the loss is the full count:
the lifted rows are a fraction of order P^{-5} of the ball. Exhaustive at small norms in
Z[ω] (rows of norm in (75, 150], lifts of norm at most 13): 21 rows, 5 lifts each, 105
distinct images, no collision, against 218871651 primary elements in the ball of norm at
most H = 724021350, a ratio 218871651/105, about 5.6 times P^5 = 371293. The slope
α = 5/6 = 1 - 1/6 is this sixth-power density. A large sieve over the sparse lifted family
would be a new lemma.

**11 and 12. The capacities.** Lemma marked needs both r + 2z < 1 and 2r + 8z < 3 at width one
(line 9254). In the first, the 2z is z from the length of the combined polynomial and z from
the mark, whose length the reflected energy charges in its row branch E_ref ≤ M + z_a (line
9904) through the first canonical invariant F - M - Q - z_0 ≥ c (line 9808; the
initialization identity at line 12208 turns it into m - r - 2z) (inferred reading). The
second comes from the second invariant 4F - 3M - 6z_0 ≥ c (line 9809), which initialization
turns into 3m - 2r - 8z (line 12209). At c_M = 1/2 the first binds and the second is slack;
the paper says it uses z_M only where the second also has a margin (lines 15182 to 15183).
The second starts to bind once c_M exceeds 37/65 (derived). Lemma plain needs
2m + 6κz ≤ 1 (line 12561); the 6κ is the exchange rate of its induction, which bounds slots
pointwise at κ per unit to buy 6κ of width (line 14259). These come from proofs this lane does
not redo; they are priced below and not improved.

**13. Count times the pointwise numerator.** The high side bounds each bin by its
cardinality U^R times the pointwise bound U^{δ/2+O(e)} for the reflected numerator, the
absolute value of L^S(w, χ_•(u)) on Re w = 1 - a - 6e (lines 15799 to 15810, the bound from
line 4317). That is a worst-case row inside the bin: rows of one bin share the bound but need
not attain it.
Replacing it by an average needs a first moment of reflected L-values over the bin, which
the paper does not prove. `FOLLOWUPS.md` reports (cited there) that Levy, Xu and Sang, and
Liu replaced the pointwise numerator by an averaged one, and lists that replacement as the
structural change in Xu and Sang's 0.8748867, whose row counts are otherwise the paper's.
It is a real loss and, by that record, the one the public frontier moved through, but it is
not a row count, so this lane records it and does not price it.

**14. The rows d ≤ 1/2.** For d_min ≤ d ≤ 1/2 the paper chooses t = 1 and selects no primes
(line 16146), so those rows count 1 - 2δ/3, enlarged to R = 76/75 - 2δ/3 to cover the floor
(line 16151), and the frequency range needs E(1/2) < 0 (lines 16155 to 16160). On M + ℓ = 1
that is ℓ ≤ 188/1593 + 223b/531 (derived, `d_half_line`; the end δ = 1/50 is slack). The
same no-slot counts hold at every t in [1, 3/2]: the inverse side for each fixed t (line
15453) and the zero-slot plain case without length restriction (line 12557), so the short
count is 1 - 2δt/3 and balancing it against L(t) gives R_*(δ, 0) (inferred: the paper states
the no-slot count only at t = 1). At σ* both counts are slack, the paper's at about -0.0027.
At every optimum in the third column of answer 5 the paper's count fails (E(1/2) > 0) and the
recount holds (exact sign checks, `e_half_max_balanced`). The first version of this report
and its evaluator left these rows out entirely, so every perfect-input value it gave silently
assumed the recount.

## 4. The exact evaluator

`rowcounts.slice_optimum` takes (α, c_M, c_P) and returns the exact optimum; it is exact
while Lemma marked's second condition is slack (`marked_second_slack`, c_M ≤ 37/65 at the
paper's c_P). It rests on three facts. (i) At fixed (δ, x), -E_* is affine in the geometry
(ℓ, M, b), and along a constant target the slope 1 + δ(1/2 - x) > 0 does not involve the
counts (hunt #134), so M + ℓ = 1 at the optimum for any inputs. (ii) On M + ℓ = 1 and a fixed
x, J(-E_*) is a quadratic in δ whose coefficients are affine in (ℓ, b); the binding condition
is a double root at an interior δ, so its discriminant vanishes, and stationarity in b (or
b = 0) closes the system. For fixed inputs ℓ* is a quadratic irrationality; with the tied
capacity it is a root of a b-resultant. (iii) The slice optimum is a lower bound for the full
problem, made rigorous by a rational LP on three δ points around the double root
(`lp_lower_bound`); an upper bound is a rational geometry just inside the optimum whose
-E_* > 0 on the whole box (0, 5/6] × [0, 1/2] is checked by Bernstein coefficients with
bisection in exact rationals (`bernstein_positive`, 51 boxes at the paper's inputs).

At the paper's inputs the bracket is [σ* - 5 × 10^-23, σ* + 2.5 × 10^-9] (both ends exact
rationals; the test pins a width below 3 × 10^-9). All other inequalities of the assembly
hold there (`side_conditions`): the floor (about -0.0059 with δ_0 = 1/50), the rows d ≤ 1/2
of lines 16146 to 16160 (the largest E(1/2) is about -0.0027 with the paper's
R = 76/75 - 2δ/3; the first version used R = 1 - 2δ/3 and so overstated this slack about 3.5
times, at about -0.0093), the dual length, the Gram condition b ≤ 3(M - 2ℓ)/8, b ≥ 0, the
supply ℓ/h ≈ 0.2055 > 7/37, the small-row margin, Lemma marked's second condition, and
M ≥ (1 + 3ℓ)/2. The paper's per-summand reading M - 2ℓ ≥ 1/2 fails there (ℓ* > 1/6): every
abscissa below 7/8 in this assembly needs the total-accounting reading of the low side,
inferred in hunt #134 and, per this hunt's `FOLLOWUPS.md`, claimed with proof in
unrefereed preprints by Liu, Guo, and Xu and Sang (this lane has not checked those proofs).
Cross-checks: -E_* agrees with hunt #134's `probe.py` at 162 of 162 exact points, and with a
fresh transcription of line 15729; the slice optima with the excess scaled by 3/4, 1/2 and
1/4 are 0.8728554, 0.8707660 and 0.8687000, each within 2 × 10^-6 below #134's float table
(0.872856, 0.870767, 0.868701), as its coarser b-grid predicts.

The measured evaluator `sigma_general` handles what the closed form cannot: each selected
capacity capped by the supply ℓ/h, the marked one also by Lemma marked's second condition,
the paper's floor δ_0 = 1/50, the rows d ≤ 1/2 (as the paper counts them, or recounted), the
Gram condition and the small rows, and any binding x. Its short-row step takes the maximum
of min(A, S) over every breakpoint and crossing in r, so it assumes no monotonicity (the
marked count is not monotone once 2x c_M > 1), and a dense brute-force grid agrees with it to
10^-4 (pinned). It reproduces σ* to 10^-8 when the caps are slack, and the x = 0 wall to
10^-8 when it binds (both pinned). With the second marked condition and the rows d ≤ 1/2
both left out it agrees with the first version at c_M = 1: that version printed 0.8731594,
and the finer b-search used now gives about 0.8731593 (both pinned).

## 5. Pricing

Shadow prices at the paper's inputs, by the envelope theorem on the binding slice (exact,
and confirmed by central differences of exact optima, `test_shadow_prices_two_routes`):
dσ*/dα = 0.0047006, dσ*/dc_M = -0.0095711, dσ*/dc_P = -0.0019777. Per one percent of each
input that is about 3.9, 4.8 and 0.44 × 10^-5 (hedged: a linearization). The second marked
condition and the rows d ≤ 1/2 are slack at the paper's inputs, so their own shadow prices
there are zero.

Break-even values to reach 0.8748867, each the root of an exact polynomial (degree 7 for α,
8 for c_M and c_P) and confirmed by recomputing the optimum: α = 0.8186904 (1.76 % below 5/6),
c_M = 0.5073017 (1.46 % above 1/2), c_P = 0.2565019 (15.4 % above 2/9). To reach 0.8748087
the same inputs would have to move to 0.8031897 (3.62 %), 0.5152786 (3.06 %) and 0.2916823
(31.3 %). Both c_M values are below 37/65, so the second marked condition does not change
them (checked exactly). The rows d ≤ 1/2, as the paper counts them, are slack at five of the
six geometries and violated at α = 0.8031897; there, holding b on their line, α has to reach
0.8028731 (3.66 %, the root of an exact quadratic), and 0.8031897 needs those rows recounted.

Perfect inputs (measured, with the supply caps, Lemma marked's second condition, the paper's
floor δ_0 = 1/50 and the Gram condition, unless marked exact). As the paper counts the rows
d ≤ 1/2:

- α = 0, that is e(r) = 1: 84031/96156 ≈ 0.8739028, where the floor meets the line of those
  rows (exact).
- c_M = 1, c_P = 1, or both: about 0.8740525; the line of those rows and the x = 0 rows bind,
  and the exact intersection on the x = 0 slice is the same number.

With the rows d ≤ 1/2 recounted at the balancing t:

- α = 0: the floor binds at ℓ = 3/16, b = 0: 167/192 ≈ 0.8697917 (exact), and b ≥ 0 binds there
  as well: a negative b eases the floor through C_0, and b = -12/317, where the floor and the
  rows x = 1/2, δ = 5/6 bind together, would give 826/951 ≈ 0.8685594 (derived, outside Prop.
  probe-gram). With the floor pushed to a = 1/2 the corner 13/15 is reached (exact); there b = 0
  is optimal without the constraint b ≥ 0, because a negative b lowers -E_* at the rows
  x = 1/2, δ = 5/6 (derived).
- c_M = 1: about 0.8734852. The second marked condition binds and the supply does not:
  removing the supply cap leaves the value unchanged, and c_M = 10 gives the same. With the
  second condition dropped as well the value is about 0.8731593 and the supply binds;
  removing the supply cap then falls to the x = 0 wall. The first version of this report gave
  0.8731594 for c_M = 1 alone, which silently dropped both the second condition and the
  paper's count of the rows d ≤ 1/2; that is corrected here.
- c_P = 1: about 0.8734556.
- c_M = c_P = 1: the x = 0 wall, 101/108 - √286/270 ≈ 0.87254987212856, at b = 0, with or
  without the second condition.

## 6. Ranking

By the abscissa a perfect input would buy, at the paper's floor and with b ≥ 0. As the paper
counts the rows d ≤ 1/2: α (to 84031/96156), then any capacity (each, and both together, to
about 0.8740525). With those rows recounted: α (to 167/192, or 13/15 with the floor at 1/2),
then both capacities together (to the x = 0 wall), then c_P (about 0.8734556), then c_M (about
0.8734852, where the second marked condition binds; about 0.8731593 if that condition is
relaxed too). The first version ranked c_M ahead of c_P here; with the second condition kept,
c_P is ahead by about 3 × 10^-5. By leverage near the paper, which is what matters for any
realistic sharpening: c_M first (1.46 % passes 0.8748867, 3.06 % passes 0.8748087), α second
(1.76 % and 3.66 %), c_P a distant third (15.4 % and 31.3 %). Of the other losses in section 3,
the recounts and the Gram correlation buy zero at the paper's inputs, the κ tie buys
5.04 × 10^-8, and the averaged numerator (item 13) is outside this lane's pricing.

## 7. Controls

- 39 selected row-count constants, 10 endpoint and frequency-range constants, and the five
  #134 numbers (7/8, -1/48, 7/30672, 13/15, 5655673/6464057) are reproduced exactly; 98 of 98
  citations sit on their lines.
- Planted faults, each confirmed red: a marked capacity 1/3 breaks 15 reproductions and a
  slope 4/5 breaks 2; R = 1 - 2δ/3 for the rows d ≤ 1/2 breaks 4 endpoint reproductions;
  increasing-order slot selection fails the selection inequality; dropping the covering
  constraint lets the grid adversary beat R_*; the wrong compensating exponent fails the
  Gram bookkeeping; a dropped sign fails the local formula; dropping Lemma marked's second
  condition moves the c_M = 1 answer by more than 2.5 × 10^-4; with it dropped, removing the
  supply cap moves the answer by more than 5 × 10^-4; leaving the rows d ≤ 1/2 out moves the
  c_M = 1 answer by more than 5 × 10^-4; three wrong cells in a copy of this page's tables
  fail the page test.
- Independent routes: the general -E_* against #134's code (162 points), the closed-form
  R_* against the capped evaluator (agreement to 10^-12 when the caps are slack), the capped
  evaluator's short-row step against a dense brute-force grid, the numpy local sums against a
  pure-Python double loop (325 sums), the envelope-theorem prices against finite differences,
  the measured evaluator against the exact optima, including both exact walls of section 5.

## 8. Limitations

- The moment lemmas, the detector and the Gram bound are inputs. If any is wrong, all of
  this concerns a different argument. The proofs of the capacities were read only where the
  capacities are produced.
- Every abscissa below 7/8 here uses the total-accounting low side (inferred in #134, and
  claimed with proof in unrefereed preprints per `FOLLOWUPS.md`, not checked here) and #134's
  general-geometry transcription of the high exponent (derived there, cross-checked here).
- The two public goals 0.8748867 and 0.8748087 are cited from `MISSION.md` and `FOLLOWUPS.md`.
  The numerator averaging of item 13 is the change the public frontier moved through; this
  lane neither checks nor prices it.
- The recount of the rows d ≤ 1/2 (item 14) is a reading of the paper's no-slot counts, not a
  proof; every value in the third column of answer 5 depends on it.
- The perfect-c_M numbers keep Lemma marked's second condition at the paper's value; relaxing
  both conditions together is reported separately, and no reading here says which of the two
  canonical charges a sharper argument would relax first.
- The Gram verdict rests on a reading of the exceptional coefficient's structure (inferred),
  supported by enumeration (a), not on a recomputation of the Gram bound.
- The dead verdict for item 2 assumes no correlation between witnesses at different t
  beyond what Proposition detector-witness states.
- The measured numbers carry grid and bisection errors; the pinned tolerances are 5 × 10^-6.

## 9. Prior art

No literature search was run by this lane. The parallel followups lane did read the public
follow-ups, and by its record (`FOLLOWUPS.md`, cited there) both headline numbers here are
already printed: σ* is Liu's B_alg (arXiv:2610.12234v1, with the same ℓ* and b*), and σ†
is Liu's B_new (v2), which also equals Guo's σ_dagger. Its X8 also has 167/192, and tomoto0's
barrier analysis gives 0.86979 for the same floor. This lane's derivations reproduce them
independently, which checks the transcription of the assembly; they are not results. The
assembly lane (`assembly.py`) gets the same closed forms and the same three shadow prices by
a separate code path. What this lane adds, as far as these records show, is the loss inventory
of section 3 (in particular that the single detector length per bin is exact, that the Gram
exceptional term survives every choice of ξ, and that the paper's count of the rows d ≤ 1/2
binds at every perfect-input optimum), the x = 0 wall in both counts, the
threshold at which Lemma marked's second condition starts to bind, the break-even values, and
the exact rational brackets. `FOLLOWUPS.md` section 4 lists tracker entries on marked counts
(PR 48, 50 and 66) and on the detector count (PR 56) whose Lean sources were not read, so
whether they contain the same observations was not checked. Nothing here claims novelty.

## 10. What the repair changed

An independent verifier reproduced σ*, σ†, the x = 0 wall, the shadow prices and the
break-even values by its own route, and found three major issues and seven minor ones. All
are addressed above:

- **Major, corrected:** the free-input model left out Lemma marked's second condition. It is
  now modelled (`Inputs.c_M2`, `marked_second_margin`, `marked_second_threshold`, the capped
  evaluator); perfect c_M is about 0.8734852 with the rows d ≤ 1/2 recounted, not 0.8731594,
  the ranking of c_M against c_P by perfect value is reversed, and the doors name the
  condition.
- **Major, withdrawn:** the sharper bound on |L_{p^c}| of item 8 was false when p divides one
  of n1, n2; the enumeration now covers that case and the bound is restated as φ(p^c).
- **Major, cut back:** answers 1 and 6 no longer say that no count can be recovered or that
  the priced inputs are unproved everywhere; they say what was tried and what was not checked.
- **Minor:** the 13/15 and floor statements now carry the floor they assume (167/192 at the
  paper's floor); b ≥ 0 is named as active at the x = 0 wall; the page test now checks whole
  table rows and every decimal on this page; item 2's grid search is described as a check
  that cannot fail; item 7(b) is described as orthogonality; "39 of 39" became 39 selected
  constants plus 10 endpoint constants; the rows d ≤ 1/2 use the paper's R = 76/75 - 2δ/3.
- The verifier also called b ≥ 0 active at the 13/15 corner. Checked here: it is active at the
  paper's-floor corner 167/192 (b = -12/317 would give 826/951), and not at 13/15 itself, where
  a negative b lowers -E_* (section 5), so the constraint has no price there.
- **Found during the repair, major:** the first version's perfect-input values, and the
  repair's own first pass at them, ignored the rows d ≤ 1/2. As the paper counts those rows
  they bind at every perfect-input optimum and at α to 0.8748087; the second column of answer
  5, item 14 and the doors are new. This was not in the verifier's list.

## The doors

This lane measures where one assembly stops, so the section is owed. Candidate status: the
assembly's smallest target is σ* = (1507 - 2√921)/1653 with the paper's counts and
σ† = 0.8749570194200989 with κ tied (derived, conditional on the low-side reading); the
parameter range is ℓ, M ≥ 0 and b ≥ 0 with M + ℓ ≤ 1, the paper's floor and the paper's moment
constants; nothing here is a proved ceiling of the method.

### Active constraints at the optimum

1. **The endpoint inequality at δ* ≈ 0.38858, x = 1/2** (a double root): the only active one.
   Its prices are the shadow prices of section 5.
2. **The dual length M + ℓ = 1**: active at every optimum (input-free slope).
3. **Everything else is slack** at σ*: the floor (about -0.0059), the Gram condition, the
   supply, the rows d ≤ 1/2 (about -0.0027), the small rows, b ≥ 0 (b* ≈ 0.12340544), and
   Lemma marked's second condition (margin 1/16 at x = 1/2).
4. **Under perfect inputs other constraints take over** (measured unless marked exact). As the
   paper counts the rows d ≤ 1/2, their line ℓ ≤ 188/1593 + 223b/531 comes first: with the
   x = 0 rows for any capacity (0.8740525, exact on the slice) and with the floor at α = 0
   (84031/96156, exact). With those rows recounted: for c_M = 1, Lemma marked's second
   condition, not the supply; with that condition dropped as well, the supply; with both
   capacities perfect, the x = 0 rows and b ≥ 0 (exact on the x = 0 slice); with α = 0, the
   floor and b ≥ 0 (167/192, exact), or, with the floor at 1/2, C_0 ≤ 0 and the low side
   ℓ ≤ 1/5 (13/15, exact).

### The frozen-constant inventory

| constant | value | relaxing it trades | trade shape |
|---|---|---|---|
| t for the rows d ≤ 1/2 | 1 (line 16146) | nothing new: the balancing t uses the same no-slot counts (inferred) | genuine, needs no new lemma (inferred); slack at σ*, binds at every perfect-input optimum |
| amplification slope α | 5/6 (line 15300) | sixth-power lift density against the ball | genuine; the only route to the floor |
| marked capacity c_M | 1/2 (line 15182) | the mark's length in the reflected energy | genuine; largest leverage, alone down to about 0.8734852 |
| second marked condition c_M2 | 1/4 (line 9254) | the 6z_0 charge of the second invariant | slack at the paper's inputs; binds once c_M exceeds 37/65 |
| plain capacity c_P | 2/9 (line 15327) | the induction's exchange rate 6κ | genuine; small leverage |
| κ_0 in c_P | 3/4 | Lemma plain's stated range | worth 5.04 × 10^-8, taken by Guo |
| Gram offset b ≥ 0 | P_a ≥ 1 (line 8345) | a Gram estimate for P_a < 1 | slack at σ*; active at the x = 0 wall (0.8723955 at b = -1/50) and at 167/192, not at 13/15 |
| detector window t | [1, 3/2] (line 4513) | nothing: one t per bin is exact | none |
| slot mesh | fine (line 16246) | nothing: its loss tends to zero | none |
| floor | 51/100 (line 15843) | slack except at α = 0 | 167/192 to 13/15, only at α = 0 |

### The information class

- **Inside the current data, recomputation only:** the geometry, the detector window, the
  choice of t per row, the slot order, the copies and strata, and the t used for the rows
  d ≤ 1/2. Exhausted at the paper's inputs for the recounts tried here: σ* is exact, and
  every recount here is dead or buys zero there; the recount of the rows d ≤ 1/2 matters only
  once an input moves well past the paper's value (α by 3.62 % already).
- **Inside the current family, better inputs:** a larger c_M (worth at most down to about
  0.8734852 while the second marked condition stays, about 0.8731593 with it relaxed too) or
  a larger c_P (new moment-lemma proofs), together worth at most down to the x = 0 wall; a
  smaller α (a large sieve over the sparse lifted family), worth down to 167/192 at the
  paper's floor. All of these need the rows d ≤ 1/2 recounted; without that recount no input
  of this family goes below 84031/96156.
- **Reading more inside the same probe:** an average of the reflected numerator over each
  bin (item 13), which the follow-ups use (per `FOLLOWUPS.md`); not priced here.
- **Outside the lemmas as stated:** a Gram estimate for P_a < 1, which would admit b < 0 and
  move the x = 0 wall (0.8723955 at b = -1/50 and 0.8722121 at b = -1/20 on that slice).
- **Reading more:** below 13/15 needs a different probe (hunt #134). Below the x = 0 wall
  needs α, a better no-slot count for rows with no prime amplitude (their counts 1 - δr and
  1 - 2δm come from the zero-slot cases of the two lemmas), or b < 0.
