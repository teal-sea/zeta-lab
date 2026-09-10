# Independent audit of this hunt's headline

An adversarial audit by a separate agent with no part in producing the result,
given the write-up and the repository and told to break the claim rather than
review it. Fifteen attacks. **Four of them landed**, and one of the four took the
headline down.

Its report is reproduced below as returned. Every correction has been applied to
`RESULTS.md`, and the four that carry numbers were recomputed here first rather
than accepted on the audit's word:

- **The stated reason for reformulating the programme is false.** The factorial
  objective returns the same optimum: relative difference `2.7e-14`, `2.9e-14`,
  `2.4e-14` and `7.0e-14` at the four diagonal cutoffs. The cancellation is real
  as arithmetic and the solver absorbs it.
- **The model comparison was not like for like.** On the same 20 rows,
  conjectured exponents `(1, 1/2)` with `log C` linear in `alpha`, which is two
  parameters and is how `BARRIER.md` states the conjecture, give rms `0.1198`
  against the free three-parameter fit's `0.1258`. The conjectured shape wins,
  with one parameter fewer.
- **The conjecture as an inequality is untouched.** `E >= 0.1704 N/sqrt(y)` holds
  at all 20 measured points. The published constant `0.2` is 15 percent too
  large at one of them.
- **A fourth threshold row was omitted**, and it changes a reading: `N = 10^6`,
  `y* = 1938`, ratio `0.970`, `alpha* = 0.5479`, so `alpha*` falls monotonically
  `0.5998, 0.5595, 0.5540, 0.5479`.

**Verdict: survives-with-corrections.**

## Attacks run

### 1. held: Claim (a). Derive the Chebyshev identity independently and check that the reformulated LP really is the published factorial programme, not a different object. If Q_N or the constraint set differs, every number is of a different object.

**Ran:** /tmp/claude-0/-home-user/0b62659d-7e9f-5dec-8365-a09378a3b2ca/scratchpad/exact_identity.py: pure INTEGER check, no floats. log(floor(N/j)!) and sum_{q in Q_N} w_q floor(q/j) are both integer combinations of {log p}; I compared the integer coefficient of every log p on both sides, using v_p(M!) = sum_k floor(M/p^k) on the right and the prime-power decomposition of Lambda on the left. Ran at N = 27, 100, 997, 1000, 1024, 10^4, 30030, 10^5, for every j up to min(200, N). Also compared lp.quotient_cells against the source's Q_N = {floor(N/d) : 2 <= d <= N} in hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/RESULTS.md line 81.

**Outcome:** Zero failures at every (N, j). sum_q w_q = psi(N) exactly and sum_q w_q floor(q/j) = log(floor(N/j)!) exactly. Dropping q = N is free because Lambda(1) = 0, and the source's constraint set is the same Q_N, so B_c(N) = sum_q w_q W_c(q) and the two programmes have identical feasible sets with objectives differing by the constant psi(N). The identity is not merely measured to 1e-16 as RESULTS section 2 says, it is an exact integer identity.

### 2. BROKE IT: Claim (a)'s stated REASON. lp.py and RESULTS section 2 assert the factorial objective 'asks a float solver for a quantity near 1e4 as a difference of quantities near 1e8, and the answer is carried entirely in the cancelling digits'. Nobody in the hunt ever ran the factorial form to check. Run it.

**Ran:** scipy linprog on min sum_j c_j lgamma(N//j + 1) s.t. A c >= 1, c free (HiGHS dual simplex and HiGHS interior point), at (10^3, 56/62/63), (10^4, 100/157/172/173), (10^5, 316), (10^6, 1000), (3x10^6, 1732); compared against the hunt's reformulated values.

**Outcome:** The factorial form loses nothing. 10^5: 1035.2339342960 vs 1035.2339342959. 10^6: 6414.832163714 vs 6414.832163713 (4.5e-10 on 6.4e3, 13 significant digits), 93 s against the hunt's 20 s. 3x10^6: 14477.154080 vs 14477.154080 (7.6e-8), 494 s against 143 s. Interior point agrees with dual simplex on every case. So the reformulation buys a factor 3.5 to 4.7 in wall clock and nothing in accuracy, and it makes the programme LARGER (it adds m variables and an m x m identity block to the same dense A). The sentence in lp.py's docstring and RESULTS section 2 is refuted as a statement about float behaviour, and it also contradicts the hunt's own door 2, 'the 10^7 ceiling is memory, not time'.

### 3. held: Claim (d). A zero reported by a float LP is the classic place to plant a wrong claim. Check feasibility of the y* = 173 zero at N = 10^4 in exact rational arithmetic: does W(q) >= 1 hold at every attainable cell?

**Ran:** scratchpad/exact_zero.py and exact_zero2.py. Zero excess is equivalent to: exists c in Q^y with A_S c = 1 on S = {q : w_q > 0} and A_Z c >= 1 on Z = {q : w_q = 0}, where S and Z are decided exactly by whether the d-interval (N//(q+1), N//q] contains a prime power. Solved A_S c = 1 exactly with python-flint fmpz_mat.nullspace, reduced the remaining inequalities onto the exact nullspace, found a float interior point, snapped it to rationals and re-verified every constraint in fractions.Fraction. Ran at (10^3, 62/63), (10^4, 172/173), (10^5, 588/589).

**Outcome:** Did not break it; it upgrades the claim. At (10^4, 173) I have an explicit rational c with denominator 60 and max|c| = 721/10 for which W(q) = 1 exactly at all 99 positive-weight cells and W(q) >= 1 exactly at all 198 attainable cells, min W = 1, zero violations. Same at (10^3, 63) (denominator 2, max|c| = 89/6) and (10^5, 589) (denominator 10^6, max|c| = 433473/6250, 630 cells checked, zero violations). The zeros at y* = 63, 173, 589 are exact rational facts, not float LP outputs.

### 4. held: Claim (d), the other half: is the collapse really SHARP, or is the last positive value at y*-1 also secretly zero and just not found by the solver?

**Ran:** scratchpad/farkas.py: exact Farkas certificates. On the exact nullspace of A_S, infeasibility of M z >= b is witnessed by lam >= 0 with M^T lam = 0 and lam.b > 0. Took the float dual, restricted to its support, re-solved the normalisation exactly with flint, and verified lam >= 0, M^T lam = 0 and lam.b = 1 in exact rationals. Ran at (10^3, 62), (10^4, 172), (10^5, 588).

**Outcome:** All three carry an exact Farkas certificate (support sizes 8, 5 and small). Zero excess is exactly impossible at y* - 1 at all three cutoffs, so the collapse at y* = 63, 173, 589 is sharp as an exact statement. Claim (d) survives at a higher grade than the write-up claims for it.

### 5. held: Claim (d), attack 5: is the staircase real or solver tolerance? Re-solve plateau points at tighter tolerance and by a different method, and verify a plateau value exactly.

**Ran:** (i) Four independent routes at (10^3, 56 and 62) and (10^4, 157 and 172): the hunt's reformulation with HiGHS dual simplex, the same with HiGHS interior point, the factorial objective with dual simplex, the factorial objective with interior point. (ii) scratchpad/exact_opt2.py: rebuilt the optimum in exact arithmetic over Q[log 2, log 3, ...], using the active set to get an exact rational vertex, an exact dual multiplier vector from A_k^T lam = L verified as an identity over the primes, Arb enclosures at 300 bits for the sign checks, and compared the two plateau ends coefficient by coefficient. (iii) monotonicity and plateau spread from artifacts/staircase_N1000.json and staircase_N10000.json.

**Outcome:** Did not break it. All four routes agree to 10 decimal places at every plateau point. E(y) is monotone non-increasing with zero violations and the within-plateau spread is 4e-14. In exact arithmetic the value at y = 56 and y = 62 (N = 10^3) is the identical element of Q[log p], fully verified with a nonnegative dual and an exact rational primal point, and it is exactly (7/2) log 2 = 2.42601513195980858. At N = 10^4 the value at y = 157 and y = 172 is the identical exact element too, and it is exactly 3 log 23 = 9.40648264778744907. The staircase is a fact about the rank of floor(q/j), not a tolerance artefact.

### 6. held: Claim (c), attack 3: 18 (now 20) points, a and b correlated, narrow alpha range. Compute the design correlation and honest error bars, and ask whether a = 1.150 (now 1.159), b = 0.878 (now 0.874) is overstated.

**Ran:** Loaded fit.load() directly. Computed corr(log N, log y) = 0.799, VIF(a) = VIF(b) = 2.8, condition number 65, OLS standard errors, 95% CIs, leave-one-out and leave-one-N-out refits, a cluster-robust covariance clustered by N (6 clusters), and the joint F test of H0: (a, b) = (1, 0.5).

**Outcome:** This attack FAILED. The collinearity is mild because alpha is varied within each N: a = 1.150 +/- 0.020 (cluster-robust 0.023), b = 0.878 +/- 0.034 (cluster-robust 0.044), joint F(2,15) = 66.4, leave-one-N-out keeps a in [1.133, 1.181] and b in [0.864, 0.936]. Within the stated model the point estimates are stable and (1, 0.5) is rejected. The problem with claim (c) is not the error bars, it is the model, which is the next attempt.

### 7. BROKE IT: Claim (c), the real attack: is the free power law even the right model, and is the comparison in RESULTS section 4 like for like? It pits a 3-parameter free power law against a 1-parameter version of the conjecture. BARRIER.md section 3 explicitly says of the same family 'away from y = sqrt(N) the constant moves but the exponent does not', so the conjecture's own stated form has a moving constant and was never tested.

**Ran:** Fitted six models to the same 20 rows with alpha <= 0.5 and compared rms and AIC: (1) E = C N/sqrt(y), 1 par; (2) conjectured exponents with log C linear in alpha, 2 par; (3) free power law E = C N^a y^-b, 3 par; (4) conjectured exponents with log C quadratic in alpha, 3 par; (5) free power law plus an alpha term, 4 par; (6) conjectured exponents with a free constant per alpha slice, 5 par.

**Outcome:** BROKE the shape conclusion. Model (2), which keeps the conjectured exponents (1, 1/2) intact and lets only the constant depend on alpha, fits BETTER than the free power law with one fewer parameter: rms 0.1198 against 0.1258, AIC -80.9 against -76.9. Model (6) gives rms 0.0726, AIC -94.9. And model (5) is decisive: once the constant is allowed to move with alpha, the fitted exponents snap back to a = 1.042, b = 0.609, i.e. essentially the conjectured pair. The anomalous (1.159, 0.874) is what a pure power law produces when it is forced to absorb an alpha-dependent constant. What the grid actually measures is that C moves by a factor 2.5 across alpha in [0.30, 0.50] while moving by only about 8 percent rms across two to four decades of N at fixed alpha.

### 8. BROKE IT: Claim (c), independent check on the same point: does the fitted (a, b) reproduce the N-dependence it claims to describe? Under E = C N^a y^-b, E sqrt(y)/N at fixed alpha must go like N^{a - 1 + (0.5 - b) alpha}.

**Ran:** For each alpha slice in the grid (0.30, 0.35, 0.40, 0.45, 0.50) fitted d log(E sqrt(y)/N) / d log N from the measured points and compared it with the fitted prediction 0.159 - 0.374 alpha.

**Outcome:** BROKE it. The fitted exponents get the SIGN of the N-trend wrong at three of the five alpha slices. alpha = 0.30: measured -0.030, fitted +0.047. alpha = 0.35: measured -0.008, fitted +0.028. alpha = 0.45: measured +0.017, fitted -0.009. Only alpha = 0.40 and the diagonal alpha = 0.50 agree in sign, and the diagonal is where the extra rows sit. Consequently RESULTS section 4's conclusion sentence, 'If the fitted exponents persisted, E sqrt(y)/N would decrease without limit and no fixed positive constant would survive', is false over its own grid: under those exponents the N-exponent at fixed alpha is positive for alpha < 0.425, so for the lower half of the measured alpha window the same fit predicts E sqrt(y)/N GROWING without limit and the conjecture surviving comfortably.

### 9. BROKE IT: Claim (c) and (b), attack 4: the conjecture is a LOWER bound and the hunt fits an EQUALITY. Is the caveat adequate, or does the framing still read as a refutation?

**Ran:** Computed min over every measured point of E sqrt(y)/N, on the 20 rows with alpha <= 0.5 and on all positive rows; checked the actual bite on the published statement 'the conjecture ... with the constant 0.2 in place of 0.32'.

**Outcome:** Partial hit. The caveat paragraph in section 4 ('a worse fit of an equality shape is not a counterexample to an inequality') is correct and present, but it is one paragraph against a document title, a section 1 headline table and a section 4 heading that all read as refutation. The measured content is much narrower: E >= c N/sqrt(y) holds at EVERY one of the 20 measured points with c = 0.1704, and fails the published constant 0.2 only at the single new 10^7 diagonal point, by 15 percent. RESULTS never states the surviving lower bound, which is the form the conjecture is actually in. Combined with the previous two attempts, the honest summary of the grid is 'the constant in front of N/sqrt(y) is not constant in alpha', which is what BARRIER.md section 3 already said for V*, and not 'N/sqrt(y) is not the shape of T*'.

### 10. held: Claim (b): do the four published diagonal values 'reproduce exactly'?

**Ran:** Compared the hunt's floats against the exact-rational pinned values in hunts/prime_pair_error/frontier/2026-09-06/certificate_lp_frontier/DUAL_WITNESS.md lines 65-66.

**Outcome:** Minor hit. Published 41.28216944295939183072..., hunt 41.28216944295942: agreement to 14 significant digits, absolute miss 2.8e-14. Published 226.83268961232150239965..., hunt 226.83268961232105: agreement to 15 significant digits, absolute miss 4.5e-13. RESULTS' own wording 'to every printed digit' is right for the two-decimal table in section 4.6 but wrong for the two rows the source pins to 40 digits. 'Exactly' is not available to a float LP and should not be claimed.

### 11. held: Claim (b): are the two new rows (3x10^6 and 10^7) trustworthy, and were the identity oracles the MISSION requires actually run at them?

**Ran:** Re-solved N = 3x10^6, y = 1732 by the independent factorial objective (494 s) and compared. Read the identity fields out of artifacts/lp_large.json for all six diagonal cutoffs and compared with the table in RESULTS section 2.

**Outcome:** 3x10^6 confirmed to 7.6e-8 by the independent objective. The identity oracles WERE run at 3x10^6 and 10^7 (relative defects 2.3e-15 and 2.4e-15, three times the 10^6 value) but the RESULTS section 2 table, introduced as 'measured ... at every cutoff', lists only 10^3 through 10^6 and omits exactly the two new cutoffs it is there to license. 10^7 itself is still a single solver route: I did not re-solve it (the reformulated solve was 917 s, the factorial route would be roughly an hour).

### 12. held: Structural: is |Q_N| the right denominator for claim (d)'s 1.03 / 0.87 / 0.93, and what actually keeps the excess positive below y*?

**Ran:** Exact rank computations with flint. Counted the positive-weight cells S and zero-weight cells Z exactly, and found the smallest y at which the equality part alone, A_S c = 1, becomes consistent.

**Outcome:** Not a refutation, a correction of emphasis. Only about half the attainable cells carry any prime mass: |S| = 40, 99, 275 of |Q_N| = 61, 198, 630. The equality condition W = 1 at every prime-carrying cell is already satisfiable at y = 44, 104, 391, far below y* = 63, 173, 589. At both y* and y* - 1 the equality system is consistent; what separates them is entirely the W >= 1 requirement at cells carrying ZERO von Mangoldt weight. So the ratio y*/|Q_N| that section 1 and section 6 report compares against a denominator that mixes two structurally different constraint types, and the real door under door 2 ('which columns are the two that matter') is the zero-weight cells, not the cell count.

### 13. held: Reporting completeness: does the write-up use all the evidence its own artifacts contain?

**Ran:** Diffed RESULTS.md against artifacts/threshold.json, artifacts/sweep2.log, artifacts/lp_large.json, artifacts/fit.json. Note: RESULTS.md and the fit artifacts were being edited by a concurrent session during this audit (RESULTS.md mtime moved from 00:07 to 00:45 while I worked, and sweep_1e7_partial.json appeared at 00:44), so some of this may already be in flight.

**Outcome:** Three gaps as of the version I read (commit e2ad76c). (1) artifacts/threshold.json carries a fourth measured row, N = 10^6, y* = 1938, y*/|Q_N| = 0.970, alpha* = 0.5479, which appears nowhere in RESULTS; section 6 and the section 1 headline report three of four. (2) The alpha of y* falls monotonically, 0.5998, 0.5595, 0.5540, 0.5479, at about -0.0070 per log N, reaching 0.5 near N = 10^8.6. That is the natural explanation for why the within-N slope b_N drifts (I measure 0.946 +/- 0.039, 0.917 +/- 0.078, 0.777 +/- 0.065 at 10^4, 10^5, 10^6), and it is not mentioned. (3) Section 4 says 'the 21 positive rows with alpha <= 0.5' while artifacts/fit.json says n = 20 and I count 20.

### 14. held: Small checkable numbers in section 5 and the doors.

**Ran:** Recomputed the staircase steps from artifacts/staircase_N1000.json, the binding-cell ratios and the rank of A on the diagonal (flint exact rank), and the memory arithmetic in door 2.

**Outcome:** Mostly clean, two nits. Door 1's vertex argument is sound: exact rank(A) = y on the diagonal at N = 10^3, 10^4, 10^5, so a vertex does have y active rows and 'half is arithmetic' is right. Door 2 says the dense 2 sqrt(N) x y block 'at N = 10^8 is 3.2 GB'; the stated formula gives 2e4 x 1e4 x 8 bytes = 1.6 GB, so the number is twice what its own formula yields (the extra factor is the code's own CSR copy in lp.py, which is not what the sentence says). Section 5's 'the next seven buy a factor of 4.2' is loose: the whole factor is bought at y = 56 alone and y = 57..62 buy nothing, which is the point the paragraph is making.

### 15. held: Withdrawn attack, recorded because it looked like a hit and is not. RESULTS section 4's table row 'free a and b (a = 1.159, b = 0.874) | 0.1258 | 0.0639' looked like it was reporting the grid-fitted model's residual on the diagonal, when the 0.0639 comes from a separate diagonal refit with completely different parameters.

**Ran:** Evaluated the grid-fitted (a, b) on the six diagonal points, both with the grid's own constant and with a constant refit on the diagonal, and computed the singular values of the diagonal design.

**Outcome:** The table's reading is fair: with each model getting its own constant, the grid fit gives rms 0.0647 on the diagonal against 0.1063 for the conjectured pair, so 0.0639 is essentially the fitted shape's own diagonal residual. (With the grid's constant it would be 0.1115, worse than the conjectured shape, but that is not the comparison the table makes.) What does survive is smaller: the diagonal design has singular values [34.3, 0.632, 0.0112], condition 3078, and the 'free a and b' diagonal refit returns a = 0.510, b = -0.424, min-norm pseudo-inverse values with a NEGATIVE b, determined entirely by the 0.0029 that floor(sqrt 1000) knocks alpha off 0.5 at one point. So 'three of them to three decimal places' is forced by the design, not measured, and the hunt applies its own doors-section standard ('the ratio looks meaningful and is not') to the binding count but not here.

## Corrections required

- RESULTS section 2 and the lp.py module docstring: delete or replace 'The factorial form asks a float solver for a quantity near 1e4 as a difference of quantities near 1e8; this one does not' as a justification for the reformulation. Measured, the factorial objective returns 1035.2339342960 at (10^5, 316), 6414.832163714 at (10^6, 1000) and 14477.154080 at (3x10^6, 1732), agreeing with the reformulated values to 11 to 13 significant digits. The reformulation buys 3.5x to 4.7x in wall clock and nothing in accuracy, and it enlarges the programme. The section heading 'why it is the reason 10^7 was reachable' should say time, and should be reconciled with door 2's 'the 10^7 ceiling is memory, not time'.
- RESULTS section 4 and the section 1 headline: the model comparison is not like for like. It pits a 3-parameter free power law against a 1-parameter reading of the conjecture, while BARRIER.md section 3 states the conjecture's own form with a moving constant ('away from y = sqrt(N) the constant moves but the exponent does not'). On the same 20 rows, conjectured exponents (1, 1/2) with log C linear in alpha give rms 0.1198 and AIC -80.9 against the free power law's 0.1258 and -76.9, with one fewer parameter; a free constant per alpha slice gives 0.0726 and -94.9; and adding an alpha term to the free power law returns a = 1.042, b = 0.609. Report the measured statement, which is that the constant moves by a factor 2.5 across alpha in [0.30, 0.50] and by only about 8 percent rms across decades of N at fixed alpha, rather than a = 1.159, b = 0.874 as 'the shape'.
- RESULTS section 4, the closing sentence: 'If the fitted exponents persisted, E sqrt(y) / N would decrease without limit and no fixed positive constant would survive' is false over the lower half of its own grid. Under (a, b) = (1.159, 0.874) the N-exponent at fixed alpha is 0.159 - 0.374 alpha, positive for alpha < 0.425. Either qualify it to alpha above 0.425, or drop it, and note that the fitted exponents get the sign of the measured N-trend wrong at three of the five alpha slices (alpha = 0.30 measured -0.030 against fitted +0.047; 0.35 measured -0.008 against fitted +0.028; 0.45 measured +0.017 against fitted -0.009).
- Add the surviving lower bound, since the conjecture is a lower bound: E >= c N / sqrt(y) holds at every one of the 20 measured points with c = 0.1704, and the only failure of the published statement is that the constant 0.2 is 15 percent too large at the single new 10^7 diagonal point. That is the measurement's actual bite and RESULTS never states it.
- RESULTS section 1 and section 3: replace 'reproduce exactly' / 'to every printed digit' with the measured agreement. Against DUAL_WITNESS.md's exact-rational pins the hunt's floats agree to 14 and 15 significant digits (41.28216944295942 against 41.28216944295939183..., 226.83268961232105 against 226.83268961232150240...). A float LP value is not exact and the MISSION's own agents_may_not forbids describing it as one.
- RESULTS section 2: the identity table stops at 10^6 while introducing itself as 'measured at every cutoff'. The 3x10^6 and 10^7 rows exist in artifacts/lp_large.json with defects 2.3e-15 and 2.4e-15, three times the 10^6 value, and they are precisely the cutoffs whose numbers are new. Add those two rows.
- RESULTS section 6 and the section 1 headline: artifacts/threshold.json contains a fourth measured row, N = 10^6, y* = 1938, y*/|Q_N| = 0.970, alpha* = 0.5479, which the write-up omits. Include it, and record that alpha* falls monotonically (0.5998, 0.5595, 0.5540, 0.5479, about -0.0070 per log N), which is the obvious explanation for the drift in the within-N slope b_N (0.946, 0.917, 0.777 at 10^4, 10^5, 10^6) that the grid fit averages away.
- RESULTS section 4 says 'the 21 positive rows with alpha <= 0.5'; artifacts/fit.json says n = 20 and I count 20. (The file was being edited by a concurrent session while I audited it, so this may already be fixed.)
- Claim (d) can be stated at a much higher grade than 'measured'. Exact rational witnesses exist for all three cutoffs: at y* = 63, 173, 589 an explicit rational c (denominators 2, 60, 10^6) has W(q) = 1 at every positive-weight cell and W(q) >= 1 at every one of the 61, 198, 630 attainable cells; at y* - 1 = 62, 172, 588 an exact Farkas vector proves zero excess impossible. The plateau values are exact too: (7/2) log 2 at (10^3, y = 56..62) and 3 log 23 at (10^4, y = 157..172), the same element of Q[log p] at both ends of each plateau. The write-up reports these as six-decimal floats.
- Door 2: 'at N = 10^8 it is 3.2 GB' does not follow from the stated formula. 2 sqrt(10^8) x 10^4 float64 is 1.6 GB. Either correct the number or say that the doubling comes from lp.py's own CSR copy of the dense block.
- RESULTS section 4's 'diagonal only' column: the 'free a and b' entry is a rank-deficient min-norm refit (design singular values [34.3, 0.632, 0.0112], returned a = 0.510 and b = -0.424, a negative exponent), and the agreement of the three two-parameter rows 'to three decimal places' is forced by the design rather than measured. It is broken only by the 0.0029 that floor(sqrt 1000) knocks alpha off 0.5 at one point. This deserves the same one-paragraph treatment door 1 gives the binding-cell ratio.
- RESULTS sections 1 and 6 compare y* to |Q_N|, but only about half the attainable cells carry prime mass (|S| = 40, 99, 275 of 61, 198, 630) and the equality condition W = 1 on all of those is already satisfiable at y = 44, 104, 391. What keeps the excess positive up to y* is the W >= 1 requirement at the ZERO-weight cells. Stating that sharpens door 2 and replaces a ratio against a mixed denominator.

## Sentences the audit called overclaims

- 'The factorial form asks a float solver for a quantity near 1e4 as a difference of quantities near 1e8; this one does not' (RESULTS section 2 and lp.py docstring). True as arithmetic, false as the claimed consequence: the factorial form returns the same optimum to 11 to 13 significant digits at every size tested up to 3x10^6. The hunt never ran the comparison it uses to justify its central move.
- 'The reformulation, and why it is the reason 10^7 was reachable' (section 2 heading), against door 2's 'the 10^7 ceiling ... is memory, not time'. The two cannot both be the operative reason, and the reformulated programme is the larger of the two.
- 'reproduced, four published diagonal values, to all printed digits' and 'they reproduce to every printed digit'. The source prints two of them to 40 digits in DUAL_WITNESS.md; the hunt's floats agree to 14 and 15 significant digits.
- 'from a formulation that shares no objective with theirs' (section 3). The implementation's objective differs, but the identity the reformulation rests on is the source's own equation (E), stated in section 2 of the very document being cross-checked. The check is independent of the source's code, not of its derivation.
- 'the conjectured shape is 2.7 times worse' / 'three times worse' (section 4). This compares a 3-parameter free power law against a 1-parameter reading of a conjecture whose own source states it with a moving constant. Given that constant one degree of freedom, the conjectured exponents beat the free power law on rms and on AIC with fewer parameters.
- 'What the measurement does say is that N / sqrt(y) is not the shape of T*' (section 4). What it shows is that the CONSTANT in front of N/sqrt(y) depends on alpha. Allowing that, the fitted exponents return to a = 1.042, b = 0.609, and BARRIER.md section 3 had already recorded the same phenomenon for V* ('away from y = sqrt(N) the constant moves but the exponent does not').
- 'If the fitted exponents persisted, E sqrt(y) / N would decrease without limit and no fixed positive constant would survive' (section 4). Under those exponents this is true only for alpha above 0.425; over the rest of the hunt's own grid the same fit predicts the opposite. And the fitted exponents get the sign of the measured N-trend wrong at three of the five alpha slices.
- The document title 'the barrier law is not the shape the diagonal suggested' and the section 1 headline table, which juxtapose a fitted equality against a conjectured inequality. Every measured point satisfies E >= 0.1704 N/sqrt(y); the only thing refuted is the published constant 0.2, at one point, by 15 percent. The section 4 caveat paragraph says this correctly and is outweighed by everything around it.
- 'On the diagonal the four models are indistinguishable, three of them to three decimal places' (section 4), presented as a finding. On the diagonal those three models are the same two-parameter model, so their agreement is forced; the free-fit row's diagonal parameters are a min-norm artefact with a negative exponent.
- 'measured, not assumed, at every cutoff before the solve is trusted' (section 2), followed by a table that omits the two new cutoffs the hunt is claiming credit for.
- Understatement rather than overstatement, and worth fixing in the other direction: claim (d) is graded 'measured (floating LP)' when exact rational witnesses exist for the zeros at y* = 63, 173, 589, exact Farkas certificates for the strict positivity at 62, 172, 588, and exact closed forms for the plateau values ((7/2) log 2 and 3 log 23).
