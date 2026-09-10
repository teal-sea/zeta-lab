# Independent audit of this hunt's headline
An adversarial audit run by a separate agent with no part in producing the
result, given the write-up and the repository and told to break the claim
rather than review it. Its report is reproduced below as it was returned: the
attacks it ran, the verdict it reached, the corrections it required and the
sentences it called overclaims. This page is the audit's, not the hunt's.

Every correction it required has been applied to `RESULTS.md` and
`PROPOSAL.md`, and the three that carried numbers were recomputed here first
rather than taken on the audit's word:

- 41 forms across the 14 discriminants, 14 principal and 27 not (the class
  numbers sum to 41). The write-up had said 44 and 30. Recomputed: 41 and 27.
- `R = |1 - a(1)| * max_n |c(n)|` identically, so the residual is not an
  independent diagnostic. Recomputed on every form: the difference is `0.0`
  exactly on all but one row and `1.6e-30` on that one.
- The published non-principal numbers are exactly the composite defect of
  `1 + Z_Q(s)`. Recomputed on all 27 rows: worst absolute disagreement `0.0`.

**Verdict: survives-with-corrections.**

## Attacks run

### 1. Attack 1: check a(1) for every non-principal reduced form directly, without using zeta.epstein.epstein_representation_count or the hunt's artifact.

**Ran:** /tmp/adv1.py: brute-force count of integer (x,y) != (0,0) with a*x^2+b*x*y+c*y^2 = n over an explicit box, for all 41 reduced forms of the 14 discriminants; independently re-checked the reduction conditions and b^2-4ac; compared brute force against epstein_representation_count for n <= 30 on all 41 forms.

**Outcome:** Brute-force r(1) is w (6, 4 or 2) for exactly one form per discriminant and 0 for every other. Exactly one reduced form per discriminant has leading coefficient 1, and epstein_reduced_forms returns it at index 0 in all 14 cases (which is what probe.py assumes when it takes per[0] as principal). The minimum of a reduced positive definite form is its leading coefficient, so 'represents 1 iff principal' is exact, not approximate. rep() matched brute force in 0 of 41x30 cases mismatching. Class numbers matched the known values 1,1,1,1,1,2,2,3,2,3,4,5,7,8.

**Broke the claim:** no

### 2. Attack 2: derive the identity from -f'/f myself and check probe.py's spectrum() against a route that shares no code with the recursion.

**Ran:** /tmp/adv2.py: derived -f' = (-f'/f)*f giving a(n) log n = sum_{d|n} c(d) a(n/d); then computed c independently as c(n) = b(n) log n where log f = sum b(n) n^-s was built from the Dirichlet logarithm b = sum_k (-1)^{k+1} u^{*k}/k with u = a - delta_1 and repeated Dirichlet convolution. Compared to spectrum() on all 14 principal forms at dps 40.

**Outcome:** The identity in probe.py is the correct one. spectrum() reproduces the Dirichlet-logarithm route to at worst 5.3e-40 on every principal form, so the recursion is not computing the wrong object. The residual function also matches the identity as written (it sums d over all divisors including d = n).

**Broke the claim:** no

### 3. Attack 2b: is the residual an independent diagnostic, as RESULTS section 2 claims, or is it algebraically forced?

**Ran:** /tmp/adv2.py and /tmp/adv9.py: compared the reported residual vector against |c(n)| on all 27 non-principal forms, then tested the general identity R = |1 - a(1)| * max_n |c(n)| across all 41 forms with a(1) additionally forced to 0.5, 2 and 7.

**Outcome:** BROKE THE FRAMING, NOT THE CLAIM. Because spectrum() defines c[n] := a(n) log n - sum_{d|n,d<n} c(d) a(n/d), the residual at n is identically c(n)*(1 - a(1)). Measured: max over 41 forms and 4 normalisations of |R - |1-a(1)|*max|c(n)|| = 1.5e-39. So R carries exactly the information in a(1) and nothing else; it is a re-encoding of the a(1) column, not a second oracle. Consequences: the hunt's stated kill condition ('the residual is zero for every form') could never have fired independently, and 'the largest published defect is the largest residual' is two norms of one vector (corr = 0.9900 over the 27 rows, same argmax by construction).

**Broke the claim:** no

### 4. Attack 3: find a different valid reading under which the 30 (in fact 27) published numbers mean something, which would make 'the rows are empty' wrong.

**Ran:** /tmp/adv3.py: tested the hypothesis that the recursion run on a series with a(1) = 0 returns the log-derivative coefficients of ftilde = 1 + Z_Q (i.e. a with a(1) overwritten by 1), computing c(ftilde) by the independent Dirichlet-logarithm route; separately enumerated the represented values of (2,1,2) at d = -15 and their ratios n/m as exact fractions.

**Outcome:** A reading exists and is exact: the published non-principal numbers are the composite defect of 1 + Z_Q(s), matching to 1.5e-39 across all 27 forms. It does not rescue the table: the zeros of 1 + Z_Q are the points where Z_Q = -1, not the zeros of Z_Q, so the number says nothing about the object docs/34 section 6 is talking about. The honest object -Z_Q'/Z_Q is a generalised Dirichlet series whose frequencies are log of 1, 3/2, 5/2, 4, 6, 17/2, 9, 10, 23/2 ... and their semigroup products, so an integer-indexed 'composite line' has no object to attach to. Net: the hunt's headline survives, but 'those rows carry no information at all' is imprecise.

**Broke the claim:** no

### 5. Attack 3b: if the recursion's particular c is inadmissible, can some other integer-indexed c solve the identity for a non-principal form (letting c(1) be free, which the recursion fixes at 0)?

**Ran:** /tmp/adv6.py: built the full linear system a(n) log n = sum_{d|n} c(d) a(n/d) for n = 2..60 in unknowns c(1..60) and solved it by numpy least squares for each of the 27 non-principal forms.

**Outcome:** No integer-indexed c solves it at all. The least-squares residual is 2.18 to 5.79 for every one of the 27 forms, and the fitted c(1) (2.4 to 3.0) is nowhere near log m. So the system is inconsistent, not merely under-determined. This is a stronger statement than the hunt makes: no re-choice of coefficients repairs those rows, and the rescaling check in RESULTS section 3 was not the only door that had to be closed.

**Broke the claim:** no

### 6. Attack 4: break the Kronecker symbol in probe.py, which would make a broken class-number-one control look like a passing one.

**Ran:** /tmp/adv4.py: compared probe.kronecker against sympy.kronecker_symbol for every d = 0,1 mod 4 in [-400,400] and every n in [1,299] (about 60,000 pairs); compared it against a second implementation built from sympy.legendre_symbol and factorint plus the d mod 8 rule at p = 2; checked Gauss's identity sum_over_reduced_forms r_Q(n)/w = sum_{m|n} chi_d(m) for all 14 discriminants and n < 61; re-derived c(n) = Lambda(n)(1 + chi_d(n)) from zeta_K = zeta * L(chi_d) and compared it to the recursion; and applied the same prediction to h > 1 principal forms to see whether the control has teeth.

**Outcome:** Zero mismatches against sympy, zero against the Legendre build. Gauss's identity holds for all 14 discriminants (which also validates rep() and the class-group-sum row). The h = 1 control agrees with the recursion to at worst 5.3e-40 at dps 40 (the hunt reports 2.8e-30 at dps 30, consistent). It is not vacuous: applied to the principal form of d = -15, -23, -95 the same prediction misses by 16.4, 8.1 and 8.0. The control is sound.

**Broke the claim:** no

### 7. Attack 5: attack the correlations. Are -0.82 and -0.69 reproducible, are they an artifact of the frozen NMAX = 61 cutoff, and can nine points support the interpretation placed on them?

**Ran:** /tmp/adv5.py and /tmp/adv8.py: recomputed the nine principal-form defects at NMAX = 61, 101, 201, 401; Pearson, tie-corrected Spearman, Fisher 95% CIs, partial correlations, a 200,000-draw permutation test on the gap |r_logd| - |r_h|, leave-one-out correlations, OLS of defect on log|d| and h jointly, and a cutoff-normalised defect (composite L2 divided by total L2).

**Outcome:** Numbers reproduce exactly: -0.8165 and -0.6946. The negative sign is robust (it strengthens to -0.918 and -0.801 at NMAX = 401; Spearman is -0.983 and -0.979 tie-corrected), so that attack failed. But the interpretation does not survive: corr(h, log|d|) = +0.968 on these nine points, the Fisher CIs are (-0.960, -0.333) and (-0.930, -0.057) and overlap almost entirely, the permutation p-value for the observed gap is 0.113, tie-corrected Spearman makes the two predictors indistinguishable (-0.983 vs -0.979), and in the joint regression defect ~ log|d| + h the class-number coefficient is +0.4104 (t = +2.13), i.e. it flips sign once |d| is held fixed. Separately, under a cutoff-normalised defect (the hunt's own named door) the correlations flip to +0.73 with log|d| and +0.83 with h.

**Broke the claim:** no

### 8. Attack 5b: test the stated mechanism ('c near |d|/4, so it represents fewer integers below 61 and its coefficient sequence is sparser').

**Ran:** /tmp/adv5.py and /tmp/adv8.py: counted represented n < NMAX for each of the nine principal forms and regressed the defect on that count alone and jointly with log|d|.

**Outcome:** The count is 19, 20, 22, 22, 20, 17, 18, 14, 12, not monotone in |d|. corr(defect, #represented) = +0.466, R^2 = 0.217, t = 1.39, not significant on nine points; and in the joint model with log|d| the coefficient reverses to -0.160 (t = -3.21), the opposite sign to the mechanism as stated. The mechanism sentence claims an explanation the data does not carry.

**Broke the claim:** no

### 9. Attack 6: break the hunt's own door-2 claim, that the class-group characters give a(1) = 1 and defect zero everywhere and so 'no axis at all'.

**Ran:** /tmp/adv7.py: formed sum_Q chi(Q) zeta_Q for the real character at d = -15, -20, -24 (C2), the two complex cubic characters at d = -23 and one at d = -31 (C3), and the complex quartic and the quadratic character at d = -39 (C4, with the ambiguous form (3,3,4) as the element of order 2); ran the recursion in complex arithmetic and also checked coefficient multiplicativity a(mn) = a(m)a(n) for coprime m,n.

**Outcome:** Every character combination has a(1) = 1 exactly and composite defect between 5.1e-31 and 4.4e-30, with coefficients multiplicative to 9.4e-31. The door-2 claim holds, including for complex characters, which the hunt asserted but did not compute.

**Broke the claim:** no

### 10. Attack 7: check the write-up's own arithmetic and reproducibility against the artifact.

**Ran:** Counted forms in hunts/euler_defect_axis/artifacts/axis.json; re-ran hunts/euler_defect_axis/probe.py end to end and compared the md5 of axis.json; cross-checked every number in the RESULTS section 2 and section 5 tables against the artifact; grepped the repository for the number 44.

**Outcome:** PARTIAL BREAK, on the write-up rather than the mathematics. probe.py reproduces axis.json byte for byte and every table entry checks out (36.0644 with residual 189.6888 at d = -15, form (2,1,2); the class-group-sum residuals are 1.6e-30 to 6.3e-30). But the artifact holds 41 forms, not 44, and 27 non-principal forms, not 30: the class numbers sum to 41. RESULTS section 1 ('forms in the published table 44', 'forms whose a(1) equals 0 30'), RESULTS section 2 ('all thirty of the others') and the MISSION huntspec ('44 reduced forms') are wrong, and contradict the same document's own '0 of 27 checked' and 'all 27 non-principal forms'. The number 44 appears nowhere in the repository outside this hunt's two files.

**Broke the claim:** no

### 11. Attack 8: is the 'narrow band' disposition that kills the issue #93 compute job stable under the one constant the hunt itself flags as frozen?

**Ran:** /tmp/adv5.py and /tmp/adv8.py: recomputed the corrected axis at NMAX = 61, 101, 201, 401 and compared band width, ratio and width/mean.

**Outcome:** The band is 2.96..5.08 (ratio 1.72, width/mean 0.53) at the published cutoff and 5.02..10.57 (ratio 2.11, width/mean 0.71) at NMAX = 401. The qualitative disposition (no 36, no monotone-upward knob) survives, but the specific characterisation 'a two-point effective axis (zero, or about four)' is a statement about NMAX = 61, and the hunt's own door 2 says the statistic is not scale-free.

**Broke the claim:** no

## Corrections required

- Counts: replace 44 with 41 and 30 with 27 everywhere. hunts/euler_defect_axis/artifacts/axis.json holds 41 forms across the 14 discriminants (the class numbers 1,1,1,1,1,2,2,3,2,3,4,5,7,8 sum to 41), of which 14 are principal and 27 are not. The affected lines are RESULTS.md section 1 ('forms in the published table 44', 'forms whose a(1) equals 0 30'), RESULTS.md section 2 ('bounded away from zero on all thirty of the others') and MISSION.md's huntspec frontier field ('44 reduced forms'). The same document already says 27 twice, so the verdict block contradicts its own body.
- The residual is not an independent oracle and must stop being described as one. By construction of spectrum(), residual(n) = c(n)*(1 - a(1)) identically, so the reported R equals |1 - a(1)| * max_{2<=n<61} |c(n)|; measured across all 41 forms and three artificial normalisations of a(1), |R - |1-a(1)|*max|c(n)|| <= 1.5e-39. RESULTS.md section 2's 'computed by a separately written function that sums over all divisors including d = n, so it does not share the recursion's isolation step' should say that the residual is algebraically equivalent to reading a(1), and the huntspec's 'required_oracles' entry naming the residual as an independent oracle should be withdrawn. The grade line 'the load-bearing step an exact residual that is zero or is not' should name a(1) as the load-bearing step.
- Withdraw or rewrite 'The largest published defect is the largest residual.' The defect is the L2 norm of the composite part of c and R is the max modulus of the same c, so the two agree at corr = 0.9900 over the 27 rows and share an argmax by construction. It is not a coincidence detected by a second instrument.
- Correct 'those rows carry no information at all' (section 7, door 1). The published non-principal numbers are exactly the composite defect of ftilde(s) = 1 + Z_Q(s), verified to 1.5e-39 by an independent Dirichlet-logarithm route on all 27 forms. They are a well-defined functional of a well-defined series; what is true is that the zeros of 1 + Z_Q are not the zeros of Z_Q, so the numbers are about a different function, not about nothing.
- Strengthen section 3 rather than weakening it: the rescaling check is not the only repair that had to be excluded, and the stronger fact is available. Least squares on the full system a(n) log n = sum_{d|n} c(d) a(n/d) for n = 2..60, over all c(1..60) with c(1) free, leaves residual 2.18 to 5.79 for every one of the 27 forms. No integer-indexed coefficient vector solves the identity, so the rows cannot be repaired by any re-choice of c.
- Rewrite the section 5 correlation paragraph. The numbers reproduce (-0.8165 and -0.6946), and the negative sign is robust to the cutoff and to Spearman, so keep those. But drop 'the discriminant explains it better than the class number does': corr(h, log|d|) = +0.968 on these nine points, tie-corrected Spearman is -0.983 versus -0.979, the Fisher 95% CIs are (-0.960,-0.333) and (-0.930,-0.057), and a 200,000-draw permutation test gives p = 0.113 for the observed gap. And qualify 'larger class number goes with a smaller defect': in the joint regression defect ~ log|d| + h the class-number coefficient is +0.4104 (t = +2.13), so the marginal negative sign is inherited from log|d| and reverses when |d| is held fixed. Nine collinear points support a monotone trend and its sign, and nothing about which variable is responsible.
- Qualify or drop the mechanism sentence in section 5. Tested against its own natural proxy, corr(defect, count of represented n < 61) = +0.466 with R^2 = 0.217 and t = 1.39, and the coefficient reverses to -0.160 (t = -3.21) once log|d| is in the model. 'The mechanism is not mysterious' asserts an explanation that nine points do not carry.
- Attach the cutoff caveat to the disposition in section 5, since the section itself is being used to cancel a compute job. At NMAX = 401 the corrected band is 5.02 to 10.57 (ratio 2.11, width/mean 0.71) rather than 2.96 to 5.08 (ratio 1.72, width/mean 0.53), and under the cutoff-normalised defect the hunt names as its own door (composite L2 divided by total L2) the correlations flip sign to +0.73 with log|d| and +0.83 with h. The disposition can stand; the sentence 'a two-point effective axis (zero, or about four) with the spread inside it explained by sparsity' is a statement about NMAX = 61 and should say so.
- PROPOSAL.md section 3's 'The section's argument is unaffected' is too broad. docs/34 section 6's summary sentence 'Class number above one: every individual form is loud' is a claim about the 27 ineligible rows and does not survive; only 'the principal form is loud' does. Say which sentence goes, not only which table column.
- Flag one caveat the hunt inherits and does not state: docs/34's F4 gloss, that c(n)/sqrt(n) is the weight of frequency log n in the zero distribution, presumes the zeros lie on the critical line, and the rows the hunt keeps are exactly the h > 1 principal forms, whose Epstein zeta functions are classically known to have zeros off that line. I did not verify that off-line claim computationally, so it should be checked before it is written down, but the entitlement argument in the hunt is about a(1) = 1 only, and a(1) = 1 is necessary rather than sufficient for the Weil reading.

## Sentences the audit called overclaims

- RESULTS.md section 2: 'was computed by a separately written function that sums over all divisors including `d = n`, so it does not share the recursion's isolation step.' Separately written it may be, but residual(n) = c(n)*(1 - a(1)) identically, so it shares everything with the recursion and measures only a(1).
- RESULTS.md header: 'Grade: measured, with the load-bearing step an exact residual that is zero or is not.' The load-bearing step is a(1), which is an exact integer count of representations of 1. The residual is downstream of it and adds nothing.
- RESULTS.md section 2: '**The largest published defect is the largest residual.** ... The number the table calls loudest is the number produced furthest outside the recursion's hypothesis.' Two norms of the same coefficient vector, correlated at 0.99 with a shared argmax by construction. This is presented as a corroborating coincidence.
- RESULTS.md section 2: 'is bounded away from zero on all thirty of the others.' There are 27 others, and the same document says so twice elsewhere.
- RESULTS.md section 1: 'forms in the published table 44' and 'forms whose a(1) equals 0: 30'. The artifact holds 41 and 27. The number 44 appears nowhere else in the repository.
- RESULTS.md section 5: 'Class number is not the knob, and what correlation there is runs backwards.' Class number rank-orders the nine loud rows at tie-corrected Spearman -0.979, statistically indistinguishable from log|d| at -0.983. What fails is the direction and the range, not the ordering, and the direction claim is specific to the unnormalised statistic.
- RESULTS.md section 5: 'Larger class number goes with a *smaller* defect, and the discriminant explains it better than the class number does.' Nine points with corr(h, log|d|) = +0.968 cannot separate the two, permutation p = 0.113 for the gap, and the joint-regression coefficient on h is +0.41 (t = +2.13).
- RESULTS.md section 5: 'The mechanism is not mysterious: the principal form (1, b, c) of a large discriminant has c near |d|/4, so it represents fewer of the integers below 61 and its coefficient sequence is sparser.' r = +0.466, R^2 = 0.217, t = 1.39 against the represented count, and the sign reverses once log|d| is controlled for.
- RESULTS.md section 5: 'The experiment ... would therefore have been run against a two-point effective axis (zero, or about four) with the spread inside it explained by sparsity.' The band width is cutoff-dependent (width/mean 0.53 at NMAX = 61, 0.71 at NMAX = 401) and the sparsity explanation is the one just contradicted.
- RESULTS.md section 7, door 1: 'The shadow price is total: those rows carry no information at all, rather than biased information.' They are exactly the composite defect of 1 + Z_Q(s), a well-defined series; the correct statement is that the series is not the one under discussion.
- PROPOSAL.md section 3: 'The section's argument is unaffected. ... Only the numbers attached to non-principal forms go.' The sentence 'every individual form is loud' in docs/34 section 6 also goes.
