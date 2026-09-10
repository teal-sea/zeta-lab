# Independent audit of this hunt's headline

An adversarial audit by a separate agent with no part in producing the result.
Seventeen attacks. **Eleven landed.** The claim that the routine fails silently
survived every attack on the oracle, including a class-number-formula route that
touches no lattice at all. Almost everything else needed correcting, and two of
the corrections were serious.

Every correction has been applied. The four that carry numbers were reproduced
here first:

- **The guard had a hole and its own fault ladder could not see it.**
  `guarded_epstein_zeta((2,1,3), 8+80i, dps=required_dps(8,80,4), want_digits=4)`
  is allowed at `dps = 24` and returns `0.59` correct digits. Reproduced: the
  form-blind law puts the loss at `39.90` digits and the form-aware one at
  `44.07`, a gap of `4.17`, which is exactly the `-log10|zeta_Q(s)|` term the
  form-blind rule drops. Every one of the six rungs held the form fixed.
  `guard2.py` is the rebuild, and its new rung tests the contract rather than
  another planted fault: it samples the calls the guard ALLOWS and fails if any
  is short.
- **The title was wrong.** `zeta/heatflow.py` already implements this guard for
  `H_0` with `pi/8/ln10`, live and used, and `zeta/core.py`'s `_eta_workload`
  does the same for `eta`. `hunts/gate5_p6_b/probe.py` carries the constant as
  an executable rule, not a comment. The core has the pattern twice; the Epstein
  module is the gap.
- **`from_log.py` was written on a false premise and had become destructive.**
  `surface.log` is complete, 120 cells, and ends with the probe's own success
  line. It now refuses rather than overwriting the richer JSON.
- **The `+1.068` uniform offset is not what the write-up said it was.** It is
  mpmath's `dps_to_prec` rounding a decimal request up to whole bits, worth
  0.87 to 1.15 digits, not "the largest quantity formed is a little smaller
  than 1/t".

**Verdict: survives-with-corrections.**

## Attacks run

### 1. held: Oracle attack 1: recompute the representation counts by a different algorithm. probe.representation_counts groups lattice points by represented value inside a box of radius sqrt(qmax/lam_min); zeta.epstein.epstein_representation_count solves the quadratic in m for each k instead. Different code, different loop shape.

**Ran:** /tmp/claude-0/-home-user/0b62659d-7e9f-5dec-8365-a09378a3b2ca/scratchpad/a_oracle.py: compared counts for q <= 60 on forms (1,1,4), (2,1,3), (1,0,1).

**Outcome:** Zero mismatches on all three forms. The enumeration bound is also correct as stated: Q(m,k) >= lam_min*(m^2+k^2) with lam_min = ((a+c) - sqrt((a-c)^2+b^2))/2 the smaller eigenvalue of [[a,b/2],[b/2,c]], so no point with Q <= qmax escapes the box.

### 2. held: Oracle attack 2: sum the lattice a completely different way, enumerating points one at a time with no grouping by represented value, over the whole box.

**Ran:** raw_lattice() in a_oracle.py at s = 5+10i and 5+100i for all three forms, dps 60.

**Outcome:** Grouped and raw agree to 8.8e-19 (t=10) and 9.6e-20 (t=100) for (1,1,4), and similarly for the others. The whole difference is the box corners with Q > qmax, i.e. the truncation itself. No defect.

### 3. held: Oracle attack 3: is the stated truncation bound honest? Re-sum at qmax = 400000 and compare against qmax = 20000, against the bound the probe reports.

**Ran:** /tmp/.../a2_tail.py, forms (1,1,4)/(2,1,3)/(1,0,1) at t = 10, 100, 160.

**Outcome:** Actual truncation 5.0e-20 to 1.8e-18; stated bound 1.02e-17 to 2.45e-17. Honest in every cell, conservative by 10x to 400x. Correction, not a break: the bound is measured-and-extrapolated, not proven. K = N(qmax)/qmax is measured at one point and then used as an upper bound for N(x)/x at all x > qmax; since N(x) = Cx + O(sqrt x), K can sit below C. It also carries an extra factor of sigma relative to the sharp Abel-summation result K*Q^(1-sigma)/(sigma-1), which is part of why it holds. probe.py's docstring calls it a bound; it is a measurement plus an extrapolation.

### 4. held: Oracle attack 4, the strongest: check the oracle against a route that touches no lattice at all. Class-number formula sum over reduced forms of zeta_Q(s) = w * zeta(s) * L(s, chi_D), right-hand side from mpmath's zeta plus a Hurwitz-zeta character sum.

**Ran:** /tmp/.../l_classgrp.py at D = -4, -15, -23 (h = 1, 2, 3) and t = 10, 100, 160, sigma = 5, dps 50, using sympy's kronecker_symbol.

**Outcome:** Relative agreement 3.1e-20 to 1.1e-18, i.e. 18.0 to 19.5 digits, which is exactly the qmax=20000 truncation limit. The oracle is sound. Attack 1 fails: the surface rests on a correct oracle.

### 5. held: Check the dps + 20 claim by instrumenting mp.dps at the point of evaluation rather than reading the source.

**Ran:** /tmp/.../b_dps.py: monkeypatched mp.gammainc to record mp.dps at the moment the cancelling combination's terms are built, for caller dps 15, 30, 80.

**Outcome:** epstein_zeta: 15 -> 35, 30 -> 50, 80 -> 100. epstein_completed alone: 15 -> 25, 30 -> 50-10=40, 80 -> 90. The dps + 20 claim is correct and the mechanism is as stated (epstein_zeta opens workdps(dps+10) then passes dps=mp.dps into epstein_completed, which opens workdps(dps+10) again). The fit is not absorbing a wrongly-stated guard.

### 6. BROKE IT: Follow-up on dps + 20: is dps + 20 the epsilon the caller actually gets? mpmath converts dps to bits with dps_to_prec(n) = round((n+1)*log2(10)), which does not land on a decimal digit.

**Ran:** /tmp/.../j_derived.py and k_prec.py: computed dps_to_prec(dps+20)*log10(2) - (dps+20) for every dps in the artifacts, and re-ran the residual with that in place of dps+20.

**Outcome:** The conversion buys 0.87 to 1.15 extra decimal digits (dps 35 -> 120 bits = 36.12 digits). Substituting it moves the derived-law residual from mean +1.086 to +0.086. This matters because docs/37 attributes its own leftover +1.068 offset to 'the model assumed the largest quantity formed is exactly 1/t, it is a little smaller'. I replaced 1/t by the exact largest term |1/s| and the mean moved by 0.002 digits. That explanation is wrong; the offset is mpmath's dps-to-prec granularity.

### 7. held: Derive |Gamma(sigma+it)| independently and check the sigma term of the law numerically against mpmath.

**Ran:** /tmp/.../e_gamma.py: -log10|Gamma(sigma+it)| vs 0.68219 t - (sigma-1/2) log10 t - 0.399 at sigma = 0.5, 2.5, 3, 5, 8 and t = 10, 40, 100, 160.

**Outcome:** The Stirling form is right: exact at sigma = 0.5 to 5 decimal places, and within 0.003 digits everywhere for t >= 100. Worst case is sigma = 8, t = 10 at 0.26 digits. The Gamma half of the law is not where the error is.

### 8. BROKE IT: Measure the intermediate terms the routine actually forms, to test law.py's premise that the largest is O(1/t). law.py's derivation writes '- log10 sqrt(2 pi) - log10 t + log10 t' and cancels the 1/t contribution against a +log10 t that appears from nowhere.

**Ran:** /tmp/.../d_terms.py: rebuilt first, second/sqrt(d), 1/(sqrt(d)(s-1)) and 1/s at sigma=5, t = 10, 40, 100, form (1,1,4), at working precision 60 + 0.6822 t.

**Outcome:** |1/s| is the largest term at every height (8.94e-2 vs 8.82e-3 / 5.01e-2 / 4.79e-2 at t=10; 9.99e-3 vs 8.65e-4 / 5.69e-3 / 5.16e-3 at t=100). So the -log10 t is real and should not have been cancelled. Measured log10(max term / |mellin|) is 2.997 / 20.254 / 59.002 at t = 10 / 40 / 100, against L_law = 1.923 / 19.680 / 58.820, i.e. the law under-states the cancellation by +1.07 / +0.57 / +0.18, a gap that shrinks like log10 t exactly as a missing -log10 t predicts. Working the algebra through gives digits lost = -log10|s| + sigma*log10(pi) - log10|Gamma(s)| - log10|zeta_Q(s)|: the law is missing three terms, of which +sigma*log10(pi) and -log10|zeta_Q| are the ones that matter.

### 9. BROKE IT: Split the residual on the hunt's OWN cells by form. The law has no form dependence at all, so a form-dependent residual is a missing term rather than noise.

**Ran:** /tmp/.../i_resid.py: 46 cells of artifacts/surface.json with 1 < correct_digits < 14 (far from both the float64 ceiling and the zero floor), residual against dps+20-L_law with no capping.

**Outcome:** (1,1,4) mean +0.848 sd 0.379; (2,1,3) mean -0.667 sd 0.444; (1,0,1) mean +1.156 sd 0.496. Spread 1.82 digits. The differences equal the differences in log10|zeta_Q(5+it)| to within 0.036 digits: measured +1.515 between (1,1,4) and (2,1,3) against log10|zeta_Q| difference +1.551; measured +0.308 between (1,0,1) and (1,1,4) against +0.313. The whole-sample mean of +0.19 that makes the fit look acceptable is manufactured by averaging +0.85 against -0.67.

### 10. BROKE IT: Out-of-sample in sigma, which the hunt never did: every cell in surface.json and boundary.json is at Re s = 5. Test at Re s = 3 and Re s = 8, where the lattice oracle still converges.

**Ran:** /tmp/.../f_sigma.py and f2_sigma.py: forms (1,1,4) and (2,1,3), t = 60, 80, 100, dps chosen from law.required_dps at margins 4 and 7, comparison done at high precision, oracle strength recorded per cell (7.6 to 30.1 digits) and cells discarded where the oracle is too weak to judge.

**Outcome:** Law residual mean +1.230 at sigma=3, +0.135 at sigma=5 (in-sample), -1.951 at sigma=8. Worst single cell -3.51 ((2,1,3), sigma=8, t=80). The drift per unit sigma is -0.523 for (1,1,4) against a predicted -log10(pi) = -0.497 (log10|zeta_Q| is sigma-flat there), and -0.868 for (2,1,3) against a predicted -log10(pi) + dlog10|zeta_Q|/dsigma = -0.807. Both within 0.06. The missing +sigma*log10(pi) - log10|zeta_Q| is confirmed by predicting the drift from quantities the law never sees.

### 11. BROKE IT: Out-of-sample at sigma = 1/2, the line MISSION.md and law.py single out as the worst case and the line count_zeros_box and Z_epstein actually work on. The lattice oracle diverges there, so build a different one: for D = -4 the class number is 1, so zeta_{(1,0,1)}(s) = 4 zeta(s) beta(s) exactly, with beta from Hurwitz zeta. No lattice, no shared code with epstein_completed.

**Ran:** /tmp/.../m_crit.py: sanity-checked the identity against the lattice oracle at s = 5+100i (agreement 4.7e-20), then measured epstein_zeta at sigma=0.5, t = 40, 60, 80, 100, margins 4 and 8.

**Outcome:** Law residual mean +4.66, rms 4.68, range +4.06 to +5.36. The law over-states the loss by nearly five digits on the critical line. Combined with -1.95 at sigma=8, the law's error swings 8.2 digits across sigma in [0.5, 8]. The claim that the sigma term 'decides whether a rule fitted on one vertical line transfers to another' is right; the term itself does not transfer.

### 12. BROKE IT: Replace the law with the derived one and see whether the structure disappears, which is the test that the missing terms are the right ones rather than three free parameters.

**Ran:** /tmp/.../j_derived.py: predicted = prec_digits(dps+20) - (-log10|s| + sigma*log10(pi) - log10|Gamma(s)| - log10|zeta_Q(s)|), evaluated on the same 46 cells and on the out-of-sample sigma and critical-line runs.

**Outcome:** Per-form means collapse from +0.848/-0.667/+1.156 to +0.084/+0.089/+0.082 (spread 0.026 digits), overall mean +0.086 rms 0.357. Across sigma: +1.05 at 3, +1.18 at 5, +1.04 at 8 before the precision correction. At sigma = 0.5 the derived residual is +1.35 against the law's +4.66. Nothing is fitted; every term is computed.

### 13. BROKE IT: Check whether the 'oracle floor' / 'oracle ceiling' law.py uses to cap predictions and to select the cells that test the law is what its comment says it is ('a property of the ORACLE at each (form, height), set by where the lattice sum was truncated').

**Ran:** /tmp/.../c_ceiling.py: probe.py computes err = float(abs(mp.mpc(got) - truth)/truth_abs) outside any workdps block, so mp.dps is 15 there. Compared probe's number against the same comparison at dps 66, and against a qmax=200000 oracle.

**Outcome:** At (1,1,4), dps=80, t = 10/20/40 probe reports 16.00/16.45/16.12 correct digits; the same comparison at dps 66 gives 18.33/18.60/18.90 and against qmax=200000 gives 22.33/22.60/22.90. Confirmed mp.mpc(x) rounds to the current precision. The 16-to-17.6 digit ceiling that law.py prints as 'oracle floor' and stores per cell as oracle_ceiling_here is float64 rounding in the probe's own comparison, not the lattice truncation. It does not corrupt the transition-band cells (mpmath subtraction is exact-then-rounded, so a difference in the 5th digit is still accurate), but it does set which cells count as saturated and what the prediction is capped at.

### 14. BROKE IT: Verify from_log.py's reconstruction is faithful, and verify its premise that the run was cut short partway through the third form.

**Ran:** /tmp/.../g_fromlog.py and g2.py: re-implemented the parse in /tmp (never writing into the repo), compared against surface.json and boundary.json by (form, t, dps), and compared the 'seconds' field.

**Outcome:** The premise is false against the artifacts present. surface.log holds 120 data lines = 8 heights x 5 dps x 3 forms, the complete grid with 40 cells for every form including (1,0,1), and its last line is the probe's own '-> artifacts/surface.json'. surface.json (158 rows) is exactly the 120 log cells union 38 of boundary.json's 42, carries all 10 fields at full precision, and its 'seconds' match the log exactly on all 120 rows. from_log.py writes 6 fields parsed from 4-significant-figure text; running it now would replace 158 full-precision rows with 120 rounded ones and drop oracle_truncation_bound and oracle_abs. Where the parse does apply it is faithful to the printed precision: max |(-log10 rel_err) - printed correct_digits| = 0.0499 over 120 rows, which is the 1-decimal print format.

### 15. held: Re-run cells and compare against the recorded values, as instructed.

**Ran:** /tmp/.../h_rerun.py: re-ran (1,1,4) t=60 dps=20; (2,1,3) t=100 dps=30; (1,0,1) t=80 dps=50; (1,1,4) t=120 dps=15 through probe.surface.

**Outcome:** Bit-for-bit identical relative errors, ratio 1.000000 on all four. 5.762935e-09, 7.480392e+09, 2.307774e-18, 2.346323e+36. The recorded numbers are reproducible and claim (a) is independently confirmed: at t=120, dps=15 the routine returns a value wrong by 2.3e+36 with no exception and no warning.

### 16. BROKE IT: Attack the guard's own contract: find a call guarded_epstein_zeta allows whose answer has fewer correct digits than the caller asked for.

**Ran:** /tmp/.../n_guard.py: for each case set dps = law.required_dps(sigma, t, want) and called guarded_epstein_zeta with that dps and want_digits, then measured against the lattice oracle, asserting per case that the oracle is at least a digit stronger than the measurement.

**Outcome:** (2,1,3) at sigma=8, t=80, want 4 digits: allowed, delivered 0.59. Shortfall 3.41 digits. Also sigma=8, t=100, want 4: delivered 1.16. sigma=8, t=60, want 10: delivered 7.53. The guard hands back a value with no correct digits in exactly the failure mode it was written to prevent. Separately, guard.py's own six-rung planted-fault ladder passes clean, because every rung tests only the leading 0.68219 t term: rung 4 checks the sign of the sigma effect (58 > 49) and never its size, and no rung varies the form.

### 17. BROKE IT: Check whether some other guard in the tree already covers this, which would make the finding smaller than 'the rule the core never learned' claims.

**Ran:** grep for the constant and for height-aware precision rules across zeta/, tests/, hunts/ and docs/; read zeta/heatflow.py lines 130-165 and 450-461, zeta/core.py lines 277-322, tests/test_interface_dps_is_honoured.py, hunts/gate5_p6_b/probe.py and hunts/gate5_p6_c/probe.py.

**Outcome:** Partial hit. There is no Epstein guard anywhere, so claim (a) stands. But zeta/heatflow.py line 460 is already the guard the hunt proposes, for H_0: ceil(digits + 2 + _DIGITS_LOST_PER_Z*|z_max|) + 3 with _DIGITS_LOST_PER_Z = pi/8/ln10, live and used, with a docstring that says it over-provisions by 6 to 11 digits on purpose. zeta/core.py line 313 (_eta_workload) carries the same pi/2/ln10 factor and uses the exact log10(1/|Gamma(s)|) instead of a Stirling asymptotic, which is precisely the correction the hunt's sigma term needs. The constant has reached zeta/ twice; what it has not reached is the Epstein evaluator. Also, MISSION.md's 'a constant in a comment is not a guard' understates the prior art: gate5_p6_c/probe.py's dps_for and gate5_p6_b/probe.py's _dps_for are executable rules, not comments, and zeta/epstein.py's find_offline_zero caps count_dps = min(max(20, dps//2+10), dps+_GUARD) height-blind, which is a live consumer of the defect.

## Corrections required

- Claim (b)'s formula is wrong. L(sigma,t) = 0.68219 t - (sigma-1/2) log10 t - 0.399 is missing three terms. The correct statement, with nothing fitted, is: digits lost = -log10|s| + sigma*log10(pi) - log10|Gamma(s)| - log10|zeta_Q(s)|, which reduces to 0.68219 t - (sigma-1/2) log10 t - 0.399 - log10 t + sigma*log10(pi) - log10|zeta_Q(s)| after Stirling. law.py's derivation writes '- log10 t + log10 t' and cancels the first of these against a term with no stated origin; the measured intermediates show |1/s| is the largest quantity formed at every height, so the -log10 t is real.
- law.py's docstring must stop saying the sigma term 'is the reason the critical line is the worst case: at sigma = 1/2 it vanishes'. Measured at sigma = 1/2 against an exact oracle (zeta_{(1,0,1)} = 4 zeta beta, class number 1 at D = -4), the law's residual is +4.66 digits. The critical line is still the worst case at large t, but the law over-provisions it by about 4.7 digits while under-provisioning sigma = 8 by up to 3.5, an 8.2-digit swing the surface could not see because every cell in it is at Re s = 5.
- Claim (c) must be restricted to Re s = 5 or withdrawn. On the hunt's own cells, restricted to 1 < correct_digits < 14 so neither end can matter, the residual is rms 0.917 with per-form means +0.848, -0.667, +1.156. That is 1.82 digits of deterministic form dependence in a law with no form term, and the reported whole-sample mean of +0.19 exists only because the two largest biases have opposite signs. The MISSION's own kill condition ('the fitted law's residual exceeds a decimal digit on the cells that test it') is met as soon as the cells are not all on one vertical line.
- The dps + 20 half of claim (b) is correct as a statement about mp.dps and must not be corrected, but it is not the epsilon the caller receives. mpmath's dps_to_prec buys 0.87 to 1.15 extra decimal digits. That, not 'the largest quantity formed is a little smaller than 1/t', is the uniform +1.068 offset docs/37 reports: substituting the exact largest term |1/s| for 1/t moves the mean by 0.002 digits, substituting prec*log10(2) for dps+20 moves it from +1.086 to +0.086.
- law.py's comment that the per-cell ceiling is 'a property of the ORACLE at each (form, height), set by where the lattice sum was truncated' is false and must be fixed. probe.py computes the relative error outside any workdps block, so mp.mpc(got) rounds the routine's answer to 53 bits first. The oracle at qmax=20000 is good to 18.3 to 19.5 digits and the printed ceiling is 16 to 17.6. Fixing the comparison changes which cells count as saturated and what the prediction is capped at.
- from_log.py's premise is false against the artifacts in the directory and the file is now destructive. surface.log is complete (120 cells, 40 per form, three forms) and its last line is the probe's own success message; surface.json is the probe's own full-precision output merged with 38 boundary cells, with matching per-cell timings on all 120. Running from_log.py would overwrite 158 ten-field rows with 120 six-field rows rounded to four significant figures. Either delete it or make it refuse when surface.json is newer and richer than the log.
- guard.py must not be presented as a rule that refuses rather than returning noise until it can see the form and the correct sigma term. guarded_epstein_zeta((2,1,3), 8+80i, dps=required_dps(8,80,4), want_digits=4) is allowed and returns 0.59 correct digits. Its planted-fault ladder passes all six rungs while this is true, so the ladder needs a rung that varies the form at fixed (sigma, t) and a rung that checks the size of the sigma effect against an oracle rather than its sign.
- MISSION.md's framing of the prior art is too thin. hunts/gate5_p6_b/probe.py (EPSTEIN_LOSS_PER_T, _dps_for) and hunts/gate5_p6_c/probe.py (GUARD_PER_UNIT_HEIGHT, dps_for) both carry the constant as an executable precision rule, not a comment. More important for the title: zeta/heatflow.py line 460 already implements exactly this guard for H_0 using pi/8/ln10, live and used, and zeta/core.py's _eta_workload carries pi/2/ln10 and uses the exact log10(1/|Gamma(s)|) rather than a Stirling fit. The core has learned this rule twice; it has not learned the Epstein instance.
- probe.py's module docstring says 'at Re s = 3 the defining lattice sum converges absolutely' while its default and every artifact use sigma = 5, and probe.py records "digits_available": dps + 10 with the comment # zeta.epstein._GUARD in all 158 rows of surface.json, contradicting law.py's correct dps + 20.
- The truncation bound should be described as measured and extrapolated rather than as a bound. K = N(qmax)/qmax is measured at one point and used as an upper bound for N(x)/x at all x > qmax; since N(x) = Cx + O(sqrt x) that is not guaranteed. It holds in every cell I checked, by 10x to 400x, helped by an extra factor of sigma over the sharp Abel result K*Q^(1-sigma)/(sigma-1).

## Sentences the audit called overclaims

- 'the digits lost are L(sigma, t) = 0.68219 t - (sigma - 1/2) log10 t - 0.399'. Presented as derived rather than fitted, and the derivation is shown in law.py's docstring. That derivation contains a step, '- log10 t + log10 t', that cancels a real term against nothing, and it drops sigma*log10(pi) and log10|zeta_Q(s)| entirely. The formula is correct only near Re s = 5 and only up to a form-dependent constant of 1.8 digits.
- 'the sigma term is the part that decides whether a rule derived on one vertical line transfers to another'. Correct as a diagnosis, and then the hunt tested only one vertical line. Every cell in surface.json and boundary.json is at sigma = 5. The first genuine transfer test, sigma = 3 and 8 with the lattice oracle and sigma = 1/2 with 4 zeta beta, puts the law between +4.66 and -3.51.
- 'residual observed - predicted: mean +0.13, rms 0.86' read as evidence the mechanism is the one claimed. The mean is +0.13 because +0.85 and -0.67 cancel across forms, and the rms is computed over cells selected by a ceiling that is float64 rounding in the probe's own comparison.
- 'the critical line is the worst case: at sigma = 1/2 it vanishes'. The conclusion survives at large t but for a different reason, and the size is wrong by 4.7 digits, which is the number a guard would act on.
- 'A guard that fires. A rule stated as code, with the planted faults that make it fire, so it is not another constant in a comment.' The guard fires on the leading term, which was already right. On the terms this hunt added it does not fire when it should: it allows a call promising 4 digits and delivering 0.59.
- 'The rule the core never learned' (docs/37 title) and MISSION.md's 'None of that reached zeta/epstein.py'. The second is true. The first is not: zeta/heatflow.py line 460 is the same guard for H_0 with pi/8/ln10, and zeta/core.py's _eta_workload carries pi/2/ln10 and does the Gamma term better than this hunt does, by evaluating it instead of approximating it.
- from_log.py's 'the run that produced this surface was stopped by its own wall clock partway through the third form' and 'so it is obvious that the third form is partial'. The log has all 40 cells of the third form and ends with the probe's own '-> artifacts/surface.json'.
- docs/37's 'the model assumed the largest quantity formed is exactly 1/t, it is a little smaller, and the routine carries about one digit more than the bound says', offered as the explanation of the residual +1.068. Using the exact largest term changes the mean by 0.002 digits. The offset is mpmath's dps-to-prec rounding, 0.87 to 1.15 digits, which tracks the residual dps by dps.
