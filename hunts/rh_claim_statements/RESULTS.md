# Results: the readable statements of the claimed RH archive, tested

Hunt #162, 2026-11-20. Exploratory. Nothing here is a result about the
Riemann hypothesis, and nothing here is evidence for or against the archive's
main claim.

## 0. Outcome

**No statement failed.** 79 intermediate statements of the Alpoge archive that
are written in Mathlib's vocabulary were transcribed with Lean's conventions
made explicit and tested by exact arithmetic or Arb ball arithmetic. All 79
hold in the sense of their grade: 10 by a complete enclosure-carrying cover of
the stated domain (each resting on one cited classical bound where the domain
is not compact), 15 exactly on a finite domain, 54 measured (51 on a stated
range of an unbounded domain; the limit C12 and the identities C11 and C79 to
a stated width).
These counts are after the review of section 11, which regraded C11 and C79
from exact to measured and C17 from measured to complete cover. Each statement has at least one mutant, the
same statement with one constant, one hypothesis or one inequality changed
so that it is false; all 98 mutants were rejected, each with a witness. The
stop rule of `MISSION.md` was not triggered.

What this is worth, stated before the table:

- A statement that is false as Lean reads it cannot be accepted by a kernel,
  so each of these was a chance to refute the archive cheaply. None did.
- A true lemma says nothing about the proof that uses it. Every one of the 79
  is a classical or elementary fact, or an explicit finite computation. None
  has the strength of the main claim. The archive's strength enters through
  `def ... : Prop` layers with archive-local names, which this hunt does not
  read (section 10).
- About a quarter of the statements (17 of the 68 that are not explicit
  primes) have constants so loose that their survival carries almost no
  information (section 5). The useful ones are the sharp
  ones (section 4), and there the test has teeth only to the measured
  resolution listed in section 4 (for the C15 strip edge, about 0.03).
- The archive has not been checked by any kernel. Every sentence below about
  it means "the archive states".

## 1. Which statements, and how they were read

**Selection.** Two readers scanned the archive this morning for statements
with explicit constants in plain vocabulary (their notes list about 100
candidates out of about 819,000 theorem and lemma statements, pre-tested
with floats on one route). This hunt took the 79 that (a) are stated with
Mathlib identifiers only, or with one short archive-local definition that
could be quoted and unfolded (4 claims), and (b) have a conclusion that a
computation can contradict. Preference went to zeta, Gamma and L-functions
(21), primes (24, of which 11 are explicit primality statements), finite
fields (11) and sharp arithmetic or real inequalities (23). Left out, with
the reason: statements conditional on an archive `Prop` (`zeta_right`,
`L_right`), statements with an existential constant or an eventual
quantifier (the zero-free regions, `badBound_numbers`), `def ... : Prop`
nodes for which the readers found no assertion (`FermatCount`), statements about objects whose
definition was not read (`log_rd`, `cS_approx`), two measure-theoretic
integrals, and weaker duplicates of statements that are in.

**Reading.** For every claim `claims.json` records:

- the archive path and line, the verbatim statement from the declaration
  keyword to the first top-level `:=`, its sha256 and the file's sha256;
- the namespace, every `open`, `variable` and notation line in force at that
  line, and every global (non-local, non-scoped) instance declared earlier in
  the same file (added after review: C19 has `instance : Fact (Nat.Prime 7)`
  at `CfunOmStatements.lean:110`, which `legendreCharacter 7` needs; C37 has
  two instances on the archive-local fields `KQ d`; an instance of a `Prop`
  cannot change a statement's meaning, and the other two touch no type in C37);
- every identifier of the statement, resolved to the Mathlib file and line
  that defines it at the pinned revision (75 distinct definition sites), to
  Lean core, or to an archive-local definition quoted with its path and line;
- the transcription into ordinary mathematics, the list of Lean conventions
  the transcription depends on, and the quantifier range.

`build_ledger.py` stops if any identifier of a statement is neither bound in
the statement nor resolved. Three text-level scans support the resolution:

1. Capture. For every identifier written in a statement, every archive
   declaration whose full name ends in it (666 declarations for the 77 names
   in play) is checked against the statement's namespace, its prefixes and its
   opened namespaces. No archive declaration can capture a Mathlib identifier
   in any of the 79 statements. The only hits are the four quoted local
   definitions (`legendreCharacter`, `Fbar`, `sigNOK`, `sigE`).
2. Notation. The archive has 33 top-level notation-family lines: 22 tactic
   macros, 4 `elab` (2 tactic, 2 command), 5 `run_cmd`, 2 `open ... renaming`.
   None is term-level notation, so no global notation can change how a
   statement parses. No `local` or `scoped` notation, local instance or
   `autoImplicit` option precedes any of the 79 statements in its file.
   Scoped instances reachable through an opened namespace exist for four
   claims (C37, C38, C39, C52); they are instances on archive-local types
   (module structures, topologies on adele rings) and touch no type in those
   statements.
3. Auto-bound variables. The lakefile sets `autoImplicit = false` and
   `relaxedAutoImplicit = false`, so a misspelt identifier in a statement is
   an error, not a silently introduced variable.

Two questions the morning's readers left open are settled by the Mathlib
source: `riemannZeta₁` is Mathlib's (the entire function `(s - 1) zeta(s)`,
`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:536`), and `Nat.primesLE` is
Mathlib's (`Mathlib/NumberTheory/PrimeCounting.lean:132`).

**Limit of the reading.** It is one reading, at text level. Lean's elaborator
was not run, so coercions and instance choices (which power operation, which
cast) are inferred, not observed. A second, independent reading is owed only
on a failure, and there was none. The review's reading attacker made one
anyway, at text level, for all 79 (section 11) and found no transcription
error; it is a second reading by text, not by an elaborator. The kernel
replay, owned by another session and pending, is the real second reading.

## 2. Grades

- **complete cover**: every point of the stated domain is covered. On a
  compact part by Arb enclosures (Taylor models with a rigorous remainder, or
  sign enclosures by bisection); where the domain is not compact, by one named
  classical bound for the rest, cited in the claim's `route` (the Euler-product
  floor for C07 and C17, the Dirichlet series for C09, the reflection formula
  for C14, the integral tail for C28, monotonicity of t^E e^-t for C72 and
  C73). The grade is earned by the test, not set by the ledger: the test must
  return `tail_covered` True with a `cover_basis`, and `runner.py` downgrades
  anything else to measured (added after review; before it, only C07 reported
  its tail). This is the hardened rung of the lab's ladder for the statement
  itself, given that Arb's enclosures and the cited classical bound are
  correct; it is not a kernel check.
- **exact, finite**: the stated domain is finite and every instance was
  decided, by exact integer or rational arithmetic or by an Arb enclosure of a
  strict inequality.
- **measured on a range**: the stated domain is unbounded (or a limit, or an
  identity in a real variable, or an identity between real numbers). The test
  is exact, or a complete Arb cover, or Arb at sample points, on the range
  written in the claim's `tested_range`. A finite range is never the
  statement. The two value identities C11 (zeta(6) = pi^6/945) and C79 (the
  HasSum for pi^2/6) are here: a partial-sum bracket of width 1.6e-20 or 1e-12
  cannot decide an identity, and their exact rational coefficient holds only
  given Euler's formula for zeta at even integers, which is the archive's own
  proof step (`riemannZeta_two_mul_nat`, `hasSum_zeta_two`), so it is not an
  independent check.

## 3. The table

`margin` is the distance from failing (a ratio margin `1 - sup(LHS/RHS)` for
bounds with a multiplicative constant, the smallest gap otherwise; 0 means
equality is attained). `slack` is how far the stated constant is from the
tightest one the test would still accept on the tested domain: a ratio
(an interval when it comes from a branch-and-bound enclosure), or an additive
gap where the ledger says so. Both are produced by `report.py` from
`results.json`.

| id | statement (archive name) | where | grade | cases | margin | slack | mutants rejected |
|---|---|---|---|---|---|---|---|
| C01 | `zeta_norm_le_on_circle` | BqGrowth.lean:29 | complete cover | 264 | 0.8957 | [9.586, 9.587] | 1/1 |
| C02 | `re_ge_and_norm_zeta_le_of_near_eleven_tenths` | ZetaLogDerivLandauBound.lean:22 | measured on a range | 6486 | 0.9601 | [25.04, 25.34] | 2/2 |
| C03 | `zeta_log_deriv_landau_bound` | ZetaLogDerivLandauBound.lean:57 | measured on a range | 5432 | 0.9997 | [3842, 3995] | 2/2 |
| C04 | `zeta_one_sub_le` | LGrowthZeta.lean:12 | measured on a range | 8306 | 0.978 | [45.54, 45.69] | 2/2 |
| C05 | `norm_zeta_sub_le` | DifferentiableAtFractInt.lean:121 | measured on a range | 25610 | 0.5 | [2, 2.005] | 1/1 |
| C06 | `norm_zeta_sub_sum_le` | NormRiemannZetaSubPartialSumLe.lean:103 | measured on a range | 12422 | 0.4987 | [1.995, 2.002] | 1/1 |
| C07 | `le_norm_zeta₁` | LogDerivRiemannZetaLocalZeroSum.lean:74 | complete cover | 2014 | 0.8723 | [7.831, 7.837] | 1/1 |
| C08 | `riemannZeta_ne_zero_of_mem_Ioo` | RiemannZetaNeZeroOfMemIoo.lean:150 | complete cover | 4908 | 0.4999 | - | 1/1 |
| C09 | `no_real_zero` | RiemannZetaNeZeroOfMemIoo.lean:256 | complete cover | 4983 | 0 | - | 1/1 |
| C10 | `zeta_neg_odd_ne_zero` | RHofHalfPlane.lean:9 | measured on a range | 3001 | 0.003968 | - | 1/1 |
| C11 | `riemannZeta_six` | JInvariant.lean:45 | measured on a range | 2000 | 0 | 1 | 1/1 |
| C12 | `zeta_logderiv_limit` | PsiZeroIntegral.lean:216 | measured on a range | 20 | 1.875e-17 | - | 1/1 |
| C13 | `norm_sq_Gamma_half` | LGrowthGamma.lean:28 | measured on a range | 9 | 0 | 1 | 1/1 |
| C14 | `half_line` | LGrowthGamma.lean:45 | complete cover | 5488 | 0.1645 | 1.197 | 1/1 |
| C15 | `Gamma_decay` | LGrowthGamma.lean:222 | measured on a range | 6094 | 0.1662 | [1.199, 1.2] | 2/2 |
| C16 | `lfunction_one_lower_bound` | LfunctionOneLowerBound.lean:34 | measured on a range | 8394 | 47.37 | 48.37 | 1/1 |
| C17 | `dhl_inv` | PNTDHLocalB.lean:66 | complete cover | 14602 | 0.3757 | [1.602, 1.602] | 2/2 |
| C18 | `norm_L_one_sub_le` | LGrowthFE.lean:49 | measured on a range | 1511 | 0.9781 | 45.56 | 1/1 |
| C19 | `LFunction_legendreCharacter_seven_one_ne_zero` | CfunOmStatements.lean:128 | exact, finite | 3 | 1.187 | - | 1/1 |
| C20 | `mult_zero_of_even` | LStructB.lean:150 | measured on a range | 600 | 0.4812 | - | 1/1 |
| C21 | `small_nat` | CountSuccLe.lean:93 | exact, finite | 131071 | 0.004941 | 1.004 | 1/1 |
| C22 | `three_mul_primeCounting_le` | InvFiveLogLeSumInvPrimes.lean:121 | measured on a range | 9999995 | 4 | 4 | 1/1 |
| C23 | `primeCounting_le` | IRRPrimeRecipSum.lean:186 | measured on a range | 9999995 | 4 | 4 | 1/1 |
| C24 | `centralBinom_le_pow_primeCounting` | InvFiveLogLeSumInvPrimes.lean:129 | measured on a range | 3998 | 5 | - | 1/1 |
| C25 | `inv_five_log_le_sum_inv_primes` | InvFiveLogLeSumInvPrimes.lean:303 | measured on a range | 9999901 | 1.94 | 2.94 | 2/2 |
| C26 | `mertens_upper_psi_bound` | mertensUpper.lean:31 | measured on a range | 2000000 | 1.659 | 2.238 | 1/1 |
| C27 | `mertens_upper_nat` | mertensUpper.lean:72 | measured on a range | 2000000 | 2 | 2 | 1/1 |
| C28 | `prime_sum_le` | PlaceSumSquares.lean:261 | complete cover | 10000000 | 0.006407 | [1.013, 1.013] | 1/1 |
| C29 | `primeLogSum_small` | PrimeLogSum.lean:229 | exact, finite | 1 | 0.08399 | 1.116 | 1/1 |
| C30 | `sum_log_primes_le_mul_log_four` | SPsqLe.lean:10 | measured on a range | 2000001 | 0.3867 | 1.387 | 1/1 |
| C31 | `sum_div_mul_log_le_log_factorial` | PrimeSum.lean:22 | measured on a range | 5001 | 0 | 1 | 2/2 |
| C32 | `foundations_prime_fact_ter` | FoundationsPrimeFact.lean:43 | exact, finite | 1 | - | - | 1/1 |
| C33 | `prime_128860109809` | FoundationsPrimeFact.lean:47 | exact, finite | 1 | - | - | 1/1 |
| C34 | `foundations_prime_fact` | FoundationsPrimeFact.lean:51 | exact, finite | 1 | - | - | 1/1 |
| C35 | `foundations_prime_fact_bis` | FoundationsPrimeFact.lean:55 | exact, finite | 1 | - | - | 1/1 |
| C36 | `siteGood_prime_torsion` | FoundationsPrimeFact.lean:59 | exact, finite | 1 | - | - | 1/1 |
| C37 | `siteGood_prime_torsion` | BaseInst.lean:329 | exact, finite | 1 | - | - | 1/1 |
| C38 | `prime_fourteen_billion_example` | ColFormsInst.lean:26 | exact, finite | 1 | - | - | 1/1 |
| C39 | `prime_seven_hundred_trillion_example` | NonDeg.lean:600 | exact, finite | 1 | - | - | 1/1 |
| C40 | `gA_prime` | Primes.lean:86 | exact, finite | 1 | - | - | 1/1 |
| C41 | `gB_prime` | Primes.lean:155 | exact, finite | 1 | - | - | 1/1 |
| C42 | `prime_large` | Primes.lean:518 | exact, finite | 1 | - | - | 1/1 |
| C43 | `log_abs_eval_one_cyclotomic_eq_vonMangoldt` | RdDiff.lean:9 | measured on a range | 5999 | 0 | 1 | 1/1 |
| C44 | `weight_sum` | RdArith.lean:45 | measured on a range | 29805 | 0 | 1 | 1/1 |
| C45 | `sq_le_totient` | DzDigTot.lean:90 | measured on a range | 9999999 | 0 | 1 | 2/2 |
| C46 | `two_n_N_lt` | DzDigTot.lean:121 | measured on a range | 151852 | 3 | 4.923 | 1/1 |
| C47 | `le_totient_sq` | IsIntegralOfMulMem.lean:14 | measured on a range | 10000001 | 0 | 1 | 1/1 |
| C48 | `dvd_twelve_of_totient_le_two` | QuadFacts.lean:158 | measured on a range | 10000000 | 0 | 1 | 2/2 |
| C49 | `totient_mul_sigma_pow_le_pow_succ` | ArithmeticLargeSieveOneResidueClassPerPrime.lean:49 | measured on a range | 35000 | 0 | 1 | 2/2 |
| C50 | `sum_inv_le_mul_sum_squarefree_inv_totient` | ArithmeticLargeSieveOneResidueClassPerPrime.lean:78 | measured on a range | 84210 | 0 | 1 | 1/1 |
| C51 | `card_quadric_even` | FiniteFieldQuadraticFormPointCount.lean:108 | measured on a range | 44213 | 0.07692 | 1.083 | 1/1 |
| C52 | `card_quadric_sub_sq_le` | CardQuadricSubSqLe.lean:66 | measured on a range | 126881 | 0.1142 | 1.129 | 1/1 |
| C53 | `sharp` | SharpCount.lean:134 | measured on a range | 40014 | 0 | 1 | 2/2 |
| C54 | `card_herm_norm_eq` | CardSumNormFibres.lean:243 | measured on a range | 70 | 0 | 1 | 1/1 |
| C55 | `card_dot_eq` | CardSumNormFibres.lean:269 | measured on a range | 279 | 0 | 1 | 1/1 |
| C56 | `card_unitary_fin` | CardUnitaryFin.lean:235 | measured on a range | 13 | 0 | 1 | 1/1 |
| C57 | `card_proper_subfield_elements_lt` | CardProperSubfieldElementsLt.lean:67 | measured on a range | 2640 | 0.5 | 1.5 | 1/1 |
| C58 | `hda_card_qc` | HostDensityArith.lean:21 | measured on a range | 4522 | 0 | 1 | 1/1 |
| C59 | `card_pow_eq_one_le_of_isCyclic_units` | CardPowEqOneLeOfIsCyclicUnits.lean:48 | measured on a range | 11700 | 0 | 1 | 1/1 |
| C60 | `card_pow_eq_one_two_pow_le` | CardPowEqOneLeOfIsCyclicUnits.lean:52 | measured on a range | 896 | 0 | 1 | 1/1 |
| C61 | `card_GL_le` | FieldDatumSizeLogDiscriminant.lean:169 | exact, finite | 1 | 16128 | 4.5 | 1/1 |
| C62 | `exp_ge_quad` | LogSumExpBoundHolds.lean:7 | complete cover | 142 | 0 | 1.104 | 2/2 |
| C63 | `classC_const` | ClassC.lean:32 | measured on a range | 10840 | 0 | 1 | 2/2 |
| C64 | `classC_fact` | ClassC.lean:8 | measured on a range | 3001 | 0 | 1 | 1/1 |
| C65 | `thin_ptw` | IntThin.lean:16 | measured on a range | 63 | 0 | 1 | 2/2 |
| C66 | `legendre'` | MeanGam.lean:208 | measured on a range | 1600008 | 0 | 1 | 2/2 |
| C67 | `vchoose_le` | MeanGam.lean:237 | measured on a range | 1092618 | 0 | 1 | 1/1 |
| C68 | `padicValNat_factorial_le_sub_one_div` | LogStep.lean:14 | measured on a range | 1600000 | 0 | 1 | 2/2 |
| C69 | `card_tuples_le` | ClassA.lean:27 | measured on a range | 18000 | 0 | 1 | 2/2 |
| C70 | `sum_min_le_div` | SumMinLeDiv.lean:44 | measured on a range | 35875 | 9.095e-13 | 1 | 2/2 |
| C71 | `harm_le` | LogVandermondeVariationUnbounded.lean:95 | measured on a range | 1000001 | 0 | 1 | 1/1 |
| C72 | `exp_sqrt_le` | GIntegral.lean:44 | complete cover | 11590 | 0.8046 | 5.119 | 1/1 |
| C73 | `exp_neg_le_div_pow_four` | ExpNegLeDivPowFour.lean:290 | complete cover | 11570 | 0.8046 | 5.119 | 1/1 |
| C74 | `nok_exponent` | NokLemmaCVal.lean:40 | measured on a range | 369600 | 0 | 0 | 2/2 |
| C75 | `sigma_exponent_le_real` | ThmEExp.lean:7 | measured on a range | 30800 | 0.25 | 0.25 | 1/1 |
| C76 | `four_padicValNat_le` | LogCoef.lean:19 | measured on a range | 3000000 | 1 | 1 | 1/1 |
| C77 | `coef_nat` | GamDeg.lean:778 | measured on a range | 10200 | 0 | 1 | 1/1 |
| C78 | `altVand` | LevelSum.lean:7 | measured on a range | 15625 | 0 | 1 | 1/1 |
| C79 | `hasSum_inv_succ_sq` | LogRatioLowerBoundOfLogVandermondeGap.lean:7 | measured on a range | 1000000 | 0 | 1 | 1/1 |

Counts by grade: complete cover: 10, exact, finite: 15, measured on a range: 54 (total 79 of 79 hold; failed: none; undecided: none).
Mutants: 98 of 98 rejected. Run time 181.0 s on one core.

By topic and grade:
- zeta: complete cover 4; measured on a range 11
- L: complete cover 2; measured on a range 3; exact, finite 1
- primes: exact, finite 13; measured on a range 10; complete cover 1
- arithmetic: measured on a range 16
- finite_field: measured on a range 10; exact, finite 1
- elementary: complete cover 3; measured on a range 4

## 4. The tightest claims

These are the statements whose constant is close to the sharp one. Whether a
wrong constant would have been caught depends on the test's resolution, which
was measured after review and is listed below the table.

| claim | what is sharp | how close |
|---|---|---|
| C21 `small_nat` | pi(m) log m < 1.26 m below 2^17 | max of pi(m) log m / m is 1.2550587 at m = 113: 0.4 percent |
| C28 `prime_sum_le` | sum over primes of log p / p^2 <= 0.4995 | the series lies in [0.4930910, 0.4930927]: 1.3 percent |
| C53 `sharp` | the quadric count deviates from q^(2M-1) by at most q^(M-1) for s != 0 | equality in all 40,014 cases |
| C51, C52 | quadric counts, weak forms | ratio 12/13 at q = 13, and (16/17)^2 at q = 17: tends to 1 |
| C74 `nok_exponent` | additive constant 7/4 | equality at (l, g, h, j) = (3, 0, 6, 1) |
| C75 `sigma_exponent_le_real` | additive constant 11/4 | 5/2 would hold with equality at (3, 0, 4, 1); 12/5 fails |
| C65 `thin_ptw` | the constant 4 and the exponents 0.61, 0.39 | equality at v = lam = 1; 0.61 + 0.39 = 1 exactly |
| C62 `exp_ge_quad` | coefficient 1/3 on [-1, 1] | 1/e = 0.3679 is the largest admissible; double zero at 0 |
| C14, C15 | Gamma on the line and on the strip | sup is sqrt(2 pi) = 2.5066 against 3; the strip edge 11/2 is exact mathematically, but the test resolves it only to about 0.03 (below) |
| C02 (first conjunct) | radius 3/5 about 11/10 + it gives Re z >= 1/2 | attained |
| C09, C08 | L(sigma, chi_8) != 0 for sigma > 0; zeta != 0 on (0, 1) | L(0, chi_8) = 0 exactly; zeta(-2) = 0 |
| C57 | 2d * (elements of proper subfields) < g^d - 1 for g >= 5 | g = 3, d = 2 gives 8 = 8 |
| C45, C47, C63, C64, C66 to C69, C71, C31, C49, C50, C59, C60 | integer and factorial inequalities | equality attained at the listed points |
| C29 `primeLogSum_small` | one explicit inequality | margin 0.084 on 0.724 |
| C70 `sum_min_le_div` | constant 2 | ratio 1 - 2^-40 on the range, tends to 1 |
| C05, C06 | abs(zeta(s) - partial sum - main term) <= (abs(s)/Re s) M^(-Re s) | sup of the ratio is 1/2 (as s -> 0+), for every M tested |

The identities (C11, C13, C43, C44, C54, C55, C56, C58, C77, C78, C79) are
sharp by nature: a change of a constant larger than the test's bracket or
sample precision is rejected.

**Measured resolution** (`review.py`, `review.json`; each weakened constant
run through the claim's own test at full parameters, C17 at fast parameters;
"true" and "false" are the truth of the weakened statement from the stated
derivation):

| claim | sharp value | rejected (false, witness found) | not rejected |
|---|---|---|---|
| C21 | 1.2550587129 (m = 113) | K = 1.25505871 | K = 1.2550588 holds (true) |
| C01 | 1.4603545 (s = 1/2) | K = 1.460354 | K = 1.460355 undecided (true) |
| C62 | 1/e = 0.36787944 | c = 0.3678795 | c = 0.3678794 holds (true) |
| C07 | 1.30619 (t = 0) | c = 1.3063 | c = 1.306 holds on the cover, tail not covered, so measured (true) |
| C16 | 0.41350 (q = 3) | K = 0.4134 | |
| C70 | 2 (limit) | K = 1.999999 | |
| C74 | 7/4 (equality) | 1.749 | |
| C65 | K = 4; exponents 0.61 + 0.39 = 1 | K = 3.999 | e_rhs = 0.3901 undecided (false): the grid stops at v = e^400, so exponent sharpness rests on the exact reduction, a derivation reviewed only in this hunt |
| C28 | 0.4930911094 (second route, Moebius sum) | K = 0.4930909 | K = 0.4930911 undecided (false); 0.4930920 undecided (true); 0.4930928 holds (true): resolution 1.7e-6, the tail bound |
| C05 | 1/2 (s -> 0+) | | c = 0.4999 and 0.49999 undecided (false): the cover encloses the supremum only in [0.49873, 0.50004] (search tolerance 2e-3), so a false c is rejected only below about 0.4987 |
| C15 | edge 11/2 | edge 6, 5.6, 5.55 | edge 5.52 and 5.51 hold on Im w <= 200 (both false: the ratio is 1.0045 at Im w = 1e4 for 5.52, 1.10 at 1e12 for 5.51) |
| C17 | 16.233 = zeta(26/25)/zeta(52/25) | K = 5/2 | K = 16 holds on the range, floor does not cover, so measured (false); K = 17 complete cover (true) |

No row rejects a true statement. One false statement (C17 with 16) passes at
the measured grade, which is what that grade means: a finite search is silent
beyond its range.

## 5. Claims too loose for a mutant near the stated constant

For these, the nearest mutant the test can reject has its constant at least
a factor 2 away from the archive's (or changes a hypothesis instead). Their
survival carries little information.

| claim | stated | tightest the test accepts | factor |
|---|---|---|---|
| C03 `zeta_log_deriv_landau_bound` | 840 | about 0.22 on 2 <= t <= 200 | about 3900 |
| C16 `lfunction_one_lower_bound` | 20 | 0.4135 (q = 3) | 48 |
| C04 `zeta_one_sub_le` | 6 | 0.1317 (w = 1/2) | 45.5 |
| C18 `norm_L_one_sub_le` | 6 N^5 | 0.1317 (N = 1, w = 1/2) | 45.6 |
| C02 (zeta bound) | 6 | 0.24 on 2 < t <= 200 | 25 |
| C01 `zeta_norm_le_on_circle` | 14 | 1.4604 (s = 1/2) | 9.6 |
| C07 `le_norm_zeta₁` | 1/6 | 1.3062 (t = 0) | 7.8 |
| C72, C73 | 24 | 256/e^4 = 4.689 | 5.1 |
| C46 `two_n_N_lt` | 16 n^2 < p | fails only for p <= 3.25 n^2 | 4.9 |
| C61 `card_GL_le` | 20736 | 4608 | 4.5 |
| C25 `inv_five_log_le_sum_inv_primes` | 5, threshold 100 | 1.70 (N = 226), threshold 8 | 2.9 |
| C26 `mertens_upper_psi_bound` | 3 | 1.341 (N = 5) | 2.2 |
| C27 `mertens_upper_nat` | + 2 | + 0 (N = 1) | additive 2 |
| C22, C23 | + 9 | + 5 (s = 7) | additive 4 |
| C24 `centralBinom_le_pow_primeCounting` | exponent 2n/3 | 2n/30 first fails at n = 48 | not close |

In between: C17 (`dhl_inv`, slack 1.60 against the Euler floor), C30
(`sum_log_primes_le_mul_log_four`, log 4 = 1.386 against 0.99958 on the range,
slack 1.39), C57 (slack 1.5 at g = 5, d = 2) and C76 (the additive 2 could be
3).

C17 left this table at review (section 11). Its true infimum over all
characters and all t is zeta(52/25)/zeta(26/25) = 0.0616034, so the constant
26 is only 1.60 times larger than needed: every constant at least 16.233 gives
a true statement and every constant below it a false one. The first version of
this paragraph said that a mutant with 26 replaced by 17 is false; that was
wrong, a typed sentence that no code produced: 17 times 0.0616 is 1.047, so
the statement with 17 is true. The smallest false integer constant is 16.
The same Euler-product floor (26 times 0.0616 = 1.60 >= 1) covers every
modulus, character and t, so C17 is now a complete cover. The search on the
range is a second route; its smallest value of |L| is 0.318, so it cannot see
a false constant near 16 (section 4). The test rejects 26 -> 5/2, and the
abscissa mutant 26/25 -> 1/2.

Several of these loose statements still have a sharp hypothesis, and the
hypothesis mutant is where their test has teeth: the strip edge in C15
(11/2 -> 6 fails; edges of 5.55 or more are rejected, 5.52 or less pass on
|Im w| <= 200, section 4), the abscissa in C03 (1 -> 49/100 fails at the zero
at height 21.02) and in C17, the interval in C08 (0 -> -3 fails at -2).

## 6. Mutants (the lesion)

98 mutants, 98 rejected. 66 change a constant (or one term of an expression),
20 change a hypothesis and 12 change an inequality (`≤` to `<`, or `<` to `≤`). Each mutant's statement
is the archive's statement with one substring replaced; `claims.json` stores
both, and the fast test checks that the replacement is the only difference.
A rejection needs a witness: a point at which exact arithmetic or an Arb
enclosure contradicts the mutant. A ball that merely fails to prove the
mutant is recorded as undecided, not as a rejection.

One caveat on what the mutants prove. They were chosen after the sharp
constant of each claim had been measured, so they test the instrument (can it
see a violation of this size at this point?), not the archive. For the loose
claims the mutant is far from the stated constant and says correspondingly
little.

The instruments themselves are tested against planted faults in
`test_rh_claim_statements.py`: the Taylor model must enclose point values at
random points of its ball and must refuse a disc that reaches the pole; the
branch and bound must find a planted violation; the Miller-Rabin routine must
catch a strong pseudoprime to four bases; the Lucas routine must refuse an
incomplete factor list.

## 7. What Lean's conventions change

Reading the statements literally matters in a few places. None of these is a
defect of the archive; they are where a tester can go wrong.

- C25 (`inv_five_log_le_sum_inv_primes`): as Lean reads it the inequality is
  true at N = 0 and N = 1 (because `Real.log 0 = Real.log 1 = 0` and
  `1 / 0 = 0`), false for 2 <= N <= 7 and true from N = 8 on. The stated
  threshold 100 is conservative.
- C43: at the excluded value m = 1 the identity would still hold in Lean,
  because Phi_1(1) = 0 and `Real.log 0 = 0 = vonMangoldt 1`.
- C45: at N = 1 the truncated subtraction `2 * 0 - 1` is 0, the right side is
  0 and the statement fails; the hypothesis 2 <= N is needed.
- C06, C26: a big operator's body is parsed at precedence 67, so
  `∑ n ∈ S, a - b` is `(∑ n ∈ S, a) - b`. Both statements rely on it.
- C56: `(-(q : ℝ))⁻¹ ^ j` is `((-q)⁻¹)^j`.
- C74: the third argument of `sigNOK` is natural-number arithmetic (floor
  division) while the bound on the right is real arithmetic; `ℓ` need not be
  prime.
- C18: the hypothesis `χ 0 = 0 ∨ w ≠ 1` excludes w = 1 only for the trivial
  modulus.
- C21: `log` is `Real.log` through `open Real`, and `1.26` is exactly 126/100.
- Hypotheses that are not needed for truth on the tested range: `6 ≤ s` in
  C22, `2 < n` in C24, `5 ≤ p` in C76. Hypotheses that are needed: `k ≠ 0`
  in C68, `m ≠ 1` in C44, `p ≠ 2` in C58, `3 ≤ ℓ` in C74, `5 ≤ g` in C57,
  `s + j ≤ o` in C77.

## 8. Instrument notes

- **Arb on wide balls.** Arb's zeta and Dirichlet L-functions bound their
  partial sums term by term, so on a wide input ball the enclosure is far
  wider than the function's variation there. Measured radii of the real part,
  direct against Taylor model (recomputed by `review.py`, `wide_ball_radii`,
  and pinned by a test): 0.558 against 0.011 on a box of half-width
  0.04 at 1/2 + 3i; 3.13 against 0.088 at 0.2 + 0.1i; 1.21 against 0.096 on a
  box of half-width 0.1 at 0.6 + 14.1i; 0.63 against 0.23 at 1.05 + 0.35i,
  next to the pole, where the function itself varies that much. The remedy is
  a Taylor model at the exact centre of each box with a Cauchy remainder, the
  bound M taken on a circle (maximum principle) covered by 12 small balls;
  `common.taylor_ball` carries the estimate and its hypotheses. With direct
  evaluation the first covers of C02 and C05 did not reach their tolerance in
  400,000 boxes (that version also had two defects in its box logic, so the
  count is not a clean comparison); the covers of the recorded run take 6,486
  and 25,610 boxes.
- **The pole at s = 1.** C05 and C06 are statements about an entire function,
  f_M(s) = zeta(s) - sum_{n<=M} n^-s - M^(1-s)/(s-1). It is evaluated through
  Arb's deflated zeta and (e^u - 1)/u, so the cover includes s = 1 with no
  excision. The ratio of the two sides equals |M^s f_M(s)| Re s / |s|, and
  M^s f_M(s) varies slowly, which is what makes the cover converge for M = 10.
- **Arb's Dirichlet L on a ball containing 0** is undefined at every radius.
  The derivative of L(s, chi_8) near 0 (C09) is therefore taken from one
  Taylor model centred exactly at 0, whose remainder circle stays away from 0.
- **Primality.** PARI's `isprime` is a proof at these sizes: below 2^64 it is
  BPSW, which is exhaustively verified on that range; above, the n - 1 test or
  APRCL. It is not the route of record here. The nine primes below 10^15 are
  also proved by trial division by every prime up to the square root (own
  sieve). The 94-digit and 116-digit primes are proved by an own
  Pocklington-Lucas test from the complete factorisation of n - 1, each prime
  factor of which is below 10^12 and proved by trial division. For the
  116-digit number the factor list `[2, 3, 571, 599, 413718278401,
  603339156001]` is read as data from the archive's proof text
  (`Primes.lean:519`) and verified here to factor n - 1 completely.

## 9. The standing checklist

1. **Rival: not applicable.** The battery of `zeta.epstein.battery` faces a
   structural explanation of RH with functions that share the structure and
   violate RH. Nothing here is an explanation of RH. Each claim is a
   classical statement tested for truth, and the hunt's own reading is that
   survival carries no information about RH. The archive's mechanism, where a
   rival would bite, sits behind `Prop` definitions this hunt does not read.
2. **Decoy.** Does a neighbour with no arithmetic in it pass the same test?
   Three were run (`decoys.py`, recorded in `results.json`):
   - C08's shape for the Hurwitz zeta function: zeta(sigma, a) != 0 on (0, 1)
     is rejected for a = 1/4 (a zero in [0.61047, 0.61084]) and a = 1/3 (a
     zero in [0.43103, 0.43140]) and accepted for a = 2/3 and 3/4. The test is
     not vacuous on zeta-like functions.
   - C16's shape for random periodic sequences of +1 and -1 with zero mean:
     about half of 2,000 samples per period have L(1, a) < 0. The lower bound
     is a statement about characters, although its constant is loose.
   - C21's shape for Cramer random sets of density 1/log n: 97.5 percent of
     200 samples violate pi(m) log m < 1.26 m somewhere below 2^17 (49.5
     percent do so beyond m = 1000; the median of the maximal ratio is 1.66).
     The constant 1.26 is specific to the actual primes.
   For the loose claims of section 5 no decoy was run, and a density-matched
   null would be expected to pass them: they carry no arithmetic.
3. **Lesion.** The mutants of section 6: 98 of 98 rejected, each with a
   witness, plus the planted faults in the instruments.
4. **Precision response.** The 36 claims whose test uses Arb were rerun with every
   working precision doubled (`results_prec2.json`; 4 min 57 s first, 3 min
   47 s for the post-review rerun). No verdict changed. The deltas below are
   printed by `review.py` (`precision_deltas`). Every branch-and-bound enclosure of a supremum at 128 bits
   intersects the one at 64 bits: the lower ends, which are point values,
   agree to 16 digits, and the upper ends move by at most 1.9e-4 (C06), inside
   the search tolerance 2e-3. The margins that are not such enclosures move by
   at most 3.1e-5 (C17's margin on its search range, search tolerance 5e-3;
   its graded margin comes from the Euler floor) and 2e-7 (C08, an adaptive
   lower bound). The quantities in the table are margins of inequalities, not
   artifacts of 64-bit rounding: they do not respond to precision because
   there is no approximation in them to improve, and the test would have
   shown it if there were.

## 10. Not done, and limits

- The proofs in the archive were not read, and nothing was elaborated or
  replayed. A separate session owns the replay.
- 54 of the 79 statements are measured: 51 on a range of an unbounded
  domain, the limit C12 and the identities C11 and C79. For the zeta and Gamma bounds the ranges stop at |Im| <= 100 or 200.
- The statements that carry the strength of the main claim are not in this
  family. The readers' notes locate them behind definitions such as
  `UpperTheory.EveryCharacter` and the `Row0b` and `IsRecT` layers. A content
  scan on Mathlib identifiers cannot see where the strength enters.
- The quadric counts (C51 to C53) were enumerated over prime fields only.
- C12 is a limit and C13 an identity in a real variable: enclosures cannot
  decide either; they are measured. C11 and C79, identities between real
  numbers, are measured for the same reason (section 2).
- Shared inputs: the route of a claim names any classical theorem it rests on
  that the archive's proof also uses. C11 and C79 (Euler's formula), C14 (the
  reflection formula, `Complex.Gamma_mul_Gamma_one_sub`, used by the archive at
  `LGrowthGamma.lean:35`), and C04 (the functional equation, which the
  archive's proof also goes through; only 20 literal points avoid it). These
  are theorems of Mathlib, so no shared numerical failure follows, but the
  check is not independent of the archive's mathematics at that step.
- The only second reading of the Lean text is the reviewer's, at text level
  (sections 1 and 11); nothing was elaborated.
- Statements conditional on archive hypotheses, existential constants and the
  two integral identities in the readers' notes were not tested.

## 11. Review findings and dispositions

Two attackers reviewed this hunt on 2026-11-20, one on the reading (does the
transcription match the archive's Lean text?), one on the numerics. Both
returned "holds": neither found a transcription error, a wrong verdict or a
statement that fails. The reading attacker independently re-verified all 79
verbatim statements and file hashes (0 mismatches), the import cone, all 75
Mathlib definition sites and the absence of shadowing. The numerics attacker
reran the full runner (79 of 79 hold, 98 of 98 mutants rejected) and
reimplemented 25 claims with mpmath, PARI and sympy, with agreement
throughout. Every finding was reproduced here before it was disposed of. No
statement fails as Lean reads it after the changes, so the stop rule was not
triggered. Each finding, and what was done:

| # | from | severity | finding | reproduced? | disposition |
|---|---|---|---|---|---|
| R1 | reading | minor | C11 and C79 graded exact, finite, but neither has a finite domain; the exact step (Euler's formula) is the archive's own proof step, and a bracket cannot decide an identity | yes: `JInvariant.lean:46` uses `riemannZeta_two_mul_nat`, `LogRatioLowerBoundOfLogVandermondeGap.lean:8` uses `hasSum_zeta_two` | **fixed**: both regraded to measured (domain "identity"); routes name the shared input; counts now 15 exact and 54 measured (sections 0, 2, 3, `MISSION.md`) |
| R2 | reading | minor | complete-cover grades were set by the ledger: the runner downgraded only on `tail_covered` False, and only C07 reported it | yes: the other eight complete covers had `tail_covered` None | **fixed**: every complete-cover test now returns `tail_covered` and a `cover_basis`; `runner.py` downgrades anything but True; a test plants a silent check and sees the downgrade. No grade changed from this (all ten tails hold) |
| R3 | reading | minor | `MISSION.md`'s "a route that shares nothing with the archive" overstates independence for C04, C11, C14, C79 | yes: `LGrowthGamma.lean:35` (reflection formula), `LGrowthZeta.lean:15` (via the functional equation) | **fixed**: the sentence is softened; each route names its shared classical input; section 10 lists them |
| R4 | reading | minor | C19 needs the file-level `instance : Fact (Nat.Prime 7)` (`CfunOmStatements.lean:110`), which the context record omitted | yes | **fixed**: `build_ledger.py` records global instances in force; C19 and C37 have entries; harmless (an instance of a `Prop`, and archive-local types for C37); a test pins C19's |
| R5 | numerics | major | section 5 said the C17 mutant with 26 replaced by 17 is false; it is true (17 times 0.0616 = 1.047) | yes: Arb at 128 bits, `review.json` `c17_floor`; 16 times the floor is 0.986 | **fixed**: the sentence is corrected in place with the error stated (section 5); the smallest false integer constant is 16. The suggested upgrade was taken: the Euler floor covers every M, psi and t, so C17 is a complete cover (counts now 10 complete covers) |
| R6 | numerics | major | section 4 listed C15's strip edge as a constant "that would have been caught"; the test accepts false edges 5.52 and 5.51 | yes: `review.json` `c15_edge`; the ratio is 1.0045 at Im w = 1e4 for 5.52 and 1.10 at 1e12 for 5.51 (Arb lower bounds) | **fixed**: section 4 no longer says it would have been caught; the measured resolution (rejects 5.55 and up, passes 5.52 and below on Im w <= 200) is stated in sections 4 and 5 and in the doors |
| R7 | numerics | minor | the rejection resolution of the sharp claims was not stated; C05, C28 and C65 are coarse | yes: all twelve weakenings reproduced, plus four more (C17 at 16 and 17, C28 at two more constants) | **fixed**: `review.py` runs 21 weakenings through the hunt's own tests; the resolution table is in section 4; C65's exponent sharpness is attributed to the exact reduction (a derivation reviewed only here); a second route for the C28 series (Moebius sum, 0.4930911094) labels its rows |
| R8 | numerics | minor | the C14 complete cover rests beyond abs(t) = 200 on the reflection formula, which C13 grades only as sampled | yes | **fixed in wording**: C14's route cites the reflection formula as a theorem (Mathlib `Complex.Gamma_mul_Gamma_one_sub`) and notes that C13 is graded only as sampled; C07 and C17 cite the Euler-product floor, C09 the Dirichlet series. The grade stays complete cover, on the stated condition that the cited classical bound is correct (section 2) |
| R9 | numerics | minor | numbers in sections 8 and 9 were produced by no code | yes: reproduced 0.5585/0.0108, 3.128/0.0878, 1.212/0.0964, 0.628/0.227 and 1.894e-4, 3.113e-5 | **fixed**: `review.py` prints them into `review.json`; a test recomputes both from code and the two result files |
| R10 | numerics | minor | `RUNS.md` named an absolute machine-local path; the runner docstring wrote an absolute temporary path; the precision run had no estimate | yes | **fixed**: paths are relative or `SCRATCH`; the missing estimate is recorded as missing, and the post-review runs carry their estimates (`RUNS.md`) |

What the review changed in the outcome: the grade counts (9, 17, 53 became 10,
15, 54), one wrong sentence (C17) and one overstated one (C15), and the
statement of what the sharp tests can see. What it did not change: no
verdict, no margin outside its enclosure, no mutant. The post-review full run
and precision run reproduce every verdict of the first (`RUNS.md`).

## The doors

This hunt measures a ceiling of a modest kind: the falsification power of
"test the readable statements". What binds it, what was frozen, and what
would need more information.

**1. Active constraints, ranked by how much each limits the power.**

1. The family itself. About 80 of about 819,000 statements are readable in
   plain vocabulary with a refutable conclusion, and all of them are
   classical. Testing more of the same kind of statement adds little.
2. Looseness. 17 of the 68 statements that are not explicit primes have a
   constant at least a factor 2 from what the test would accept (section 5).
   A false proof that states loose true lemmas is invisible here.
3. Ranges. For the 54 measured statements the test is silent
   beyond its range. This binds least: the constants that are sharp are sharp
   at small arguments (m = 113, N = 226, s = 1/2, N = 2), not at infinity.

**2. Frozen constants.** Each was chosen, not optimised.

| constant | value | relaxing it trades |
|---|---|---|
| heights for zeta, Gamma covers | 200 (C02, C03, C07, C14, C15), 100 (C04, C05), 40 (C06, C17) | time, linearly; no claim is tight at large height except C15, whose ratio is still rising at 200 (0.8337 against the limit 0.8355); the height also sets C15's edge resolution (about 0.03 at 200), a **real trade** |
| sieve ranges | 10^7 for pi, phi, omega; 2*10^6 for psi, theta | memory (about 0.5 GB at 10^7) |
| branch-and-bound tolerance | 1e-5 to 2e-3 by claim | resolution of the sharp constant; a mutant inside the tolerance is not rejected |
| Taylor order and circle | order 6 to 10, radius max(6 r, 0.05), 12 arcs | cost per box against box size; order is capped at 10 by python-flint's series cap |
| working precision | 64 bits for covers, 128 or 256 for point comparisons | nothing found to trade (section 9, item 4) |
| sample grids | C18 (9 points per character), C65 (63 points), C70, C74 | these four are samples, not covers: **real trade**, a cover would raise their grade |
| moduli and fields | q <= 2000 (C16), M <= 16 (C17), conductors <= 30 (C18), 80 (C20); prime fields q <= 17 | time; C17's true infimum is out of reach of a search at any affordable size, and its grade now rests on the Euler floor instead |
| the mutants | one or two per claim, chosen after the sharp constant was measured | **real trade**: a blind mutant protocol (mutants fixed before the run) would test the transcriptions as well as the instrument |
| the selection | 79 of about 100 candidates | the excluded conditional and existential statements need a different instrument |

**3. Information class.** Everything above stays inside the data this family
reads: statements whose identifiers are Mathlib's. The next door is outside
it: unfolding the archive's `Prop` layers until the hypotheses of its final
theorems are expressed in Mathlib's vocabulary, and testing those. That
requires reading definitions this hunt deliberately did not read, and it is
where a false statement, if there is one, would have to be. Candidate: the
definitions named in the readers' notes; range: unknown; proof status: none.
Allocation is the owner's decision.
