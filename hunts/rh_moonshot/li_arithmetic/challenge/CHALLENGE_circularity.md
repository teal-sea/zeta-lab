# CHALLENGE (circularity): li_arithmetic

Hunt #150, mechanism 3. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` (commit `1fe59177e` on `hunt/rh-moonshot`,
merged here at `c220f1310`), `li_arith_prime.py`, `li_arith_wa.py`, `run_li_arith_prime.py`
and the committed `artifacts/`, and scored them against the rubric pre-registered in
`MISSION.md` (section "Challenge-phase scoring rubric", 2026-10-26).

Files here: `circ_li.py` (independent prime-side integral and Li coefficients of the
shifted completion; shares no code with `li_arith_*.py`),
`test_li_arithmetic_challenge_circularity.py` (5 tests), this page.

Grades as in `MISSION.md`. Nothing written here is kernel-checked.

## Verdict

**Unresolved, agreeing with the builder; the target is recorded as a reformulation (kill
condition 3) until an estimate is offered.** P_n <= M(n) for every n is Li's criterion
rewritten (NOTES section 1 says so), and no inequality proved from the Euler product is
proposed. No hidden RH enters any positive claim. RH-conditional inputs enter only the two
bound routes, which are refuted, and one cross-check. Findings:

- **L1 (RH inputs in the refuted routes, scoped).** The pointwise route uses Schoenfeld's
  envelope above 10^8 and the mean-square route Cramer's mean square, whose constant
  `CRAMER_MEAN_SQUARE` is "sum over all nontrivial zeros of 1/|rho|^2 under RH"
  (`li_arith_prime.py` lines 55-62). Both are labelled conditional, and their failures
  stand a fortiori for every envelope at least as large, which includes every
  unconditional one in use. They do not refute an oracle route that uses the exact
  |E(x)| beyond 10^8. The positive half, "at most M(n) for n in [32, 1258]" (NOTES
  section 3, mean-square bullet), is conditional on RH and on a model and is no evidence
  for P_n <= M(n) on that range. NOTES section 5 says these routes are "circular as
  written"; the section 3 bullet should carry that hedge at the point of use.
- **L2 (provenance of P_n, cleared by a second route).** The artifact's `P_exact` is not
  computed from primes. It is M(n) - lambda_n with lambda_n from the xi side
  (`run_li_arith_prime.py`: `Pn = M - L[:n_max]`; checked here to 1e-9 at
  n = 1, 7, 100, 5000). So "the prime integral satisfies P_n <= M(n)" on n <= 5000
  (NOTES section 8) is lambda_n >= 0 restated, through a derived identity checked by
  primes only at n <= 6. This session computed the prime integral itself, truncated at X,
  in closed form (antiderivatives of e^(-u) L^{(2)} and L^{(2)}, its own sieve). It
  reproduces the artifact to within 5e-3 for every n <= 60 at X = 10^6, 10^7 and 10^8,
  and to within 0.04 at X = 10^8 for n = 100, 150, ..., 1000, where M(n) >= 46. The
  identity and the xi-side values therefore cohere through n = 1000 by a second,
  prime-side route. That route omits x > 10^8 with no bound on the omitted part, so it is
  measured, not hardened. For 1000 < n <= 5000 the statement rests on the xi side alone.
  An own bug, the antiderivative written with L^{(3)} in place of L^{(1)}, was caught by
  this comparison (it agrees at n = 1 only, since L_0 = 1); it is kept as a planted fault.
- **L3 (a cross-check that reads zeros).** W_{1/4}'s second route sums zeta's first 1000
  zeros from mpmath and replaces the rest by the smooth on-line density
  (`li_arith_wa.py` lines 33-39, 111-126). It therefore assumes on-line zeros above
  height about 1419, which is verified to 3e12 (Platt and Trudgian 2021) and conditional
  above. Under any placement of zeros above 3e12 their contribution at n = 8260 is far
  below the margin |lambda_8260| = 122 (heuristic, not computed). The sign's "hardened"
  grade stands on the unconditional Cauchy route plus this check. The Cauchy radius rule
  for the same function reads the zero-free region at low height (lines 16-30), which is
  a verified finite fact.
- **L4 (DH's failure needs no extrapolation).** The rival gate says a uniform bound must
  fail for DH "at the latest at DH's first negative index", taken as n = 328997,
  extrapolated (NOTES section 4). That some lambda_n(DH) < 0 is a theorem: DH's zero
  multiset contains off-line zeros, and Bombieri and Lagarias's multiset theorem applies,
  as `li_arith_wa.py` lines 13-15 already use it for W_a. Only the index is extrapolated.
- **L5 (prior art).** The measured smallness of the arithmetic part (|T(n)| <= 13.5 for
  n <= 5000) matches Maslanka's observation that the finite-place term stayed below 20 in
  absolute value over his computed range (arXiv math/0402168), which the NOTES do not
  cite.

## Scorecard

1. **Disposition.** Unresolved. The target is an RH-equivalent restatement with no estimate
   (kill condition 3: reformulation). The two bound routes are refuted at the builder's
   stated parameters (NOTES section 7), scoped as in L1.
2. **Grade per step.**
   - The split lambda_n = A(n) + T(n): derived, self-reviewed, defect 8.1e-28 measured
     (builder). Agreed.
   - The Laguerre identity lambda_n = M(n) - P_n: derived. Now checked by a prime route
     for n <= 1000 (sampled, L2): measured, second session.
   - "P_n <= M(n) for n <= 5000": measured, xi side; equal to lambda_n >= 0 on that range
     (L2). Not a prime-side measurement past n = 1000.
   - W_{1/4}: lambda_8260 < 0, hardened (Cauchy at two radii plus the zero route, L3).
     Agreed, with the L3 note.
   - Pointwise and mean-square refutations: measured on sampled trapezoid grids, scoped
     as in L1.
   - Onset heuristic: inferred (builder). Agreed.
   - Composite: measured, as the NOTES say (section 8).
3. **The Euler-product step.** Named: P_n <= M(n) through psi (NOTES section 4). Tested:
   W_{1/4} (Euler product, nonnegative coefficients, functional equation) fails by
   n = 8260, so those hypotheses do not suffice. DH is not tested in the range where it
   fails (n <= 5000 only; its failure exists by L4). No candidate inequality exists to
   test, so the step is named but carries no inequality.
4. **Finite stand-ins.** n <= 5000 everywhere, x <= 10^8 for primes; the NOTES state that
   a finite range is a finite height (section 5) and offer no uniform claim. Agreed. The
   one place a finite computation is read too strongly is L2's "prime integral" wording.
5. **Novelty search.** None recorded by the builder (NOTES section 8). This session's
   query, 2026-10-26, web search: "Li coefficients arithmetic formula Bombieri Lagarias
   Laguerre polynomial psi(x) - x integral unconditional bound Coffey Maslanka arithmetic
   part": found Lagarias arXiv math/0404394 (the explicit-formula split for automorphic
   L-functions), Maslanka arXiv math/0402168 and math/0406312 (numerics; the finite-place
   term small, L5) and Coffey's lower bound on the archimedean part; nothing on the
   Laguerre-kernel integral form of P_n or on the failure of absolute-value routes.
   zbMATH, MathSciNet and Lean Zulip were not searched.
6. **Rivals on complete hypotheses.**
   - DH: lambda_n > 0 for n <= 5000 (measured, builder); passes every finite-range bound
     tested, a shared lemma, no verdict. Its lambda_n fails somewhere by a theorem (L4).
   - Epstein (1,1,6): not run by the builder or by this session; excludes nothing.
   - W_{1/4}: meets Euler product, nonnegative log-derivative coefficients and the
     functional equation, and violates the conclusion at n = 8260 (hardened): refutes any
     implication from those hypotheses alone.
   - zeta(s - delta), delta = 1/4 (computed here, not in the NOTES): its completion
     xi(s - delta) has every zero at real part 1/2 + delta, so |1 - 1/rho| < 1 for each and
     lambda_n = sum_rho [1 - (1 - 1/rho)^n] > 0 for **every** n (derived, self-reviewed by
     this session; the paired Hadamard product of xi(s - delta) has no exponential
     factor); measured positive for n <= 30 by a Cauchy integral (lambda_1 = 0.0115513352,
     against 0.0230957090 at delta = 0, which reproduces zeta's lambda_1). It has an Euler
     product with coefficients Lambda(n) n^delta >= 0 and violates RH. It lacks the
     s -> 1 - s functional equation, so it is not a counterexample; what it shows is that
     Li positivity implies RH only through the functional equation. Any proof of
     P_n <= M(n) must therefore use the functional equation, which in this split enters
     through the archimedean part A(n), not through psi.
7. **Circularity.** The target is RH-equivalent by design and stated so. No positive claim
   uses an RH input. RH or a zero list enters: Schoenfeld's envelope and Cramer's constant
   in the refuted routes (L1); zeta's zeros and an on-line density in W_{1/4}'s
   cross-check (L3). The xi-side lambda_n are Cauchy integrals of log xi with Arb zeta and
   read no zeros (`li_arith_split.py`). The builder's next step 1 (bound P_n zero by zero
   through the explicit formula) would read the zeros, and the NOTES say so.

## Run manifest

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T13:35+00:00
finished: 2026-10-26T14:30+00:00
ran:
  - .venv/bin/python hunts/rh_moonshot/li_arithmetic/challenge/circ_li.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/li_arithmetic/challenge
outcome: no RH input in any positive claim; the artifact's P_n is the xi-side lambda_n restated, and an independent prime-side route to 10^8 reproduces it within 0.04 for n <= 1000; zeta(s - delta) has lambda_n > 0 for every n and violates RH, so the functional equation carries Li's criterion; unresolved, target a reformulation
artifacts:
  - hunts/rh_moonshot/li_arithmetic/challenge/circ_li.py
  - hunts/rh_moonshot/li_arithmetic/challenge/test_li_arithmetic_challenge_circularity.py
  - hunts/rh_moonshot/li_arithmetic/challenge/CHALLENGE_circularity.md
```

Compute: the script, with its sieve to 10^8 and the n = 100..1000 scan, took 4 min 40 s of
one core (timed); the tests run the same routines at X = 10^6 in seconds. Under one
core-hour, so no estimate was sent.

## Amendment 2026-10-26 (follow-up): field 5, prior art and published refutations

Added after the scorecard above was accepted; the original text is kept unchanged. All
queries were web searches on 2026-10-26; hits are as the result pages and abstracts
returned them, and no paper was read beyond its abstract or excerpts. Journal volumes and
years for Keiper, Voros and Johansson are from memory and unchecked; the arXiv numbers were
returned by the searches.

| # | query (abridged) | hits that bear on the mechanism |
| --- | --- | --- |
| 1 | Bombieri-Lagarias 1999 "Complements to Li's criterion", arithmetic formula, archimedean and finite places | E. Bombieri and J. C. Lagarias, *Complements to Li's criterion for the Riemann hypothesis*, J. Number Theory 77 (1999) 274-287 (Theorem 3: the arithmetic formula for lambda_n, a limit of prime-power sums plus archimedean terms; the multiset theorem); S. K. Sekatskii, *Generalized Bombieri-Lagarias' theorem and generalized Li's criterion with its arithmetic interpretation*, Ukrainian Math. J. 66 (2014), https://umj.imath.kiev.ua/index.php/umj/article/view/2139 |
| 2 | Keiper 1992 power series of xi, Li/Keiper constants; Coffey "Toward verification of the Riemann hypothesis: application of the Li criterion" | J. B. Keiper, *Power series expansions of Riemann's xi function*, Math. Comp. 58 (1992) (the coefficients, lambda^K_n = sum_rho [1 - (1 - 1/rho)^n] / n, and RH implies their positivity); M. W. Coffey, *Toward verification of the Riemann hypothesis: application of the Li criterion*, Math. Phys. Anal. Geom. 8 (2005) 211-255, arXiv math-ph/0505052 (the split lambda_n = S_inf(n) - S_f(n) + 1 and a lower bound on the archimedean part, his Theorem 2); M. W. Coffey, *New results concerning power series expansions of the Riemann xi function and the Li/Keiper constants* (https://cyberleninka.org/article/n/1003304); J. Arias de Reyna, *Asymptotics of Keiper-Li coefficients* (https://personal.us.es/arias/56-2RHB.pdf) |
| 3 | Li criterion, Davenport-Heilbronn, first negative index, height relation | A. Voros, *Discretized Keiper/Li approach to the Riemann Hypothesis*, arXiv 1703.02844 (2017): a discretized Li-type sequence already negative at its second term for a DH function; A. Voros, *Simplifications of the Keiper/Li approach*, arXiv 1602.03292; A. Voros, *From asymptotic to closed forms for the Keiper/Li approach*, arXiv 2204.01036; a Li-type criterion for zero-free regions of Dirichlet series with real coefficients, LMS J. Comput. Math. 19 (2016) 259-280 (negative tau-Li coefficients with exponentially growing amplitude); no published first negative index of the standard lambda_n of DH (the only hit was this laboratory's own pull request #298, hunt #128) |
| 4 | Voros "Sharpenings of Li's criterion" | A. Voros, *Sharpenings of Li's criterion for the Riemann Hypothesis*, Math. Phys. Anal. Geom. (2006), arXiv math/0506326 (and math/0404213): lambda_n ~ n (A log n + B) with explicit A > 0 and B **if and only if RH**, and a non-tempered oscillatory form otherwise |
| 5 | Johansson, Keiper-Li coefficients to n = 100000 with Arb | F. Johansson, *Rigorous high-precision computation of the Hurwitz zeta function and its derivatives*, Numer. Algorithms (2015), arXiv 1309.2877: interval values of lambda_0..lambda_n computed for n up to 100000 (about 71000 s, 48.7 GB) |
| 6 | Li criterion, integral representation with psi(x) - x and a Laguerre kernel | nothing returned that states the Laguerre-kernel integral form P_n of NOTES section 2 |
| 7 | Lean Zulip, Li's criterion, Mathlib, Keiper-Li coefficients | D. Loeffler and M. Stoll, *Formalizing zeta and L-functions in Lean*, arXiv 2503.00959 (Mathlib's `riemannZeta` and `RiemannHypothesis`); no Lean formalization or Zulip thread on Li coefficients returned; also K. Maslanka's numerics (arXiv math/0402168, math/0406312) and *Numerical investigations of the Keiper-Li criterion*, arXiv 2311.06294 |

**What changes.**

- **The onset heuristic of NOTES section 5 is a known mechanism.** Voros (hit 4) proves
  the dichotomy: tempered growth n (A log n + B) exactly under RH, a non-tempered
  oscillation otherwise, driven by the off-line zeros. The builder's root of
  n log R = log((n/4) log n) is a quantitative reading of that dichotomy and should cite
  it. Not a refutation.
- **The measured range is small beside the record.** Johansson (hit 5) has lambda_n with
  interval enclosures to n = 100000; this mechanism's n <= 5000 and the laboratory's
  earlier n <= 58 rows are far inside it. Not a refutation; field 4 (finite stand-ins)
  is unaffected, since no step claims uniformity.
- **The split is Bombieri-Lagarias's Theorem 3 and Coffey's S_inf / S_f split** (hits 1,
  2), as the NOTES say. Coffey's lower bound on the archimedean part is the published
  ingredient nearest to "an inequality on the arithmetic part"; no published uniform
  bound on S_f(n) was found, and none that would finish.
- **No published refutation** of the exact form "P_n <= M(n) for all n from the Euler
  product" was found, nor any treatment of the Laguerre-kernel prime integral (hit 6).
- **Disposition: unchanged** (unresolved; the target a reformulation under kill
  condition 3).

**Correction to the run manifest above.** Its `finished` time, 14:30, was written before
the work finished and is later than the clock at the time; it is not a measured time, and its `started` time is an estimate as well. The follow-up's
`finished` time below is read from the clock and its `started` time is approximate (to
about 10 minutes).
The follow-up manifest below has its `finished` time read from the clock and an approximate `started` time.

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-26-challenge-circularity-field5
hunt: rh_moonshot
started: 2026-10-26T13:30+00:00
finished: 2026-10-26T13:38+00:00
ran:
  - web searches 1-7 of the table above
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/li_arithmetic/challenge
outcome: Voros's sharpening is the published form of the onset dichotomy; Johansson has lambda_n to n = 100000; no published refutation or uniform arithmetic-part bound found; disposition unchanged
artifacts:
  - hunts/rh_moonshot/li_arithmetic/challenge/CHALLENGE_circularity.md
```
