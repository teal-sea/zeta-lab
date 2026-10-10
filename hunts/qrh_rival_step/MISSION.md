# MISSION: where the quasi-Riemann argument spends its Euler product, and a rival that cannot pay

**Opened 2026-10-08. Hunt #120.** Nothing in this directory is a result until the
case log in `hunts/README.md` says how it ended. The strongest words used here
are *measured* (one float route), *observed*, *hardened* (independent routes
agree, or balls carry the step), and *cited* (somebody else's theorem, with the
page). A composite claim takes the grade of its weakest step. The reserved
enclosure word belongs to `zeta/rigor.py` and appears nowhere in this directory.

## The question

On 2026-10-06 OpenAI published `github.com/openai/math`. Family 003 claims that
every finite-order Hecke L-function over Q(sqrt(-3)) and every Dirichlet
L-function, zeta included, is zero-free in Re s > 7/8 (the lab's reading of the release, `38-the-quasi-riemann-claim.md` on the
branch `claude/openai-math-release-2026-10-06`, read but not replayed). The lab's standing test for a structural claim about zeros
(`ALIGNMENT.md` section 5, `docs/08` section 4.3) is a rival: a function that
satisfies the claim's complete hypotheses but not its conclusion refutes it; a
rival that merely passes a shared lemma does not, so the job is to find the
distinguishing step and test it.

The classical rival class is right there. An Epstein zeta function of a positive
definite binary quadratic form of class number above one is a finite linear
combination of Hecke L-functions of an imaginary quadratic field, has a
functional equation and real coefficients, has no Euler product, and has
infinitely many zeros in Re s > 1 (Davenport and Heilbronn 1936, cited). That is
the paper's object class with one property removed. So:

> Where exactly does the argument use that its target is a single Hecke
> L-function with an Euler product, and does a measured rival with a zero
> beyond 7/8 fail that step?

```huntspec
id: qrh_rival_step
question: Where does the OpenAI quasi-Riemann argument (the 7/8 paper of 2026-09-30 and the 11/12 paper of 2026-10-05) use that its target is a single Hecke L-function with an Euler product rather than a finite linear combination of them, and does a measured rival with a zero beyond 7/8 fail that step?
frontier: the lab's reading 38-the-quasi-riemann-claim.md (2026-10-07, on the branch claude/openai-math-release-2026-10-06 of the main checkout, not yet on main) records the claim as read, text-scanned and unreplayed; the battery pins one Davenport-Heilbronn zero at Re s = 0.80851718 (below 7/8) and locates no Epstein zero at all; Davenport and Heilbronn 1936 give infinitely many zeros with Re s > 1 for Epstein zeta functions of class number above one, at unmeasured heights
proposed_attack: read Proposition 2.1, Section 7.2 and Lemma 7.1 of the 7/8 paper and Sections 2 to 3 of the 11/12 paper for the exact use of the Euler product; locate zeros of the Epstein zeta functions of discriminants -15 and -23 beyond 7/8 by argument-principle counts and Newton refinement on independent evaluation routes, with a ball-arithmetic winding number on the located zeros; compute the exact Dirichlet inverse of the rival's coefficients to show what the Moebius-sum input becomes when the Euler product is removed
dead_routes:
  - treating a zero of a linear combination of L-functions as a counterexample to a theorem about single L-functions, which section 6 of 38-the-quasi-riemann-claim.md already rules out for the Davenport-Heilbronn zeros
  - evaluating the Epstein zeta function by its Dirichlet series near Re s = 1, where the tail decays like N^(1 - sigma)
  - the mpmath Fourier-Bessel route above height about 100 at fifteen digits, which loses accuracy without warning (measured 0.04 at t = 100 and 0.73 at t = 200 against the Dirichlet L-function route)
required_oracles:
  - the argument principle on rectangles, evaluated with mpmath on independent evaluation routes (the lattice incomplete-gamma sum of zeta/epstein.py, the Fourier-Bessel expansion, and for discriminant -15 the genus-character factorization into Dirichlet L-functions)
  - python-flint ball arithmetic with segment enclosures for the winding number and the Bessel tail bounded in closed form
  - the exact integer Dirichlet inverse of the representation numbers, computed by sieve
  - the papers' stated hypotheses, quoted with page and proposition numbers
  - Davenport and Heilbronn 1936 (J. London Math. Soc. 11), parts I and II, as published, and Titchmarsh section 10.25
  - mpmath's zeta for the positive control gamma_1 = 14.134725141734694
kill_conditions:
  - the paper's Proposition 2.1 applies verbatim to a linear combination, in which case the rival's zero is a candidate refutation and this hunt withdraws any weaker claim and reports it for independent review
  - the evaluation routes disagree at a located zero by more than the stated tolerance, in which case that zero is withdrawn
  - the positive control fails to recover gamma_1, or a planted fault goes undetected, in which case the detector is not trusted and no zero is reported
  - no zero with Re s > 7/8 is found below the stated height bound, in which case the hunt reports the bound and does not call the rival a rival to the 7/8 conclusion
agents_may:
  - read the papers and quote them with citations
  - derive the expansion conventions numerically and check them against the lab's lattice route
  - code, measure, locate zeros, run controls
  - record what was not done and why
agents_may_not:
  - assign evidentiary status to the hunt's own output
  - declare the paper refuted or confirmed
  - declare novelty
  - use the reserved enclosure word or any word sharing its stem
  - edit anything outside hunts/qrh_rival_step/ and the one case-log entry in hunts/README.md
```

## What is fixed before any number is produced

- The target 7/8 = 0.875 and the comparison threshold Re s > 1 come from the
  papers, not from the data.
- The rivals are the principal forms of discriminants -15 (class number 2,
  form x^2 + xy + 4y^2) and -23 (class number 3, form x^2 + xy + 6y^2), the
  two smallest discriminants with class number above one that
  `zeta.epstein.epstein_reduced_forms` returns. The class-number-one form
  x^2 + xy + 5y^2 (discriminant -19) is the control with an Euler product.
- Three evaluation routes, chosen for sharing no code: (A) the lattice
  incomplete-gamma sum of `zeta/epstein.py`; (B) the Fourier-Bessel expansion
  of the Eisenstein series, with every constant derived by matching route A at
  four points rather than taken from a reference; (C) for discriminant -15 only,
  the genus-character identity zeta_Q(s) = zeta(s) L(s, chi_-15) +
  L(s, chi_-3) L(s, chi_5), each factor a Hurwitz-zeta sum.
- A zero counts as located when the argument-principle count in a square of
  side 0.1 around it is 1 on route C (or B) in mpmath, the ball-arithmetic
  winding number on route B is 1 with every segment enclosure excluding zero,
  and the Newton-refined positions on two routes agree to the stated digits.
- The height bounds of every scan are reported as the scan's limit, never as a
  statement about what lies above them.

## What this hunt does not try to do

It does not check the paper's proofs of its estimates. It does not replay the
Lean development. It does not search for novelty. It does not say anything
about whether 7/8 is true; it says where the argument needs the Euler product
and shows one concrete object that has everything else and a zero past 7/8.
