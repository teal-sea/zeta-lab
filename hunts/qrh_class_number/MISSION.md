# An explicit class-number bound from the quasi-Riemann hypothesis

Base commit: `ef4e0564` (origin/main). Branch `hunt/qrh-class-number`.
Status: bounded construction on top of an unreviewed input theorem.

## Question and scope

OpenAI, "The Quasi-Riemann Hypothesis" (preprint dated 30 September 2026),
Theorem 1.1: no Dirichlet L-function has a zero with Re s > 7/8 (the pole of
the principal character excepted). Its two Lean statements were checked by
this lab on two kernels on 2026-10-08 (section 7 of the input-theorem page numbered 38 on unmerged PR #271).
No human has reviewed the argument, so every result here is stated as
"proved, given OpenAI's Theorem 1.1". The input is used, not re-checked.

The October 5, 2026 OpenAI paper proves the weaker half-plane Re s > 11/12 as
its own Theorem 1.1, cites the 7/8 paper as its reference [36], and states in
its introduction that Littlewood's short Euler product gives
h(D) >> sqrt|D| / log log |D| with an absolute computable constant, which it
does not compute.

This hunt computes that constant and spends it:

1. an explicit inequality L(1, chi_D) >= c / log log |D| for negative
   fundamental D, with every numerical constant enclosed in Arb;
2. from it, an explicit bound D(h) with h(D) = h implying |D| <= D(h);
3. an unconditional class-number computation (reduced-form counting, no
   GRH) over |D| <= D(H), completing the list of imaginary quadratic fields
   with class number h for every h <= H, conditional only on Theorem 1.1.

Controls: the bound against exact L(1, chi_D) for every |D| in the computed
range, with the margin printed; the same bound with the abscissa weakened to
11/12 and 15/16 (and specialised to 1/2 against the published GRH bound of
Lamzouri, Li and Soundararajan); the class-number code against brute force,
PARI and Watkins' counts for h <= 100.

## Resource boundary

Four shared cores and 15 GB. One heavy process at a time, under 3 GB, about
120 CPU-minutes in total, about three hours of wall clock. Time one unit and
write the estimate in `RUNS.md` before each scaled run; checkpoint anything
over twenty minutes. No paid compute, no push, no pull request. Write only
this directory, its case-log entry, `docs/37-methods.md` and `CONTEXT.md`.

```huntspec
id: qrh_class_number
question: What explicit constant does a zero-free half-plane Re s > 7/8 give in L(1,chi_D) >> 1/log log|D|, and for which H does it complete the imaginary quadratic class number lists h <= H beyond Watkins' h <= 100?
frontier: Watkins 2004 unconditional lists for h <= 100 (largest |D| 2383747); GRH-conditional lists for odd h < 10^6 (Holmin, Jones, Kurlberg, McLeman, Petersen); OpenAI states h(D) >> sqrt|D|/log log|D| from the quasi-Riemann hypothesis without a constant
proposed_attack: Littlewood short Euler product with a two-cutoff Cesaro weight, zero sum bounded by Hadamard positivity, prime sums exact below 10^7 and Rosser-Schoenfeld above, then a reduced-form sieve over all |D| <= D(H)
dead_routes:
  - Explicit zero counting (Bennett-Martin-O'Bryant-Rechnitzer) for the low zeros, whose error term exceeds the main term near height zero
  - A Bach-type generator bound from the 7/8 half-plane, which needs primes up to about (log|D|)^8 and so exceeds sqrt(|D|/3) below |D| near 10^30
required_oracles:
  - Arb ball arithmetic (python-flint) for every constant in the inequality
  - Exact class numbers from reduced-form counting checked against brute force and PARI qfbclassno
  - Watkins' published counts for h <= 100 (OEIS A046125, A038552)
kill_conditions:
  - Any computed L(1,chi_D) falls below the claimed lower bound
  - Weakening the abscissa does not weaken the bound, or the GRH specialisation beats the published GRH bound by an implausible margin
  - The class-number code disagrees with brute force, PARI or Watkins on any checked discriminant
  - A step of the written proof uses a property of the zeros that Theorem 1.1 does not supply
agents_may:
  - derive
  - compute bounded ranges
  - implement local instruments and tests
  - search the literature
agents_may_not:
  - claim novelty from an empty search
  - promote their own claim
  - re-check or replay the input theorem
  - alter shared implementations or launch heavy parallel work
```
