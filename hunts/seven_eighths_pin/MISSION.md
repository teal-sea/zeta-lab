# MISSION: `seven_eighths_pin`, which step of the quasi-Riemann argument fixes the number 7/8

**Opened 2026-10-16. Hunt #134.** Nothing in this directory is a result until the
case log in `hunts/README.md` says how it ended. Grades used here: *cited* (a line of
the paper's LaTeX source, quoted), *derived* (algebra done here from cited formulas,
checked in exact rational arithmetic by this hunt's test), *inferred* (a reading of
the paper's structure that no computation here checks). The reserved enclosure word
belongs to `zeta/rigor.py` and appears nowhere in this directory.

## The question

OpenAI's preprint of 2026-09-30 (`docs/38`, `docs/39`) proves that no Dirichlet
L-function, zeta included, has a zero with real part above 7/8. RH is the same
statement at 1/2. The lab has rebuilt the Lean statement and built four results on
it, but nobody here has read past sections 1 to 3 of the 199-page argument
(`docs/38`, "What was not checked"), and nobody has located the step that stops the
method at 7/8 rather than at a smaller number. Hunt #120 (`qrh_rival_step/`) read the
places where the Euler product is used and recorded that the paper's second Euler
region reads `x_r >= 7/8`; it did not ask what fixes that value.

> Which inequality in the 7/8 argument binds, as a function of the parameters the
> paper chooses, and what is the smallest target the same assembly would allow if
> those choices were re-optimized with every cited input held fixed?

The paper's source is public: `github.com/openai/math` at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`
(16,677 lines, Apache-2.0). Line numbers below refer to that file.

## Scope

- **In scope.** Reading the final assembly (Part II, Section "The seven-eighths
  bound", lines 15495 to 16677) and the lemmas it cites; rewriting each of its
  numerical inequalities as a function of the free geometry (the prime-slot length,
  the scale offset, the frequency scale, the contour positions); reproducing every
  printed margin from those general formulas in exact arithmetic as a control;
  then varying the free parameters to see which inequality fails first.
- **Out of scope.** Checking the paper's lemmas themselves (the moment
  inductions, the sieve, the detector). Those are taken as cited inputs, at the
  exponents the paper proves them with. Any statement about RH: a smaller
  half-plane, if the re-optimization found one, would still be a candidate about
  this assembly, not a theorem, and nothing here says anything about real part 1/2.
- **Budget and stop rule.** One session. No heavy compute: the arithmetic is
  exact rational algebra on a laptop scale. Stop when the binding constraint is
  located and stated with its parameter range, or when a cited input turns out to
  depend on the target in a way the reading cannot resolve, and report that wall.

```huntspec
id: seven_eighths_pin
question: In OpenAI's 7/8 zero-free half-plane argument (preprint of 2026-09-30), which inequality of the final assembly binds as a function of the chosen geometry, and what is the smallest target the same assembly allows when that geometry is re-optimized with every cited lemma input held at the exponents the paper proves?
frontier: the theorem is kernel-checked here as a formal statement (docs/38 section 7) but its argument is unreviewed by any person; sections 1 to 3 were read (docs/38); hunt 120 located the Euler-product step (Lemma 7.1, Section 7.2) and recorded the second Euler region condition x_r >= 7/8; the Part II endpoint certificate prints a margin of 49/440640 and the low estimate matches the Mellin signal exactly at 7/8 (C_II(7/8) = 3/16 = l_x/2 + b/12, line 8642); no location of the binding step was found in this tree
proposed_attack: express the Mellin target, the low exponent and every high-side exponent of Section 15495 to 16677 as functions of the slot length ell, the offset b, the frequency scale h and the contour positions; reproduce each printed constant from the general formulas in exact rational arithmetic; then vary the free parameters with the row-count inputs held fixed and record which inequality fails first and at what target
dead_routes:
  - reading the 7/8 half-plane as information about real part 1/2, which docs/39 rules out
  - treating a zero of a linear combination of L-functions as a counterexample to a statement about single L-functions, which hunt 120 and docs/38 section 6 rule out
  - lowering the target by substituting a smaller number for 7/8 in the final section alone, without rederiving the row counts and the bootstrap that the final section inherits
required_oracles:
  - the paper's LaTeX source at the pinned commit, quoted by line number
  - exact rational arithmetic in Python fractions reproducing each printed constant of the paper
kill_conditions:
  - a general-parameter formula fails to reproduce a constant the paper prints, at the paper's own parameter values
  - a parameter treated here as free is fixed by a cited lemma this hunt did not read, and that lemma changes the binding constraint
  - the derived relation between the slot length and the target fails at either stage of the argument (11/12 with no slots, 7/8 with slot length 1/6)
agents_may:
  - read and quote the paper
  - derive
  - code exact arithmetic
  - attack the derivation
agents_may_not:
  - declare novelty
  - declare theorem status
  - claim any improvement to the half-plane as established
  - promote their own claim
```
