# 44. The constant in the wedge: explicit constants for Jensen hyperbolicity, and whose wedge it is

**Hunt #135, `hunts/jensen_wedge/`.** The derivations, the reviews and the doors are in
that directory; `RESULTS.md` sections 18 to 20 carry the landing. This page is the front
door.

> **Landed on main 2026-10-19.** The owner funded six weeks (to 2026-11-29); the hunt
> landed after two days. Every number on this page is quoted from the hunt's own record
> (`RESULTS.md`, `EFFECTIVE.md`, the review files and `results_effective.json`); the four
> constants and c = 1 are pinned by `test_effective.py`.

**Nothing here bears on RH.** Every result below is about Jensen polynomials at shifts n
that are large compared with their degree d. RH is the statement that every `J^{d,0}` is
hyperbolic, at shift n = 0, and a wedge of this shape excludes n = 0 whatever its constant.
The construction also succeeds for the Davenport-Heilbronn function, which violates RH, so
it cannot be reading what RH is about.

Grade: **derivation, self-reviewed and reviewed once by an independent session in this
lab; not a theorem; pending external review.** Every numeric step is an Arb ball
enclosure (python-flint through `zeta.rigor`), which makes each number a bound and does not
review the argument.

## 1. The question

With `xi(1/2 + w) = sum gamma(n) w^(2n)/n!`, the Jensen polynomial of degree d at shift n is
`J^{d,n}(X) = sum_j C(d, j) gamma(n + j) X^j`, and it is hyperbolic if all its zeros are
real. Before this hunt, Griffin, Ono, Rolen, Thorner, Tripp and Wagner (Adv. Math. 2022)
had every n for `d <= 9.36e20`, through Platt's check of RH to height 3.06e10, and
`n >= c e^(d/2)` for every d with c not computed. Holland (arXiv:2608.08682, August 2026)
replaced the exponential by a polynomial wedge, `n^3 log^2(n+2) >= K d^5`, with an absolute
K that his paper says it does not try to compute.

The hunt asked two things: whether Holland's matching of five coefficients extends to six,
giving exponent 2/3 instead of 3/5, and whether his K can be made explicit.

## 2. What it found

| statement | constant | the chain covers |
| --- | --- | --- |
| Holland's wedge, using GORTTW for d <= 9.36e20 | **K = 17 900** | n >= 9.91e33 |
| Holland's wedge, no outside input | **K = 9.10e19** | n >= 789 702 (empty below) |
| six-coefficient form `n^4 log^2(n+2) >= K' d^6 log^12(d+2)`, using GORTTW | **K' = 7.21e9** | n >= 5.65e35 |
| the same, no outside input | **K' = 3.61e30** | n >= 14 237 025 (empty below) |

The first line makes **c = 1** admissible in GORTTW's Theorem 1.1: `J^{d,n}` is hyperbolic
for every `n >= e^(d/2)`. The constants come from replacing every non-explicit step of
Holland's proof by an explicit one. The central piece is an explicit remainder for the
complex saddle of xi's moment weight, which stands in for his Proposition 4.1. The
uniformity in n comes from interval Krawczyk tests over a cover of `1/v_1(2n)`, which
reaches n = infinity at a finite point. `docs/37-methods.md` has both as entries.

## 3. Whose wedge it is

The literature search (`hunts/jensen_wedge/NOVELTY.md`, every query listed) found that the
first question had been answered before the hunt asked it:

- **Savva**, Zenodo 10.5281/zenodo.22293642, 3 September 2026, posted the 2/3 wedge as
  `n^2 log(n+2) >= K d^3`, which is stronger than the hunt's `log^12 d` form. His K is not
  computed. The deposit is AI-assisted and claims no human review.
- **Sarnowski**, Zenodo Papers 134Z and 134AA, 20 August 2026, posted the rank-r diagonal
  Pade spine; its r = 2 case is the hunt's sixth-coefficient match, constants included.

Neither deposit has been reviewed, and the hunt did not check their proofs. Its phase 1 is
an independent re-derivation of both. What has no prior instance in the searched set is the
explicit constants of section 2.

## 4. Why it cannot touch RH

The hunt preregistered a prediction: the construction would succeed for the
Davenport-Heilbronn function too, because it reads the weight only through its
double-exponential decay, which that function shares. It did, on every item, on two
routes (`RESULTS.md` section 15), while Davenport-Heilbronn's own `J^{d,0}` stops being
hyperbolic near d = 20 785. A property both functions have cannot be why zeta's zeros are on
the line; that is the rival test of `docs/doors/refute.md`, met by a proof route rather than
by a pattern.

"The doors" (`RESULTS.md` section 20) lists where the constants are loose: the closing
condition of Holland's Lemma 9.1 (up to about 1.2e3 in K) and the root-gap radius of the
six-coefficient chain (up to about 5e19 in K'). Every door that tightens the argument
reads only what the construction already reads; the one lever from outside, a higher RH
verification height for GORTTW's corollary, reads more zeros and moves where the chain
starts. None of them moves the corridor of small n and large d, which contains RH;
entering it would need information that tells zeta from Davenport-Heilbronn.

## 5. A check that claimed more than it did

Phase 2 wrote every intermediate constant down as a claim, recomputed all of them, and
planted a 0.1 percent weakening of each: 44 of 44 plants turned the check red, which is the
hunt's kill condition not met. But a recomputation from the same formulas cannot see a wrong
formula, and phase 2 relied on independent measurements for that. The independent review
planted four formula faults; three passed all 36 tests, because a measurement with slack 785
cannot see a constant five times too small. Phase 3 added checks of those steps against
their own derivation, and replays each plant as a source edit the suite must reject; all
four are now rejected. Writing the doors then turned up one more slip: the six-coefficient
radius is 39 to 44 times what is needed, not 36 to 44 as recorded (a figure read in the
wrong units), so K' has more room than stated. Both corrections are dated in `RESULTS.md`
section 18, with the original text kept.

## 6. Read and reproduce

`RESULTS.md` (sections 18 to 20 first), `EFFECTIVE.md` (the derivation), `NOVELTY.md`,
`REVIEW_PHASE1.md`, `REVIEW_H1_H3.md`, `REVIEW_PHASE2.md`.

```bash
.venv/bin/python hunts/jensen_wedge/effective.py                  # about 1 min, writes results_effective.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/test_effective.py
.venv/bin/python hunts/jensen_wedge/review_p2/plant_formula_faults.py   # about 6 min
```
