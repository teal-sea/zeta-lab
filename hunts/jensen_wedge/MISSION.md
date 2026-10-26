# MISSION: `jensen_wedge`, hunt #135: the polynomial hyperbolicity wedge for Jensen polynomials of xi

Opened 2026-10-18 as a **depth hunt** by owner decision: the owner asked for one
mechanism worked for weeks rather than a one-day forage. The forage stop rule does
not apply here. The hunt stops on a kill condition below or at the time box, and an
absence of results before a checkpoint is not a kill condition. Time box: through
**2026-11-29** (six weeks). Checkpoints on 2026-10-25, 2026-11-08 and 2026-11-22.
The owner confirmed this funding and time box on 2026-10-18 ("Fund hunt #135 as
scoped"), and the allocation record belongs on fulcrum's roster, not here.

> **Closed 2026-10-19 by owner decision**, after landing in PR #317, about six weeks
> inside the time box. No kill condition fired. The remaining checkpoints and the rest
> of the time box are released, and this is an allocation decision, not a mathematical
> verdict. The open doors are listed in `RESULTS.md`, "The doors". Reopening them is a
> new allocation.

This hunt cannot promote its own claims (`hunts/README.md`). Nothing in it is a
statement about RH, and section "What success would mean" says why that holds even
if every phase succeeds.

## Why this hunt exists, and the target it replaced

It was requested as "explicit Jensen hyperbolicity thresholds at degree 4 and up via
the gauss_positivity saddle instrument", following `hunts/gauss_positivity` section 6
(hunt #134). **That target was already met in the literature before this tree
proposed it**, and the tree's own frontier statements (`docs/12` section 8.1,
`zeta/li.py`'s module docstring, hunt #134 section 6) read the frontier from GORZ
2019 alone. Checked 2026-10-18 against the primary sources:

- **All n, every degree up to about 10^21.** Griffin, Ono, Rolen, Thorner, Tripp and
  Wagner, *Jensen polynomials for the Riemann xi-function*, Adv. Math. 397 (2022)
  108186, arXiv:1910.01227v3. Theorem 1.2: if RH holds to height `T` then `J^{d,n}`
  is hyperbolic for all `n >= 0` whenever `d <= floor(T)^2`. Their Corollary 1.3, with
  Platt's `T = 3.06e10`: hyperbolic for all `n >= 0` when `d <= 9.36e20`. Chasse had
  `d <= 2e17` earlier. Applying the same Theorem 1.2 to the Platt-Trudgian height
  `T = 3e12` gives `d <= 9e24`; that last figure is derived here from their theorem,
  not quoted from their v3 text.
- **Large n, every degree, explicit shape.** The same paper, Theorem 1.1: there is a
  constant `c > 0` with `J^{d,n}` hyperbolic for `n >= c e^{d/2}` (v3; the published
  version states `n >= c e^d`). The constant is not computed.
- **The current frontier, two months old.** Jonathan Holland, *A new hyperbolicity
  wedge and a joint semicircle limit for Jensen polynomials of Riemann's xi-function*,
  arXiv:2608.08682v1 (9 August 2026). Theorem 1.1: there is an absolute `K > 0` such
  that `n^3 log^2(n+2) >= K d^5` implies `J^{d,n}` has `d` distinct negative real
  zeros, i.e. `d <~ n^{3/5}` up to logarithms. This replaces the exponential threshold
  by a polynomial one. Its section 12 says plainly that no attempt is made to
  optimise the eventual absolute constant.

So no finite unresolved set exists at any degree an explicit-threshold computation
could reach. The unresolved region of the `(d, n)` plane begins above `d = 9.36e20`
and lies below Holland's wedge. Every point in it is far beyond any finite check;
it can be reached only by proof.

*Frontier, 2026-10-19 (phase 3, from `NOVELTY.md`):* two deposits that predate this hunt
reach past the list above. Both are unreviewed, and neither proof was checked here.
**Savva**, Zenodo 10.5281/zenodo.22293642 (3 September 2026), posted the 2/3 wedge
`n^2 log(n+2) >= K d^3` with K not computed, stronger than the
`n^4 log^2(n+2) >= K d^6 log^12(d+2)` this hunt later derived; it is AI-assisted by its
author's account. **Sarnowski**, Zenodo Papers 134Z and 134AA (20 August 2026), posted the
rank-r diagonal Pade spine whose r = 2 case is this hunt's [2/2] Pade point. So Q1 had been
answered, in unreviewed form, before this hunt asked it. What the hunt adds with no prior
instance in the searched set is Q2: explicit constants, K = 17 900 with GORTTW Cor. 1.3 and
K = 9.10e19 standalone for Holland's Theorem 1.1, K' = 7.21e9 and 3.61e30 for the `log^12`
six-coefficient form, and c = 1 in GORTTW Theorem 1.1 (`RESULTS.md` section 19; derivation,
reviewed once internally, not a theorem). The bullets above are kept as written.

## The mechanism this hunt works, as Holland states it

Normalise `R_j = gamma(n+j)/gamma(n)`, so `J^{d,n}(X)/gamma(n) = sum_j C(d,j) R_j X^j`.
Holland builds a real-rooted polynomial in the positive-root class that matches
`R_0..R_4` exactly, through three nested families: Laguerre (matches `R_1, R_2`;
its error at `R_3` has a definite positive sign), Jacobi (absorbs `R_3`; leaves a
defect of the opposite sign at `R_4`), and a second Jacobi factor joined by
finite-free multiplicative convolution (absorbs `R_4`). His Proposition 2.2,
*fifth-order multiplier stability*, then shows the remaining coefficient multiplier
`c(j)`, which equals 1 at five consecutive indices, cannot move the zeros off the
axis when `sup |c - 1|` is small on a neighbourhood of radius `r ~ sqrt(nd)`. The
multiplier's fifth derivative is `O(1/(n^4 log n))`, so the residual error is
`O((nd)^{5/2} / (n^4 log n)) = O(d^{5/2} / (n^{3/2} log n))`, and requiring it small
is exactly `d^5 <~ n^3 log^2 n`. The analytic input is the complex saddle estimate
of GORTTW section 3, which is the same object `hunts/gauss_positivity` section 3
reproduces in real form (`pi e^{u_*} = 1/4 + 2n/u_*`, hardened against exact
quadrature to 4-6 digits at n = 100..3200).

*Correction, 2026-10-18 (phase 1, from the PDF):* the paraphrase of Proposition 2.2
above is loose. Its threshold is sup over Omega_r of |c - 1| <= eps < 16, on the
2r-neighbourhood of [0, d], and it has a second hypothesis on the model alone, (6):
|y^k p^(k)(y)/p(y)| <= r^k at every critical point y of p. The radius enters only
through (6), which Holland's Lemma 9.1 verifies with r_F = K_6 sqrt(Bd).
`RESULTS.md` section 9 has the line-by-line check.

## The questions, ranked

**Q1 (exponent).** Can the matching be carried to order `m = 6`, giving
`n^4 log^2(n+2) >= K' d^6`, i.e. `d <~ n^{2/3}`?

Heuristic, derived here from Holland's displayed error and not proved: if matching
`R_0..R_{m-1}` succeeds inside the positive-root class and the stability scale stays
`sqrt(nd)`, then with `g_i = O(n^{1-i})` (GORTTW equation (2.1)) the residual is
`O(d^{m/2} / (n^{m/2-1} log n))` and the wedge is `d <~ n^{1-2/m}`. Setting `m = 5`
recovers Holland's exponent exactly, which is the consistency check that licenses
writing the heuristic down. Under the same heuristic the method class stalls at
`d ~ n`, where the terms `n (d/n)^i` of the `log R_j` expansion stop decaying. That
barrier is a conjecture about this class, recorded so that nobody mistakes it for a
theorem.

The concrete open step at `m = 6`: after Holland's five-coefficient match, does the
defect at `R_5` have a **definite sign** across `n`, and is there a third
real-rootedness-preserving factor (Jacobi or Laguerre, joined by finite-free
multiplicative convolution, Martinez-Finkelshtein-Morales-Perales IMRN 2024) whose
parameters stay in the positive-root class while matching it? Then: does
Proposition 2.2 generalise to six-point vanishing with the same radius?

**Q2 (effectivity).** For whichever wedge stands at the end (Holland's `m = 5` or a
new `m = 6`), compute an explicit admissible constant, with every numeric step in
the saddle error bounds carried by ball arithmetic (`zeta/rigor.py`, Arb backend).
This is the closest form of the originally requested "explicit threshold" that is
still open. Combined with GORTTW's all-`n` range it would give a fully explicit
hyperbolic region.

## Plan and checkpoints

0. **By 2026-10-25: reproduce before extending.** Build `R_j(n)` and the quotient
   coordinates `q_k = R_{k+1}^2/(R_k R_{k+2})` from the exact `gamma(n)` table
   (`zeta/li.py`, two routes pinned in `tests/test_li.py`), and the saddle expansion
   of `log R_j` through order 7. Reproduce Holland's two sign facts numerically (the
   Laguerre error at `R_3` is positive, the Jacobi defect at `R_4` is negative) over
   `n = 50..3200`. A failure here means the paper was misread; fix the reading
   before anything else.
1. **By 2026-11-08: the sixth-order step (Q1).** Measure the `R_5` defect after the
   five-coefficient match: its sign, and its scaling in `n` and `d`, on two
   independent routes (exact table and saddle). Attempt the third factor. Attempt
   the six-point stability lemma. Output: a derivation with explicit hypotheses, or
   an obstruction at that order graded per `ALIGNMENT.md` section 5.
2. **By 2026-11-22: effectivity (Q2).** Explicit constants for the standing wedge,
   ball-arithmetic enclosures for each numeric input, and a planted-fault check that
   the bound goes red when a constant is deliberately weakened.
3. **By 2026-11-29: rival, doors, hand-off.** The Davenport-Heilbronn run (below),
   `RESULTS.md` with "The doors", the methods entry in `docs/37-methods.md`, and
   routing through `docs/doors/refute.md`. A Lean formalisation is out of scope:
   finite-free convolution and the saddle machinery are not in Mathlib, and sizing
   that port is a separate decision.

## The rival gate, with its expected outcome stated in advance

The wedge's inputs are the asymptotics of the weight `Phi` (double-exponential decay
`e^{-pi e^u}`), which Davenport-Heilbronn's weight shares. **Prediction: the same
construction succeeds for DH at the same `(d, n)`**, using the DH `gamma` table that
`hunts/jensen_clock/probe.py` builds by two quadratures. DH violates RH, and its
`J^{d,0}` stops being hyperbolic near `d* = 20785` (`hunts/jensen_clock`). If the
prediction holds, the wedge is shared structure that cannot tell an RH-true function
from an RH-false one. That is a measured, in-tree form of Farmer's critique (Adv.
Math. 411 (2022) 108781) and of GORTTW's Remark 3. If DH *fails* where zeta passes,
that is unexpected, and it gets the bug, assumption and shared-failure checks of the
certainty ladder before anyone reads it as arithmetic content.

## What success would mean, and what it would not

Full success is a theorem of the shape "`n^4 log^2(n+2) >= K' d^6` with explicit
`K'` implies `J^{d,n}` hyperbolic", stated as a delta against Holland's
arXiv:2608.08682 Theorem 1.1. That would be a real, citable result on the Jensen
program, pending external review. **It would not be progress on RH.** Every wedge of
this shape leaves out the corridor of small `n` and large `d`, and `n = 0` with all
`d` is RH itself. No known mechanism converts partial Jensen hyperbolicity into
zeros on the line: Farmer 2022, GORTTW Remark 3 and Holland section 12 all say so,
and this tree's `jensen_clock` P5 says the clock reads zero configuration, not
arithmetic. The owner chose depth over breadth; this mission does not claim that
this lane is the deep route to RH.

```huntspec
id: jensen_wedge
question: Can Holland's five-coefficient positive-root comparison for J^{d,n} be carried to six coefficients, giving a hyperbolicity wedge n^4 log^2(n+2) >= K d^6, and can the constant of the standing wedge be made explicit?
frontier: All n hyperbolic for d <= 9.36e20 (GORTTW Cor 1.3, arXiv:1910.01227v3, via RH to 3.06e10); n >= c e^{d/2} for every d with c not computed (GORTTW Thm 1.1); wedge n^3 log^2(n+2) >= K d^5 with K absolute and not computed (Holland, arXiv:2608.08682, Thm 1.1, August 2026). Added 2026-10-19: unreviewed deposits predating the hunt claim the 2/3 wedge n^2 log(n+2) >= K d^3 with K not computed (Savva, Zenodo 10.5281/zenodo.22293642, 2026-09-03) and the rank-r Pade spine (Sarnowski, Zenodo Papers 134Z, 134AA, 2026-08-20).
proposed_attack: Reproduce Holland's sign facts at R_3 and R_4 from the exact gamma(n) table and the saddle expansion of log R_j, measure the sign and scaling of the R_5 defect after the five-coefficient match, attempt a third finite-free Jacobi or Laguerre factor and a six-point multiplier stability lemma, then make the constants of the standing wedge explicit with ball arithmetic.
dead_routes:
  - Explicit N(d) at fixed degree d >= 4 plus a finite check; done in the literature (GORTTW Thm 1.1 and 1.2, Chasse), and the open region begins above d = 9.36e20, beyond any finite computation.
  - Newton inequalities for J^{d,n} at higher degree; implied by the d = 2 Turan inequality, proved in hunts/gauss_positivity section 5b (hunt #134).
  - Low-degree hyperbolicity scans as a falsification route; they cannot fail, by the de Bruijn-Newman smoothing t_eff(d) = |x0|/(8d) measured in hunts/jensen_clock and hunts/gauss_positivity section 5c.
  - Positivity of the weight Phi as the real-zeros criterion; refuted by the positive measure delta_0 + delta_1 + delta_3, hunts/gauss_positivity section 1.
required_oracles:
  - the exact gamma(n) table of zeta/li.py, two independent routes pinned in tests/test_li.py
  - mpmath quadrature at two working precisions for every saddle-expansion coefficient
  - Arb ball arithmetic through zeta/rigor.py for every numeric constant stated as explicit
  - exact rational Sturm root counts (zeta.li.is_hyperbolic, method sturm) for spot checks at small d
  - the Davenport-Heilbronn gamma table built by two quadratures in hunts/jensen_clock/probe.py, as the rival
  - the published statements of GORTTW Theorems 1.1 and 1.2 and Holland Theorem 1.1 and Proposition 2.2, as the targets any claim is a delta against
kill_conditions:
  - Holland's sign facts at R_3 (positive) and R_4 (negative) fail to reproduce from the exact table, which means the construction was misread
  - the saddle expansion of log R_j disagrees with the exact gamma table beyond its stated error at any n <= 3200
  - the R_5 defect after the five-coefficient match changes sign within the measured n range, on both routes, which blocks a single sixth-order factor of Holland's type
  - every candidate third factor needs a parameter outside the positive-root class (negative or complex) to match R_5
  - a planted weakening of an explicit constant does not turn the effectivity check red
  - the time box of 2026-11-29 passes, after which the hunt is paused by allocation, which is not a mathematical verdict
agents_may:
  - search
  - derive
  - compute
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - claim any bearing on RH
  - run heavy work locally
```

## Compute discipline

Phases 0 and 1 are light: the `gamma(n)` table to a few thousand terms and saddle
expansions at symbolic `n`. Anything heavier runs on GitHub Actions, never
locally (`AGENTS.md`, "Compute discipline"). Time one unit and write the
estimate in `RUNS.md` before any sweep. Every run appends a `runmanifest` block to
`RUNS.md`, including runs that produced nothing.
