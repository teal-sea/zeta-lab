# A finite adversary excludes the recorded pressure target

**Status: candidate refuted at the stated scope (`ALIGNMENT.md` section 5,
disposition 1).** The refuted claims are `hunts/amtopa_ceiling`'s recorded
lower endpoint 0.007916857810 and its target 19791/2500000; the same bound
also excludes the later target 19786/2500000. All of this holds only at
AMTOPA's fixed 17-term window and total pressure B = 93/23000. Grade, step
by step: the numerical leaves are **hardened**.
Every transcendental leaf carries an Arb enclosure at 128 and 256 bits
(python-flint backend), an independent mpmath quadrature route agrees with
the closed form and with Arb at all 148 distances, and the probabilities,
budgets and final combination are exact `Fraction` arithmetic. The step that
joins them (finite weak duality and the coefficient budgets, section 3) is
an ordinary mathematical argument, written out below and not reviewed by
anyone outside this run. `Symmetry.lean` states the abstract deductions and
the rational arithmetic, but it has never been run through Lean, so nothing
here is kernel-checked. The composite takes its weakest grade: a hardened
numerical bound inside an unreviewed ordinary derivation, pending external
verification. The counting audit (section 8) is a derived refinement with
exact finite checks; its projected zeta proportions are candidates awaiting
a replacement assembly. No new zeta proportion is claimed.

> **Dated note, 2026-10-21 (landing).** Main's
> `hunts/amtopa_ceiling/RESULTS.md` section 7.7 withdrew the 0.007916857810
> endpoint on 2026-09-06, by a different route: AMTOPA's own verifier
> refused the candidate's target, float descents found basins of the LP's
> functional below the claimed floor, and a re-solve with a stronger oracle
> bracketed the optimum as [0.0079107, 0.0079111939]. There the lower end is
> the target AMTOPA's branch-and-bound accepts and the upper end is graded
> MEASURED (a float LP value). This hunt's bound was obtained on 2026-09-04,
> before and independently of that withdrawal. It agrees with the later
> bracket, since 0.0079111939 < 0.007914014. It is looser than the bracket's
> float upper end, by about 2.8e-6, and it is enclosure-carrying where that
> end is not. It also excludes 19786/2500000 = 0.0079144, the target that
> section 7.7 tried after backing off from 19791/2500000, by about 3.9e-7.
> The refutation is therefore not superseded. Its numbers are unchanged from
> 2026-09-04; the landing edits are this note, the grading language in the
> status and in section 6, two dated remarks in section 7 and a name there
> replaced by its role, and sections 8 and 9.

## 1. What was found

At the exact 17-term AMTOPA window and total pressure B = 93/23000 used by
`hunts/amtopa_ceiling`, the best possible local floor over all admissible
pair coefficients and position pressures is less than 0.007914014. This
contradicts that hunt's reported lower endpoint 0.007916857810 and excludes
its proposed rational target 19791/2500000 = 0.0079164. The countercertificate
uses seven rational gap vectors and their reversals, extracted from the
hunt's already saved cut pool. It applies to every feasible coefficient
choice, so recovering the missing candidate file is unnecessary.

It does not refute AMTOPA's smaller target 0.0079107, establish a new lower
bound for zeta zeros, or bound constructions with a different window or
pressure budget.

## 2. Exact mathematical statement

Let

\[
v(t)=10^{-9}\sum_{j=0}^{16}n_j\cos(\omega_jt),\quad
\omega_0=\sqrt2,\quad\omega_j=2\pi j\ (j\ge1),
\]

where the exact integer vector n is the `window_numerators` field of
`adversary.json`. It matches `amtopa_ceiling/family.py` and the primary
[AMTOPA deduction](https://raw.githubusercontent.com/AMTOPA/zeta-exact-pressure/main/proof.md),
read 2026-09-04. Define

\[
K(x)=\int_{-1/2}^{1/2}v(t)\cos(2\pi xt)\,dt,\qquad
W(x)=\left(K(x)/K(0)\right)^2.
\]

For g in [0,infinity)^6, put y_0 = 0, y_j = g_1+...+g_j, and

\[
F_{a,b}(g)=\sum_{r=1}^6 b_rg_r+
\sum_{0\le i<j\le6}a_{ij}W(y_j-y_i).
\]

Over the polytope

\[
\mathcal P=\{a,b\ge0:\ \sum_{i=0}^{6-s}a_{i,i+s}=2\ (1\le s\le6),\
\sum_{r=1}^6b_r=93/23000\},
\]

the derived bound is

\[
\boxed{\sup_{(a,b)\in\mathcal P}\inf_{g\ge0}F_{a,b}(g)
\le\frac{182022320819207}{23000000000000000}
<\frac{7914014}{10^9}.}
\]

The quantifiers matter: this excludes the old target for the entire
fixed-window, fixed-pressure polytope, including asymmetric coefficients.
Even span budgets at most two, rather than exactly two, obey the bound
because W is nonnegative.

## 3. Proof with finite, inspectable numerical leaves

`adversary.json` gives exact positive rational orbit weights p_l summing to
one and seven nonnegative rational six-gap vectors g_l. Give g_l and its
reversal probability p_l/2 each. Let M_ij be the resulting expectation of
W(y_j-y_i), and let d_r be the expected gap.

For arbitrary (a,b) in the polytope,

\[
\begin{aligned}
\inf_g F_{a,b}(g)&\le\mathbb E_\mu F_{a,b}(g)\\
&=\sum_{i<j}a_{ij}M_{ij}+\sum_rb_rd_r\\
&\le2\sum_{s=1}^6\max_i M_{i,i+s}
+\frac{93}{23000}\max_rd_r.
\end{aligned}
\]

The first inequality needs only a finite probability measure. The last
needs only nonnegative coefficients and their exact budgets. No minimax
interchange, global minimizer, LP feasibility tolerance, or strong duality
is involved in verification.

The 21 transcendental expectations satisfy these rational upper bounds:

| Span s | Upper bound for every M_(i,i+s) |
|---|---|
| 1 | 0.000634884759717 |
| 2 | 0.000010127109795 |
| 3 | 0.000073116002704 |
| 4 | 0.000045872037949 |
| 5 | 0.000083018119185 |
| 6 | 0.000058811254374 |

Every d_r is strictly below the rational 1.509184664171. Combining these
seven rational caps gives exactly 182022320819207/23000000000000000. The
remaining gap to 7914014/10^9 is exactly 1180793/23000000000000000.

`verify.py` constructs each rational input in Arb, evaluates the entire
sinc function in the explicit transform formula, encloses K(0) away from
zero, and checks all 21 inequalities individually. Each arithmetic step
retains its enclosure. The probability sum, mean gaps, budgets, and final
combination are checked separately with `Fraction`.

An independent mpmath route integrates the trigonometric window directly
on eight subintervals of [0,1/2], at all 148 distinct distances including
zero. It compares both with its own closed form and with the Arb evaluator.
Quadrature is a cross-check, not the proof of the leaf inequalities.

## 4. The structural statement

Let R reverse six gaps and send a_ij to a_(6-j,6-i), b_r to b_(7-r).
Then R preserves the domain and polytope, and

\[
F_{R(a,b)}(g)=F_{a,b}(Rg),\qquad
F_{(a,b)+R(a,b)\over2}(g)
=\tfrac12\big(F_{a,b}(g)+F_{a,b}(Rg)\big).
\]

Consequently averaging coefficients with their reflection cannot reduce a
uniform floor. The achievable floors, and hence the supremum, are exactly
the same with or without palindromic coefficient restrictions. This does
not say every optimizer is symmetric, nor that one hand-picked symmetric
candidate is optimal. It says asymmetry provides no additional optimal
value over the full symmetric subspace.

The coefficient representation shrinks from 21 pair coordinates plus six
pressures to 12 pair orbits plus three pressure orbits. After the six span
constraints and total-pressure constraint, affine dimension falls from 20
to eight. Reversal of (i,j) fixes exactly the three pairs with i+j=6.

The argument is classical convex averaging, not new mathematics. The
specific finite countercertificate and its contradiction of the recorded
target are the output of this run. A narrow web search for the exact
numbers found the old lab claim; that is not a systematic novelty search.

## 5. Experiments, including failures

The original 2,200-cut LP replays at 0.00791936539887148. Closing precisely
that pool under reversal, with no search for new gaps, gives the floating
LP upper value 0.007914013948652049. Its nonzero dual coefficients form
seven reversal orbits. Rounding those to rational probabilities and gaps
produces the artifact, whose directly enclosed objective is
0.0079140139486524494635982723615771522630...

The input pool SHA-256 is
`cab31f1b8f634799b1eb60b7e39abe69687f4fb0c949feed612352b0ead6f4f4`.

The claimed converged lower endpoint exceeds the new rational target by
284381/100000000000. The proposed target 19791/2500000 also exceeds it.
These are exact inequalities. The old runtime explanation that an
inconclusive verifier merely needs a different revision cannot rescue this
particular target: a sound verifier cannot prove a false uniform inequality.

The first research idea, the stronger uncapped total-energy Gram profile,
was killed as new work after finding the identical formula in AMTOPA's
primary source. No novelty claim survives for that idea.

One attempted negative test was itself wrong: replacing the 17-term window
by the fundamental alone was expected to break the upper bound. It did
not, because changing the window can make an upper bound easier to satisfy.
That test expectation was withdrawn. The replacement keeps probabilities
and window fixed but moves all gaps to 100, so pressure alone invalidates
the proposed upper bound. Other lesions remove probability mass, insert a
negative gap, lower a leaf cap to zero, and demand an unattainable target.

## 6. Scope and strongest objection

This is a narrow obstruction within an existing construction, obtained by
standard convexity and finite weak duality. It is not a conceptual advance
in analytic number theory. The exact target it rules out was already
unproved; no established zeta theorem is being withdrawn. Its value is
that it replaces an expensive unresolved computation with an explicit
reason the target is impossible.

The strongest mathematical objection is a mismatch between the finite
functional tested here and the functional behind the old claim. The
window's 17 exact coefficients, six span budgets, pressure budget, gap
domain, and square normalization are all stated above so that objection
can be checked directly. Moving any of those parameters falls outside
this result.

The composite conclusion takes its weakest grade: hardened numerical leaves
inside an unreviewed ordinary derivation, pending external verification. A
Lean check of `Symmetry.lean`, if one is ever obtained, would cover only the
abstract deductions and the rational arithmetic, so it would not change that
grade. No outside validation is claimed. (Landing, 2026-10-21: this
paragraph first graded the conclusion in a session-local status vocabulary;
it now uses the repository's ladder, with the same content.)

## 7. Reproduction and next experiment

From the repository root:

```sh
.venv/bin/python hunts/reversal_minimax/verify.py --quadrature
.venv/bin/python -m pytest -q -o addopts='' hunts/reversal_minimax/
```

`verify.py` rewrites `verification.json`; at landing (2026-10-21, python-flint
backend) the rewrite was byte-identical. The pytest line runs both test files,
`test_probe.py` and `test_counting_audit.py`. Only discovery uses the saved
pool and SciPy:

```sh
.venv/bin/python hunts/reversal_minimax/probe.py
```

The single next research experiment is to repeat the coupled window search
with every adversarial cut closed under reversal and both sides represented
by checkable witnesses: a finite mixed adversary for the upper bound, a
uniform interval proof for the lower bound. Start with the already saved
window candidates. Do not count multistart agreement as a lower bound.

The experiment the operator probably would not have asked for: reflect the
adversaries already on disk before funding any larger parameter search.
That experiment has now been run, and it excludes the recorded target.
(Landing, 2026-10-21: main's `amtopa_ceiling` has since re-solved the same
polytope with a stronger gap oracle, section 7.7 there, but in floating
point. Making a reversal-closed adversary from that larger pool
enclosure-carrying is the cheapest door in section 9.)

## 8. The counting audit (code and data 2026-09-04, written up at landing 2026-10-21)

The operator asked whether overlapping combinatorial estimates subtract the
same zeros repeatedly (`MISSION.md`, operator-directed continuation).
`counting_audit.py` answers that for the pressure side of the n-point bridge
by counting window incidences exactly. Until this landing the audit existed
only as code, `counting_audit.json` and `test_counting_audit.py`; this
section is its write-up, and it adds no new computation beyond the two
pinned checks named below.

**What is counted.** The bridge applies the local inequality on every window
of n consecutive points inside every block of m consecutive points, and pays
for it with pressure on the gaps. `pressure_coefficients` enumerates both
window levels directly and counts, for each gap, how many local windows over
all blocks contain it. The bridge's early span estimate instead charges every
gap of a block n - 1 times for each block that contains it. That is the
per-gap charge n - 1 and the penalty (n - 1)(m - 1)/(pm) in the bridge's
coefficient (`docs/37-methods.md`, the n-point certificate-to-proportion
bridge).

**The exact incidence result.** An interior gap lies in n - 1 local windows,
and each of those lies in m - n + 1 blocks, so its exact coefficient is
(n - 1)(m - n + 1), against the coarse (n - 1)(m - 1). The smallest witness
(7 points, m = 4, n = 3) has exact coefficients [1, 3, 4, 4, 3, 1] against
coarse [2, 4, 6, 6, 4, 2]. The tests check, for n from 2 to 7, m from n to
11 and four lengths of the point set, that the exact coefficients never
exceed (n - 1)(m - n + 1), never exceed the coarse ones, and attain the bound
once the set has at least 2m points; a planted refund one below the bound
fails at an interior gap. Pressure is linear in the gaps, so checking the
coefficient of every gap covers every nonnegative gap vector in those finite
cases. Grade: exact integer arithmetic over that finite range, plus the
two-line counting argument above for general (n, m), an ordinary derivation
that nobody outside this run has reviewed and that is not in Lean.

**The pair side was already exact.** `pair_coefficients` regroups every local
pair occurrence by its global pair, with weight 2/(n - s) at span s. Every
interior pair receives total weight exactly 2, the span budget, and no pair
exceeds it (checked exactly for n from 2 to 7, at m = 3n). So the overcharge
sits in the pressure term only, and the span budget 2 of section 2 is the
bridge's exact normalization, not a loose constant.

**What it projects: candidates.** With q = n - 1, the bridge's leading
constant is (mH - q(m - 1)/p)/(m - c(m - n + 1)). Charging the exact count
replaces q(m - 1) by q(m - n + 1). `projection` gives both values as exact
affine expressions in H:

| parameters | coarse count (as built) | exact count (candidate) | exact gain |
|---|---|---|---|
| n = 3, c = 1345/10^6, m = 745, p = 3000 | 0.6727373345 (the registered three-point theorem) | 0.6727382306 | 400/446400399, about 8.96e-7 |
| n = 4, c = 2310/10^6, m = 435, p = 2500 | 0.6728470198 (the registered four-point theorem) | 0.6728525497 | 5/904171, about 5.53e-6 |
| n = 4, c = 2330/10^6, m = 432, p = 2500 | 0.6728603588 (main's 2026-09-28 build) | 0.6728659273 | 80/14366681, about 5.57e-6 |

The rational coefficients and gains are exact. The decimals are 60-digit
mpmath values of exact expressions in H: accurate, not enclosure-carrying.
In every row the coarse column is exactly the coefficient of a lab theorem,
which is how the audit checks that it has the bridge's formula right. The
first two rows are the Palomar-registered instances; the third is the build
in `hunts/four_point_pressure/`, kernel-checked at its pinned revision, which
appeared after this audit and still uses the coarse count. The third row was
computed at landing with the audit's own `projection` and is pinned by
`test_counting_audit.py`. Note that the second row's candidate is already
below the third row's kernel-checked value, by about 7.8e-6: the refined
count is worth something only as an addition at the best parameters, where
it would add 80/14366681.

Every exact-count value is a **candidate**. The finite incidence counts are
exact, but no replacement assembly that charges the exact count has been
written, reviewed or built in Lean, and a projected constant is not a
theorem until that assembly is checked end to end. No literature search was
run for the refined count, so its novelty is unsearched; it is original to
this hunt as a matter of provenance only.

**Measured kernel examples.** `kernel_example` evaluates three gap
configurations on the actual normalized Montgomery-Taylor Gram matrix:
alternating gaps 1.04 and 1.97 at (n, m) = (3, 4) and at (4, 6), and uniform
gaps 0.25 at (3, 4). In all three the exact nested pressure is strictly below
the coarse one and within the improved cap; the block inequality and the
local-to-block inequality hold with the exact pressure; and splitting into
blocks loses positive spectral defect (the pinching loss). These are float
measurements at three points, not uniform statements; one Gram transform is
checked against direct mpmath quadrature to 1e-14. Re-running
`counting_audit.py` rewrites `counting_audit.json`. At landing the exact
fields and projections replayed identically and the float fields within
5e-14 relative, except the near-singular minimum Gram eigenvalue of the
uniform example, about 7.8e-14, which moved by 1.2e-16 absolute.

## 9. The doors

What this hunt bounds, from above, is one construction's optimum: the
finite adversary bounds the supremum over the whole pair-weight and pressure
polytope of inf_g F, at AMTOPA's window and B. It is not a ceiling on the
pressure family with the window, B or the number of points free, and it says
nothing about any wider information class. Its leaves are hardened and its
derivation is ordinary and unreviewed.

**Active constraints at the optimum.** The bound is 2 sum_s lambda_s + B nu,
with lambda_s = max_i M_(i,i+s) and nu = max_r d_r. These are its exact
partial derivatives in the six span budgets and in B, so they are this
bound's shadow prices. The adversary also reproduces the float optimum of
the reversal-closed pool LP to 4e-16, so up to float tolerance they are a
set of budget multipliers for that LP as well (measured). Ranked by share of
182022320819207/23000000000000000:

| constraint | shadow price | term in the bound | share |
|---|---:|---:|---:|
| total pressure B = 93/23000 | 1.5091846642 per unit of B | 0.0061023554 | 77.1% |
| span-1 budget | 6.3488e-4 | 0.0012697695 | 16.0% |
| span-5 budget | 8.3018e-5 | 0.0001660362 | 2.1% |
| span-3 budget | 7.3116e-5 | 0.0001462320 | 1.8% |
| span-6 budget | 5.8811e-5 | 0.0001176225 | 1.5% |
| span-4 budget | 4.5872e-5 | 0.0000917441 | 1.2% |
| span-2 budget | 1.0127e-5 | 0.0000202542 | 0.3% |

The pressure term binds hardest. All six mean gaps d_r agree to within 2e-13
(`verification.json`), so the bound prices every position pressure b_r the
same and no pressure profile has leverage against this adversary. Within
each span every pair coordinate attains the span's maximum moment except
(0,2) and (4,6), about 2.8% below the span-2 maximum, and (1,5), about 2.2%
below the span-4 maximum; pair weight placed on those three is strictly
wasted against this adversary. This active-set structure is pinned by
`test_probe.py`.

**The frozen-constant inventory.**

- *The 17-term window* (`window_numerators`, AMTOPA's, with fundamental
  sqrt(2)). Every M_ij moves with it, and the adversary is specific to it.
  Trade shape: genuine. In the assembly a window trades the base constant H
  against floor; `amtopa_ceiling` section 7.4 measured AMTOPA's window
  spending about 3.1e-4 of H to buy about 8.8e-4 of floor, on an LP that
  predates its section 7.7 withdrawal. This hunt's own withdrawn test
  (section 5) is the reminder that changing the window can make an upper
  bound easier to satisfy, so nothing here transfers to another window.
- *B = 93/23000.* The binding constant: the bound moves by 1.509 per unit
  of B. Trade shape: genuine. B buys floor here and is paid for in the
  assembly's pressure penalty, so it must be priced in the assembled
  constant, not in the floor alone.
- *Seven points, six gaps*, fixed by AMTOPA's construction. More points add
  spans and pairs and give a new polytope; nothing here prices that.
- *Span budget 2*, the bridge's exact pair normalization (section 8), not a
  tunable constant. The bound also holds with budgets at most 2.
- *The adversary's support*: seven reversal orbits drawn from the saved
  2,200-cut pool, with no new gap search. This is the slackest frozen
  choice. Main's strong-oracle re-solve (`amtopa_ceiling` section 7.7,
  14,060 cuts) reaches a float LP value of 0.0079111939, about 2.8e-6 under
  this bound, so a reversal-closed adversary from that pool, checked the same
  way, would tighten the hardened upper bound toward it. It trades nothing
  binding away: the cost is computation only.
- *Rounding*: probabilities to 10^-12, gaps to 15 significant digits, the
  seven rational caps to 15 decimals. The remaining slack to 7914014/10^9 is
  1180793/23000000000000000, about 5.1e-11. Slack, not binding.
- *The square normalization W = (K/K(0))^2 and the gap domain [0, infinity)^6*
  define the functional; they are not choices.
- *On the assembly side* (section 8), the block cap c(m - n + 1) <= 1 binds
  by construction (0.99957 at main's m = 432 build), and the pressure charge
  q(m - 1)/p is the frozen coarse count that the exact count lowers. That
  door is worth 80/14366681 at main's build parameters, a candidate, and
  every capped assembly stays under H*m/(m - 1), 0.674061030138 at m = 432
  (`RESEARCH_TARGET.md`).

**The information class.** Everything above reads pair data only: F sees the
six gaps, through the pressure term, and the pairwise kernel values
W(y_j - y_i), and nothing about triples. The window, B, the number of
points, a richer cut pool and the refined incidence count are all doors
inside that class, and so under its configuration ceiling, whatever that is;
`family_wall` bounds the fixed-window capped family. Reading more, joint
statistics of three or more zeros, is the separate proposal in
`RESEARCH_TARGET.md`, and nothing in this hunt measures that class.

**What this closes and what it does not.** Closed, as a candidate refuted at
the stated parameters (`ALIGNMENT.md` section 5, disposition 1): the recorded
endpoint 0.007916857810 and the targets 19791/2500000 and 19786/2500000, at
this window and B, for every choice in the polytope. Not closed: AMTOPA's
target 0.0079107, every other window or B, and the pressure family as a
route; no restricted-class obstruction is claimed. By share the next door is
B, but its price is paid in the assembly, so it has to be compared in the
assembled constant against the window and the refined count, under the
current complete argument. The cheapest door is the richer pool, which
tightens this bound without changing what it bounds.
