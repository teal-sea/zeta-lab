# A finite adversary excludes the recorded pressure target

**Status: PROVISIONAL RESULT.** The derivation is complete and its numerical
leaves are checked with Arb at two precisions and against direct quadrature.
It has not been independently audited outside this run. A separate Lean
file covers abstract deductions and rational arithmetic only; it must not
be read as a Lean proof of the transcendental numerical leaves.

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

The numerical conclusion remains PROVISIONAL under the user's requested
status system until independent review. Abstract Lean checks, if obtained,
do not change that composite status. No outside validation is claimed.

## 7. Reproduction and next experiment

From the repository root:

```sh
.venv/bin/python hunts/reversal_minimax/verify.py --quadrature
.venv/bin/python -m pytest -q -o addopts='' hunts/reversal_minimax/test_probe.py
```

Only discovery uses the saved pool and SciPy:

```sh
.venv/bin/python hunts/reversal_minimax/probe.py
```

The single next research experiment is to repeat the coupled window search
with every adversarial cut closed under reversal and both sides represented
by checkable witnesses: a finite mixed adversary for the upper bound, a
uniform interval proof for the lower bound. Start with the already saved
window candidates. Do not count multistart agreement as a lower bound.

The experiment Thomas probably would not have asked for: reflect the
adversaries already on disk before funding any larger parameter search.
That experiment has now been run, and it excludes the recorded target.
