# A zero-surplus rational construction at N=144

**Result: the specified finite feasibility problem is feasible.** The vector

\[
20(c_1,\ldots,c_{12})=(20,-20,-20,0,-20,-13,7,6,0,0,0,13)
\]

has harmonic balance, coverage one through `q=5`, mass `119/20`, and no
positive surplus at any prime power through 144. Its complete saturated cost
is exactly `psi(144)`. The earlier endpoint has strictly positive surplus
`4.414404304141713666...`, so changing coefficients removes that finite gap.

This is an ordinary finite argument with exact rational executable checks and
two independent logarithm enclosure implementations. The independent test
implementation is by the same producer, not an independent reviewer. Review
status is **pending independent challenge**; there is no Lean proof, novelty
claim, uniform estimate, or claimed asymptotic family. The finite construction
is an original output of this pass. An unrun literature search establishes
nothing about priority.

## Exact class and source boundary

Fix `N=144`. The class consists of all rational vectors supported on
`1<=j<=12` with

\[
\sum_{j=1}^{12}\frac{c_j}{j}=0,\qquad
W(q):=\sum_{j=1}^{12}c_j\lfloor q/j\rfloor=1\quad(1\le q\le5),
\qquad\sum_{j=1}^{12}|c_j|\le23.
\]

There are no additional sign conditions. Coverage already forces `c_1=1`.
Deficits, including negative `W`, are allowed and their complete bill is paid.
Rational refers to the coefficient domain, not a finite denominator grid.

This is a relaxation of the balanced-prefix construction at base
`fd04f1fac9d48a4d769048817e678acdea3b4bdb`,
[scaling, section 3](../paid_shortfall_scaling/RESULTS.md#3-explicit-scale-dependent-coefficients).
Every old prefix with cutoff `6<=h<=12` belongs: its balance is zero, it
covers `q<h`, and its mass is at most `2h-1<=23`. The new vector is outside
their convex hull: every such prefix has `c_7<=0`, whereas this vector has
`c_7=7/20>0`. In detail, the old `c_7` is zero for `h=6`, `-14/15` for
`h=7`, and `-1` for `h>=8`. All seven inclusions and signs are tested.

The reviewed predecessor is
`af13799d3034b4d6a07e76c0d6a409dc7421f056`. Its old zero repair-difference
field is not used as a surplus measurement here. The comparison reconstructs
the unchanged endpoint `h=12` from its rational coefficients and prices the
actual positive part. No other worker's source or output is modified.

## Finite proof

Write `b_j=20c_j`. Harmonic balance follows from the integer identity

\[
840\sum_j b_j/j
=16800-8400-5600-3360-1820+840+630+910=0.
\]

The absolute numerators sum to 119, proving the mass bound. For `1<=q<=5`,
the weights reduce to `q-floor(q/2)-floor(q/3)-floor(q/5)=1`.

For `2<=d<=144`, set `W_d=W(floor(144/d))`. The nested-floor identity gives
`W_d=sum_j c_j floor(144/(dj))`. If `d>=25`, its quotient lies between
1 and 5, so coverage gives `W_d=1` without knowing whether d is a prime power.
The prime powers at most 24 are exactly the following thirteen; primes count
as powers of exponent one. Direct integer substitution gives every remaining
constraint:

| d | floor(144/d) | W_d |
|---:|---:|---:|
| 2 | 72 | 3/10 |
| 3 | 48 | 3/10 |
| 4 | 36 | 0 |
| 5 | 28 | 1 |
| 7 | 20 | 0 |
| 8 | 18 | 0 |
| 9 | 16 | 13/20 |
| 11 | 13 | 1 |
| 13 | 11 | 1 |
| 16 | 9 | 1 |
| 17 | 8 | 1 |
| 19 | 7 | 7/10 |
| 23 | 6 | -13/20 |

Thus every prime power through 144 has `W_d<=1`. There are 47 such powers:
13 in this table and 34 covered automatically. Eight have strict deficits;
39 have equality; zero have positive surplus. The negative row at `d=23`
is essential to retain in the repair cost, not a rejected input.

## Full cost and what was improved

Let `Lambda(p^k)=log p`, `Lambda(d)=0` otherwise, and `t_+=max(t,0)`. Define

\[
B=\sum_j c_j\log(\lfloor144/j\rfloor!)
 =\sum_{d\le144}\Lambda(d)W_d,\quad
P_\Lambda=\sum_{d\le144}\Lambda(d)(1-W_d)_+,\quad C=B+P_\Lambda.
\]

The factorial equality is finite rearrangement: the coefficient of `log p`
in `log(M!)` is `sum_{k>=1}floor(M/p^k)`. No limiting interchange is used.
Applying `w+(1-w)_+=1+(w-1)_+` row by row proves

\[
C=\psi(144)+S,\qquad
S=\sum_{d\le144}\Lambda(d)(W_d-1)_+.
\]

The table proves `S=0` exactly. Summing its eight deficit rows gives

\[
P_\Lambda=\frac{27}{10}\log2+\frac{21}{20}\log3+\log7
             +\frac3{10}\log19+\frac{33}{20}\log23.
\]

Consequently `B=psi(144)-P_Lambda` and `C=psi(144)` exactly. Every nonzero
deficit lies at `d<=24`; using the exact Mangoldt weight on this range is the
saturated-cap assumption. Computing that finite bill is not a uniform
analytic estimate. Since `C>=psi(144)` for all real vectors under this same
exact cap, the witness also attains the elementary cost lower bound at this
cutoff, without any claim that its coefficient mass is minimal.

The old endpoint is
`(1,-1,-1,0,-1,1,-1,0,0,1,-1,2/385)`. Its exact surplus is

\[
S_{old}=\frac2{55}\log2+\frac8{385}\log3
          +\frac{387}{385}\log7+\frac{387}{385}\log11>0.
\]

This strict sign needs no floating approximation. The complete cost decreases
by exactly `S_old`. The following rounded displays are pinned by rational
interval endpoints in the [saved output](computations/check-001/results.json):

| Quantity | Old endpoint | New vector |
|---|---:|---:|
| B-144 | -1.292517 | -13.366803 |
| P_Lambda | 3.367967 | 11.027848 |
| S | 4.414404 | 0 exactly |
| C-144 | 2.075449 | -2.338955 |

The repair increases; the factorial term decreases enough to give the full
improvement. S is already included in `B+P_Lambda` and is not added twice.

## Controls, reproducibility and remaining uncertainty

The optional discovery pass is one linear feasibility program with an
auxiliary coefficient-mass objective. Its floating result is reconstructed
over the rationals and every constraint is checked exactly. Neither its
status text nor its apparent optimality supplies the proof above. The default
script verifies the displayed witness without invoking an optimizer.

The independent test code factors integers and factorials using a different
implementation, counts the multiples defining W without calling the producer's
floor routine, and verifies the complete cost. The producer separately checks
145 floor-versus-divisor-prefix identities. It evaluates both candidate costs
with `python-flint` and `mpmath.iv` at 35 and 70 requested decimal digits:
40 expression evaluations, with all four enclosures overlapping for each of
10 expressions, and smaller nonzero widths after precision refinement.

Controls retain the complete hypotheses:

- The old endpoint belongs to the class but violates five surplus constraints,
  including the higher power `d=8`.
- Adding `3/5` to `c_6` and subtracting `6/5` from `c_12` preserves class
  membership but creates four positive-surplus rows, which the check rejects.
- The zero vector passes all no-surplus constraints but fails all five coverage
  equations. It cannot serve as a fake solution to this class.
- Separate tests reject domain, support, balance, coverage and mass lesions.

These finite coefficient controls address the actual claim. There is no
structural RH explanation or proposed zero-location implication to test against
the Davenport-Heilbronn rival.

The complete intended target is still a uniform estimate for the whole paid
bound, such as `C_N<=N+O(sqrt(N) log(N)^2)`, with all costs included. The
original finite feasibility uncertainty has been resolved affirmatively.
The first remaining uncertain step is an explicit scale-dependent admissible
construction with a proved complete-cost estimate. Even zero surplus at other
cutoffs would only identify `C_N=psi(N)` there, not supply that estimate.
There is no new bound for the complete two-sided prime-pair energy `E(N)`.
This witness rules out an infeasibility claim for this declared class at
144; it does not rule out obstructions in other classes or at other cutoffs.

Reproduce from the repository root with its installed environment:

```sh
.venv/bin/python hunts/paid_surplus_obstruction/construction.py --output /tmp/paid-surplus-check.json
.venv/bin/python -m pytest -q -n 0 tests/test_paid_surplus_obstruction.py
```

The [run record](RUNS.md) gives validation and failures. The versioned
[manifest](computations/check-001/manifest.json) records the optional discovery
run, source hashes, software, timing, bounded execution and exact output hash.
No larger cutoff search was performed after the witness passed.
