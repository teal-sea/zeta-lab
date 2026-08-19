# `hunts/epp_herglotz`: the mechanism, and the step where it died

**Nothing here is a result about the Riemann Hypothesis.** This is the report
of one attack on one mechanism, and the mechanism did not survive it. No
progress on RH was made. The value of the run, if it has any, is that the
death is located precisely rather than described.

The mechanism was written first, in `MISSION.md`, in a commit containing
nothing else. What follows is what happened to it.

## Verdict, in one paragraph

The mechanism claimed that Euler-product positivity (`Lambda(n) >= 0`, called
EPP here) plus the functional equation compose into `Re (xi'/xi) >= 0` on
`Re s > 1/2`, which is equivalent to RH. **It is false.** The composition step
is refuted by an explicit function that carries every hypothesis the mechanism
uses, carries each of them in larger quantity than zeta does, and has zeros
off its own critical line unconditionally:

    W_a(s) = zeta(s+a) zeta(s-a),      Xi_a(s) = xi(s+a) xi(s-a),     a = 1/4.

`Xi_a(1-s) = Xi_a(s)` exactly; `Xi_a(1/2+it)` is real; `W_a` has a scalar Euler
product; its log-derivative coefficients are `Lambda(n)(n^a + n^{-a}) >= 0`,
which is EPP with room to spare; its archimedean term is exactly twice zeta's
and positive; and its zeros are the points `rho +- a`, so Hardy's theorem puts
infinitely many of them on `Re s = 1/4` and on `Re s = 3/4`. The mechanism's conclusion is
therefore false for a function satisfying its hypotheses, and no repair
internal to those hypotheses can exist.

What separates zeta from `W_a` is not a positivity at all. It is a
normalisation, in four faces of one shift: the size of the coefficients, the
abscissa of the Dirichlet series, the location of the poles, and
`Re mu_j >= 0` in the gamma factor. Once the mechanism is repaired by importing
it, the mechanism has nothing left to run on, for a reason that stage F
measures: **the inequality it must prove is
an identity on the boundary of the region where it must hold**, and its entire
content is the first-order term inside, which is the zero-counting measure.
That is the exact step, and it is unavoidable in the sense given in section 6.

## 1. The target, measured (stage A)

`Re (xi'/xi)` is the quantity whose sign the mechanism was trying to force.
It behaves exactly as the mechanism's first sentence says, which is a check on
the arithmetic and evidence for nothing.

| measurement | value |
| --- | --- |
| `xi'/xi` by explicit split vs by contour differentiation of `xi` | agree to 7.6e-42 |
| `zeta.core.xi` vs the probe's own `xi` | 1.7e-32 |
| `max abs Re (xi'/xi)` on `Re s = 1/2`, five heights | 2.3e-41 |
| `min Re (xi'/xi)` over 49 points with `1/2 < sigma <= 3` | +4.6e-06, at `sigma = 0.5001` |
| `max Re (xi'/xi)` over 9 points with `sigma < 1/2` | -4.7e-06 |

The vanishing on the line is `F(1-s) = -F(s)`, and it is why the mechanism
believed the functional equation was giving it exact boundary data. It is,
and section 6 is about what that data is worth.

## 2. The rival carries every hypothesis (stage B, `a = 1/4`)

| hypothesis the mechanism uses | measurement for `W_a` |
| --- | --- |
| exact `s -> 1-s` functional equation for the completion | max relative defect 1.2e-16 over four points |
| real on the critical line (a Hardy-style `Z`) | max relative imaginary part 0.0 |
| real, non-negative Dirichlet coefficients | min over `n <= 60` is 1.0 |
| a scalar Euler product | truncation defect 3.1e-06 at 400 primes, `s = 2.5+1.5i` |
| EPP: non-negative log-derivative coefficients | min over `n <= 200` is -2.0e-34, i.e. zero to working precision |
| `Re (Xi_a'/Xi_a) = 0` on `Re s = 1/2`, the boundary data the mechanism leans on | max abs value 1.3e-51 over four heights |
| the same, by a second route | recursion from the coefficients vs the closed form `Lambda(n)(n^a+n^{-a})`: max difference 1.3e-15 |

The EPP measurement was made twice on purpose. The closed form is a
derivation; the recursion `b_n log n = sum_{d|n} Lambda_F(d) b_{n/d}` reads
only the Dirichlet coefficients and never sees an Euler product, so it is the
route the battery uses on the rivals.

## 3. The kill (stage C)

| measurement | value |
| --- | --- |
| `abs Xi_a(3/4 + i gamma_1)` | 8.1e-22 |
| `abs Xi_a(1/2 + i gamma_1)`, same height, on the line | 1.2e-07 |
| zeros of `Xi_a` in the box `[0.1, 0.9] x [10, 25]`, argument principle | 4 |
| sign changes of the real `Z` on `Re s = 1/2` over `10 < t < 25`, 900 samples | 0 |
| `Re (Xi_a'/Xi_a)` at `sigma = 3/4 - 0.001`, `t = gamma_1` | **-998.0** |
| the same at `sigma = 3/4 - 0.01 / 0.05 / 0.12` | -97.9 / -17.8 / -5.7 |

Four zeros in the box and none on the line. For comparison the standing
Davenport-Heilbronn window in `zeta/epstein.py` has five in the box and three
on the line. The mechanism's conclusion, `Re (xi'/xi) >= 0` to the right of
the critical line, is violated by three orders of magnitude at a point where
the mechanism's hypotheses all hold.

Note that the off-line zeros of `Xi_a` do not depend on any assumption about
zeta. `Xi_a(s) = 0` exactly when `s = rho +- a` for a zero `rho` of `xi`, and
Hardy's theorem gives infinitely many `rho` with `Re rho = 1/2`. So infinitely
many zeros of `Xi_a` sit at distance `a` from its own critical line, whatever
is true of the rest of zeta's zeros.

## 4. The mechanism's two positivities are shared, and larger (stage D)

| quantity | zeta | `W_a` |
| --- | --- | --- |
| min eigenvalue of the 7x7 Toeplitz matrix `[A(sigma + i(t_j - t_k))]`, `sigma = 2.5` | +0.0053 | +0.0166 |
| `Re G(0.6 + 10i)` | 0.234 | 0.468 |
| `Re G(0.6 + 50i)` | 1.037 | 2.074 |
| `Re G(0.6 + 1000i)` | 2.535 | 5.070 |

Both Bochner matrices are positive semidefinite, as EPP forces. Both
archimedean terms are positive and grow. The rival has more of each, and its
conclusion is false. A mechanism whose inputs are monotone in these two
quantities cannot be repaired by making either of them bigger.

## 5. Gate #3, and the truncation that flips it (stage E)

`zeta.epstein.battery` was run on EPP, read from the Dirichlet coefficients
alone. **The verdict depends on where the coefficient scan stops, and the
dependence is not cosmetic.**

| truncation | verdict | shared with |
| --- | --- | --- |
| `n <= 40` | does not distinguish | `epstein_1_1_6` |
| `n <= 200` | distinguishes | none |

The detail, at `n <= 200`:

| function | EPP | first negative `n` | min `Lambda_F` |
| --- | --- | --- | --- |
| zeta | holds | none | -9.2e-41 |
| Davenport-Heilbronn | fails | 3 | -6.78 |
| Epstein `(2,1,3)`, non-principal | undefined: `a_1 = 0` | n/a | n/a |
| Epstein `(1,1,6)`, principal | fails | **48** | -19.88 |
| `W_a` | holds | none | -2.0e-34 |

Three things are worth recording exactly as they are.

**The 40-coefficient reading is a false pass for the rival, and it was the
first reading this run took.** It said EPP is shared with a function that
violates RH, which would have killed the mechanism at gate #3 for the wrong
reason. The principal Epstein form's first negative log-derivative coefficient
is at `n = 48`. Unique factorisation in the principal-class ideal monoid of
discriminant -23 first fails at `n = 36`, where `(2)(3) = (p2 p3bar)(p2bar p3)`,
and the measured `Lambda_F(36)` there is 0 to 4.6e-41; `Lambda_F` is also 0 at
24, 32 and 40. So the coefficients sit on the boundary of the claim for a
while before crossing it, which is precisely why a short scan reads as a pass. A coefficient claim run through the
battery therefore carries its truncation as part of the claim.

**The non-principal Epstein form has no log-derivative Dirichlet series in
this normalisation at all.** `a_1 = 0`, so the recursion is undefined rather
than negative. Reporting that as "the claim fails" is correct for the battery's
boolean and wrong as a description, so both are recorded.

**EPP passes gate #3 and the mechanism still died.** That is the methodological
content of the run: the standing rivals are linear combinations of legitimate
Euler products, so they cannot test a hypothesis that a genuine scalar Euler
product also satisfies. `W_a` is such a rival and the battery does not contain
one. This is an observation about the battery, not a proposal; the hunt does
not promote it and did not pursue it.

## 6. Why the step is unavoidable (stages F and G)

`W_a` differs from zeta in more than one way, so the repair has to be named
carefully. It has degree 2 rather than 1; its poles sit at `1 +- a` rather than
at 1; its coefficients grow like `n^a`, so its Dirichlet series converges only
for `Re s > 1 + a`; and its gamma factor has `Re mu_j = -a/2 < 0`. Those are
four faces of the same shift, and **none of them is a positivity**. Every
positivity-shaped hypothesis the mechanism named is shared, and shared with
more of it (section 4).

Suppose then that the mechanism is repaired by adding the shift-excluding
hypothesis in any of its faces: the coefficients do not grow, equivalently the
Dirichlet series converges for `Re s > 1`, equivalently `Re mu_j >= 0`. No
rival can then be exhibited, since exhibiting one would refute RH, and a
degree-1 element of the Selberg class is zeta or a shifted Dirichlet
L-function by Kaczorowski-Perelli. What is left of the mechanism is measured
here, and it is nothing.

**The inequality is an identity on the boundary.** The functional equation
gives `Re A(1/2+it) = Re G(1/2+it)` exactly, for every `t`. That is the same
fact as `Re F = 0` on the line, measured in stage A at 2.3e-41. The mechanism
must prove `Re A <= Re G` on `Re s > 1/2`, and its target holds with **zero
margin** along the entire boundary of that region. An inequality proved by
bounding one side loses something; here there is nothing to lose.

**Just inside, the margin is the zero-counting data itself.** `Re F(1/2+eps+it)`
is linear in `eps` with slope `sum_rho abs(s - rho)^{-2}`:

| `t` | `Re F / eps` at `eps = 1e-3` | at `1e-5` | at `1e-7` |
| --- | --- | --- | --- |
| 7 | 0.0621641 | 0.0621641 | 0.0621641 |
| 20 | 1.0768414 | 1.0768423 | 1.0768423 |
| 50 | 20.048188 | 20.048571 | 20.048571 |

and the same slope, assembled from the ordinates by a disjoint route
(`mpmath.zetazero` for the first 300 zeros plus the Riemann-von Mangoldt
density tail), is **0.0621709** against the `F`-route's **0.0621641** at
`t = 7`. The margin the mechanism has to produce is the zeros, to five
digits. This is the circularity, as a number.

**EPP's bound on the prime side is off by a growing factor.** All EPP gives is
`abs A <= sum Lambda(n) n^{-sigma}`, which diverges at `sigma = 1/2`. Cut at
the approximate-functional-equation length `N ~ sqrt(t/2pi)`:

| `t` | `N` | EPP triangle bound | actual partial sum | archimedean target | bound / target |
| --- | --- | --- | --- | --- | --- |
| 1e3 | 12 | 4.26 | 1.43 | 2.53 | 1.68 |
| 1e4 | 39 | 9.65 | 4.60 | 3.69 | 2.62 |
| 1e6 | 398 | 37.30 | 3.70 | 5.99 | 6.23 |
| 1e8 | 3989 | 123.67 | 8.22 | 8.29 | **14.92** |

The actual prime sum tracks the target, as it must, since the two are equal on
the line. The bound EPP supplies exceeds the target by a factor growing like
`sqrt(N)/log t`, without bound. So the mechanism needs square-root cancellation
in the prime sum, and square-root cancellation in the prime sum is RH.

That is the unavoidability, stated plainly: EPP is a statement about signs and
the target is a statement about cancellation. The functional equation converts
neither into the other, because what it supplies at the critical line is an
equality, not slack.

## 7. What this run does not say

- It does not say anything about whether RH is true.
- It does not say the Euler product is irrelevant to RH. It says that
  `Lambda(n) >= 0`, together with the functional equation and the Euler product
  itself, is not enough, with a witness.
- `W_a` is not offered as new. The one-sided shift `zeta(s - delta)` is already
  in this tree at `docs/18` section 6 and `docs/24` section 6, which cite
  Conrey-Ghosh 1992 remark 2 for the observation itself; the symmetric product
  is the standard reason the Selberg class carries a Ramanujan axiom. What the
  run did with it is the attack, not the object.
- No claim here has been through the funnel or been promoted. Per
  `hunts/README.md`, a hunt cannot say yes about itself, and this one is saying
  no about itself anyway.

## 8. Reproduce

```bash
.venv/bin/python hunts/epp_herglotz/probe.py     # writes results.json, ~15 min
```
