# INDEPENDENCE: what this hunt's cross-checks actually bound

**Written 2026-08-16 to close `GATE.md` item (e).** The hunt said "two
independent winding routes" (`MISSION.md` WP1, pre-registered prediction P2)
and printed that adjective in its headline. The gate measured it and found
it much weaker than it sounds. This file replaces the adjective with the
measurement, spells out the layer lists so a reader can check them, and then
records the two legs that do carry real independence.

Everything here is reproducible from the repo root:

```
.venv/bin/python hunts/lambda_dh_bounds/independence_decl.py     # the measurement
.venv/bin/python hunts/lambda_dh_bounds/crosscheck_quadfree.py   # route 4, ~10 s
.venv/bin/python hunts/lambda_dh_bounds/crosscheck_dhflow_winding.py  # route 3, ~6 min
```

writing `independence_results.json`, `crosscheck_quadfree_results.json` and
`crosscheck_dhflow_results.json` respectively.

The tool is `harness/independence.py`, built after the director run
(`docs/25`, `docs/26` section 1) around one sentence: *a cross-check bounds
only what is actually duplicated.* A `VerificationPath` is an ordered list of
named layers from input to verdict; `compare()` reports the independence
radius, the shared layers, the reconvergent ones and the distinct segments.
There is no aggregate score and `bool(report)` raises.

---

## 1. The headline number

| pair | radius | shared | layers each | agreement is evidence about |
| --- | --- | --- | --- | --- |
| route 1 vs route 2 | **9** | **9** | 12 / 12 | 3 + 3 bookkeeping layers |
| route 1 vs route 3 (DHFlow) | 0 | 0 | 12 / 8 | everything either one runs |
| route 1 vs route 4 (quadrature-free) | 0 | 1 (reconvergent) | 12 / 6 | everything except the ball backend |
| route 3 vs route 4 | 0 | 0 | 8 / 6 | everything either one runs |

**Routes 1 and 2 share nine of twelve declared layers, with independence
radius nine: the entire evaluator is one implementation run twice.** Their
agreement is evidence about the three bookkeeping layers each one adds after
the evaluator returns a ball, and about nothing else.

### On the gate's "8 of 11"

The gate reported 8 shared of 11 and this file reports 9 of 12. The two are
the same declaration at different granularity: the gate counted the period-5
coefficient table and the theta recurrence that consumes it as one layer,
and this file splits them. `independence_decl.py` re-runs the coarse version
and reproduces `8 shared of 11, radius 8` exactly, so the difference is one
merge and not a disagreement about any layer's status. **The invariant that
neither count depends on: the two winding routes duplicate none of the
evaluator.** Prefer that sentence to either number.

---

## 2. The layer lists, spelled out

A layer here is one identifiable implementation stage between an exact input
coordinate and an integer. A name identifies *one implementation*: two paths
listing the same name are declaring that they run the same code, which is
precisely the thing being surfaced.

### The evaluator (nine layers, run by both winding routes)

Everything from an exact rational coordinate to an Arb ball for `H_t(z)` at
that point:

1. exact rational input conversion (`instrument._exact_q` / `_q_to_arb` / `_as_acb`)
2. kappa by the self-duality linear solve at `s0 = 3/4 + 3i/2` (`instrument.kappa_ball`, Arb Hurwitz zeta)
3. period-5 coefficient table `a_n = (1, kappa, -kappa, -1, 0)` (`instrument._truncated_integrand`)
4. truncated omega by the theta recurrence `q^{n^2}` (`instrument._truncated_integrand`)
5. series truncation tail bound (`instrument._series_tail_finite` via `_omega_tail_upper`)
6. discarded-u-tail bound on `[U, inf)` (`instrument._u_tail`)
7. integration limit policy `U` (`instrument.default_U`)
8. rigorous adaptive integrator (flint `acb.integral`)
9. ball arithmetic backend: python-flint 0.9.0 (Arb)

### Route 1, segment-argument winding (`winding.py`)

Layers 1 to 9, then:

10. uniform second-derivative bound `M2` by the shifted u-contour (`winding.second_derivative_bound`)
11. chord-tube segment decision with dyadic subdivision (`winding._chord_clearance`, `winding.winding_rectangle`)
12. integer from the sum of per-segment `Arg q` divided by `2 pi` (`winding.winding_rectangle`)

### Route 2, H'/H ball quadrature (`winding_quad.py`)

Layers 1 to 9, then:

10. panel-local Taylor models of `H` and `H'` with explicit remainder balls (`winding_quad.moment_integrals`, `winding_quad.taylor_remainders`)
11. contour quadrature of `H'/H` along the four edges (`winding_quad.main`)
12. integer from the contour-integral ball (`winding_quad.main`)

### Route 3, the DHFlow argument-principle count (`crosscheck_dhflow_winding.py`)

1. float input conversion (mpmath `mpf`/`mpc` from the exact box rationals)
2. kappa by the `zeta.epstein` mpmath linear solve (different implementation, **same equation** as `instrument.kappa_ball`)
3. `omega_dh` direct summation with a term-size stopping rule (`flow_repair.probe.omega_dh`)
4. Phi_DH memoised at fixed quadrature nodes (`flow_repair.probe.phi_dh_raw`)
5. composite Gauss-Legendre rule on `[0, U]` with an oscillation-resolving panel count (`flow_repair.probe.DHFlow`)
6. float arithmetic backend: mpmath at dps 130
7. uniform boundary sampling with continuous-argument tracking and step refinement (`crosscheck_dhflow_winding.winding_sampled`)
8. integer from the total argument divided by `2 pi` (`crosscheck_dhflow_winding.winding_sampled`)

### Route 4, the quadrature-free ball evaluator (`crosscheck_quadfree.py`)

1. exact rational input conversion (`crosscheck_quadfree.q`, its own)
2. kappa from the Gauss sum `tau(chi)` of the odd character mod 5 (`crosscheck_quadfree.kappa_gauss`, a **different equation**)
3. `F(s)` by Hurwitz zeta, no series in u and no quadrature (`crosscheck_quadfree.F_ball`)
4. Taylor in t from `dH/dt = -d^2H/dz^2`, coefficients by `acb_series` (`crosscheck_quadfree.F_taylor`)
5. explicit Taylor truncation remainder bound (`crosscheck_quadfree.taylor_remainder`)
6. ball arithmetic backend: python-flint 0.9.0 (Arb)

---

## 3. What each cross-check is and is not evidence about

**Routes 1 and 2 agreeing** is evidence that the two integer-extraction
schemes agree: the chord-tube segment decision with its `M2` bound, and the
panel-local Taylor model with its contour quadrature. It is evidence about
nothing in the evaluator. A fault in the kappa solve, in the theta
recurrence, in either tail bound, in the `U` policy, or in `acb.integral`
would move both routes identically and both would still agree.

There is a second caveat the layer count does not carry, and it is the
sharper one: **route 2 ran only at `t = 23/400`, and on its own recipe box
rather than route 1's**, because route 1's output file did not exist when it
ran (`winding_quad_results.json`, field `route1_box`). So even the
bookkeeping agreement is one t and one box wide. The stretch value that
carries the published floor, `t = 36/625`, has no route-2 witness at all.

**Route 3 (DHFlow) agreeing** is evidence about the whole evaluator and the
whole integer extraction, since it duplicates all of it: radius 0, no shared
layer. It is float grade by construction, so it cannot decide an integer;
its job is to catch a wrong one. It ran at **both** published t values, on
route 1's own boxes, which makes it the first second witness the headline
value `0.0576` has had.

One thing route 3 does **not** duplicate: its kappa comes from
`zeta.epstein.kappa`, the mpmath form of the *same* self-duality linear
solve `instrument.kappa_ball` runs in balls. Different implementation, same
equation. Agreement between routes 1 and 3 is therefore not evidence about
the equation that defines kappa.

**Route 4 (quadrature-free) agreeing** is evidence about everything in the
evaluator except the ball arithmetic itself, and it is the leg that closes
the kappa gap: it derives kappa from the Gauss sum `tau(chi)`, a different
equation with different failure modes. It carries balls with an explicit
remainder, so its agreements are ball overlaps and not float comparisons.
Its single shared layer, python-flint, is *reconvergent* in the director-run
sense: independent middles funnelling back through one arithmetic.

---

## 4. The measured agreements

### Route 3, argument-principle counts (`crosscheck_dhflow_results.json`)

mpmath dps 130, `DHFlow` with 5814 nodes, 256 boundary evaluations per box,
every consecutive argument step under 0.40 radians.

| t | box | total argument | N | instrument |
| --- | --- | --- | --- | --- |
| 23/400 | Re in [122929/512, 123185/512], Im in [3/512, 61/1024] | 6.283185307179587 | 1.0000000000000002 | 1 |
| 36/625 | Re in [245909/1024, 123159/512], Im in [3/1024, 35/1024] | 6.283185307179587 | 1.0000000000000002 | 1 |

Minimum `|H_t|` on the boundary was 2.45e-84 at `t = 23/400` and 8.64e-85 at
`t = 36/625`, which is the scale that makes the count hard and is why the
instrument needs balls rather than floats.

### Route 4, evaluator agreement (`crosscheck_quadfree_results.json`)

* kappa: the Gauss-sum ball overlaps `instrument.kappa_ball` at 200, 400 and
  600 bits.
* `t = 0`: the Hurwitz-zeta ball overlaps `instrument.H_ball` at six points,
  heights 10 to 420.
* `t > 0`: the Taylor-in-t ball overlaps `instrument.H_ball` at five assorted
  points and at all eight distinguished points of the `t = 23/400` box
  boundary, at `K = 100` and 900 bits, zero mismatches.
* measured relative agreement on those eight points: **40.3 to 42.7 decimal
  digits**, limited by the instrument's own ball radius (about 1.17e-124
  against values about 1e-83, so about 41 digits of resolution). The gate's
  summary said "about 22 digits"; that was the width of the printed
  comparison, not a measurement, and the measurement is deeper.

---

## 5. The two validation gaps the gate named, and what replaced them

Both were the same kind of defect: a check pointed somewhere the claim does
not live. Both are repaired in `validate.py`, and the superseded text is
kept at each check rather than deleted.

### (i) The `mpmath.iv` cross-leg pointed at a function no decision path calls

`validate.py` check 5 built `Phi_DH(u)` in mpmath's directed-rounding
interval context and compared it against `instrument.phi_ball`. Everything
in that sentence was true and it checked the wrong function: **`phi_ball` is
called by no decision path**, because `_H_core` carried its own inline copy
of the series. A fault in that copy was invisible to the second backend.

The repair has two parts. `instrument._truncated_integrand` was hoisted out
of `_H_core` as a module-level factory, unchanged in operations, order and
precision, so the callable the integrator receives is reachable. Check 5 now
evaluates that exact callable at seven points, real and complex `z`, both
the cosine and the sine branch, including a point on the `t1` box boundary,
against an iv leg that sums the series **term by term with one `exp` per
term** while the Arb leg walks the recurrence
`q^{n^2} = q^{(n-1)^2} q^{2n-1}`.

The refactor moved no number, checked two ways. `H_ball` at
`z = 240.4165 + 0.02i`, `t = 23/400`, prec 420 returns midpoint
`4.3658433958660405e-83` and radius `1.4894837452822593e-124`, bit-identical
to the values already in `validation.json`. And re-running
`winding_rectangle` on both stored boxes reproduces every decided field
exactly:

| t | status | N | segments | H evals | min chord margin | min ball margin | winding ball width | M2 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 23/400 | decided | 1 | 71 | 71 | 0.02 | 40.32 | 1.8935338382884234e-40 | 1.1886642645115153e-78 |
| 36/625 | decided | 1 | 79 | 79 | 0.02 | 39.87 | 5.454660423479934e-40 | 1.137082903400534e-78 |

`winding_results.json` was therefore not rewritten: there was nothing in it
to change.

**Measured purchase.** Planting a fault in the recurrence, seeding
`w = q^2` instead of `q^3` so every term carries the wrong power of `q`, is
caught at 6 of the 7 points. The point that misses is `u = 5/2`, where
`exp(-pi e^{2u}/5)` is about `e^{-93}` and the truncated sum is its own
first term to well below the interval width. A check at large `u` sees only
`n = 1`; that is the blind spot to know about.

### (ii) The tail bounds had no check with any purchase

The instrument adds two hand-derived error balls to every `H` value:
`_series_tail_finite` (the series truncated at `N` on `[0, U]`) and
`_u_tail` (the integral discarded beyond `U`). An adversary re-derived both
and found them valid in 59 of 59 tests. Nothing in `validation.json` could
see them: at every containment point they sit 36 to 41 orders of magnitude
below the delivered ball radius, so a bound could be wrong by thirty orders
and every containment row would still read `True`.

New check 6 compares each bound against a high-precision mpmath computation
of the **true remainder it bounds**, and reports the domination ratio. The
difficulty of doing this honestly is worth stating: at the instrument's
working `N = 27` the true series remainder is about 1e-215 and at the
working `U = 51/16` the true discarded integral is about 1e-161, so mpmath
at dps 90 returns exactly zero for both and the comparison is vacuous. Every
row states a working precision at which the true remainder is resolved, and
records the quadrature's own error estimate.

Series truncation tail, `bound / true`:

| point | N | true | bound | ratio |
| --- | --- | --- | --- | --- |
| working N, t = 0, z = 10 | 27 | 1.32e-215 | 4.95e-210 | 3.7e5 |
| working N, the t1 box point | 27 | 1.25e-215 | 9.47e-210 | 7.6e5 |
| working N, the t1 box point, H' | 27 | 5.80e-219 | 3.02e-209 | 5.2e9 |
| N = 8, \|Im z\| = 1 | 8 | 3.52e-29 | 4.73e-17 | 1.3e12 |
| **\|Im z\| = 5, stress** | 12 | 8.25e-48 | 2.14e-34 | 2.6e13 |
| **\|Im z\| = 20, stress** | 12 | 1.89e-47 | 1.76e-06 | 9.4e40 |
| **\|Im z\| = 50, stress, H'** | 12 | 4.47e-50 | 9.20e+46 | 2.1e96 |
| tiny N = 3, H' | 3 | 8.99e-10 | 2.64e+01 | 2.9e10 |

Discarded-u tail, `bound / true`:

| point | U | true | bound | ratio |
| --- | --- | --- | --- | --- |
| working U, t = 0, z = 10 | 51/16 | 1.10e-161 | 8.78e-161 | 8.02 |
| working U, the t1 box point | 51/16 | 2.10e-161 | 1.68e-160 | 8.03 |
| working U, the t1 box point, H' | 51/16 | 7.57e-162 | 5.36e-160 | 70.8 |
| **working U, \|Im z\| = 5, stress** | 51/16 | 8.82e-155 | 1.38e-153 | 15.6 |
| **\|Im z\| = 20, stress** | 5/2 | 3.41e-20 | 1.02e-18 | 30.0 |
| **\|Im z\| = 20 at the instrument's own U** | 105/32 | 5.18e-166 | 8.50e-165 | 16.4 |
| **\|Im z\| = 50 at the instrument's own U, H'** | 217/64 | 1.40e-167 | 2.76e-166 | 19.7 |
| \|Im z\| = 50 at U = 5/2, deliberately too small | 5/2 | 5.07e+13 | refused | n/a |
| small U, large t | 3/2 | 2.30e-04 | 7.33e-03 | 31.9 |
| U at its floor | 1 | 5.05e-03 | 5.49e-02 | 10.9 |

The stress regime is the one the gate asked for: `|Im z|` up to 50, where
`|cos(zu)|` grows like `e^{|Im z| u}` and both bounds lean on the
`|cos(zu)| <= cosh(yu) <= e^{yU}` step. If that step were wrong this is
where it would fail first, and it does not.

The refusal row is not a failure. `_u_tail` returns `None` exactly when its
own hypothesis `c = pi/5 - (t U^2 + (3/2+y) U) e^{-2U} > 0` cannot be
decided, and `_H_core` then raises `"tail bound not established ... raise U"`
rather than integrating. The companion rows at `U = default_U(t, |Im z|,
420)`, the limit the instrument itself would pick, show the bound existing
and dominating at exactly the parameters the instrument would use.

**Blindness factor: 8.02.** That is the smallest domination ratio over all
eighteen rows, so a bound deflated by more than about a factor of 8 is
caught at one of these points and a bound deflated by less is not. Reported
because `docs/25`'s standing consequence is that a lesion threshold without
a blindness radius is half a measurement, and because `controls.py`'s
control 5 is the same lesson in the other direction: a deflated `M2` makes
`winding.py` return a wrong integer with the health metric moving the wrong
way.

Grade for all of check 6: **measured** (mpmath floats; the true remainders
are not enclosed). Necessary, not sufficient, exactly like
`winding.measured_h2_guard`. Passing does not make a bound right; failing
proves one wrong.

---

## 6. What is still not covered

Stated plainly, because the point of this file is that an unstated bound is
worse than a small one.

* **The quadrature is single-backend.** `acb.integral` has no counterpart in
  mpmath's `iv` context, and the in-tree precedent
  (`zeta.rigor.enclose_weil_functional`) is flint-only and says so. Route 4
  is the answer to this, and it is a route rather than a backend: it reaches
  `H_t` with no quadrature at all, and agrees to the instrument's full
  resolution. What no leg supplies is a second *rigorous integrator*.
* **`M2` is exercised by no cross-route.** Routes 3 and 4 evaluate `H`;
  neither computes a uniform second-derivative bound. `M2` is checked only
  by `winding.measured_h2_guard`, a necessary-not-sufficient float sample,
  and lesioned by control 5 in `controls.py`. See `GATE.md` known assumption
  6.
* **Route 2's witness is one t and one box.** See section 3.
* **A declaration is not an attestation.** Nothing in
  `harness/independence.py` verifies that these layer lists are *complete*,
  and an undeclared shared layer is exactly the fault the structure cannot
  see. `independence_decl.check_anchors` pins ten attribute names against
  drift, which catches a rename that would silently make a layer name a
  fiction; ten anchors are not a completeness proof. That caveat is
  `docs/25`'s and it is why this section exists.
* **Route 3 and the kappa equation.** Recorded in section 3: route 3 does
  not duplicate it, route 4 does.

## 7. The sentence that replaces "two independent winding routes"

> The two winding routes share the whole evaluator (independence radius 9 of
> 12 declared layers, measured by `harness/independence.py`) and their
> agreement is evidence only about the two schemes that turn H-balls into an
> integer, at one t and one box. The independence the claim rests on comes
> from two other legs, both run and both landed in this directory: a DHFlow
> argument-principle count sharing no declared layer with the instrument,
> which returns N = 1 at both t = 23/400 and t = 36/625, and a
> quadrature-free ball evaluator with a different kappa equation, which
> reproduces `instrument.H_ball` at all eight boundary points of the t1 box
> to 40 or more decimal digits.

`MISSION.md` prediction P2 should be read against that. It said "the two
winding routes agree exactly (both decide N = 1)", which they did; what it
did not say, and what this file now says, is how little that agreement was
ever going to bound.
