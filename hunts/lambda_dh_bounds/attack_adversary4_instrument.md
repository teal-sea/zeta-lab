# Adversary 4 (the instrument and independence): findings

Scratch analysis, 2026-08-16. Written by an adversary tasked with breaking
`0.0576 < Lambda_DH <= 0.4006343708899557` at the instrument layer, not with
defending it. Every number below came from code I wrote from the definitions,
in `/tmp/claude-0/-home-user-zeta-lab/ea2c50e5-c6c1-5be9-ac30-eda79b8fac85/scratchpad/`
(`a4_tails.py`, `a4_indep.py`, `a4_box.py`, `a4_validation.py`,
`a4_independence.py`). No file already in this directory was modified.

## Verdict

The claim **survives** this lane. I could not break either tail bound, and I
built a route to `H_t(z)` that shares no layer with the instrument below the
Arb library itself. It agrees with `instrument.H_ball` at eight points on the
boundary of the very box that decides `N = 1` at `t = 23/400`, with a ball
**34 orders of magnitude tighter** than the instrument's.

What does not survive is the **independence story**. Measured with the
repository's own module, the two winding routes have an independence radius of
**8 of 11 layers**: they share the whole evaluator and diverge only in the
bookkeeping that turns a bag of H-balls into an integer. And three of the five
validation checks turn out to have no purchase on the parts of the instrument
that are neither a library call nor cross-checked.

---

## 1. Independence radius: 8 of 11, and the divergence is at the very end

`harness/independence.py` exists for exactly this question, and docs/25 records
why: two backends sharing a faulty input layer are one check. I declared both
routes and ran `compare` (`a4_independence.py`). Result:

```
route 1 (winding.py) vs route 2 (winding_quad.py): radius 8 of 11
```

The eight shared leading layers, in order, all inside `instrument.py`:

| # | layer | second implementation anywhere? |
|---|---|---|
| 1 | `_exact_q` / `_as_acb` exact rational coercion | no |
| 2 | `kappa_ball` (self-duality solve at s0 = 3/4 + 3i/2) | yes: `zeta.epstein` mpmath solve behind `KAPPA_REF`; and now my Gauss-sum route (section 4) |
| 3 | `_H_core` inline theta-recurrence truncation of omega to N | no interval or ball second implementation (see section 3) |
| 4 | `_omega_tail_upper` + `_series_tail_finite` | no |
| 5 | `default_U` | no |
| 6 | `_u_tail` | no |
| 7 | `flint acb.integral` on the truncated integrand over [0, U] | no |
| 8 | `H_ball` / `Hprime_ball` acb ball | no |

`reconvergent` is empty, which sounds reassuring and is not: it is empty
because the paths do not diverge until layer 9, after the answer has already
been computed. Everything either route contributes of its own is downstream
bookkeeping:

* route 1 distinct: `second_derivative_bound` (M2), chord clearance plus affine
  tube plus `Arg(H(z_b)/H(z_a))`, sum of segment arguments over 2 pi;
* route 2 distinct: `moment_integrals`, `taylor_remainders` plus the panel-local
  Taylor model, the outer `acb.integral` of H'/H, `I/(2 pi i)`.

**The honest statement.** The two routes are two ways of counting the winding
of one function-evaluator. Their agreement is evidence about the argument
principle bookkeeping and about the M2 / Taylor-model machinery. It is evidence
about nothing in layers 1 to 8. A wrong `kappa`, a wrong coefficient in the
inline series, an understated `_u_tail`, or a bug in `acb.integral` corrupts
both routes identically, and both will still report a decided integer with a
40-digit ball margin. Section 3 demonstrates that with a planted fault.

**One further reduction the code-level declaration does not show.** Both
routes' *distinct* layers reuse the same hand derivation. `winding.py`'s
docstring says its M2 tail is "copied from the instrument's `_u_tail` algebra";
`winding_quad.py`'s says its moment tails are "exactly the `instrument.py`
pattern with one extra factor". So the shared surface is wider than the shared
call graph: the mathematics of the u-tail is transcribed three times from one
derivation, and a mistake in that derivation would be present in all three
copies. My section 2 is the first check of it.

**Reporting note.** `MISSION.md` WP1 says "Two independent winding routes". By
the repository's own vocabulary that is an overstatement. The accurate phrase is
"two independent winding *counts* over one evaluator", and the evaluator needs
its own second implementation, which section 4 now supplies at the decision box.

---

## 2. The tail bounds: re-derived from scratch, no failure found

`a4_tails.py` re-derives both tails independently and compares each claimed
bound against the true remainder computed at much higher precision and much
larger truncation order. The hunt's formulas are never imported as ground truth;
they are only evaluated, at prec 600, for comparison.

### 2a. The omega tail (36 cases, all dominate)

Claimed: for `Re X >= rho > 0`, `|omega(X) - omega_N(X)| <= (N+1) r^{N+1}/(1-r)^2`
with `r = exp(-pi (N+1) rho / 5)`. I re-derived it (`|a_n| <= 1` from the ball
deciding `0 < kappa < 1`; `n^2 >= n(N+1)` for `n > N`; `sum_{n>=m} n x^n =
x^m (m - (m-1)x)/(1-x)^2`) and confirmed the closed form is right, including
the relaxation `(N+1) - N r <= N+1`.

Against the true remainder at dps 200 with 600 extra terms, over
`rho` in {1/100, 1/10, 1/2, 1, 3, 10} and `N` in {3, 5, 10, 20, 27, 40}:

| rho | N = 3 | N = 10 | N = 27 |
|---|---|---|---|
| 1 | 1.184 | 1.002 | true term underflows, bound 3.3e-213 |
| 1/2 | 1.959 | 1.066 | 3.52 |
| 1/10 | 35.4 | 3.84 | 4.66 |
| 1/100 | 7910 | 324 | 55.5 |
| 3 | 1.001 | 1.000 | bound 4.4e-641 |

(entries are bound/true). Every case dominates; the bound is essentially sharp
at the `rho = 1` used on the decision path. **No defect.**

### 2b. The series-truncation tail on [0, U] (12 cases, all dominate)

Claimed: `U * 4 exp(t U^2 + (3/2 + y) U) * tail1(N)`, one extra factor `U` for
the derivative. I re-derived it and got the identical expression. The
`|Im z|` growth is handled correctly: `|cos(zu)| <= cosh(y u) <= e^{y U}` on
`[0, U]`, and `|u sin(zu)| <= U e^{y U}`, which is exactly the `y_hi` that
`_H_core` passes in as `z_b.imag.abs_upper()`.

I pushed `|Im z|` hard, since that is where `cos(zu)` grows like `e^{|Im z| u}`:

| U | t | Re z | Im z | N | deriv | true error | claimed bound | ratio |
|---|---|---|---|---|---|---|---|---|
| 2 | 0 | 0 | 0 | 3 | no | 3.35e-5 | 3.28e-2 | 978 |
| 2 | 0 | 5 | 3 | 3 | yes | 6.92e-7 | 26.4 | 3.8e7 |
| 4 | 1/10 | 0 | **100** | 12 | no | 6.75e-48 | 1.66e+133 | 2.5e180 |
| 4 | 1/10 | 0 | **100** | 12 | yes | 3.61e-50 | 6.65e+133 | 1.8e183 |
| 51/16 | 23/400 | 240.4165 | 0.02 | 27 | both | below dps 90 | 9.5e-210 | dominates |
| 7/2 | 23/400 | 0 | 50 | 27 | no | below dps 90 | 1.8e-133 | dominates |

The growth is inside the bound, wildly so. At `Im z = 100` the bound is useless
(1e133) but it is a bound, and a useless bound produces a useless ball, which is
a visible refusal rather than a silent error. **No defect.**

### 2c. The integral tail beyond U (11 cases, all dominate)

Claimed: `4 e^{-cV}/(cV)` with `V = e^{2U}`, `c = pi/5 - (t U^2 + (3/2+y) U) e^{-2U}`,
one extra factor `U` for the derivative. I re-derived every step: `sum n r^{n^2}
<= r/(1-r)^2 <= 2r` once `r <= 0.29`; `u e^{-2u}` and `u^2 e^{-2u}` decreasing
for `u >= 1` giving `E(u) <= -c e^{2u}`; the substitution `v = e^{2u}` and
`int_V^inf e^{-cv} dv / v <= (1/V) int_V^inf e^{-cv} dv`; and for the derivative
`(log v)/v` decreasing for `v >= e`, with `log V = 2U`. All correct.

| U | t | Re z | Im z | deriv | true tail | claimed bound | ratio |
|---|---|---|---|---|---|---|---|
| 51/16 | 0 | 10 | 0 | no | 3.856e-161 | 8.782e-161 | 2.28 |
| 51/16 | 23/400 | 240.4165 | 0.02 | no | 7.384e-161 | 1.682e-160 | **2.28** |
| 51/16 | 23/400 | 240.4165 | 0.02 | yes | 2.115e-161 | 5.361e-160 | 25.3 |
| 205/64 | 23/400 | 240.4165 | 5 | no | 2.771e-159 | 1.222e-158 | 4.41 |
| 7/2 | 23/400 | 0 | 20 | no | 8.330e-270 | 3.606e-269 | 4.33 |
| 1 | 0 | 0 | 0 | no | 1.778e-2 | 5.494e-2 | 3.09 |

The bound at the actual decision parameters clears the true tail by a factor of
only 2.28, so this test has real discriminating power: a derivation error of a
factor of 3 would have shown up. It did not. **No defect.**

### 2d. Refusal behaviour under hostile parameters

`c <= 0`, `U < 1` and `t < 0` all raise, loudly, naming the reason. At
`Im z = 1000` with the auto `U`, the integrand overflows and the returned ball
is non-finite, which is a refusal and not an answer. I found no parameter regime
in which the instrument silently returns a ball that does not enclose `H_t`.

### 2e. The finding that comes out of 2a-2c anyway

The two tail bounds are the only part of the instrument that is a hand-derived
inequality rather than a library call, and **before this audit nothing tested
them**. Measured at the parameters `validate.py` uses:

| point | e1 (series tail) | e2 (u tail) | ball radius | validate.py allowance | allowance / e2 |
|---|---|---|---|---|---|
| z = 10, t = 0, prec 420 | 4.95e-210 | 8.78e-161 | 5.59e-125 | 1e-135 | **1.14e+25** |
| z = 240.4165+0.02i, t = 23/400, prec 420 | 9.47e-210 | 1.68e-160 | 1.49e-124 | 1e-135 | **5.95e+24** |
| z = 420.0625, t = 0, prec 600 | 2.43e-275 | 1.41e-219 | 1.18e-178 | 1e-190 | **7.07e+28** |

Both tails sit 36 or more orders of magnitude below the ball radius, and 25 or
more orders below the float reference's error allowance. `validation.json`
check 1 would therefore read `contains_float: true` on every row even if
`_u_tail` were understated by a factor of `1e25` and `_series_tail_finite` by a
factor of `1e75`. The eleven containment rows establish that the *integrator*
and the *series* are right. They establish nothing at all about the tails.
Section 2a-2c is, as far as I can tell, the first evidence about them.

---

## 3. Cross-backend: what the mpmath.iv leg actually covers

`validate.py` is honest that the quadrature is flint-only. It is less clear
about how little the second backend covers.

**The mpmath.iv leg (check 5) and the evenness check (check 3) both exercise
`phi_ball`. No decision path calls `phi_ball`.** `grep` over this directory:
`phi_ball` appears in `instrument.py` and in `validate.py`, and nowhere else.
`winding.py`, `winding_quad.py`, `strip.py`, `controls.py` and `census.py` all
go through `H_ball` / `Hprime_ball`, and `_H_core` contains its **own inline
copy** of the theta-recurrence series. The two copies are never checked against
each other.

Demonstration, with a fault planted in a **copy** of `instrument.py` loaded as a
separate module (the file on disk was not touched): drop the factor `n` from the
`n = 4 (mod 5)` coefficient inside `_H_core` only.

```
phi_ball(1/10), phi_ball(1/4), phi_ball(1/2): bit-identical under the fault
  -> validate.py checks 3 and 5, the only interval second-backend legs, are blind

z = 10, t = 0          good 0.003956249831075141   bad 0.003977305606553039
z = 122929/512 + 3i/512, t = 23/400
                       good 6.207819689750818e-82  bad 1.660848646933020e-07
```

At the box corner the planted typo moves `H` by 75 orders of magnitude and both
winding routes would inherit it identically. It would be caught by check 1 (the
mpmath float route), which is measured grade, and by nothing else.

**What has no second implementation at all**, stated plainly:

* `_H_core`'s inline series: checked only against a float route;
* `_series_tail_finite`, `_u_tail`, `_omega_tail_upper` at the `rho = 1` call
  site: checked by nothing until section 2;
* `default_U`: nothing, though it steers cost only and correctness rests on the
  tails;
* `acb.integral`: nothing, in this hunt or in the repository.

`kappa` is the exception and is well covered: the Arb self-duality solve, the
`zeta.epstein` mpmath solve behind `KAPPA_REF`, and now a third route below.

---

## 4. New evidence: a route to H_t that never calls acb.integral

This is the load-bearing addition. `a4_indep.py` and `a4_box.py` implement a
route written from the definitions, sharing with `instrument.py` only the Arb
library:

**kappa from the Gauss sum.** With `chi` the odd primitive character mod 5,
`chi(2) = i`, the coefficients `(1, kappa, -kappa, -1) = A chi + B chibar` with
`A = (1 - i kappa)/2`, `B = (1 + i kappa)/2`. The completed L-functions obey
`Lambda(1-s, chibar) = (i sqrt5 / tau(chi)) Lambda(s, chi)`, so `F(s) = F(1-s)`
forces `A/B = w := i sqrt5 / tau(chi)` and `kappa = (1 - w)/(i(1 + w))`, with
`tau(chi) = sum_{n=1}^{4} chi(n) e^{2 pi i n/5}` an exact ball. This is a
different equation from `kappa_ball`'s numerical solve at `s0 = 3/4 + 3i/2`.
Overlap with `kappa_ball` at 200, 400 and 600 bits: yes, all three.

**H_0 by Hurwitz zeta, no quadrature.** `F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2)
* 5^{-s} sum_{j=1..4} a_j zeta(s, j/5)`, all acb balls. Overlaps `H_ball(z, 0, prec)`
at z = 10, 10 + i/2, 240.4165, 240.4165 + 0.02i and 420.0625, at prec 420 and
600, with my radius (for example 1.19e-203 at z = 240.4165) far inside the
instrument's.

**H_t by Taylor in t, no quadrature.** From `d/dt H = -d^2/dz^2 H` and
`H_0(z) = F(1/2 + iz)`,

```
H_t(z) = sum_{k>=0} (t^k / k!) F^{(2k)}(1/2 + iz),
```

with the Taylor coefficients of `F` from `acb_series` (Hurwitz zeta series times
Gamma series) and a truncation remainder I derived and bounded explicitly:
`|M_k| <= int u^{2k} |Phi| cosh(yu) du` and `sum_{k>=K} x^k/k! <= x^K e^x/K!`
give `R_K <= (1/K!) int_0^inf 4 (t u^2)^K e^{t u^2} e^{(3/2+y)u} W(u) du`,
split at `U0 = 4` with a monotone head bound and a doubly-exponential tail.

At K = 100, prec 900, remainder ball 3.0e-158, at **eight points on the boundary
of the t1 winding box** (`Re` in [122929/512, 123185/512], `Im` in [3/512, 61/1024],
the box `winding_results.json` records for `t = 23/400`):

```
z = 240.095703125 + 0.005859375i
  taylor     6.207819689750818412859e-82 - 2.962088004188706337397e-83 i
  instrument 6.207819689750818412859e-82 - 2.962088004188706337397e-83 i
  taylor ball radius 3.00e-158   instrument ball radius 1.16e-124   overlap: yes
... 8 of 8 agree, 0 mismatches
```

My ball is **34 orders of magnitude tighter** than the instrument's at the same
point, so this is not a weak overlap test: the instrument's ball is confirmed to
contain a value pinned to 3e-158, and its midpoint sits far inside. The same
route also agrees at z = 10 with t = 23/400 and at z = 85.6993 + 0.3085i with
t = 3/100 (remainder 9.6e-77 against a ball radius 4.2e-54).

Coverage of this new leg: layers 2, 3, 4, 5, 6, 7 and 8 of the shared list, at
the decision parameters. It does **not** cover `_exact_q` (I convert inputs the
same way) nor Arb itself. Route 1 evaluates `H` at 71 points, so a point-valued
independent check is exactly the right shape for it; route 2 additionally
evaluates `H_ball` over wide z-balls, which I checked separately for enclosure
validity (a ball over a 1/64-box encloses `H_ball` at all nine interior grid
points tested).

A caution I have to record about my own work: my first implementation of this
route disagreed with the instrument at z = 10, t = 23/400 in the 11th digit. The
fault was mine, not the instrument's. `python-flint`'s series truncation length
is the **global** `ctx.cap`, default 10, and the `prec=` keyword on the
`acb_series` constructor does not change it, so every series operation was
silently truncated after 10 coefficients. With `ctx.cap` set correctly the two
routes agree to the full ball width. Anyone reproducing this should set
`ctx.cap` explicitly and assert `len(coeffs) == order`.

---

## 5. Validating the validation: the widening is load-bearing on 4 of 22 checks

`validate.py` widens the ball by `eps = 1e-(dps-15)` on both components before
`contains()`. The docstring says the allowance "sits orders of magnitude BELOW
the ball radius on every component whose value is nonzero". That is true, and it
is the wrong quantifier: on every component whose value is **zero** the
allowance is orders of magnitude ABOVE the ball radius. I recomputed four rows
with no widening (`a4_validation.py`):

| row | eps / radius (re) | eps / radius (im) | RAW contains re | RAW contains im | widening load-bearing |
|---|---|---|---|---|---|
| z = 10, t = 0 | 1.8e-11 | **1.14e+25** | yes | **no** | im |
| z = 85.6993, t = 0 | 1.4e-11 | **1.14e+25** | yes | **no** | im |
| z = 240.4165, t = 0 | 6.9e-12 | **1.14e+25** | yes | **no** | im |
| z = 240.4165+0.02i, t = 23/400 | 6.7e-12 | 6.3e-10 | yes | yes | neither |

So on the four real-z rows of `validation.json` (rows 1, 3, 6, 9; row 9 at
prec 600 has `eps/radius = 7.1e+28` on the imaginary component) the reported
`contains_float: true` is produced by the widening, not by the data. The
unwidened check fails: the instrument's imaginary ball has radius 8.78e-161 and
correctly contains 0, while the dps-150 float quadrature returns a spurious
imaginary part around 2.7e-154, roughly 3e6 ball radii out.

**This is the reference's round-off, not an instrument defect**, and the
docstring anticipates it. Two things are still worth fixing:

1. `validation.json` reports one boolean per row. It should report per
   component, so that a reader can see that four of the twenty-two component
   checks are decided by the allowance rather than by the comparison.
2. The fix is available and costs nothing: my Hurwitz ball route settles those
   same components with no widening at all. At z = 240.4165, t = 0 the two
   imaginary balls are `[+/- 1.21e-203]` (mine) and `[+/- 8.78e-161]`
   (instrument), and they overlap.

---

## 6. Out of my lane, recorded because I saw it

`winding_results.json` reports `min_ball_margin_digits = 40.32` and
`min_chord_margin_digits = 0.02` for the t1 run (39.87 and 0.02 for t2). The
binding constraint on route 1 is therefore not ball precision at all: it is the
chord-clearance versus Taylor-tube inequality, clearing by a factor of about
1.05. That inequality depends on `M2`, whose derivation is `winding.py`'s own
and whose tail algebra is transcribed from `_u_tail`. Route 2's decided ball is
`1 +/- 1.28e-12`, comfortable by comparison. Adversaries 2 and 3 own this;
I record only that route 1's margin is thin and rests on a bound whose
derivation is shared with the instrument.

Also noted: the two routes do not use the same box. Route 1 uses
`Re in [122929/512, 123185/512], Im in [3/512, 61/1024]`; route 2 uses
`Re in [2400953/10000, 2405953/10000], Im in [1/250, 3/50]`. They overlap and
both decide N = 1, which is fine and arguably better than identical boxes, but
the results files should say so in one place rather than leaving a reader to
diff two JSONs.

---

## 7. What I would change

1. Say "two independent winding counts over one evaluator", with the radius
   8-of-11 stated, wherever the hunt currently says "two independent winding
   routes". Declaring it with `harness.independence` costs ten lines.
2. Move the mpmath.iv leg from `phi_ball` to `_H_core`'s inline series, or
   delete `phi_ball` if nothing calls it. As it stands the only interval
   second-backend check in the hunt covers code no decision uses.
3. Add the tail-bound domination test (section 2) as a standing check. It is
   cheap, it has real discriminating power at the decision parameters
   (factor 2.28), and without it the tails are untested.
4. Report `validation.json` containment per component, and replace the four
   real-z imaginary-component rows with the unwidened Hurwitz comparison.
5. Land the quadrature-free route as a fifth validation check at the box
   corners. It is the only evidence in the hunt that the evaluator is right at
   `t > 0` without going through `acb.integral`.
