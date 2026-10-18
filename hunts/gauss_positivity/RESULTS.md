# gauss_positivity: RESULTS

**Nothing here is a result about the Riemann Hypothesis.** No zero exclusion,
no new bound on zeros, no claim of progress on RH. What follows is a reduction
of one classical criterion to a moment inequality, an analytic instrument for
that inequality, an asymptotic law, and two counterexamples that sharpen what
the criterion has to be. Grade: **measured** throughout, with the instrument
**hardened** by a second independent route.

Reproduce with:

```bash
.venv/bin/python hunts/gauss_positivity/reproduce.py
```

The script validates its ratio routine against the committed `zeta/li.py`
table (n = 1..40, 30 digits) and raises if it disagrees, before printing any
large-n number.

---

## 1. The two counterexamples, which are the sharpest thing here

The route that looked promising is "`Ξ` is the cosine transform of a positive
weight `Φ`, so Pólya's classical theorem forces the zeros of `Ξ` to be real."
**Both halves of that shortcut are false**, and both are killed by explicit
computed witnesses. Neither witness is a statement about ζ, and neither is a
counterexample to RH.

**(a) Convexity of the Fourier-side exponent is not sufficient.** The folklore
version asks for `φ ≥ 0` even with `φ(√x)` convex. Take `φ(t) = e^{-|t|}`:
`φ(√x) = e^{-√x}` has `d²/dx² = e^{-√x}(√x+1)/(4x^{3/2}) > 0`, so it is convex.
Its transform is `∫e^{-|t|}e^{izt}dt = 2/(1+z²)`, whose zeros are `z = ±i`.
Computed for `φ(t)=e^{-t^4}` (also convex exponent): `F(z)=∫e^{-t^4}e^{izt}dt`
has complex zeros, by argument-principle counts of 2, 2, 4 and 6 zeros in
rectangles of half-width 4, 6, 8 and 10 about the imaginary axis.

**(b) Positivity of the Fourier weight is *itself* not sufficient.** This is the
sharper and more consequential one. Let

```
    f(t) = 1 + cos t + cos 3t,
```

the cosine transform of the positive measure `δ₀ + δ₁ + δ₃`. Its zero equation
is `4cos³t − 2cos t + 1 = 0`, a cubic in `c = cos t` with **one real root and two
complex conjugate roots**. So `f` has complex zeros. Computed:

```
    t = 1.13662270206 + 0.319561426779j,     f(t) = 0.
```

`f` has 4 real zeros in `(0,10)` as well, so it is not degenerate.

**Consequence.** `Φ ≥ 0` does not imply real zeros, and a construction that
uses only the positivity of the weight proves nothing about `Ξ`. The correct
classical criterion is Schoenberg's: `Ξ` lies in the Laguerre–Pólya class iff
the weight is a **Pólya frequency function `PF_∞`**, which is equivalent to
total positivity of every translation kernel `det(Φ(x_i−y_j)) ≥ 0`. In the
moment form those determinants are the Hankel/Toeplitz determinants of the
moments. That is the target, and it is strictly sharper than positivity.

## 2. The reduction

From `zeta/li.py`'s own documented Mellin derivation, which the module already
pins by two independent routes:

```
    γ(n) = 8 n! b_n,   b_n = [z^{2n}] ξ(1/2+z) = J_{n-1} − J_n/4,
    J_k = I_k / (4^k (2k)!),   I_k = ∫₀^∞ u^{2k} w(u) du,
    w(u) = e^{u/4} ω(e^u) > 0  on the real axis.
```

`w > 0` is the only input used. `I_k` is then the k-th moment of a **positive**
measure on `[0,∞)`, so Cauchy–Schwarz gives, for all n,

```
    D_n := 1 − I_n²/(I_{n−1} I_{n+1})  ≥  0        (automatic)
```

and, with `q_n := γ(n)/γ(n−1) = n b_n/b_{n−1}` and `r_n := q_{n+1}/q_{n+2}`
(the Turán ratio `γ(n+1)²/(γ(n)γ(n+2))`),

```
    r_n = [(n+2)/(n+1)] · (1 − D_n) · (1 + O(J_n/J_{n−1})),   J_n/J_{n−1} = O(1/n²).
```

**So the Turán inequality `r_n ≥ 1` is, up to the stated correction, exactly
`D_n ≤ 1/(n+1)`**, a statement about the moment sequence of one explicit
positive weight, with no zeros in it.

Measured (exact quadrature, dps 80):

| n | `D_n` | `n D_n` | `1/(n+1)` |
| --- | --- | --- | --- |
| 100 | 4.94999923433e-3 | 0.49499992 | 9.90099010e-3 |
| 400 | 9.76518836015e-4 | 0.39060753 | 2.49376559e-3 |
| 1600 | 1.99572321184e-4 | 0.31931571 | 6.24609619e-4 |
| 3200 | 9.12230485529e-5 | 0.29191376 | 3.12402374e-4 |

`0 < D_n < 1/(n+1)` at every computed n, with `nD_n` decreasing across the whole
range. All-pass is **not** evidence for RH (`docs/08` section 3).

## 3. The analytic instrument (hardened)

For `u ≳ 1`, `ω(e^u) = e^{−πe^u}(1 + O(e^{−3πe^u}))`, so
`w(u) = exp(u/4 − πe^u + o(1))` and `I_n = ∫₀^∞ exp(Ψ(u))du` with
`Ψ(u) = 2n log u + u/4 − πe^u`, whose saddle satisfies

```
    ** π e^{u_*} = 1/4 + 2n/u_* **
```

Laplace: `I_n ≈ e^{Ψ(u_*)}√(2π/A)`, `A = −Ψ''(u_*) = 2n/u_*² + 2n/u_* + 1/4`.
Differentiating the Legendre-type conjugate gives `D_n ≈ 4/(u_*²A) ≈ 2/(n u_*)`.

Cross-check against exact quadrature (two independent routes, hence *hardened*):

| n | `D_exact` | `4/(u_*²A)` | relative error |
| --- | --- | --- | --- |
| 100 | 4.94999923433e-3 | 4.93127773143e-3 | 3.78e-3 |
| 400 | 9.76518836015e-4 | 9.74735969005e-4 | 1.83e-3 |
| 1600 | 1.99572321184e-4 | 1.99438651673e-4 | 6.70e-4 |
| 3200 | 9.12230485529e-5 | 9.11877025182e-5 | 3.87e-4 |

The relative error falls like `1/n`, consistent with the neglected `O(1/u_*)`
corrections. Saddle values: `u_* = 3.04416034523` (n=100), `5.85265634287`
(n=3200), `24.0013292` (n=10¹²), `41.8656534` (n=10²⁰), matching
`u_* = log n − log log n + O(1)`.

## 4. The asymptotic law

Eliminating `D_n` between `D_n ≈ 2/(n u_*)` and `u_* = log n − log log n + O(1)`:

```
    D_n     = 2/(n log n) · (1 + O(log log n / log n))
    r_n     = 1 + 1/n − 2/(n log n) + o(1/(n log n))
    n(r_n−1) → 1
```

| n | `u_*` | `1 − n(r_n−1)` | `2/u_*` | `2/(log n − log log n)` |
| --- | --- | --- | --- | --- |
| 10⁶ | 10.9688681 | 0.16710097 | 0.18233422 | 0.17873550 |
| 10¹² | 24.0013292 | 0.07999575 | 0.08332872 | 0.08226363 |
| 10²⁰ | 41.8656534 | 0.04665740 | 0.04777186 | 0.04736874 |

The three columns agree to a few percent with the gap shrinking. Grade
**measured**: the subleading term is not resolved and the constant is not
claimed exact, so the `1/log n` correction is a supported numerical law, not a
theorem. It is stated as such.

## 5. The Gate-3 rival: a correction, and the correct rival

**Correction notice.** An earlier version of this section, and the matching
paragraph in `journal.md`, claimed a "structural discrimination" reading

> `Xi_a(t) = xi(1/2+it+a) xi(1/2+it-a)`, so every on-line zeta zero produces
> `Xi_a` zeros at `t = 1/2 + i(gamma +- a)`.

**That is false and it was an algebra error.** The `a` was moved inside the
factor `-i(rho - 1/2)` when it does not belong there. The correct solution of
`1/2 + i(t+a) = rho` is `t + a = -i(rho - 1/2)`, so for `rho = 1/2 + i gamma`
the zero is at `t = gamma - a`, **real**. Computed:
`|Xi_a(13.884725141735)| = 9.914e-37` and `|Xi_a(14.384725141735)| = 5.551e-37`,
against `695.04` and `1180.41` at the values the earlier version claimed. The
claimed obstruction does not exist and was removed.

**What the algebra actually gives.** For a completed function
`Xi_f(t) = F(1/2 + it)` that is real and even in `t`, a zero `rho = sigma + i gamma`
of `F` produces a zero of `Xi_f` at `t = gamma - i(sigma - 1/2)`. So `t` is real
iff `sigma = 1/2`:

> **the real-rootedness of `Xi_f` in `t` is exactly the critical-line statement
> for `F`, transported. It is a genuine criterion, not a restatement of
> anything weaker.**

**This changes which rival is the right one.** For `W_a = zeta(s+a)zeta(s-a)`,
the zeros of `F_a = xi(s+a)xi(s-a)` are `rho +- a` for zeta zeros `rho`, and
the `t`-zeros of `Xi_a(1/2+it)` are real iff zeta's own zeros are on the line.
So `W_a` does **not** refute the criterion: its `t`-real-zero statement is
*zeta's* RH, which is not known to fail. `W_a` violates its own critical line in
`s` while satisfying the transported statement in `t`. Using it as the rival
here is a category error.

**Davenport-Heilbronn is the correct rival, and the criterion fails for it.**
`zeta/epstein.py` carries DH's completed function
`F(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2) f(s)` with `F(s) = F(1-s)`, real on the
critical line, and an off-line zero at
`sigma = 0.80851718245663738...` (`zeta.epstein.OFFLINE_ZERO_RE`). A zero of `F`
at `rho = sigma + i gamma` gives an `Xi_DH` zero at `t = gamma - i(sigma - 1/2)`,
whose imaginary part is `-(sigma - 1/2) = -0.3085171824566374`, nonzero.
Computed:

```
    t0 = 85.69934848537759 - 0.3085171824566374j,    |Xi_DH(t0)| = 4.74e-53
```

So **`Xi_DH` has a complex zero and the real-rootedness criterion genuinely
fails for Davenport-Heilbronn.** A criterion of the `PF_infinity` / all-real-zeros
shape therefore does discriminate, and DH is the rival that tests it. `W_a` is
not, and the `hunts/epp_herglotz` obligation is inherited with that distinction
made explicit rather than in the shape that hunt recorded.

**The `PF_infinity` obligation itself is still open.** Showing that DH's weight
is not `PF_infinity` is a different and harder computation than exhibiting a
complex zero of `Xi_DH`, and this hunt has not done it. What is established is
that the criterion has a discriminating rival and that the rival fails the
criterion in its zero form.

## 5a. A wrong measurement, kept in

An earlier attempt to test whether `Xi_a` has a positive weight used an
uncalibrated inversion `Phi_inv(u) = (1/2pi) int Xi(t) e^{-itu} dt` and returned
"positive". **That computation is wrong and is not evidence.** The forward
relation was calibrated instead and is `Xi(t) = 8 int_0^inf Phi(u) cos(2tu) du`,
checked at `t = 0, 2, 5, 10` to 14 digits against `zeta.core.xi`; the wrong
formula had `cos(tu)` for `cos(2tu)`.

## 5b. Newton's inequalities collapse to Turan: a proof, and a route closed

For the Jensen polynomial `J^{d,n}(X) = Σ_k C(d,k) γ(n+k) X^k` whose coefficients
are `A_k = C(d,k) γ(n+k)`, Newton's inequality at order `k` states
`A_k² ≥ A_{k−1} A_{k+1}`, i.e.

```
    γ(n+k)²                     C(d,k−1)C(d,k+1)        k(d−k)
    ────────────────  ≥  ──────────────────────  =  ─────────────────────
    γ(n+k−1)γ(n+k+1)               C(d,k)²           (k+1)(d−k+1)
```

(the second form uses `C(d,k−1)C(d,k+1)/C(d,k)² = k(d−k)/((k+1)(d−k+1))`, exact).

The right-hand side is **strictly less than 1 for every `d ≥ 2` and every
`1 ≤ k ≤ d−1`**, because `k < k+1` and `d−k < d−k+1`. Its maximum over the whole
allowed range is `0.93548387...` at `d = 59, k = 29`, and it increases toward 1
as `d` grows without ever reaching it.

The left-hand side is `> 1` whenever the `d = 2` Turán inequality
`γ(m+1)² ≥ γ(m)γ(m+2)` holds, and by the reduction of section 2 it holds with
margin `1/γ`-controlled decay. Hence:

> **Proposition.** If the Turán inequality `γ(m+1)² ≥ γ(m)γ(m+2)` holds for all
> `m ≥ 0`, then Newton's inequalities for `J^{d,n}` hold for every `d ≥ 2`,
> every `n ≥ 0` and every order `k`.

**Proof.** Immediate from the two displays: `LHS > 1 > RHS`. ∎

Verified numerically over `d = 2..59`, all `k`, against the minimum of the
left-hand side over `m = 0..150`: the worst ratio `RHS/LHS` is `0.9321` at
`d = 59, k = 29`, i.e. the bound is never approached.

**Consequence, which is the point of the section.** The family of Newton
inequalities over all degrees `d` and all orders `k` adds **nothing** beyond the
classical `d = 2` Turán inequality for the ξ-coefficients. In particular
`newton_battery.py`'s table, which scans `d ≤ 10`, `n ≤ 60`, is measuring the
same underlying inequality repeatedly with different `C(d,k)` normalisations,
and its tiny "margins" are that normalisation and not a near-failure. Chasing
Newton at higher `d` is a closed route, closed by the elementary computation
above rather than by a search that failed to find a violation.

This does **not** close the higher-order problem: **hyperbolicity of `J^{d,n}` is
strictly stronger than its Newton inequalities**, and it is hyperbolicity that
GORZ leave open for a finite set of `n` at each `d ≥ 4`. What the proposition
says is that the Newton/real-rootedness-necessary family is not the way in.

## 5c. Why the higher-degree hyperbolicity gap cannot be attacked from below

This was the hunt's chosen next step and it is now closed, by a measured
mechanism inherited from `hunts/jensen_clock` rather than by a failed search.
The reasoning is recorded because it is the difference between a route that was
tried and a route that is structurally blind.

`hunts/jensen_clock` establishes that the finite Jensen degree acts on the zeros
as **de Bruijn-Newman heat with effective time**

```
    t_eff(d) = |x0| / (8d),     x0 = (rho - 1/2)^2  the pair's image,
```

and measures the Davenport-Heilbronn pair's own landing time as `t* = 0.0441263`
(pair 1, `sigma = 0.80851718, gamma = 85.69935`), reached only at
`d* = 20785.13`. For that pair `|x0| = 7344.47351367`, so:

| d | `t_eff(d)` | versus `t* = 0.0441263` |
| --- | --- | --- |
| 2 | 459.03 | 10^4x overheated |
| 10 | 91.81 | 2081x overheated |
| 32 | 28.69 | 650x overheated |
| 1000 | 0.9181 | 21x overheated |
| 20785 | 0.04417 | at landing (d* from hunts/jensen_clock) |

**The degree itself real-roots the polynomial before it can be inspected.** So a
hyperbolicity scan at degree `d` below the configuration-dependent threshold
`d*(x0) = |x0|/(8t*)` **cannot fail**, and a pass there carries no information.
Measured on zeta directly: `min |Im root|/|root|` over the roots of `J^{d,0}` is
`0.0` for every `d = 2..24`, i.e. the condition is slack throughout the reachable
range, not tight. This is consistent with `newton_battery.py` and the earlier
hyperbolicity scans passing everywhere: they were in the blind region.

**Consequence for `docs/12`'s statement of the gap.** That page says GORZ leave
"a finite unresolved set for every `d`". The refinement is that the unresolved
set at small `d` is not merely unresolved but *unfalsifiable in principle by a
hyperbolicity scan at that `d`*: any actual violation has been smoothed away by
the time the polynomial is written down, and becomes visible only at
`d` on the order of `10^4` to `10^5` for a height-85 pair, larger for higher
zeros since `|x0|` grows like `gamma^2`. A certificate strategy for the higher
order must therefore operate **above** `d*(x0)`, which is not a degree range any
of this hunt's tables reach.

**Also a null control, inherited.** `jensen_clock`'s P5 shows the effect tracks
zero **configuration, not arithmetic**: a pair planted into zeta's own
gamma-table is detected on the same clock, and pure configuration-only N-body
dynamics predicts the timing to `0.094%`. So a hyperbolicity certificate at high
`d` reads the positions of the zeros, not the Euler product, which is the same
information-class finding `hunts/epp_herglotz` section 6 and
`hunts/local_positivity` reach from other directions.

This hunt does not claim to have tested high-degree hyperbolicity, and makes no
statement about it. It claims that the low-degree version is blind, with the
mechanism and the numbers above.

## 6. What this is and is not

- **Is:** an exact reduction of the Turán inequality to a Cauchy–Schwarz
  deficit of the moments of one explicit positive weight; an analytic saddle
  instrument valid at arbitrary n with a shrinking cross-checked error; a
  measured asymptotic law with a `1/log n` correction; two computed
  counterexamples that move the target from "positivity" to Schoenberg's
  `PF_∞`; and an exact structural obstruction for the `W_a` rival.
- **Is not:** a proof of the Turán inequality (already known unconditionally,
  Csordas–Norfolk–Varga 1986, and this hunt does not improve on it), any
  statement about RH, or a resolution of the `PF_∞` obligation for the rivals.
- **Why it may still matter.** The `D_n` reduction is the `2×2` case of the
  total-positivity family, and the same reduction is available at higher order
  where the Jensen hyperbolicity at `d ≥ 4` has a finite unresolved set for each
  degree (Griffin–Ono–Rolen–Zagier). If the saddle instrument extends there, it
  would give an explicit threshold, which is a sharper object than
  "sufficiently large n". That is a proposal, not a result, and it is the
  next experiment, not a claim.

> **Correction, 2026-10-18 (on landing as hunt #134).** The bullet above reads the
> frontier from GORZ 2019 alone and is stale. Griffin, Ono, Rolen, Thorner, Tripp
> and Wagner (*Adv. Math.* 397 (2022) 108186, arXiv:1910.01227v3) already prove
> `J^{d,n}` hyperbolic for `n ≥ c·e^{d/2}` (Theorem 1.1), and prove that RH verified
> to height `T` gives hyperbolicity for all `n ≥ 0` when `d ≤ ⌊T⌋²` (Theorem 1.2,
> generalising Chasse, who had `d ≤ 2·10^17`). With Platt's `T = 3.06·10^10` that
> is their Corollary 1.3, `d ≤ 9.36·10^20`. So there is no finite unresolved set at
> any degree an explicit threshold computation could reach. The experiment proposed
> above was done before this hunt opened. The live frontier is the
> polynomial wedge `n³log²(n+2) ≥ K d⁵` of Holland (arXiv:2608.08682, August 2026),
> whose constant is not computed; hunt #135 (`hunts/jensen_wedge/`) is scoped
> against it. The bullet is kept as written, because it is what this hunt believed.

## 7. The doors

Per `AGENTS.md`, every hunt that measures a ceiling owes this section. This hunt
measures no ceiling, so the honest version is short.

1. **Active constraints.** At the computed optima the binding object is the
   saddle location `u_*` through `D_n ≈ 2/(n u_*)`; the moment inequality
   `D_n ≤ 1/(n+1)` is satisfied with `nD_n` falling from 0.495 to 0.292 over
   n = 100..3200 and no sign of saturating, so nothing is tight in the computed
   range and there is no measured shadow price to report.
2. **Frozen constants.** One: the weight `w(u) = e^{u/4}ω(e^u)` is ζ's, not a
   free choice. Relaxing it is exactly the rival experiment in section 5, and
   that is the door worth opening next.
3. **Information class.** Everything here reads the coefficients `γ(n)` (or
   equivalently the moments `I_k`) and nothing else. By `hunts/epp_herglotz`
   section 6 that class cannot, on its own, locate the critical line; the
   reduction's value is as a finite form of `PF_∞`, which is a *structural*
   condition on the weight and therefore not confined to that class.