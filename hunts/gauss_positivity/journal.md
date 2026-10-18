# Journal: the Gauss-positivity lane, session 2026-10-03

Chronological, with the errors kept in. Grades per `ALIGNMENT.md` section 2:
*measured* is one route at working precision, *hardened* is two independent
routes agreeing, *decided* is an enclosure that settles a sign.

## Dead on arrival: the folklore Pólya convexity criterion

The tempting shortcut is "Φ ≥ 0 and even, with a convex Fourier-side exponent,
so Pólya's 1926 theorem gives only real zeros." **It is false and this hunt
killed it before it could be believed.** Computed with `mpmath`:

* `φ(t) = e^{-t^4}` is positive, even, and has a convex exponent `h(t)=t^4`.
* `F(z) = ∫ φ(t)e^{izt} dt` has **complex** zeros. Zero count by the argument
  principle on rectangles: winding 2 for `R=4, cy=2`, 2 at `R=6,cy=4`, 4 at
  `R=8,cy=6`, 6 at `R=10,cy=8` (counts are the number of zeros enclosed, so
  the outermost rectangle encloses 6 and the box excludes the real zeros on
  `|z|<20`, of which there are 7 sign changes).
* The cheapest true witness is even simpler: `φ(t)=e^{-|t|}` has convex
  `φ(√x)`, and `F(z)=2/(1+z²)` has zeros at `z=±i`.

So convexity of the exponent is not sufficient, and any usable criterion is
strictly sharper than the folklore version. `docs/08` section 4.3's two-sided
test applies: a criterion that admits a witness with complex zeros is refuted,
and neither witness is a statement about ζ.

## The criterion is sharper than positivity: a second counterexample

The first counterexample (`e^{-t^4}`) shows convexity is insufficient. A second,
much sharper one shows **positivity of the Fourier weight is itself
insufficient**, which is the point the whole lane turns on:

    f(t) = 1 + cos t + cos 3t

is the cosine transform of the positive measure `delta_0 + delta_1 + delta_3`
(three atoms of weight 1), so its weight is positive. It has
`4 cos^3 t - 2 cos t + 1 = 0` as its zero equation, and that cubic in
`c = cos t` has one real root and two complex conjugate roots, so `f` has zeros
at complex `t`. Computed: `t = 1.136622702 + 0.3195614268j`, `f(t) = 0`. It also
has 4 real zeros in `(0,10)`.

**So `Phi >= 0` does not imply that the transform has only real zeros.** The
correct classical criterion is Schoenberg's: `Xi` is in the Laguerre-Polya class
iff the weight is a Polya frequency function `PF_infinity`, and `PF_infinity` is
equivalent to **total positivity of every translation kernel**
`det(Phi(x_i - y_j)) >= 0` for all `n` and all ordered tuples. Those
determinants, in the moment formulation, are exactly the Toeplitz/Hankel
determinants of the moments `I_n`.

**This is what makes `D_n` the right object.** `D_n >= 0` is the `n`-th order
total-positivity condition in its simplest form (the `2x2` Hankel case); the
Turán inequality is the statement that the `2x2` case holds with room to spare
controlled by the moment shift. The Lane is therefore not a portfolio of
restatements: it has a named classical target (`PF_infinity` of `Phi`) and the
`D_n` family is the correct finite approximation to it.

## The reduction that worked

Everything below is validated against the committed `data/li_gamma_*.json`
table before use.

Starting from `zeta/li.py`'s own derivation (Riemann's Mellin representation,
which the module documents and tests):

    gamma(n) = 8 n! b_n,   b_n = [z^{2n}] xi(1/2+z) = J_{n-1} - J_n/4,
    J_k = I_k / (4^k (2k)!),   I_k = int_0^inf u^{2k} w(u) du,
    w(u) = e^{u/4} omega(e^u),   w(u) > 0 on the real axis.

`w > 0` is the load-bearing input: `I_k` is then the k-th moment of a
*positive* measure on `[0,inf)`, so Cauchy-Schwarz applies and

    D_n := 1 - I_n^2 / (I_{n-1} I_{n+1})  >=  0     automatically.

With `q_n := gamma(n)/gamma(n-1) = n b_n / b_{n-1}` and `r_n := q_{n+1}/q_{n+2}`
(the Turán ratio `gamma(n+1)^2 / (gamma(n) gamma(n+2))`),

    r_n = [(n+2)/(n+1)] * I_n^2/(I_{n-1}I_{n+1}) * (1 + O(J_n/J_{n-1}))
        = [(n+2)/(n+1)] * (1 - D_n) * (1 + O(J_n/J_{n-1})).

**So the Turán inequality `r_n ≥ 1` is, up to the correction
`J_n/J_{n-1} = O(1/(n^2))`, exactly the statement `D_n ≤ 1/(n+1)`.** The
positivity of `w` gives `D_n ≥ 0`; the inequality `D_n ≤ 1/(n+1)` is the whole
content, and it is a statement purely about the moment sequence of the positive
weight `w`, with no zeros anywhere in it.

Measured (exact quadrature, `--dps 80`):

| n | `D_n` | `n D_n` | `1/(n+1)` |
| --- | --- | --- | --- |
| 100 | 4.9499992e-3 | 0.4949999 | 9.901e-3 |
| 400 | 9.7651884e-4 | 0.3906075 | 2.494e-3 |
| 1600 | 1.9957232e-4 | 0.3193157 | 6.246e-4 |
| 3200 | 9.1223049e-5 | 0.2919138 | 3.124e-4 |

`D_n > 0` throughout and `D_n < 1/(n+1)` throughout, with `nD_n` decreasing
slowly across the whole range.

**An error kept in.** A first version of the ratio routine dropped the index
offset in `J` and returned `r_10 = 1.1145` against the committed table's
`1.0276`. It was caught by validating against `zeta/li.py` *before* any large-n
use, and the fix carries the exact `b_n` rather than the asymptotic shortcut.
A second variant, `n(r_n-1) -> c` with `c` estimated at 0.9 by naive geometric
extrapolation of the doubling decrements, is also wrong: the ratio of successive
decrements climbs (0.843, 0.843, 0.846, 0.852) rather than staying constant,
which is the signature of a `1/log n` correction, not a limit.

## The analytic instrument

For `u >= ~1`, `omega(e^u) = e^{-pi e^u}(1 + O(e^{-3 pi e^u}))`, so
`w(u) = exp(u/4 - pi e^u + o(1))` and

    I_n = int_0^inf exp(Psi(u)) du,   Psi(u) = 2n log u + u/4 - pi e^u,

with saddle `Psi'(u_*) = 0`:

    ** pi e^{u_*} = 1/4 + 2n/u_* **            (the saddle equation)

Solved numerically: `u_* = 3.04416034523` (n=100), `5.85265634287` (n=3200),
`24.0013292` (n=1e12), matching `u_* = log n - log log n + O(1)`.

Laplace: `I_n ≈ exp(Psi(u_*)) sqrt(2 pi / A)` with
`A = -Psi''(u_*) = 2n/u_*^2 + 2n/u_* + 1/4`. Legitimate differentiation of the
Legendre-type conjugate gives, to leading order,

    D_n ≈ 4 / (u_*^2 A) ≈ 2 / (n u_*).

**Cross-check.** `4/(u_*^2 A)` against the exact `D_n`:

| n | `D_exact` | `4/(u_*²A)` | relative error |
| --- | --- | --- | --- |
| 100 | 4.9499992e-3 | 4.9312777e-3 | 3.45e-5 |
| 800 | 4.3970425e-4 | 4.3920850e-4 | 2.92e-7 |
| 3200 | 9.1223049e-5 | 9.1187703e-5 | 7.12e-9 |

The relative error falls like `1/n`, consistent with the neglected
`O(1/u_*)` corrections. This is a *hardened* instrument: two independent routes
(quadrature and saddle) agree with a stated and shrinking error.

## The asymptotic law

Eliminating `D_n` between `D_n ≈ 2/(n u_*)` and `u_* = log n - log log n + O(1)`:

    D_n = 2/(n log n) * (1 + O(log log n / log n))
    r_n = 1 + 1/n - 2/(n log n) + o(1/(n log n))
    n (r_n - 1) = 1 - 2/log n + o(1/log n)  ->  1

Measured against the saddle route:

| n | `u_*` | `1 - n(r_n-1)` | `2/u_*` | `2/(log n - log log n)` |
| --- | --- | --- | --- | --- |
| 1e6 | 10.96887 | 0.16710097 | 0.18233422 | 0.17873550 |
| 1e12 | 24.00133 | 0.07999575 | 0.08332872 | 0.08226363 |
| 1e20 | 41.86565 | 0.04665740 | 0.04777186 | 0.04736874 |

The three columns agree to a few percent with the gap shrinking, so the
`1/log n` law with `r_n - 1 -> 1/n` is supported. It is **not** claimed exact
at this stage: the subleading term is not resolved, and the honest grade is
*measured* for the law and *hardened* for the instrument.

## A calibration error, kept in

The first attempt to test whether the shifted rival `W_a` has a positive weight
used an uncalibrated inversion `Phi_inv(u) = (1/2pi) int Xi(t)e^{-itu}dt` and
returned "positive". **That computation was wrong and is not evidence.** The
forward relation was calibrated instead and is `Xi(t) = 8 int_0^inf Phi(u)
cos(2tu) du`, checked at `t = 0, 2, 5, 10` to 14 digits against
`zeta.core.xi`. The wrong formula had `cos(tu)` rather than `cos(2tu)`, which
is a factor-and-argument error of exactly the kind `AGENTS.md` warns about, and
it is recorded here rather than deleted because the conclusion it produced
("W_a has a positive weight") is the opposite of interesting if true.

What survives is not what was first claimed. The first claim in this space was
that `Xi_a`'s zeros sit at `t = 1/2 + i(gamma +- a)`, off the real axis, giving
an unconditional obstruction for the rival. **That was an algebra error: the `a`
was moved inside the factor `-i(rho - 1/2)`.** The correct zero of `Xi_a` from an
on-line zeta zero is `t = gamma - a`, *real*, and the numeric check confirms it:
`|Xi_a(13.884725141735)| = 9.914e-37` against `695.04` at the claimed value.

The correct identification, which is more useful, is: for a completed
`Xi_f(t) = F(1/2+it)` with a zero `rho = sigma + i gamma` of `F`, the `t`-zero is
`t = gamma - i(sigma - 1/2)`, so **real iff `sigma = 1/2`**. The real-rootedness
of `Xi_f` in `t` is the critical-line statement, transported, and it is a genuine
criterion. For `W_a = zeta(s+a)zeta(s-a)` that transported statement is *zeta's*
RH, which is not known to fail, so **`W_a` is the wrong rival here**: it violates
its own critical line in `s` while satisfying the `t`-statement. That is a
category error that an earlier draft of this journal made.

**Davenport-Heilbronn is the correct rival and the criterion fails for it.**
DH's completed function has an off-line zero at `sigma = 0.80851718245663738...`
(`zeta.epstein.OFFLINE_ZERO_RE`), whose `t`-zero is
`85.69934848537759 - 0.3085171824566374j`, with `|Xi_DH(t0)| = 4.74e-53`. The
imaginary part is nonzero, so `Xi_DH` has a complex zero and the
real-rootedness criterion genuinely fails for DH. The `PF_infinity` obligation
for DH itself is still open and is not claimed.

## What this is and is not

* It does **not** touch RH. `r_n > 1` for all n is the Turán inequality, known
  unconditionally (Csordas–Norfolk–Varga 1986), and an all-pass table is not
  evidence for RH (`docs/08` section 3).
* What is possibly useful: an exact reduction of the Turán inequality to a
  Cauchy-Schwarz deficit of the moments of an explicit positive weight, an
  analytic saddle instrument for `D_n` at arbitrary `n`, and an asymptotic law
  with a clean `1/log n` correction. The reduction is the kind of object that
  could transfer to the higher-order Newton inequalities at `d ≥ 4`, which is
  where GORZ leaves a finite unresolved set for each degree.
* The rival gate has **not yet been run**. `W_a = ζ(s+a)ζ(s-a)` and
  Davenport-Heilbronn must be tried against any candidate criterion before
  anything is reported as more than an observation.
* The `D_n` reduction is a finite form of Schoenberg's `PF_infinity` condition
  on `Phi`, which is the correct classical target (see above). That is a
  statement about the shape of the problem, not a proof of anything.
## A route closed by proof: Newton's inequalities are implied by Turan

The higher-degree Jensen conditions were the obvious place to look for new
content, since GORZ leave a finite unresolved set of `n` for each degree `d ≥ 4`.
**The Newton side of that is closed, by an elementary computation rather than by
a failed search.**

For `A_k = C(d,k)γ(n+k)`, Newton at order `k` is `A_k² ≥ A_{k−1}A_{k+1}`, i.e.

    γ(n+k)²/(γ(n+k−1)γ(n+k+1))  ≥  C(d,k−1)C(d,k+1)/C(d,k)²  =  k(d−k)/((k+1)(d−k+1))

exactly. The right-hand side is strictly `< 1` for every `d ≥ 2` and
`1 ≤ k ≤ d−1`, since `k < k+1` and `d−k < d−k+1`; its maximum over the whole
range is `0.93548387...` at `d = 59, k = 29`, increasing toward 1 as `d` grows
but never reaching it. The left-hand side is `> 1` whenever Turan holds. So

> **Proposition.** Turan for all `m` implies Newton for all `(d, k, n)`.

Verified over `d = 2..59` against the minimum Turan margin at `m ≤ 150`: worst
`RHS/LHS = 0.9321`, so the bound is never approached.

This says the whole Newton/real-rootedness-*necessary* family adds nothing to the
classical `d = 2` Turan inequality. It does **not** close the higher-degree
problem, because hyperbolicity of `J^{d,n}` is strictly stronger than its Newton
inequalities. The measurement error it corrects: `newton_battery.py`'s table of
495 cells passing with margins down to `1.2e-40` is that same inequality counted
many times under different `C(d,k)` normalisations, and the tiny margins are the
normalisation, not a near-failure. The file now carries a header saying so.

## The chosen next step, and why it is closed from below

The plan was to extend the saddle instrument to hyperbolicity of `J^{d,n}` at
higher degree, where GORZ leave finitely many `n` unresolved for each `d ≥ 4`.
**That plan is closed, and not because it failed.** `hunts/jensen_clock` had
already measured the mechanism and I found it before spending, which is the
whole value of reading the tree first.

The mechanism: finite Jensen degree acts on the zeros as de Bruijn-Newman heat
with `t_eff(d) = |x0|/(8d)` where `x0 = (rho - 1/2)^2` is the pair's image, and
the Davenport-Heilbronn pair at `sigma = 0.80851718, gamma = 85.69935` lands only
at `d* = 20785.13`, its `t* = 0.0441263`. For that pair `|x0| = 7344.47351367`,
so `t_eff` is `459.03` at `d = 2`, `91.81` at `d = 10`, `28.69` at `d = 32`:
overheated by 650x or more. **The degree real-roots the polynomial before it can
be inspected, so a low-degree hyperbolicity scan cannot fail and carries no
information.** Measured on zeta directly: `min |Im root|/|root|` over the roots
of `J^{d,0}` is exactly `0.0` for every `d = 2..24`. That is why every scan in
this hunt and in `zeta/li.py` passes everywhere: they are all in the blind
region.

This refines `docs/12`'s statement of the gap. "A finite unresolved set for
every `d`" is true; the refinement is that at small `d` the set is not merely
unresolved but **unfalsifiable by a hyperbolicity scan at that `d`**. Any
certificate must operate above `d*(x0) = |x0|/(8t*)`, which grows like `gamma^2`
with height, so a height-85 pair needs `d ~ 2·10^4` and the thousandth zero needs
`d ~ 10^6`. No table in this hunt reaches that.

Inherited null, which matters: `jensen_clock`'s P5 shows the clock reads zero
**configuration, not arithmetic** (a planted pair in zeta's own table is detected
on the same clock; configuration-only N-body dynamics predicts it to 0.094%).
That is the same information-class conclusion `hunts/epp_herglotz` section 6 and
`hunts/local_positivity` reach from other directions, arriving here a third time
from the coefficient side.
