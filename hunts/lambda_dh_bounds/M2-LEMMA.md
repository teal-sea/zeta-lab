# M2 as a lemma: the uniform bound on `|H_t''|` over the winding box

Written 2026-08-18, as task 2 of the pre-submission hardening of
`hunts/lambda_dh_bounds`.

`GATE.md` known assumption 6 recorded `M2` as the hunt's one standing blind
spot: *"an in-tree shifted-contour derivation whose numerical ingredients are
ball-computed and whose derivation is prose. It is exercised by no
cross-route."* This page replaces the prose with a lemma and a proof, turns
every constant the prose asserted into a ball with reported endpoints, and
attacks the result from four directions. It changes no decided winding
number. Where the lemma's own constant differs from the one `winding.py`
computes, the difference is reported in section 5 rather than edited away.

Vocabulary per `MISSION.md`: *measured* is one float route, *decided* is an
enclosure whose exact endpoints settle a sign or an integer, *cited* is
somebody else's theorem. A composite takes its weakest grade.

**Status of the proof, stated first so nothing below has to be hunted for.**
The proof is complete as a mathematical argument, and no step of it rests on
an unverified numerical claim: every constant it uses is a reported Arb ball
and every hypothesis it needs is a decided predicate. It rests on three
classical inputs, all named in section 6, of which exactly one is
load-bearing and specific to this lemma: the evenness `Phi_DH(-u) =
Phi_DH(u)`, which comes from the Davenport-Heilbronn functional equation and
Hecke's theta transformation and which the hunt already carries as `GATE.md`
assumption 5. The proof is written prose plus decided arithmetic, at the
*hardened* rung of the repository's ladder. It is not kernel-checked, and it
has been read by no human. Both of those are said again in section 10.

---

## 1. Objects and notation

Fixed throughout, in the narrow frame `s = 1/2 + iz` (`FRAME.md`; every
number on this page is narrow-frame, and none of them changes under the frame
conversion because `M2` is an intermediate quantity, not a headline):

    a_n         the period-5 Davenport-Heilbronn pattern (1, kappa, -kappa, -1, 0),
                a_n = a_{n mod 5}, with kappa the functional-equation constant
    Omega(rho)  = sum_{n>=1} n exp(-pi n^2 rho / 5)          (rho > 0)
    omega(x)    = sum_{n>=1} n a_n exp(-pi n^2 x / 5)
    Phi_DH(u)   = 4 e^{3u/2} omega(e^{2u})
    H_t(z)      = int_0^inf e^{t u^2} Phi_DH(u) cos(zu) du
    G(u)        = e^{t u^2} Phi_DH(u)

`kappa` is decided by `instrument.kappa_ball` (Arb, 500 bits):

    kappa in [0.284079043840 +/- 4.13e-13],   0 < kappa < 1 decided.

The only property of `kappa` this lemma uses is `0 < kappa < 1`, which gives
`|a_n| <= 1` for every `n`. That is a decided fact, not a remembered one.

For rationals `x_lo > 0` and `y_hi > 0` write the closed half-strip

    R(x_lo, y_hi) = { z in C : Re z >= x_lo, |Im z| <= y_hi }.

The two rectangles the winding count actually traverses, verbatim from
`winding_results.json` (all corners are exact dyadic rationals):

| run | t | Re z in | Im z in |
|---|---|---|---|
| `t1_run` | `23/400` | `[122929/512, 123185/512]` | `[3/512, 61/1024]` |
| `t2_stretch_run` | `36/625` | `[245909/1024, 123159/512]` | `[3/1024, 35/1024]` |

Both boxes sit inside their half-strip by exact rational comparison:
`3/512 = 6/1024 <= 61/1024` and `6/1024 >= -61/1024` for `t1`;
`3/1024 <= 35/1024` and `3/1024 >= -35/1024` for `t2`; and each box's left
edge *is* its `x_lo`. So a bound on `R(x_lo, y_hi)` is a bound on the box and
on every boundary segment of it.

---

## 2. The lemma

> **Lemma M2.** Let `t >= 0` and `x_lo > 0`, `y_hi > 0` be rational. Let
> `v` and `S` satisfy
>
>     (H1)  0 < v < pi/4,  hence  cos 2v > 0;
>     (H2)  S >= 1  and  q_S := exp(-(pi/5) e^{2S} cos 2v) <= 29/100;
>     (H3)  c := (pi/5) cos 2v - (t S^2 + beta S) e^{-2S} > 0,
>           where beta := 3/2 + y_hi + 2.
>
> Then `H_t` is entire, and for every `z` in `R(x_lo, y_hi)`
>
>     |H_t''(z)|  <=  M2(x_lo, y_hi, t; v, S)
>                 :=  e^{-x_lo v - t v^2} * ( J + T ),
>
> where
>
>     J = int_0^S (s^2 + v^2) e^{t s^2} * 4 e^{3s/2}
>                 * Omega(e^{2s} cos 2v) * cosh(y_hi s) ds,
>     T = 4 e^{2v} e^{-cV} / (cV),      V = e^{2S}.
>
> The bound holds for every admissible pair `(v, S)`; the smallest such bound
> may be taken.

**Instantiation, decided.** At `v = pi/4 - 1/256` and `S = 5`, with `J`
bounded above by an 800-panel interval sum with exact rational panel
endpoints, at 300 bits:

| box | `M2` (this lemma) | `M2` used by `winding.py` | headline upper bound |
|---|---|---|---|
| `t1`, `t = 23/400` | `[1.188631940614305533012462e-78 +/- 7.16e-104]` | `[1.1886642645115152480e-78 +/- 4.83e-98]` | `M2 <= 1.1887e-78` |
| `t2`, `t = 36/625` | `[1.137052030557324731604501e-78 +/- 3.23e-103]` | `[1.1370829034005339081e-78 +/- 2.51e-98]` | `M2 <= 1.1371e-78` |

Both headline decimals sit above the upper endpoint of both balls, so both
inequalities are safe under outward rounding. The lemma's own constant is
smaller than the one the count consumed on both boxes (relative difference
`-2.719e-05` at `t1`, `-2.715e-05` at `t2`), so **the count's `M2` is valid a
fortiori**. The single source of that difference is identified in section 5.

**Hypothesis values, decided, at `v = pi/4 - 1/256`, `S = 5`.**

| quantity | `t1` box | `t2` box | decided |
|---|---|---|---|
| `v` | `[0.781491913397 +/- 4.49e-13]` | same | `0 < v < pi/4` |
| `cos 2v` | `[0.00781242052738 +/- 2.84e-15]` | same | `> 0` |
| `q_S` | `[1.10565520976e-47 +/- 2.11e-59]` | same | `< 29/100` |
| `beta` | `3.55957031250` | `3.53417968750` | exact rational |
| `c` | `[0.00403540497722 +/- 1.80e-15]` | `[0.00404105514036 +/- 4.49e-15]` | `> 0` |
| `V = e^{2S}` | `22026.4657948` | same | |
| `J` | `[3786.25676398 +/- 1.48e-9]` | `[3765.93760544 +/- 3.59e-9]` | |
| `T` | `5.3635e-40` | `4.7293e-40` | |
| `e^{-x_lo v - t v^2}` | `3.1393e-82` | `3.0193e-82` | |

---

## 3. Proof

### Step 0. `Phi_DH` is holomorphic on the strip `|Im u| < pi/4`

For complex `u` put `x = e^{2u}`, so `Re x = e^{2 Re u} cos(2 Im u)`. On
`|Im u| < pi/4` we have `cos(2 Im u) > 0`, hence `Re x > 0`, and on any
compact subset `Re x >= rho_0 > 0`. Since `|a_n| <= 1`,

    |n a_n e^{-pi n^2 x/5}| <= n e^{-pi n^2 rho_0 / 5},

and `sum_{n>=1} n e^{-pi n^2 rho_0/5}` converges. So the series for `omega`
converges uniformly on compact subsets of `{Re x > 0}`, its sum is
holomorphic there, and `Phi_DH(u) = 4 e^{3u/2} omega(e^{2u})` is holomorphic
on `|Im u| < pi/4`. The same estimate gives, for real `u` and any
`sigma` with `|sigma| < pi/4`,

    (0.1)   |Phi_DH(u + i sigma)| <= 4 e^{3u/2} Omega(e^{2u} cos 2 sigma),

which is the only inequality about `Phi_DH` used anywhere below. It follows
term by term: `|4 e^{3(u+i sigma)/2}| = 4 e^{3u/2}`,
`|e^{-pi n^2 e^{2(u+i sigma)}/5}| = e^{-pi n^2 e^{2u} cos(2 sigma)/5}`, and
`|a_n| <= 1`. Note (0.1) is even in `sigma`, so it serves both shifted rays
with no appeal to Schwarz reflection.

`G(u) = e^{t u^2} Phi_DH(u)` is therefore holomorphic on the same strip, with

    (0.2)   |G(u + i sigma)| = e^{t(u^2 - sigma^2)} |Phi_DH(u + i sigma)|
                            <= e^{t u^2} * 4 e^{3u/2} Omega(e^{2u} cos 2 sigma).

### Step 1. `H_t` is entire, and `H_t''(z) = -int_0^inf G(u) u^2 cos(zu) du`

Fix `Y > 0` and let `K = {|Im z| <= Y}`. For `u >= 0` real and `z` in `K`,

    |d^k/dz^k [ G(u) cos(zu) ]| = |G(u)| u^k |cos^{(k)}(zu)|
                               <= |G(u)| u^k cosh(Y u) =: D_k(u),

using `|cos w| <= cosh(Im w)` and `|sin w| <= cosh(Im w)`, and `D_k` does not
depend on `z`.

`D_k` is integrable on `[0, inf)`. It is continuous, hence bounded on `[0,1]`.
For `u >= 1`: `u^k <= e^{k u}` (from `x <= e^x`, `x >= 0`);
`cosh(Y u) <= e^{Y u}`; and by (0.1) at `sigma = 0`, `|Phi_DH(u)| <= 4 e^{3u/2}
Omega(e^{2u})`, where `Omega(rho) <= q/(1-q)^2 <= 2q` with `q = e^{-pi rho/5}`
once `q <= 29/100` (proved in step 3(b); at `rho = e^2` already
`q = 8.6e-6`). Hence for `u >= 1`

    (1.1)   D_k(u) <= 8 exp( t u^2 + (3/2 + Y + k) u - (pi/5) e^{2u} ),

which is `<= 8 e^{-c_0 e^{2u}}` for `u >= U_0` and an explicit `c_0 > 0` by
the same monotonicity argument as step 4(b), with `U_0 >= 1` taken large
enough that `(t U_0^2 + (3/2 + Y + k) U_0) e^{-2 U_0} < pi/5`, which is always
possible because `e^{2u}` beats any polynomial in `u`. Then
`int_{U_0}^inf e^{-c_0 e^{2u}} du < infinity`, and `D_k` is continuous hence
bounded on `[0, U_0]`. So `D_k` is an integrable dominating function on `K`,
independent of `z`.

Consequences, both standard:

* `H_t` is entire. The integrand is entire in `z` for each `u`, `D_0` is an
  integrable dominant on every `K`, so `H_t` is continuous on `K` (dominated
  convergence) and `int_gamma H_t = int_0^inf G(u) (int_gamma cos(zu) dz) du
  = 0` for every closed triangle `gamma` in `K` (Fubini, legitimate because
  `int_gamma int_0^inf |G(u) cos(zu)| du |dz| <= length(gamma) * int D_0 <
  infinity`). Morera gives holomorphy on the interior of `K`, and `Y` is
  arbitrary.
* Differentiation under the integral sign is legitimate for every `k`:
  `D_k` dominates the `k`-th `z`-derivative uniformly on `K`, so by the
  standard theorem (or by Cauchy's formula for the `k`-th derivative on a
  small circle inside `K`, plus Fubini with the same dominant),

    (1.2)   H_t^{(k)}(z) = int_0^inf G(u) d^k/dz^k cos(zu) du.

  At `k = 2`, `d^2/dz^2 cos(zu) = -u^2 cos(zu)`, so

    (1.3)   H_t''(z) = - int_0^inf G(u) u^2 cos(zu) du.

**(1.3) is attacked from outside the derivation in section 9(a)**: the second
central difference of `instrument.H_ball` at step `h = 1/1024` agrees with an
enclosure of the right-hand side of (1.3) to relative `7.66e-07` against
`h^2 = 9.54e-07`. A sign slip or a wrong power would show as a relative
discrepancy of order 1, which is why that check is worth its runtime.

### Step 2. The contour shift, and why the vertical legs cancel

Write `cos(zu) = (e^{izu} + e^{-izu})/2` in (1.3):

    (2.1)   H_t''(z) = (1/2) [ I_+(z) + I_-(z) ],
            I_+(z) = int_0^inf G(u) (iu)^2 e^{izu} du,
            I_-(z) = int_0^inf G(u) (-iu)^2 e^{-izu} du,

both integrands being the restriction to `u >= 0` of functions holomorphic on
`|Im u| < pi/4` (step 0), and both integrals absolutely convergent by (1.1).

Fix `v` with `0 < v < pi/4` (hypothesis H1). Apply Cauchy's theorem to
`F_+(u) = G(u)(iu)^2 e^{izu}` on the closed rectangle with vertices
`0, R, R + iv, iv`, which lies in the strip:

    int_0^R F_+ + int_{[R, R+iv]} F_+ + int_{[R+iv, iv]} F_+ + int_{[iv, 0]} F_+ = 0.

*The far side vanishes.* On `u = R + i sigma`, `0 <= sigma <= v`, with
`z = x + iy` in `R(x_lo, y_hi)`: `|e^{izu}| = e^{-x sigma - y R} <= e^{y_hi R}`
because `x >= x_lo > 0` and `sigma >= 0`; `|(iu)^2| = R^2 + sigma^2 <=
(R+v)^2 <= e^{2(R+v)}`; and by (0.2) with `cos 2 sigma >= cos 2v` (valid since
`0 <= sigma <= v < pi/4` and `cos` is decreasing on `[0, pi/2]`) together with
`Omega(rho) <= 2 e^{-(pi/5) rho}` at `rho = e^{2R} cos 2v >= e^{2S} cos 2v`,
which is exactly the range hypothesis H2 decides (step 3(b)),

    (2.2)   |F_+(R + i sigma)| <= 8 e^{2v} exp( t R^2 + beta R
                                                - (pi/5) cos(2v) e^{2R} )
                              <= 8 e^{2v} e^{-c e^{2R}}   for R >= S,

with `beta` and `c` as in the lemma and the last inequality proved in step
4(b). The far side is therefore at most `v * 8 e^{2v} e^{-c e^{2R}}`, which
tends to 0 doubly exponentially. At `R = S` that bound is already
`7.451e-38` on the `t1` box and `6.579e-38` on the `t2` box, both decided.

Letting `R -> infinity`,

    (2.3)   I_+(z) = int_{[0, iv]} F_+ + int_0^inf F_+(s + iv) ds,

and identically, shifting `F_-(u) = G(u)(-iu)^2 e^{-izu}` down to `-iv`,

    (2.4)   I_-(z) = int_{[0, -iv]} F_- + int_0^inf F_-(s - iv) ds.

*The two vertical legs cancel.* Parametrise the first by `u = is`,
`s: 0 -> v`, `du = i ds`. Then `(iu)^2 = (i * is)^2 = s^2` and
`e^{izu} = e^{iz(is)} = e^{-zs}`, so

    int_{[0, iv]} F_+ = i int_0^v G(is) s^2 e^{-zs} ds.

Parametrise the second by `u = -is`, `s: 0 -> v`, `du = -i ds`. Then
`(-iu)^2 = (-i * (-is))^2 = s^2` and `e^{-izu} = e^{-iz(-is)} = e^{-zs}`, so

    int_{[0, -iv]} F_- = -i int_0^v G(-is) s^2 e^{-zs} ds.

Their sum is

    (2.5)   i int_0^v [ G(is) - G(-is) ] s^2 e^{-zs} ds,

which vanishes identically because `G` is even. That is **Fact E**, and it is
the one place this proof leaves the tree:

> **Fact E.** `Phi_DH(-u) = Phi_DH(u)` for all `u` with `|Im u| < pi/4`,
> hence `G(-u) = G(u)` there (`e^{t u^2}` is even).

Fact E is derived in three parts in `winding.py`'s section *"Why G is even"*
and is not re-derived here. In outline: with `x = e^{2u}`, evenness of
`Phi_DH` is exactly `omega(1/x) = x^{3/2} omega(x)`; that transformation is
Hecke's theta transformation for the odd primitive characters mod 5, and the
single real condition it imposes on the coefficient pattern is precisely the
equation that defines `kappa`, so it is the Davenport-Heilbronn functional
equation `F(s) = F(1-s)` transported through the Mellin transform; and the
extension from real `u` to the whole strip is the identity theorem applied to
the holomorphic function `Phi_DH(-u) - Phi_DH(u)`, which vanishes on the real
axis of a connected strip symmetric under `u -> -u`. `F(s) = F(1-s)` is
carried by this hunt as a cited classical fact (`GATE.md` assumption 5).
The identity is measured at dps 260 to relative defect at most `4.9e-260` at
nine real and four complex points inside the strip (`winding.py`), and the
gate measured it independently at relative `1.0e-34`.

**Nothing weaker will do.** Without Fact E the legs (2.5) are bounded only by
`2 v^3 max|G| / 3`, an `O(1)` quantity, against a target of `1e-78`. Nor can
the legs be enclosed numerically: `G(is) - G(-is)` is identically zero, and a
ball evaluation over an interval of width `w` returns a ball of radius of
order `w`, so reaching `1e-78` this way would need of order `1e78`
subdivisions of `[0, v]`. The cancellation must be structural.

*What remains.* Substituting (2.3), (2.4) and the cancellation into (2.1),

    (2.6)   H_t''(z) = -(1/2) [ int_0^inf G(s+iv) (s+iv)^2 e^{iz(s+iv)} ds
                              + int_0^inf G(s-iv) (s-iv)^2 e^{-iz(s-iv)} ds ],

where the sign comes from `(i(s+iv))^2 = -(s+iv)^2` and likewise for the
second term.

### Step 3. The majorant on the two rays

Let `z = x + iy` with `x >= x_lo` and `|y| <= y_hi`. Writing `u = s + iv` in
the first integral and `u = s - iv` in the second:

    |e^{iz(s+iv)}| = e^{-xv - ys},        |e^{-iz(s-iv)}| = e^{-xv + ys},
    |(s +/- iv)^2| = s^2 + v^2,
    |e^{t(s +/- iv)^2}| = e^{t(s^2 - v^2)}.

Averaging the two exponential factors gives
`(1/2)(e^{-ys} + e^{ys}) = cosh(ys) <= cosh(y_hi s)`, and (0.1) bounds
`|Phi_DH(s +/- iv)|` by the *same* quantity `4 e^{3s/2} Omega(e^{2s} cos 2v)`
because (0.1) is even in the imaginary part. Hence from (2.6)

    (3.1)   |H_t''(z)| <= e^{-xv - t v^2}
                          int_0^inf (s^2+v^2) e^{t s^2} 4 e^{3s/2}
                              Omega(e^{2s} cos 2v) cosh(y_hi s) ds
                       <= e^{-x_lo v - t v^2} * (that same integral),

the last step because `x >= x_lo > 0` and `v > 0`. This is the lemma's shape;
the remaining work is a decided upper bound for the integral, split at `S`.

**Two majorants for `Omega`.** Both are used, panel by panel, whichever is
smaller. Fix `rho > 0` and put `a = pi rho / 5`.

*(a) Unimodal comparison.* `f(x) = x e^{-a x^2}` increases on `[0, m]` and
decreases on `[m, inf)`, `m = 1/sqrt(2a)`. For `n <= floor(m) - 1`, `f` is
increasing on `[n, n+1] subset [0, m]`, so `f(n) <= int_n^{n+1} f`. For
`n >= ceil(m) + 1`, `f` is decreasing on `[n-1, n] subset [m, inf)`, so
`f(n) <= int_{n-1}^n f`. The two integral families are disjoint subintervals
of `[0, inf)`. The at most two remaining terms, `n = floor(m)` and
`n = ceil(m)`, are each at most `max f = e^{-1/2}/sqrt(2a)`. Therefore

    (3.2)   Omega(rho) <= int_0^inf x e^{-a x^2} dx + 2 max f
                       = 1/(2a) + 2 e^{-1/2} / sqrt(2a).

*(b) Geometric domination.* `n^2 >= n` for `n >= 1`, so with `q = e^{-a} < 1`

    (3.3)   Omega(rho) <= sum_{n>=1} n q^n = q / (1-q)^2.

If moreover `q <= 29/100` then `(1-q)^2 >= (71/100)^2 = 5041/10000` and
`10000/5041 < 2` in exact rational arithmetic, so

    (3.4)   Omega(rho) <= 2 q = 2 e^{-pi rho / 5}        (when q <= 29/100),

which is the form used in (1.1), (2.2) and step 4(b).

Both (3.2) and (3.3) are evaluated in ball arithmetic over the *panel hull*
of `rho`, so the returned upper endpoint dominates `Omega` at every point of
the panel. Section 9(b) reports an attempt to falsify both against a sharp
truncated-sum-plus-tail enclosure of `Omega` at 24 probe points spanning
`rho` from `3.4e-4` to `1.3e4`: no refutation, and the gap is decided strict
at 24 of 24 points for (3.2) and 17 of 24 for (3.3), the remaining 7 being
the large-`rho` regime where every route collapses onto the `n = 1` term and
the balls legitimately overlap.

### Step 4. The two ranges

**(a) `[0, S]`, by interval-evaluation panels.** The integrand of (3.1) is a
product of positive factors, so it is nonnegative. Partition `[0, S]` into
`n = 800` panels with exact rational endpoints `s_j = jS/n`. On panel `j`,
evaluate the integrand in ball arithmetic over the hull `[s_j, s_{j+1}]`; the
resulting ball contains every value the integrand takes on the panel, so its
upper endpoint times the panel width dominates the panel's integral. Summing,

    (4.1)   int_0^S (...) ds <= sum_j upper(integrand over panel j) * (S/n) = J.

Exact rational endpoints matter only for tidiness of the coverage argument:
the panels then tile `[0, S]` exactly, with no appeal to a rounded step size.
Decided: `J = [3786.25676398 +/- 1.48e-9]` on the `t1` box,
`[3765.93760544 +/- 3.59e-9]` on the `t2` box. Of the 800 panels, 404 take
the unimodal majorant (3.2) and 396 the geometric one (3.3).

**(b) `[S, inf)`, in closed form.** For `s >= S`, put `rho_s = e^{2s} cos 2v`
and `q_s = e^{-pi rho_s / 5}`. `rho_s` increases in `s`, so `q_s <= q_S <=
29/100` by hypothesis H2, and (3.4) applies: `Omega(rho_s) <= 2 q_s`. Also
`s^2 + v^2 <= (s+v)^2 <= e^{2(s+v)} = e^{2v} e^{2s}` and
`cosh(y_hi s) <= e^{y_hi s}`. Multiplying the five factors of (3.1):

    (4.2)   integrand(s) <= 8 e^{2v} exp( E(s) ),
            E(s) = t s^2 + beta s - (pi/5) cos(2v) e^{2s},
            beta = 3/2 + y_hi + 2.

`s e^{-2s}` decreases for `s >= 1/2` and `s^2 e^{-2s}` decreases for `s >= 1`,
and `S >= 1` by H2, so on `[S, inf)`

    s <= S e^{-2S} e^{2s},    s^2 <= S^2 e^{-2S} e^{2s},

hence, since `t >= 0` and `beta > 0`,

    (4.3)   E(s) <= [ (t S^2 + beta S) e^{-2S} - (pi/5) cos 2v ] e^{2s}
                 = -c e^{2s},

with `c > 0` by hypothesis H3. Substituting `w = e^{2s}` (`dw = 2w ds`) and
using `1/w <= 1/V` for `w >= V = e^{2S}`,

    (4.4)   int_S^inf 8 e^{2v} e^{-c e^{2s}} ds
              = 4 e^{2v} int_V^inf e^{-cw} dw / w
              <= (4 e^{2v} / V) int_V^inf e^{-cw} dw
              = 4 e^{2v} e^{-cV} / (cV) = T.

Decided: `T = 5.3635e-40` on the `t1` box, `4.7293e-40` on the `t2` box. `T`
is 42 orders of magnitude below `J`, which is a statement about how far out
`S = 5` sits, not about the bound's quality.

**(c) Assembly.** Combining (3.1), (4.1) and (4.4),

    |H_t''(z)| <= e^{-x_lo v - t v^2} (J + T) = M2,

for every `z` in `R(x_lo, y_hi)`. Each of the four ingredients
(`e^{-x_lo v - t v^2}`, `J`, `T`, and the hypothesis predicates H1 to H3) is
computed as an Arb ball at 300 bits with exact rational inputs, and the final
bound is taken at the ball's upper endpoint. **Lemma M2 is proved.**

### Step 5. Why this route and not the elementary one

The obvious proof stops at (3.1) with `v = 0`: `|cos(zu)| <= cosh(y_hi u)`
applied directly to (1.3) gives the fully valid, fully decided bound

    |H_t''(z)| <= int_0^inf e^{t s^2} |Phi_DH(s)| s^2 cosh(y_hi s) ds
               <= 0.30218534361205546          (t1 box, decided)
               <= 0.30202444299917314          (t2 box, decided)

for every `z` in the whole strip `|Im z| <= y_hi`, with no contour shift, no
Cauchy theorem and, crucially, **no appeal to Fact E**. It is implemented as
`m2_lemma.direct_bound` with the same panel machinery and the same tail
argument, and its hypotheses are decided.

It is also useless here, by a factor of `2.54e+77`. It does not see `Re z` at
all, and the entire smallness of `M2` is the factor `e^{-x_lo v} ~ 3.1e-82`
at `x_lo ~ 240.1`. Feeding `0.302` to the winding count in place of
`1.19e-78` would demand a tube radius `M2 h^2 / 2` below the chord
clearance `~1e-83`, hence subsegment half-lengths of order `1e-42`, hence of
order `1e+41` segments. The count would not be slower; it would be
impossible.

So the elementary route was written, decided and kept, but as a control on
the machinery rather than as the lemma: **the contour shift is the
load-bearing step, and it is load-bearing because of `e^{-x_lo v}`, not
because of any constant.** The corollary of that, developed in section 7, is
that the useful thing to check about `M2` is whether it carries the *right
exponential rate*, and it does: `v = pi/4 - 1/256 = 0.78149` against the
strip half-width `pi/4 = 0.78540`, which is the fastest rate any shift of
this contour can produce, since `Phi_DH` is holomorphic exactly on
`|Im u| < pi/4`.

---

## 4. The corollary the winding count actually consumes

> **Corollary.** Let `[z_a, z_b]` be an axis-parallel segment contained in
> `R(x_lo, y_hi)`, of half-length `h`, and let `g(d) = H_t(z_mid + d e)` for
> the unit direction `e` and `d` in `[-h, h]`. Let `p` be the affine
> interpolant of `g` at `d = -h` and `d = +h`. Then
>
>     |g(d) - p(d)| <= (M2 / 2) (h - d)(h + d) <= M2 h^2 / 2.

*Proof.* `g''(d) = H_t''(z_mid + d e) e^2` and `|e| = 1`, so `|g''| <= M2` on
the segment by Lemma M2. Linear interpolation error at the endpoints of
`[-h, h]` has the Green's function representation
`g(d) - p(d) = -int_{-h}^{h} K(d, tau) g''(tau) dtau` with `K >= 0` and
`int_{-h}^{h} K(d, tau) dtau = (h^2 - d^2)/2`. The representation is valid for
complex-valued `g`, which the mean-value form of the interpolation error is
not. Taking absolute values gives the claim. QED

That is exactly `winding.winding_rectangle`'s `tube = M2 * hh * hh / 2`, and
it is the only use `M2` is put to. The image of the segment therefore lies in
`chord(H(z_a), H(z_b)) + disc(M2 h^2 / 2)`; a decided
`dist(0, chord) > M2 h^2 / 2` puts that convex set strictly on one side of a
line through 0, which forces `|Delta arg| < pi` on the segment, which is what
lets the endpoint quotient's principal argument be the exact argument
variation. Every step of that chain other than `M2` was already decided.

---

## 5. Independent re-derivation, and the one place the two disagree

`m2_lemma.shifted_bound` implements Lemma M2 from the statement above,
sharing no line with `winding.second_derivative_bound`. Both were run on both
boxes at 300 bits with `S = 5`, 800 panels, and the same four candidate
values of `eps`.

| box | lemma `M2` | `winding.py` `M2` | relative difference |
|---|---|---|---|
| `t1` | `1.1886319406143055e-78` | `1.1886642645115153e-78` | `-2.719e-05` |
| `t2` | `1.1370520305573246e-78` | `1.1370829034005339e-78` | `-2.715e-05` |

The discrepancy was traced to a single panel, and it is entirely benign.
Panel `j = 404` of 800 is the crossover between the two `Omega` majorants: at
that panel's hull `rho = [1.2 +/- 0.0343]`, the unimodal bound (3.2) is
`[1.6 +/- 0.0331]` and the geometric bound (3.3) is `[1.6 +/- 0.0240]`. Their
balls overlap. `winding._omega_sum_upper` selects the geometric route only on
a *decided* ball comparison `b2 < b1`, which is undecided here, so it keeps
the unimodal value `1.6330035300998134`; `m2_lemma.omega_majorant` compares
upper endpoints and keeps the geometric value. The panel contributes
`18.664618650751343` in the first case and `18.561654764934417` in the
second, a difference of `0.10296388581692639`, which is the whole of the
`J` gap (`3786.359728210144 - 3786.2567639785207 = 0.1029642316`) to seven
digits. The other 799 panels agree to relative `1e-10` or better.

Both selections are sound: each of (3.2) and (3.3) is a valid majorant, so
taking either is valid and taking the larger is merely more conservative.
`winding.py`'s value is the larger. **No decided winding number is affected,
and none was changed.**

---

## 6. What the lemma rests on

| input | kind | grade | load-bearing for `M2`? |
|---|---|---|---|
| `Phi_DH(-u) = Phi_DH(u)` on the strip (Fact E) | Hecke's theta transformation for the odd primitive characters mod 5, plus `F(s) = F(1-s)` for the Davenport-Heilbronn function, transported through the Mellin transform, plus the identity theorem | cited (`GATE.md` assumption 5), with an in-tree transport derivation in `winding.py` and a measured check to relative `4.9e-260` | **yes**, decisively: it is what cancels the vertical legs, and section 3 step 2 shows no numerical substitute exists |
| `kappa_ball` encloses the true `kappa` | the linear solve at `s0 = 3/4 + 3i/2` determines `kappa`; the true `kappa` satisfies it, and `B` is decided nonzero | decided plus cited | only through `0 < kappa < 1`, hence the coefficient bound `abs(a_n) <= 1` |
| Cauchy's theorem, Morera, dominated convergence, Fubini, the identity theorem | classical analysis | cited (textbook) | yes, and unremarkably so |
| `x <= e^x` for `x >= 0`; `s e^{-2s}` decreasing for `s >= 1/2`; `s^2 e^{-2s}` decreasing for `s >= 1`; `(1 - 29/100)^{-2} < 2` | elementary calculus and exact rational arithmetic | proved here | yes |
| every constant: `v`, `cos 2v`, `q_S`, `c`, `beta`, `V`, `J`, `T`, the prefactor, `M2` | Arb balls at 300 bits with exact rational inputs, endpoints reported in section 2 | decided | yes |

**No step of the proof rests on an unverified numerical claim.** The one
non-elementary citation is Fact E, and it was already an acknowledged and
load-bearing assumption of this hunt before this page existed.

---

## 7. The cushion, now decided

`GATE.md` assumption 6 recorded a cushion of **55.7**, from a measured
`sup |H_t''| = 2.1357e-80` against `M2 = 1.1887e-78`. Both halves were
recomputed here, and the measured half was upgraded.

**The sup is now bounded from below by an enclosure, not a float.**
`m2_lemma.H2_ball` encloses `H_t''(z)` directly by Arb's rigorous integrator
applied to the integrand of (1.3), with its own two tail balls (the `k = 2`
case of the `k`-fold rule `instrument` carries at `k = 0` and `k = 1`, gaining
two factors of `U` in each). At a single grid point the enclosure is tight:

    H_t''(240.158203125 + 0.0595703125 i), t = 23/400, 420 bits
      = [2.1357222907398572615e-80 +/- 1.40e-100]
      + [7.8639307631720561547e-83 +/- 1.06e-103] i
    |H_t''| = [2.1357367685579024450e-80 +/- 3.16e-100]

which reproduces the published measured value `2.1357367685579024e-80` to all
17 of its digits and promotes it from *measured* to *decided*. Taking the
largest such lower endpoint over a 41 x 9 grid plus 64 extra points on the top
edge, 433 points in all:

| box | decided lower bound for the sup | attained at | measured sup (float, same evaluator as the guard) |
|---|---|---|---|
| `t1` | `2.1358117413634282e-80` | `Re z = 7746575/32256`, `Im z = 61/1024` | `2.1357367685579024e-80` |
| `t2` | `2.1139544551457620e-80` | `Re z = 2582249/10752`, `Im z = 35/1024` | `2.1103034250765648e-80` |

**The cushion.** Because the decided value is a lower bound for the true sup,
`M2 / (decided sup lower bound)` is a decided **upper bound** for the cushion:

| box | `M2` used by the count | decided sup `>=` | cushion `<=` | previously published |
|---|---|---|---|---|
| `t1`, `t = 23/400` | `1.1886642645115153e-78` | `2.1358117413634282e-80` | **`55.65`** | 55.7 (measured) |
| `t2`, `t = 36/625` | `1.1370829034005339e-78` | `2.1139544551457620e-80` | **`53.79`** | 53.9 (measured) |

The published numbers stand. They move only in the third digit, and only
because the denser grid found a slightly larger point than the guard's 9 x 3
sample (by `3.5e-05` relative at `t1` and `1.7e-03` at `t2`). Read as a
statement about the lemma: **the bound of Lemma M2 overstates the true
supremum of `|H_t''|` on these boxes by a factor of at most 55.65 and 53.79
respectively.**

**The cushion is a structural constant, not a property of these rectangles.**
`M2` depends on `x_lo` only through `e^{-x_lo v}`, and `v = pi/4 - eps` is
within `eps` of the largest rate any shift of this contour can carry. Probing
`|H_t''|` and recomputing `M2` at `Re z = x_lo + d` for `d = 0, 4, ..., 40` on
the top edge, all decided at 420 bits:

| `d` | decided `abs(H_t'')` | `M2` at that `x_lo` | cushion |
|---|---|---|---|
| 0 | 2.0905e-80 | 1.1886e-78 | 56.9 |
| 4 | 1.1570e-81 | 5.2174e-80 | 45.1 |
| 8 | 1.4869e-83 | 2.2902e-81 | 154.0 |
| 12 | 3.0084e-84 | 1.0053e-82 | 33.4 |
| 16 | 7.4304e-86 | 4.4125e-84 | 59.4 |
| 20 | 4.3850e-87 | 1.9368e-85 | 44.2 |
| 24 | 2.0467e-88 | 8.5017e-87 | 41.5 |
| 28 | 1.8321e-90 | 3.7318e-88 | 203.7 |
| 32 | 4.0558e-91 | 1.6380e-89 | 40.4 |
| 36 | 6.4537e-93 | 7.1901e-91 | 111.4 |
| 40 | 7.2756e-94 | 3.1560e-92 | 43.4 |

Across a 40-unit span of `Re z`, over which `|H_t''|` falls by 14 orders of
magnitude, the cushion stays between 33 and 204. The excursions to 154 and
204 are points where `|H_t''|` itself dips near one of its own zeros, which
inflates the ratio; the typical value is 40 to 60. The empirical decay rate
over the span is `0.7747` against the lemma's `v = 0.78149` and the strip
half-width `pi/4 = 0.78540`, the small gap being the algebraic prefactor.

That table is the answer to the sharpest thing `GATE.md` said against this
step: **the cushion is not a coincidence of the box the count happens to
use.** It is `O(10^1.7)` wherever it has been probed, because the bound
carries the true exponential rate and pays only a constant for the contour
shift.

---

## 8. Why a uniform bound cannot come from ball evaluation

This is the fact that makes the contour shift necessary, and it is worth a
number rather than an assertion. `H_t''` was enclosed at the centre of the
`t1` box over `z`-balls of growing radius, at 420 bits:

| `Re z` ball radius | enclosure of `abs(H_t'')` | excludes 0? |
|---|---|---|
| 0 (exact point) | `1.823903415611058e-80` | yes |
| `2^-80 = 8.27e-25` | `[0, 1.009e-25]` | no |
| `2^-40 = 9.09e-13` | `[0, 1.110e-13]` | no |
| `2^-20 = 9.54e-07` | `[0, 1.155e-07]` | no |
| `1/8` | `[0, 1.509e-02]` | no |

The box is `0.5` wide. At an input radius of `1e-24`, already 24 orders of
magnitude narrower than the box, the enclosure is 55 orders of magnitude
*larger* than the true value and contains 0. The reason is the cancellation
the whole hunt lives with: at `Re z ~ 240` the integrand of (1.3) is `O(1)`
while the integral is `~2e-80`, so any ball carrying an input width `w`
carries an output radius of order `w`, not of order `w` times the answer.

Pointwise enclosures are therefore cheap and uniform enclosures are
impossible, and a uniform bound must come from a representation in which the
smallness is pointwise. That is exactly what the shifted contour supplies:
after the shift the factor `e^{-x_lo v}` sits outside the integral and no
cancellation is needed anywhere. The same asymmetry is why
`winding.measured_h2_guard` can only ever be a finite sample, and why it is
labelled necessary and not sufficient.

---

## 9. Attacks run against the proof

Each of these is designed to fail loudly if a specific step is wrong, and
each shares as little as possible with the step it attacks.

**(a) Step 1, the identity (1.3).** A sign slip, a missing factor or a wrong
power in `H_t'' = -int G(u) u^2 cos(zu) du` would leave every later step
formally intact and every number wrong: the majorant machinery would
faithfully bound the wrong integral. Attacked by second central differences
of `instrument.H_ball`, which knows nothing about `u^2`, at exact dyadic step
`h = 1/1024`, at three points on each box's top edge, both sides being
enclosures:

| box | worst relative gap | `h^2` | verdict |
|---|---|---|---|
| `t1` | `7.663e-07` | `9.54e-07` | PASS |
| `t2` | `7.183e-07` | `9.54e-07` | PASS |

The gap is the difference quotient's own `O(h^2)` truncation. A formula error
would read `O(1)`.

**(b) Step 3, the two `Omega` majorants.** Attacked by a sharp
truncated-sum-plus-tail enclosure of `Omega` at 24 probe values of `rho`
spanning `3.4e-04` to `1.3e+04`, which covers both the shifted regime
(`rho = e^{2s} cos 2v`, small) and the unshifted one (`rho = e^{2s}`). A
majorant is refuted when its upper endpoint falls decidedly below the sharp
bound's lower endpoint. **No refutations.** Overlap at large `rho` is
recorded as agreement, not as failure, because there every route collapses
onto the `n = 1` term `e^{-pi rho/5}`; the gap is decided strict at 24 of 24
points for the unimodal bound and 17 of 24 for the geometric one.

**(c) The `k = 2` tail balls of `H2_ball`.** These carry the decided sup of
section 7, so an error in them would move the cushion. Attacked by moving the
truncation point: `U`, `U + 1/2`, `U + 1` produce three genuinely different
discarded remainders, and the three enclosures must still overlap. They do,
on both boxes.

**(d) The whole bound, against an independent implementation.** Section 5.
One panel differs, in the safe direction, for a reason that is understood.

**(e) The whole bound, against an implementation that shares no idea with
it.** Section 5's direct majorant `0.302` is a valid upper bound reached
without Cauchy's theorem and without Fact E, and it exceeds the decided sup
by 78 orders of magnitude, as it must.

All five are wired into `m2_lemma.main()`, whose verdict is PASS only when
every one of them passes on both boxes.

---

## 10. Scope: what this page does not establish

* **It is not kernel-checked.** The proof is written prose plus decided
  arithmetic. Nothing here has been through Lean, and the repository's ladder
  puts it at *hardened*, not at the rung above.
* **It has been read by no human.** The proof was written by an agent session
  and attacked by scripts written in the same session. That is the same
  caveat `GATE.md`'s closure log attaches to the Bombieri-Ghosh reading, and
  it is stated here for the same reason.
* **Fact E is cited, not proved in-tree.** Hecke's theta transformation and
  `F(s) = F(1-s)` are classical, and `winding.py` derives the transport
  between them, but neither is re-proved from first principles here. If
  `F(s) = F(1-s)` failed for the `kappa` this hunt computes, the vertical legs
  would not cancel and Lemma M2 would be false. That is the single point at
  which this proof could break, and it is a citation rather than a
  computation.
* **The lemma bounds `|H_t''|`, and nothing else.** It says nothing about
  `H_t` or `H_t'`, nothing about the location of zeros, and nothing about
  `Lambda_DH`. Its only consumer is the corollary of section 4.
* **It does not touch the other exposures of the lower bound.** The cited
  half-line (Dobner Theorem 1), the transported frame, and the count's own
  arithmetic are unaffected by this page in either direction.
* **The `Omega` majorants are not claimed to be sharp**, and the panel bound
  is not claimed to be sharp. A tighter `M2` is available (the truncated-sum
  route of section 9(b) would shrink `J`), and was deliberately not adopted:
  the value under test is the one the count consumed.

---

## 11. Reproduction

From the repository root, with `python-flint` present:

    .venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND)"    # python-flint
    .venv/bin/python hunts/lambda_dh_bounds/m2_lemma.py

Runtime about 105 seconds. It writes `m2_lemma_results.json` and nothing
else; in particular it does not touch `winding_results.json`,
`controls_results.json` or any decided winding number. The verdict line
reports PASS only if, on both boxes: every hypothesis H1 to H3 is decided,
the lemma's own `M2` is at most the `M2` `winding.py` uses, the two `Omega`
majorants survive falsification, the step-1 identity survives the
finite-difference attack, and the `H2_ball` tail balls survive the `U`-move
attack.

The published state at the time of writing:

    verdict PASS
    t1: M2 = 1.1886319406e-78, decided sup >= 2.135812e-80, cushion <= 55.65
    t2: M2 = 1.1370520306e-78, decided sup >= 2.113954e-80, cushion <= 53.79
    direct/shifted = 2.54e+77 (t1), 2.66e+77 (t2)
