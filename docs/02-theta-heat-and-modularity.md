# 02. Theta, the Heat Equation, and Modularity

*"Can you model the theta function with a differential equation?"*

**The short version.** Yes, and the equation is the heat equation. The function

```
theta(x, t)  =  sum over n in Z   exp(-4 pi^2 n^2 t) exp(2 pi i n x)
```

is exactly the fundamental solution (the heat kernel) of `u_t = u_xx` on the circle **R**/**Z**: put a
unit of heat at the origin at time zero and let it diffuse, and this is the temperature profile. The
same function has a *second face*, a sum of Gaussians, one for each way heat can wrap around the
circle. The statement that these two faces are the same function is **Poisson summation**; applied to
a Gaussian (which is its own Fourier transform) it collapses to Jacobi's modular identity
`theta(1/x) = sqrt(x) theta(x)`. That identity is a duality between short time and long time: the
behaviour of the system when heat has barely spread determines its behaviour when heat has almost
finished spreading. Everything downstream in this repository, the functional equation of zeta
(`docs/03-functional-equation.md`), the symmetry axis `Re(s) = 1/2`, running heat flow on `Xi` itself
(`docs/05-de-bruijn-newman.md`), is a consequence or an echo of this one self-similarity.

---

## 1. The differential equation, derived rather than asserted

Take a thin insulated ring of circumference 1. Parametrise it by `x` in **R**/**Z** (so `x` and `x+1`
are the same point). Let `u(x,t)` be the temperature. Fourier's law plus conservation of energy gives
the heat equation; with the diffusion constant normalised to `D = 1`,

```
    du/dt  =  d^2u/dx^2                     (PDE, diffusivity D = 1)
    u(x, 0) = delta(x)   on R/Z             (initial data: unit heat at the origin)
```

**Separation of variables.** Look for solutions `u = X(x) T(t)`. Substituting gives
`T'/T = X''/X = -lambda`, a constant. Periodicity forces `X` to be one of the characters
`X_n(x) = exp(2 pi i n x)`, `n` in **Z**: these are precisely the eigenfunctions of `d^2/dx^2` on
the circle with period 1. Differentiating twice:

```
    d^2/dx^2  exp(2 pi i n x)  =  (2 pi i n)^2 exp(2 pi i n x)  =  -4 pi^2 n^2 exp(2 pi i n x)
```

so `lambda_n = 4 pi^2 n^2` and `T_n(t) = exp(-4 pi^2 n^2 t)`. **Mode `n` decays at rate
`4 pi^2 n^2`.** That is the whole physics in one line: wiggly modes (large `|n|`) die fast, because a
wiggly temperature profile has large curvature and curvature is what drives diffusion. Note the
normalisation trap: the `4 pi^2` sits in the exponent *precisely so that* `D = 1`. In the other
common convention, `sum_n exp(-n^2 t) exp(i n x)` on a circle of circumference `2 pi`, the same
kernel solves `u_t = u_xx` too; but if you mix the conventions you will conclude `D = 1/(4 pi^2)`
and your numerics will not check out. The code pins this down (Section 7).

Now expand the initial data. The Dirac delta on the circle has *all* Fourier coefficients equal to 1
(since `integral over [0,1] of delta(x) exp(-2 pi i n x) dx = 1` for every `n`). Superposing modes:

```
    theta(x, t)  =  sum over n in Z  exp(-4 pi^2 n^2 t) exp(2 pi i n x)         (Fourier face)
```

Three sanity checks, all easy and all worth doing:

- **Total heat is conserved.** `integral over [0,1] theta(x,t) dx = 1` for every `t`: only the
  `n = 0` term survives the integral, and it equals 1 for all time.
- **It really solves the PDE.** Term-by-term differentiation (legitimate for `t > 0`, where the
  series converges extremely fast) gives the factor `-4 pi^2 n^2` from `d/dt` and from `d^2/dx^2`
  alike, the two derivative series are *identical*, which is exactly the statement `D = 1`.
- **It is real and even in `x`.** Pair `n` with `-n`:
  `theta(x,t) = 1 + 2 sum_{n>=1} exp(-4 pi^2 n^2 t) cos(2 pi n x)`.

What is *not* obvious from this face: that `theta > 0` everywhere. Physically it must be, heat does
not diffuse into negative temperature, but the sum of cosines gives no hint. Hold that thought.

---

## 2. The second face: heat on the line, wrapped

There is another way to solve the same problem. Forget the circle; solve on the line **R**, where
the fundamental solution of `u_t = u_xx` is the textbook Gaussian

```
    G(x, t)  =  (4 pi t)^(-1/2) exp( -x^2 / (4 t) )
```

(a normal density with variance `2t`, so the diffusion length is `sqrt(2t)`; the `4` in `4t` is
exactly what `D = 1` demands, differentiate and check).

Now use the **method of images**. A function on the circle is a periodic function on the line. Heat
released at the origin of the circle is indistinguishable from heat released simultaneously at
*every* integer point of the line: a random walker that goes once around the circle is a walker on
the line that has drifted a net distance 1. So

```
    theta(x, t)  =  sum over m in Z  (4 pi t)^(-1/2) exp( -(x - m)^2 / (4 t) )    (Gaussian face)
```

Each term is one *winding number*: `m` counts how many times the heat has gone around. From this
face positivity is obvious (a sum of Gaussians) and conservation is obvious (the images tile the
line, so the integral over one period equals the integral of a single Gaussian over all of **R**,
namely 1). What is *not* obvious from this face is the spectral decay, or even periodicity at a
glance.

**These are two descriptions of one object.** Heat on a circle = heat on the line wrapped around =
heat as a superposition of standing waves. The first is a sum over *geometry* (winding numbers,
closed paths); the second a sum over the *spectrum* (eigenvalues `4 pi^2 n^2`). That
geometry/spectrum pairing is a baby version of the duality in the explicit formula
(`docs/04-explicit-formula.md`), where the "windings" become prime powers and the "eigenvalues"
become zeros of zeta.

---

## 3. Poisson summation: the two faces agree

**THEOREM (Poisson summation).** For `f` in the Schwartz class (smooth, rapidly decaying,
Gaussians qualify comfortably),

```
    sum over m in Z  f(m)   =   sum over n in Z  fhat(n),
    where  fhat(k) = integral over R of  f(y) exp(-2 pi i y k) dy.
```

*Why it is true, in one breath:* periodise `f` by setting `F(y) = sum_m f(y + m)`. `F` has period 1,
so expand it in a Fourier series; its `n`-th coefficient is `integral over [0,1] of
F(y) exp(-2 pi i n y) dy`, and unfolding the inner sum turns that into an integral over all of
**R**, which is `fhat(n)`. Evaluate the Fourier series at `y = 0` and you have the theorem.

Now apply it. Fix `x` and `t > 0` and take `f(y) = (4 pi t)^(-1/2) exp(-(x-y)^2 / (4t))`, so the
left side is the Gaussian face. Substituting `y = x - u` in the transform:

```
    fhat(n) = exp(-2 pi i n x) * integral (4 pi t)^(-1/2) exp(-u^2/(4t)) exp(2 pi i n u) du
            = exp(-2 pi i n x) * exp(-4 pi^2 n^2 t)
```

using the one fact that makes this whole subject work: **the Gaussian is its own Fourier transform**
(precisely: the transform of `exp(-pi a u^2)` is `a^(-1/2) exp(-pi k^2 / a)`; here `a = 1/(4 pi t)`
and the prefactors cancel exactly, do the two-line check). Poisson summation now reads

```
    sum_m (4 pi t)^(-1/2) exp(-(x-m)^2/(4t))   =   sum_n exp(-4 pi^2 n^2 t) exp(-2 pi i n x)
```

and since the coefficients are even in `n` the sign in the exponent may be flipped. **Gaussian face
= Fourier face.** That is the entire content of the identity.

Watch what happened to `t`: on the left it sits in the *denominator* of the exponent (`1/(4t)`), on
the right in the *numerator* (`4 pi^2 t`). Poisson summation has inverted time.

---

## 4. The modular identity is this, at `x = 0`

Define the classical theta function on the positive reals:

```
    theta(s)  =  sum over n in Z  exp(-pi n^2 s),       s > 0
```

Set `x = 0` and `s = 4 pi t` in the previous display (so `theta_heat(0, t) = theta(4 pi t)`, the
bridge the code uses). The Fourier face becomes `theta(s)`; the Gaussian face becomes
`s^(-1/2) theta(1/s)`. Hence:

**THEOREM (Jacobi's theta transformation).** For all `s > 0`,

```
    theta(1/s)  =  sqrt(s) * theta(s)
```

That is the promised one-line derivation: *Poisson summation applied to a Gaussian, evaluated at the
origin.* The identity is classical, commonly attributed to Jacobi (1820s), and Riemann's 1859 memoir
invokes it, citing Jacobi, as the engine of the functional equation. (I am confident in the
attribution to Jacobi and in Riemann's use of it; I have not verified the exact place in Jacobi that
Riemann cites, so I omit it.)

In the heat variable, the duality is `t -> 1/(16 pi^2 t)`, with self-dual time
`t* = 1/(4 pi) = 0.0795774715...`. At that instant `theta_heat(0, t*) = theta(1) =
1.08643481121330801...` (checked at 30 digits with the code below), and the diffusion length is
`sqrt(2 t*) = 1/sqrt(2 pi) = 0.398942...`: comparable to the circle itself. The self-dual moment is
precisely when the heat has just finished discovering that the line was secretly a circle.

---

## 5. What the duality *means*: short time knows long time

This is the interpretive heart, so let us be concrete rather than poetic.

- **Small `s` (short time).** Heat has barely spread. On the Gaussian side one image dominates
  overwhelmingly and `theta(s) ~ s^(-1/2)`, a single spreading blob. On the Fourier side the profile
  is sharp, so it needs many harmonics.
- **Large `s` (long time).** Heat is nearly uniform. On the Fourier side,
  `theta(s) = 1 + 2 exp(-pi s) + O(exp(-4 pi s))`: the constant mode plus an exponentially small
  ripple. On the Gaussian side the blob has wrapped around many times, so it needs many images.

Each regime is *hard* in one language and *trivial* in the other, and modularity is the dictionary.
Numerically (all values below recomputed with `zeta.core.theta` at 40 digits before being written
down):

```
    s        theta(s)                    1/sqrt(s)            1 + 2 exp(-pi s)
  0.001     31.62277660168379332        31.62277660168379    2.9937266739699
  0.01      10.0000000000000000         10.0                 2.9381448526096
  0.1        3.162277660168522969        3.162277660168379    2.4608053820972
  1          1.086434811213308015        1.0                  1.0864278365275
  10         1.000000000000045422        0.3162277660168      1.000000000000045
  100        1.0000000000000000          0.1                  1.0000000000000
```

Look at `s = 0.01`: `theta(0.01) = 10` to well over a hundred digits, the correction is
`10 * 2 exp(-100 pi) ≈ 7.3e-136`. And at `s = 0.1` the discrepancy from `1/sqrt(s)` is `1.436e-13`,
which is *exactly* `2 exp(-10 pi)/sqrt(0.1)`, the leading term of the dual expansion. The
short-time asymptotic is not an approximation that happens to be good; it is the long-time expansion
of the *dual* problem, read backwards through Jacobi's identity.

**This is a UV/IR duality** in the physicist's sense: the ultraviolet description (short time, fine
structure, high frequencies) and the infrared description (long time, coarse structure, low
frequencies) carry the same information in different coordinates. The computational payoff is
immediate. Count the terms whose maximum size on the circle exceeds `1e-16` (so: everything a
double-precision evaluation can even see):

```
    t          Fourier modes |n| <=      Gaussian images |m| <=
   1e-1                3                        4
   1e-2                9                        2
   1e-3               30                        1
   1e-4               97                        1
   1e-6              975                        1
```

The two columns cross near the self-dual time `t* = 1/(4 pi) ≈ 0.08`. Use the Gaussian face below
`t*` and the Fourier face above it and no theta evaluation ever costs more than a handful of terms.
(This is precisely why `zeta/core.py` keeps both `theta_heat` and `theta_heat_gaussian`: they are
"computationally complementary", as its docstrings put it.)

**HEURISTIC (but load-bearing).** This self-similarity is the seed of every symmetry downstream.
When `docs/03-functional-equation.md` runs the Mellin transform

```
    pi^(-s/2) Gamma(s/2) zeta(s)  =  integral from 0 to infinity  x^(s/2 - 1) omega(x) dx,
    omega(x) = sum_{n>=1} exp(-pi n^2 x) = (theta(x) - 1)/2
```

and splits the integral at `x = 1`, the substitution `x -> 1/x` on the lower piece can only be
carried out *because* `theta(1/x) = sqrt(x) theta(x)` says what happens to the integrand. Out drops
a right-hand side visibly invariant under `s -> 1 - s`. The map `x -> 1/x` on time becomes
`s -> 1 - s` on the complex plane, and the fixed line of `s -> 1 - s` is `Re(s) = 1/2`.

Be precise about what this does and does not establish. **THEOREM:** the completed zeta function is
symmetric about the line `Re(s) = 1/2`; that is why the critical line is *that* line and not some
other. **CONJECTURE (Riemann Hypothesis):** the non-trivial zeros actually *lie* on it. The
functional equation alone does not imply RH, the Davenport–Heilbronn function is the example
usually cited of a Dirichlet series with a Riemann-type functional equation whose zeros stray off
the critical line. Modularity installs the mirror; it does not pin the zeros to the mirror.

---

## 6. The modular-forms framing (brief, and hedged where hedging is due)

Everything above is the real-analytic shadow of a complex-analytic statement. Write
`q = exp(2 pi i tau)` for `tau` in the upper half-plane and set

```
    Theta(tau)  =  sum over n in Z  q^(n^2)  =  sum over n in Z  exp(2 pi i n^2 tau)
```

Then `Theta` is the standard example of a **modular form of weight 1/2 for `Gamma_0(4)`**, with a
multiplier system: for `gamma = [[a,b],[c,d]]` in `Gamma_0(4)`,
`Theta(gamma tau) = j(gamma, tau) Theta(tau)`, where the automorphy factor `j` is essentially
`(c tau + d)^(1/2)` times a fourth root of unity built from a Jacobi symbol. Shimura's 1973 Annals
paper *On modular forms of half integral weight* is the canonical modern reference for the
half-integral-weight formalism. (I am confident of the weight, the group, and the shape of the
multiplier; I have deliberately not written the multiplier's exact normalisation, because
conventions differ across sources, check one before computing with it.)

Two accuracy notes that are classic traps:

1. In the other common normalisation, `theta_3(0 | tau) = sum_n exp(pi i n^2 tau)`, the natural
   invariance group is the **theta group**, generated by `tau -> tau + 2` and `tau -> -1/tau`. The
   two conventions differ by `tau -> 2 tau`. Both statements are correct in their own convention;
   mixing them is the standard error.
2. The inversion `S: tau -> -1/tau` is *not* an element of `Gamma_0(4)`. The true statement is the
   transformation law `theta_3(0 | -1/tau) = sqrt(-i tau) * theta_3(0 | tau)`. Setting `tau = i s`
   recovers exactly our identity, since `sqrt(-i * i s) = sqrt(s)`. So the identity we derived from
   heat *is* the `S`-transformation of theta, and `S` is what becomes the reflection `s -> 1 - s`
   after the Mellin transform.

Weight `1/2` is not a curiosity. It is where the `sqrt(s)` in Jacobi's identity comes from, and
after the Mellin transform it is where the `1/2` in `Re(s) = 1/2` comes from. The square root in
the transformation law and the axis of the critical line are the same number.

---

## 7. What the code verifies, and the numbers it reports

`zeta/core.py` implements both faces and tests every claim in this document by *direct summation*,
never by invoking the identity being tested, so a small defect is evidence, not a tautology. The
relevant functions: `theta`, `omega`, `theta_modular_defect`, `theta_heat` (Fourier face),
`theta_heat_gaussian` (Gaussian face), `theta_heat_poisson_defect`, `theta_heat_residual`, and the
constant `HEAT_DIFFUSIVITY = 1`. Numbers below were re-run for this document.

- **The heat-equation residual.** `theta_heat_residual(x, t)` computes
  `u_t - D * u_xx` with `D = 1`, using 4th-order central finite-difference stencils
  (default step `h = 1e-10`) at 30 guard digits. Measured at `x = 0.42`:

  ```
      t         |residual|          (absolute)
      0.005      1.7e-30
      0.02       1.2e-32
      0.05       5.3e-35
      0.1        1.1e-35
      0.5        3.6e-42
      1.0        6.7e-42
  ```

  The floor near `4e-42` is finite-difference round-off (`eps/h^2` at 60 working digits), not the
  PDE failing; the residual scales as `h^4` exactly as the stencil order predicts (measured at
  `x = 0.3, t = 0.05`: `h = 1e-6` gives `2.2e-18`, `h = 1e-8` gives `2.2e-26`), and raising `dps`
  pushes the floor down (at `t = 1, dps = 45` the raw residual drops to `4e-51`). Relative to
  `|u_xx|` (which is `24.3` at `t = 0.02` and `9.5` at `t = 0.05`, at `x = 0.42`), the PDE with
  `D = 1` is confirmed to better than 30 significant digits across the physically interesting
  range. Passing `diffusivity = 1/(4 pi^2)`, the wrong normalisation of Section 1, makes the
  residual order one, which is the point of exposing that parameter.

- **The two faces agree (Poisson).** `theta_heat_poisson_defect(0.3, 0.01)` returns `0.0` at 40
  digits; both faces independently give `theta_heat(0.3, 0.01) = 0.2973392216260169524`. In
  `float64` arithmetic the two faces disagree only at the rounding level.

- **Modularity.** `theta_modular_defect(x)` = `theta(1/x) - sqrt(x) theta(x)`, with both terms
  summed directly, returns `0.0` at 50 digits for every `x` tried (including `x = 0.1` and
  `x = 7.3`).

These three checks are the invariants to keep green if you extend the lab: they are cheap, they are
essentially exact, and every later result leans on them, `theta_mellin_xi` in the same module
already uses the modular relation to build the completed zeta function of the next document.

---

## Where to go next

- **`docs/03-functional-equation.md`**: the payoff. Mellin-transform `omega`, split the integral at
  `x = 1`, apply Section 4's identity, and the functional equation `xi(s) = xi(1-s)` falls out,
  along with the poles, the trivial zeros, and the reason the critical line sits where it does. This
  document exists mainly to make that one inevitable.
- **`docs/05-de-bruijn-newman.md`**: the frontier. Having watched heat flow *produce* the completed
  zeta function, run heat flow *on* it: the de Bruijn–Newman deformation asks how the zeros of `Xi`
  move under a diffusion in a new time variable, and RH becomes the statement that we live exactly
  at a critical time. `zeta/heatflow.py` is the accompanying code.
- **`docs/04-explicit-formula.md`**, Section 2's geometry/spectrum duality grown up: windings
  become prime powers, eigenvalues become zeros.
- **Play with it.** Plot `theta_heat(x, t)` for `t` from `1e-4` up through `t* = 1/(4 pi)` and watch
  the spike relax to the constant 1; plot the term counts of Section 5 and watch the two curves
  cross at `t*`. Modularity stops being an identity and becomes a picture.
