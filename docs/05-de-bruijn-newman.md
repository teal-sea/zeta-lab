# 05. The de Bruijn–Newman Constant: Running Heat Flow *on* Zeta

*The payoff of `docs/02-theta-heat-and-modularity.md`. There we watched heat flow **produce** `Xi`.
Here we run heat flow **on** `Xi` and ask how the zeros move.*

**The short version.** The completed zeta function can be written as a cosine transform,
`Xi(z/2)/8 = integral_0^inf Phi(u) cos(zu) du`, where `Phi` is built directly out of the theta
function of `docs/02` and its first two derivatives. Now insert a Gaussian factor `e^{t u^2}` into
that integral. The result `H_t(z)` is an entire function for every real `t`, it equals `Xi` (up to
normalisation) at `t = 0`, and it satisfies `dH/dt = -d^2H/dz^2`, the **backward** heat equation.
This flow has a beautiful effect on roots: increasing `t` makes real roots **repel** and spread out,
and once they are all real they stay real forever. So there is a threshold time
`Lambda = inf{t : H_t has only real zeros}`, the **de Bruijn–Newman constant**. **THEOREM** (de
Bruijn 1950): `Lambda <= 1/2`. **THEOREM** (Rodgers–Tao 2018): `Lambda >= 0`. And RH is *exactly* the
statement `Lambda <= 0`. Putting these together: **RH is equivalent to `Lambda = 0`**. The zeros of
zeta are sitting, right now, at the precise instant of criticality, there is no slack. That is what
Newman meant when he said RH, if true, is "only barely so".

---

## 1. Xi as a Fourier integral, and where `Phi` comes from

Recall from `docs/03-functional-equation.md` the completed function

```
    xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s),        Xi(z) = xi(1/2 + iz)
```

`Xi` is entire, even, real on the real axis, and RH is the statement that all its zeros are real.

Now set (this is the half-theta that `docs/02` and `docs/03` call `omega`; Riemann's own memoir
wrote `psi` for it, and it is **not** the Chebyshev `psi` of `docs/04`),

```
    psi(x) = sum_{n>=1} e^{-pi n^2 x} = (theta(x) - 1)/2
```

and define

```
    Phi(u) = 2 e^{9u} psi''(e^{4u}) + 3 e^{5u} psi'(e^{4u})
```

Differentiating `psi` term by term (`psi' = -sum pi n^2 e^{-pi n^2 x}`,
`psi'' = sum pi^2 n^4 e^{-pi n^2 x}`) and substituting `x = e^{4u}` gives the explicit form:

```
    Phi(u) = sum_{n>=1} ( 2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u} ) exp(-pi n^2 e^{4u})
```

**This is the point worth pausing on.** `Phi` is not some new special function conjured for the
occasion. It is *the heat kernel of `docs/02`*, differentiated twice and reparametrised by
`x = e^{4u}`. Everything below is still, at bottom, heat on a circle. The series is implemented as
`zeta.heatflow.Phi` and cross-checked there against an independent `mpmath.nsum` evaluation
(relative agreement `1.4e-41` at 40 digits); re-running both forms here, each gives
`Phi(0) = 0.4466969004671234440869847` and `Phi(0.3) = 0.007423456244391188221752` (dps = 40).

**THEOREM.** With this `Phi`,

```
    H_0(z)  :=  integral from 0 to infinity of  Phi(u) cos(zu) du   =   Xi(z/2) / 8
```

Nothing here is trusted to memory: `zeta.heatflow.H0_vs_Xi` *measures* both constants of the ansatz
`H_0(z) = c * Xi(a z)` from the functions themselves, `c = H_0(0)/Xi(0)` directly, and the rescaling
`a` by two independent routes (curvature at the origin, using `H_0''(0) = -integral u^2 Phi(u) du`;
and matching the first zero of `H_0` against the first zeta ordinate). Both routes return `a = 0.5`
to within `3e-41`, `c` returns `0.125` to `1.1e-42`, and the exact rational relation then verifies
pointwise to a maximum residual of `7.9e-42` over real `z` in `[0, 100]` plus complex probes
(dps = 40). Re-run for this document: both sides give `0.06214009727353926373909672` at `z = 0`, and
`|H_0(z) - Xi(z/2)/8| <= 4.4e-42` at `z = 1, 5, 14.134725, 28.2`. (The `z/2` is a normalisation
convention inherited from the Polymath15 literature; it means the zeros of `H_t` sit at `2*gamma`,
where `gamma` are the ordinates of the zeta zeros, at `t = 0` the module's `zeros_of_H_t` reproduces
`2*gamma_n` for the first ten zeros to a measured `1.3e-19` at dps = 30. Keep track of that factor of
2, it matters when you compare gaps.)

Where does the formula come from? Take the Mellin representation of `docs/03`,
`xi(s) = 1/2 + (s(s-1)/2) * integral_1^inf (x^{s/2-1} + x^{-(1+s)/2}) psi(x) dx`, integrate by parts
twice to kill the polynomial prefactor `s(s-1)`, then substitute `x = e^{4u}`. The `e^{9u}` and
`e^{5u}` are bookkeeping from the chain rule and the Jacobian; the `2` and the `3` are what the two
integrations by parts leave behind.

**One gorgeous consequence.** `Phi` is an **even** function: `Phi(-u) = Phi(u)`. That is not visible
in the series at all, under `u -> -u` the exponent `e^{4u}` becomes `e^{-4u}`, which looks like a
completely different function. It is true because `x -> 1/x` is exactly Jacobi's modular identity
`theta(1/x) = sqrt(x) theta(x)`: with `F(x) = d/dx[ x^{3/2} psi'(x) ]` one has
`Phi(u) = 2 e^{3u} F(e^{4u})`, and evenness of `Phi` is precisely `F(1/x) = x^{3/2} F(x)`, which
`zeta.heatflow` verifies independently to `1.6e-51` at `x = 1.5` (dps = 50). On the series itself,
`Phi_is_even_defect` measures the *relative* defect below `1e-34` for `|u| <= 0.5` at dps = 40,
and is scrupulous about where that test loses meaning: past `|u| ~ 0.85` the raw series is a
catastrophic cancellation (summands of size 1 conspiring to produce a value below `1e-70`) and
returns pure noise, which is why the module computes `Phi` by folding through the exact identity
`Phi(u) = Phi(|u|)` first. **The evenness of `Phi` IS the functional equation.** Which is why we may
equally write `H_t(z) = (1/2) integral over all of R of e^{t u^2} Phi(u) e^{izu} du`, a genuine
Fourier transform of an even, real, rapidly decaying function, hence an even entire function of `z`,
real on the reals.

---

## 2. The deformation, and the sign of the heat equation

Define, for real `t`:

```
    H_t(z)  =  integral from 0 to infinity of  e^{t u^2} Phi(u) cos(zu) du
```

This converges for **every** real `t`, positive or negative, because `Phi(u) ~ exp(-pi e^{4u})` decays
*doubly* exponentially, and a double exponential eats `e^{tu^2}` for breakfast. So `H_t` is entire in
`z` for all `t`, and `H_0 = Xi(z/2)/8`.

**Multiplying by `e^{tu^2}` on the transform side is running the heat equation on the `z` side.**
Differentiate under the integral:

```
    dH/dt     =  integral  u^2 e^{tu^2} Phi(u) cos(zu) du
    d^2H/dz^2 =  integral  e^{tu^2} Phi(u) * (-u^2) cos(zu) du   =   -dH/dt
```

so

```
    dH/dt  =  -d^2H/dz^2                        (BACKWARD heat equation)
```

**Verify the sign; do not trust your memory here.** `zeta/heatflow.py` owns this check as
`heat_equation_residual`, which forms `|dH/dt + d2H/dz2|` by central differences, the combination
that vanishes under the backward convention and is order-1 under the forward one. Re-measured for
this document (dps = 30, step `h = 1e-6`):

```
    (z, t) = ( 3,  0.0):    |dH/dt + d2H/dz2|  =  1.8e-18
    (z, t) = (10,  0.2):    |dH/dt + d2H/dz2|  =  1.0e-18
    (z, t) = (28, -0.1):    |dH/dt + d2H/dz2|  =  3.5e-19
```

(the residual floor is the finite-difference step, not the quadrature). The module also compares the
two integrands directly, and that check reproduces here too: at `(z, t) = (10, 0.2)`,

```
    dH/dt      =  -4.85383252228e-5
    d2H/dz2    =  +4.85383252228e-5
```

exact negatives to every displayed digit. The wrong sign is not a near-miss; it is off by a factor of
exactly `-1`.

A terminological trap worth defusing. "Backward heat equation" sounds bad, it is famously ill-posed,
it amplifies high frequencies (that is literally what `e^{tu^2}` does), and in general you cannot run
it. Here you can, because `Phi` decays fast enough to absorb any amount of amplification. Note the
direction bookkeeping:

- **`t` increasing** = backward heat = high frequencies amplified = the function becomes *more*
  oscillatory = zeros push apart and stay real.
- **`t` decreasing** = ordinary forward heat = convolution with a Gaussian = smoothing = oscillations
  washed out = zeros collide and leave the real axis.

That second bullet is the one people get backwards. Gaussian smoothing *destroys* real roots: convolve
a function whose sign changes at spacing `d` with a Gaussian much wider than `d` and the sign changes
are averaged away, they have to go somewhere, and where they go is off the real axis.

---

## 3. The constant, and the theorems

Because "all zeros real" is preserved by increasing `t` (this is the content of de Bruijn's and
Newman's work, not an obvious fact), the set of good times is a half-line, and we may define:

```
    Lambda  =  inf { t in R : H_t has only real zeros }
```

- **THEOREM (de Bruijn, 1950).** `H_t` has only real zeros for `t >= 1/2`; hence `Lambda <= 1/2`.
  (N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17 (1950), 197–226.)
- **THEOREM (Newman, 1976).** `Lambda > -infinity`: the threshold is finite, and for `t` below it
  `H_t` genuinely has non-real zeros. (C. M. Newman, *Fourier transforms with only real zeros*, Proc.
  Amer. Math. Soc. 61 (1976), 245–251.)
- **CONJECTURE (Newman, 1976).** `Lambda >= 0`. Newman's gloss, as it is universally quoted, is that
  this is *"a quantitative version of the dictum that the Riemann hypothesis, if true, is only barely
  so."* (I am confident of the sense and near-confident of the wording; check the original before
  quoting it in print.)
- **THEOREM (Ki–Kim–Lee, 2009).** In fact `Lambda < 1/2` *strictly* (H. Ki, Y.-O. Kim, J. Lee, *On
  the de Bruijn–Newman constant*, Adv. Math. 222 (2009)). To this day that is the only known strict
  upper bound; the numerical bounds below are non-strict.
- **THEOREM (equivalence, immediate from `H_0 = Xi(z/2)/8`).** RH holds if and only if `H_0` has only
  real zeros, if and only if `Lambda <= 0`.
- **THEOREM (Rodgers–Tao, 2018).** `Lambda >= 0`. Newman's conjecture is now a theorem. (Brad Rodgers
  and Terence Tao, *The de Bruijn–Newman constant is non-negative*, arXiv:1801.05914, January 2018;
  published in Forum of Mathematics, Pi 8 (2020), e6.)

**Corollary: RH is equivalent to `Lambda = 0`.** That is a genuine reformulation, not a weakening,
not a heuristic, an if-and-only-if.

On the upper bound: de Bruijn's `1/2` stood essentially alone for half a century (Ki–Kim–Lee made it
strict in 2009). The **Polymath15** collaboration (led by Tao) then pushed it to `Lambda <= 0.22`
(D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function, and a
new upper bound for the de Bruijn–Newman constant*, Res. Math. Sci. 6 (2019), paper 31), and feeding
Platt–Trudgian's verification of RH up to height `3 x 10^12` back into the same machinery gives the
current record `Lambda <= 0.2` (D. J. Platt, T. S. Trudgian, *The Riemann hypothesis is true up to
3·10^12*, Bull. Lond. Math. Soc. 53 (2021)). The full bound history, with citations checked against
the primary sources, is catalogued in code as `zeta.heatflow.lambda_facts()`.

From below, before Rodgers–Tao, the record bounds came from "Lehmer pairs" of unusually close zeros,
a chain of improvements through the 1990s (the Csordas–Smith–Varga Lehmer-pair criterion, Constr.
Approx. 10 (1994); `Lambda > -5.895e-9`, Csordas–Odlyzko–Smith–Varga 1993; `Lambda > -2.7e-9`,
Odlyzko 2000) ending with Saouter–Gourdon–Demichel's `Lambda > -1.14541e-11` (Math. Comp. 80 (2011)).
Rodgers–Tao made all of it moot, though the *mechanism* those bounds exploited is exactly the
collision heuristic of the next section.

---

## 4. The intuition: roots as repelling particles

Here is the mechanism, and it is elementary enough to verify in ten lines of numpy.

Let `p(z, t)` be a monic polynomial with roots `r_1(t), ..., r_N(t)`, evolving by the same equation
`dp/dt = -p''`. Differentiate `p = prod_i (z - r_i)` and evaluate at `z = r_k`. Using
`p''(r_k) = 2 p'(r_k) sum_{j != k} 1/(r_k - r_j)`, the factor `p'(r_k)` cancels and you get:

```
    dr_k/dt  =  +2 * sum_{j != k}  1 / (r_k - r_j)              (under  dp/dt = -p'')
    dr_k/dt  =  -2 * sum_{j != k}  1 / (r_k - r_j)              (under  dp/dt = +p'')
```

**Verify the sign; this is the second place memory betrays people.** `zeta/heatflow.py` owns this as
`polynomial_heat_flow`, and it does the verification the brutal way: it evolves the *coefficients*
exactly (for a polynomial, `exp(-t D^2) p = sum_k (-t)^k/k! p^{(2k)}` is a finite sum), takes the
roots of the evolved polynomial, and compares them against RK4 integration of the root ODE, for
**all four** sign combinations, with roots `[-3, -1, 0.5, 2, 4.5]` over `t in [0, 0.35]`:

```
    exp(-t D^2)  with const = +2   ->   max |ODE - exact| = 9.3e-15    OK
    exp(-t D^2)  with const = -2   ->   max |ODE - exact| = 1.6e+00    WRONG
    exp(+t D^2)  with const = -2   ->   max |ODE - exact| = 2.7e-14    OK
    exp(+t D^2)  with const = +2   ->   max |ODE - exact| = 1.6e+00    WRONG
```

The pairing is rigid: `exp(-t D^2)`, the de Bruijn–Newman convention, goes with `+2` and
**repulsion**; the classical forward heat equation goes with `-2` and attraction. Beware: the root
ODE is often quoted with the `-2`, and quoting it with `-2` while also claiming "roots repel as `t`
increases" is self-contradictory; the table above is the antidote. The `+` sign means repulsion
because if `r_k` sits to the right of `r_j`, the term `1/(r_k - r_j)` is positive and pushes `r_k`
further right. Closer neighbours push harder, the force goes like `1/distance`.

Integrating for a while makes the picture visceral. Re-running `polynomial_heat_flow` on those same
five roots for this document (RK4 agreeing with the exact coefficient evolution to `8.9e-15`):

```
    t:              -1.0    -0.5    -0.2     0      0.35
    spread:         2.16    5.12    6.62    7.50    8.85
    min gap:         --      --     1.13    1.50    1.92
    max |Im r|:     2.25    0.57    0       0       0
```

Real roots stay real and fly apart as `t` increases; run the flow backwards and the gaps shrink until
roots crash into each other and shoot off the axis as conjugate pairs (by the `t = -0.5` sample two
have already left; `--` marks times where a real gap no longer exists). The same monotone gap growth
is visible on the genuine `H_t`: `zero_gap_statistics` on the window `[20, 105]` (exactly the first
ten zeros) measures a minimum gap of `3.28939` at `t = -0.3`, `3.53736` at `t = 0`, and `3.94962` at
`t = +0.6`: re-verified here at all three values of `t`.

**The two-particle law.** Isolate two roots at `+-delta/2`. Then `d(delta)/dt = 4/delta`, so

```
    delta(t)^2  =  delta_0^2  +  8t
```

For an isolated pair this is not merely a heuristic, it is exact, because
`exp(-t D^2)(z^2 - delta_0^2/4) = z^2 - delta_0^2/4 - 2t`, and `polynomial_heat_flow` on roots
`+-0.25` at `t = 0.1` confirms it: `delta` agrees with `sqrt(0.25 + 0.8) = 1.0246950766` to machine
precision (difference below `1e-15`). Two facts fall out of that one line:

1. Going **forward** (`t` up), `delta` grows like `sqrt(8t)`, the pair can never collide. Real roots
   are permanent.
2. Going **backward**, `delta` hits zero at `t = -delta_0^2/8`, and past that `delta^2 < 0`, i.e.
   `delta` is imaginary: **the pair has left the real axis as a complex-conjugate pair.** A collision
   is exactly the event "two real zeros become two non-real zeros".

So `Lambda` is the moment of the *first collision* as you run the film backwards. And **Rodgers–Tao's
theorem `Lambda >= 0` says that moment is now.** Not "some time in the past", now. Run the zeta zeros
backwards by any positive amount of heat and, by their theorem, somewhere, at some height, a pair has
already collided. RH, which says `Lambda <= 0`, would say the collisions have not started yet. Both
together: the zeros of zeta sit at the exact critical instant, with zero margin. That is the precise
content of "barely true".

**Where is the tightness?** Not down at `gamma = 14.13`. It is out at large height, where the mean
spacing `2 pi / log(gamma / 2 pi)` shrinks and unusually close pairs occur. Rodgers–Tao's proof is
statistical: it shows that `Lambda < 0` would force the zeros at large height to be *implausibly*
evenly spaced, more rigid than they can be, given what is known about their pair correlation. The
obstruction is a statement about the *distribution* of gaps, not about any individual zero. The
module's `track_zeros` says the same thing in code, as an honest caveat in its docstring: over
`|t| <= 1` the first ten zeros stay real and comfortably separated, what the laboratory exhibits is
the repulsion *mechanism*, not the location of `Lambda`.

Lehmer's famous close pair makes the numbers concrete. Recomputed here (`mpmath.zetazero`, 20 digits):

```
    gamma_6709 = 7005.062866174921
    gamma_6710 = 7005.100564672647
    gap        = 0.037698498
    mean gap at this height = 2 pi / log(gamma / 2 pi) = 0.895486
    ratio      = 0.0421          (about 4% of normal spacing)
```

**HEURISTIC.** In the `H_t` variable the zeros sit at `2*gamma`, so `delta_0 = 0.0753970`, and the
two-particle law predicts collision at `t = -delta_0^2/8 = -7.1 x 10^{-4}`. If those two zeros were
alone in the world, that would show `Lambda > -7.1 x 10^{-4}`. They are not alone, every other zero
pushes on them, so this is a heuristic, not a proof. The rigorous Lehmer-pair criteria of Csordas–
Smith–Varga are the honest version, and applied to far closer pairs found at far greater heights they
gave the pre-2018 record lower bounds. But the mechanism is exactly this one.

---

## 5. Heat flow, level repulsion, and GUE are one phenomenon

The ODE `dr_k/dt = 2 sum_{j != k} 1/(r_k - r_j)` is not an accident of this problem. It is the
deterministic core of **Dyson Brownian motion**: add independent Brownian noise to each coordinate and
you get exactly the eigenvalue process of a random Hermitian matrix undergoing Gaussian diffusion,
whose stationary measure is the GUE eigenvalue density with its `prod_{i<j} |r_i - r_j|^2` Vandermonde
factor. The same `1/(r_i - r_j)` force is the Calogero–Moser interaction in integrable systems.

So three things you might have thought were separate are one thing:

- **heat flow** on `Xi` moves zeros by an inverse-distance repulsion;
- **level repulsion** in random matrix spectra is that same force, thermalised;
- **GUE pair-correlation statistics** for the zeta zeros (Montgomery 1973; Odlyzko's computations) are
  the empirical fingerprint of it.

`docs/06` covers the statistics; the thing to carry over is that the "zeros repel" you meet there and
the "zeros repel" here are literally the same `1/(r_i - r_j)`. This is a genuine structural
coincidence and one of the better reasons to believe a spectral interpretation of the zeros exists.

---

## 6. Honest status

This is a research frontier and a genuine reformulation. It is **not** a road to a proof, and it is
worth being blunt about why.

- **What is proved:** `0 <= Lambda <= 0.2`, and RH `<=>` `Lambda = 0`.
- **What is needed:** to prove RH you must push the upper bound all the way down to `0`. Every existing
  upper-bound technique, de Bruijn's, Polymath15's, works by *effective numerics plus explicit error
  control*: verify enough zeros, bound the tail, conclude no collision can have happened by time `t`.
  That style of argument gets you to `0.2` and, with enough compute, perhaps to `0.1`. It cannot reach
  `0`, because at `t = 0` the margin it needs vanishes identically. You would be trying to prove a
  strict inequality with a method whose error term is exactly the quantity going to zero.
- **Why `Lambda = 0` is hard from this side:** Rodgers–Tao proved `Lambda >= 0` precisely by showing
  that `Lambda < 0` forces impossibly rigid zero statistics. The mirror-image argument for
  `Lambda <= 0` would have to *rule out* a collision at `t = 0-` uniformly over all heights, an
  infinite amount of local information, which is RH itself. The reformulation moves the difficulty; it
  does not dissolve it.
- **What it has bought us:** a *quantitative* RH. Before, RH was true or false. Now there is a real
  number `Lambda` known to lie in `[0, 0.2]`, pinned at one end by a theorem, and any improvement to
  the upper bound is measurable progress. That is a real change in the epistemic situation, even though
  the remaining gap is a chasm.

(De Branges's approach, Hilbert spaces of entire functions and positivity conditions, is sometimes
mentioned in the same breath. It is a different programme, and its published proof attempts have not
been accepted. I mention it only so you know the two are not the same thing.)

---

## Where to go next

- **`docs/06-hilbert-polya-and-gue.md`**: random matrix statistics. Read §5 above first, then watch
  the same `1/(r_i - r_j)` reappear as the GUE Vandermonde. Montgomery's pair correlation and
  Odlyzko's numerics live there.
- **`docs/02-theta-heat-and-modularity.md`**: go back and reread §4 now that you know the evenness of
  `Phi` *is* `theta(1/x) = sqrt(x) theta(x)`. The identity that gave us the functional equation is the
  identity that makes `H_t` an even entire function.
- **`docs/04-explicit-formula.md`**, the other way to make zeros move: perturb the primes instead of
  the transform.
- **The code.** `zeta/heatflow.py`: `Phi(u)`, `H_t(z, t)`, `H0_vs_Xi()` (measures the `(1/8, 1/2)`
  normalisation from the data rather than assuming it), `heat_equation_residual`,
  `zeros_of_H_t`, `zero_gap_statistics`, `track_zeros` (follows the first ten zeros as `t` varies,
  with caching), `polynomial_heat_flow`, and `lambda_facts()` (the bound history with citations). Its
  docstrings double as a lab notebook, the accuracy claims in them are measured numbers, pinned by
  `tests/test_heatflow.py`. Zeros for the Lehmer-pair experiment come from `zeta/zeros.py`
  (`first_n_zeros`, or `zeros_by_sign_change` for a targeted window).
- **Play with it.** Take the first 50 zeros as roots of a polynomial in the `H` variable (`2*gamma`),
  flow backwards with `polynomial_heat_flow`, and time the first collision. It will happen far too
  early, the truncation destroys the delicate balance, and *that failure* is the best illustration
  available of how global the `Lambda = 0` statement is. No finite piece of the zero set knows the
  answer.
