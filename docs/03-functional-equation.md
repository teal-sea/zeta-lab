# 03. Riemann's Functional Equation, Derived Line by Line

## The short version

Riemann's functional equation is not a coincidence you verify afterwards; it is a *change of
variable*. Write `Gamma(s/2) pi^(-s/2) n^(-s)` as an integral of `exp(-pi n^2 x)` against
`x^(s/2-1)`, sum over `n`, and `zeta(s)` becomes the Mellin transform of the theta function
`theta(x) = sum_{n in Z} exp(-pi n^2 x)`. Theta has the hidden self-similarity proved in
`docs/02-theta-heat-and-modularity.md`, `theta(1/x) = sqrt(x) theta(x)`, so if you cut the integral
at `x = 1` and flip the short half onto the long half by `x -> 1/x`, you land on a formula whose
right-hand side is *visibly* unchanged by `s -> 1-s`. That one formula simultaneously (a)
analytically continues `zeta` to the whole plane, (b) proves the functional equation, and (c) shows
the only poles are simple ones at `s = 0` and `s = 1`. Everything else below, the completed function
`xi`, the critical line, the trivial zeros, the Hadamard product, is bookkeeping on top of that
single line.

*Notation.* Riemann's memoir (and Edwards) call the half-theta `psi(x)`; here, as in `docs/02` and
`zeta/core.py`: it is `omega(x)`, because `psi` is already taken by the Chebyshev prime-counting
function in `docs/04-explicit-formula.md` and in `zeta/explicit.py`. Same object.

---

## 1. The one input: theta's transformation law

We import exactly one external fact.

**THEOREM (Jacobi).** For `x > 0`, with `theta(x) = sum_{n = -inf}^{inf} exp(-pi n^2 x)`,

```
    theta(1/x)  =  sqrt(x) · theta(x)
```

It is convenient to drop the `n = 0` term and fold the two symmetric tails:

```
    omega(x)  :=  (theta(x) - 1)/2  =  sum_{n >= 1} exp(-pi n^2 x)
```

Two properties of `omega` carry the whole argument.

**Fast decay.** For `x > 0`, since `n^2 >= n`,

```
    omega(x)  <=  sum_{n >= 1} exp(-pi n x)  =  exp(-pi x) / (1 - exp(-pi x))
```

so on `x >= 1` we get `omega(x) <= 1.0452 · exp(-pi x)`. Numerically `omega(1) = 0.04321740560665...`
(consistent with `theta(1) = 1.08643481121330801...` quoted in `docs/02`) and
`omega(2) = 0.00186744274...`, already within `10^(-11)` of its single leading term `exp(-2 pi)`.

**Jacobi restated for `omega`.** Substitute `theta = 2 omega + 1` into `theta(1/x) = sqrt(x) theta(x)`:

```
    2 omega(1/x) + 1  =  sqrt(x) (2 omega(x) + 1)

    ==>   omega(1/x)  =  sqrt(x) · omega(x)  +  (sqrt(x) - 1)/2                          (*)
```

That leftover `(sqrt(x) - 1)/2` is not debris. It is exactly where the poles of `zeta` come from.
Watch it.

---

## 2. Step one: `n^(-s)` is a Gaussian integral in disguise

Start from the definition `Gamma(w) = integral_0^inf t^(w-1) e^(-t) dt`, valid for `Re w > 0`. Put
`w = s/2` and substitute `t = pi n^2 x`, so `dt = pi n^2 dx` and `t^(s/2 - 1) = (pi n^2 x)^(s/2 - 1)`:

```
    Gamma(s/2)  =  integral_0^inf (pi n^2 x)^(s/2 - 1) exp(-pi n^2 x) · pi n^2 dx
                =  (pi n^2)^(s/2) · integral_0^inf x^(s/2 - 1) exp(-pi n^2 x) dx
```

Divide by `(pi n^2)^(s/2) = pi^(s/2) n^s`:

```
    pi^(-s/2) Gamma(s/2) n^(-s)  =  integral_0^inf x^(s/2 - 1) exp(-pi n^2 x) dx,    Re s > 0    (1)
```

*Why this is the right move, not just a legal one.* On the left is one term of the Dirichlet series
with a Gamma factor bolted on. On the right is an object that knows about a *lattice*: `exp(-pi n^2 x)`
is a fixed Gaussian sampled at the integer `n`. Summing over `n` converts an arithmetic sum into a
geometric one, and geometry is where the symmetry hides. The Mellin transform is the right currency
for the reason `docs/01-sums-integrals-and-continuation.md` §4 gives: it is the Laplace transform of
the multiplicative group `(0, inf)`, whose defining involution is `x -> 1/x`.

---

## 3. Step two: sum over `n`

Take `Re s > 1` and sum (1) over `n >= 1`:

```
    pi^(-s/2) Gamma(s/2) zeta(s)  =  sum_{n>=1} integral_0^inf x^(s/2-1) exp(-pi n^2 x) dx

                                  =  integral_0^inf x^(s/2 - 1) omega(x) dx                  (2)
```

*Why the interchange is legal.* For real `s > 1` every term is positive, so Tonelli applies with no
work. For complex `s`, run the same argument on `|x^(s/2-1)| = x^(Re s/2 - 1)` to get absolute
convergence, then Fubini.

*Where (2) converges.* At the top end, `omega` decays like `e^(-pi x)`, so there is no constraint. At
the bottom end, Jacobi gives `theta(x) = x^(-1/2) theta(1/x)` and `theta(1/x) -> 1` as `x -> 0+`, so
`omega(x) ~ (1/2) x^(-1/2)`. Then `integral_0 x^(Re s/2 - 1) x^(-1/2) dx` converges precisely when
`Re s > 1`. The obstruction to continuation is *entirely* at `x = 0`, and it is a single explicit
power of `x`. That is a solvable problem.

The left-hand side of (2) deserves its own name: it is `zeta` *completed* by its archimedean factor
`pi^(-s/2) Gamma(s/2)`. The Euler product supplies one factor per prime; the Gamma factor is the
missing factor at the "prime at infinity". Nothing about `zeta` looks symmetric until you put it in.

---

## 4. Step three: split at `x = 1` and fold

Split (2) at the fixed point of `x -> 1/x`:

```
    pi^(-s/2) Gamma(s/2) zeta(s)  =  integral_0^1 x^(s/2-1) omega(x) dx
                                   + integral_1^inf x^(s/2-1) omega(x) dx
```

The second integral is already harmless. Because `omega(x) <= 1.05 e^(-pi x)` on `[1, inf)`, it
converges for **every** complex `s` and defines an entire function of `s` (differentiate under the
integral sign; the exponential decay dominates the polynomial-in-`log x` growth of `x^(s/2-1)` locally
uniformly in `s`).

Now attack the first integral with `x = 1/u`, `dx = -du/u^2`:

```
    integral_0^1 x^(s/2-1) omega(x) dx  =  integral_1^inf u^(-s/2+1) omega(1/u) u^(-2) du
                                        =  integral_1^inf u^(-s/2-1) omega(1/u) du
```

and substitute the restated Jacobi identity (*), `omega(1/u) = sqrt(u) omega(u) + (sqrt(u)-1)/2`:

```
    =  integral_1^inf u^(-s/2 - 1/2) omega(u) du
     + (1/2) integral_1^inf ( u^(-s/2 - 1/2) - u^(-s/2 - 1) ) du
```

The first piece is `integral_1^inf u^((1-s)/2 - 1) omega(u) du`, *the same shape as the tail integral
we already have, with `s` replaced by `1-s`*. That is the whole trick, and it is worth pausing on:
the inversion `x -> 1/x` on the theta side has become the reflection `s -> 1-s` on the zeta side,
because the Mellin kernel `x^s` turns multiplicative inversion into additive negation, and the
`sqrt(x)` in Jacobi's law shifts the negation's centre from `0` to `1/2`.

The second piece is elementary. For `Re s > 1` both exponents are `< -1`, so

```
    integral_1^inf u^(-s/2-1/2) du = 2/(s-1),        integral_1^inf u^(-s/2-1) du = 2/s
```

giving `(1/2)(2/(s-1) - 2/s) = 1/(s-1) - 1/s = 1/(s(s-1))`. Assemble everything:

```
    pi^(-s/2) Gamma(s/2) zeta(s)  =  1/(s(s-1))
                                   + integral_1^inf ( x^(s/2 - 1) + x^((1-s)/2 - 1) ) omega(x) dx   (3)
```

We derived (3) assuming `Re s > 1`. Nothing on the right-hand side cares.

---

## 5. Step four: read three theorems off one formula

Stare at (3). Do not compute anything.

**Continuation (THEOREM).** The integral converges for all `s` in **C** and is entire. So the whole
right-hand side is meromorphic on **C** and agrees with the left-hand side on `Re s > 1`. By the
identity theorem the two continuations coincide, so (3) *is* the continuation, a closed form, not an
algorithm. Compare `docs/01`, where Euler–Maclaurin got us the same continuation by a completely
different and far more laborious route.

**Poles (THEOREM).** The only non-analytic ingredient is `1/(s(s-1))`: simple poles at `s = 0` and
`s = 1`, nowhere else. Now split the credit. `Gamma(s/2)` has its own simple poles at
`s = 0, -2, -4, ...`. The pole of the left side at `s = 0` is therefore supplied by `Gamma`, so `zeta`
need not be singular there, and is not. The pole at `s = 1` is *not* supplied by `Gamma`, so it must
belong to `zeta`, and it is simple with residue `1`. (`pi^(-1/2) Gamma(1/2) = 1`, so the residue of
the left side at `s=1` is the residue of `zeta`, and the right side has residue `1` there.) That pole
is the primes' fingerprint, as `docs/01` §1 argues.

**THEOREM (Riemann's functional equation).** Replace `s` by `1-s` throughout (3). Inside the integral,
`x^(s/2-1)` and `x^((1-s)/2-1)` simply swap places, so the integral is unchanged. And
`1/(s(s-1))` is unchanged, because

```
    (1-s)((1-s) - 1)  =  (1-s)(-s)  =  s(s-1)
```

The right-hand side is therefore *identically the same function of `s`*. Hence

```
    pi^(-s/2) Gamma(s/2) zeta(s)  =  pi^(-(1-s)/2) Gamma((1-s)/2) zeta(1-s)
```

No computation was performed. The symmetry is a typographical property of (3), inherited straight
from the `x <-> 1/x` symmetry of the lattice **Z** inside **R**. This is why Riemann's second proof
(the theta proof, 1859) is the one everyone teaches.

---

## 6. The completed zeta function

Multiply through by `s(s-1)` to clear both poles at once, and normalise:

```
    xi(s)  :=  (1/2) s (s-1) pi^(-s/2) Gamma(s/2) zeta(s)
```

**THEOREM.** `xi` is entire, satisfies `xi(s) = xi(1-s)`, and has order 1.

Entirety and the symmetry are immediate from (3), which also gives the completely explicit form

```
    xi(s)  =  1/2  +  (1/2) s(s-1) · integral_1^inf ( x^(s/2-1) + x^((1-s)/2-1) ) omega(x) dx
```

and hence `xi(0) = xi(1) = 1/2` for free. (Numerically `xi(1/2) = 0.497120778188314...`.)

"Order 1" means `|xi(s)| <= exp(C |s|^(1+eps))` for every `eps > 0` and no smaller exponent works;
the true growth along the real axis is `exp(c |s| log|s|)`, driven by `Gamma(s/2)`. So `xi` has order
exactly 1 but *infinite type*, it is not of finite exponential type. That distinction is not
pedantry: it is what forces the convergence factors in §9.

One further consequence, small to state and enormous in practice. `zeta` is real on the real axis, so
Schwarz reflection gives `zeta(conj s) = conj(zeta(s))`, and the same for `xi`. Combine with the
functional equation:

```
    conj( xi(1/2 + i t) )  =  xi(1/2 - i t)  =  xi( 1 - (1/2 - i t) )  =  xi(1/2 + i t)
```

so **`xi(1/2 + it)` is real for real `t`** (verified numerically to 25 digits: the imaginary part at
`t = 1, 5, 30` is below `10^(-26)`). Hunting zeros on the critical line therefore reduces to finding
sign changes of a *real* function of a *real* variable. That is exactly what Hardy's `Z(t)` does; see
`zeta.zeros.Z`, `zeta.zeros.rs_theta`, and `zeta.zeros.zeros_by_sign_change`.

---

## 7. Why the critical line is `Re(s) = 1/2`

Be precise here, because the usual one-liner is slightly off. The map `sigma: s -> 1-s` is rotation by
180 degrees about the point `1/2`. Its only fixed *point* is `s = 1/2`; by itself it does not
distinguish a line. The line appears when you use both of `xi`'s symmetries together. `xi` is
invariant under the group generated by

```
    sigma : s -> 1 - s          (the functional equation)
    kappa : s -> conj(s)        (reality on the real axis)
```

which is a Klein four-group `{ id, sigma, kappa, sigma·kappa }`. The composite
`sigma·kappa : s -> 1 - conj(s)` is a genuine *mirror reflection* of the plane, and its fixed set is
the entire vertical line `Re(s) = 1/2`. That is the exact sense in which the critical line is the
mirror axis of `xi`. (`docs/02` §5 phrases this as "the fixed line of `s -> 1-s`"; the statement is
the same once reality is folded in, but the reflection doing the work is `s -> 1 - conj(s)`.)

**Consequence.** If `rho` is a zero of `xi`, so are `1-rho`, `conj(rho)`, and `1-conj(rho)`. Zeros
come in **quadruples**

```
    { rho,  1 - rho,  conj(rho),  1 - conj(rho) }
```

generically four distinct points forming a rectangle centred at `s = 1/2`, symmetric about both the
critical line and the real axis. The quadruple degenerates to a *pair* `{rho, conj(rho)}` exactly when
`rho` already sits on the mirror, i.e. `Re(rho) = 1/2`.

**CONJECTURE (Riemann Hypothesis, 1859).** Every quadruple degenerates: all non-trivial zeros have
`Re(rho) = 1/2`.

So RH is not "the zeros happen to prefer a line". It is the assertion that the zeros are as symmetric
as the function that produces them, that nothing ever breaks the mirror.

Locating the *strip* is already a theorem. The Euler product gives `zeta(s) != 0` for `Re s > 1`; the
functional equation transports that to `Re s < 0` (where the only zeros are the trivial ones of §8);
and **THEOREM (Hadamard and de la Vallée Poussin, independently, 1896)** `zeta(1 + it) != 0` for real
`t`, which by the functional equation also closes `Re s = 0`. Hence every non-trivial zero lies in
`0 < Re s < 1`. RH asks for the middle of a strip we can already fence.

Counting them is also a theorem, not a conjecture. **THEOREM (Riemann–von Mangoldt).** The number
`N(T)` of zeros with `0 < Im rho < T` satisfies

```
    N(T)  =  (T/2pi) log(T/2pi)  -  T/2pi  +  7/8  +  S(T)  +  O(1/T)
```

with `S(T)` the argument term (typically small, provably unbounded). Sanity check: at `T = 100` the
elementary terms give `29.0023...`, and there are indeed exactly 29 zeros below height 100. Code:
`zeta.zeros.riemann_von_mangoldt`, `zeta.zeros.N_of_T`, `zeta.zeros.S_of_T`, and
`zeta.zeros.verify_rh_up_to`.

---

## 8. Where the trivial zeros come from, and why they are "trivial"

Solve the definition of `xi` for `zeta`:

```
    zeta(s)  =  2 xi(s) pi^(s/2) / ( s (s-1) Gamma(s/2) )
```

`Gamma(s/2)` has simple poles at `s/2 = 0, -1, -2, ...`, i.e. at `s = 0, -2, -4, -6, ...`. A pole of
`Gamma(s/2)` sitting in the *denominator* forces a zero of `zeta`: unless something cancels it. At
`s = 0` the factor `s` in the denominator does cancel it, which is exactly why `zeta(0) = -1/2` is
finite and nonzero. At `s = -2, -4, -6, ...` nothing cancels, so

```
    zeta(-2) = zeta(-4) = zeta(-6) = ... = 0
```

These are the **trivial zeros**. "Trivial" does not mean unimportant, they contribute a genuine term
to the explicit formula in `docs/04-explicit-formula.md`. It means *forced*: they are artifacts of the
archimedean Gamma factor, predictable without knowing anything whatsoever about the primes. Note that
`xi` has none of them; it was constructed precisely to absorb them. The zeros `xi` keeps are the
interesting ones.

---

## 9. The Hadamard product: the bridge to the explicit formula

Because `xi` is entire of order 1, Hadamard's factorisation theorem applies (Hadamard, commonly dated
1893, in the paper where he studied this very function). The Riemann–von Mangoldt count gives
`N(T) ~ (T/2pi) log T`, from which `sum_rho 1/|rho|` **diverges** while `sum_rho 1/|rho|^2`
**converges**. Divergence of the first sum is exactly why a bare product `prod (1 - s/rho)` cannot
converge; convergence of the second says genus-1 elementary factors suffice:

```
    xi(s)  =  e^(A + B s) · prod_rho ( 1 - s/rho ) e^(s/rho)
```

the product taken over all non-trivial zeros (paired as `rho` with `1-rho`, or equivalently `rho` with
`conj(rho)`, so the product converges). The constants are explicit:

```
    e^A = xi(0) = 1/2                    ==>  A = -log 2

    B  =  xi'(0)/xi(0)  =  (1/2) log(4 pi) - 1 - gamma/2  =  -0.023095708966121...
```

with `gamma` the Euler–Mascheroni constant. `B` also equals `-sum_rho Re(1/rho)`. I checked both:
the closed form matches a numerical `xi'(0)/xi(0)` to 17 digits, and `sum_rho Re(1/rho)` over the
first 400 zeros gives `0.021766`, short of `0.023096` by `0.00133`, which is exactly the size the
Riemann–von Mangoldt tail estimate predicts.

Now take the logarithmic derivative of the product, substitute into a contour integral of
`-(zeta'/zeta)(s) · x^s / s`, and out falls the explicit formula relating prime powers to zeros. That
is `docs/04-explicit-formula.md`, implemented in `zeta/explicit.py` (`psi_from_zeros`, `pi_from_zeros`,
`prime_spectrum`, `convergence_table`). The functional equation is what makes the product symmetric;
the product is what makes the primes audible.

---

## 10. An honest caveat: `zeta` satisfies no differential equation

It is tempting to hope that something this structured obeys a nice ODE, the way theta obeys the heat
equation. It does not.

**THEOREM (Hölder, 1887).** `Gamma` satisfies no algebraic differential equation: there is no nonzero
polynomial `P` with `P(z, Gamma(z), Gamma'(z), ..., Gamma^(n)(z)) === 0`. (O. Hölder, *Ueber die
Eigenschaft der Gammafunction keiner algebraischen Differentialgleichung zu genügen*, Mathematische
Annalen 28. Sources differ between 1886 and 1887 for the volume date; 1887 is the usual citation.)

**THEOREM (Ostrowski, 1920).** The same holds for `zeta`, it is *differentially transcendental*
(hypertranscendental) over the rational functions. A. Ostrowski, *Über Dirichletsche Reihen und
algebraische Differentialgleichungen*, Mathematische Zeitschrift 8 (1920). Secondary sources
routinely describe this as settling an assertion of Hilbert's from around 1900 and credit
Mordukhai-Boltovskoi with an independent proof; I have not checked those attribution claims against
primary sources, so treat the *story* as hearsay and the *theorem* as solid.

So there is no hidden finite-order ODE for `zeta` waiting to be integrated. Any structural handle has
to come from somewhere else, the Euler product, the functional equation, or a spectral
interpretation.

**CURIOSITY, clearly labelled, NOT a working tool.** R. A. Van Gorder, *Does the Riemann zeta
function satisfy a differential equation?* (Journal of Number Theory, 2015), gave an elementary
construction of an **infinite-order** linear differential relation with analytic coefficients,

```
    sum_{n >= 0}  a_n(s) · zeta^(n)(s)  =  b(s)
```

which evades Ostrowski because Ostrowski forbids only *finite*-order algebraic relations. Van Gorder
was explicit that his relation was formal and claimed no region or mode of convergence. B. B. Prado
and K. Klinger-Logan, *Linear Operators, the Hurwitz Zeta Function and Dirichlet L-Functions*
(Journal of Number Theory 217 (2020), 422–442), subsequently showed that Van Gorder's operator applied
to `zeta` does **not** converge pointwise at any point of the complex plane, and constructed a
modified operator that does converge. Real mathematics, worth knowing about, but do not build
anything on the original formal operator, and do not cite it as "zeta satisfies a differential
equation" without every one of those qualifications.

**The contrast worth internalising.** Theta, unlike zeta, genuinely does satisfy a clean PDE. This is
the whole content of `docs/02`: with

```
    u(z, x)  =  sum_{n in Z} exp(-pi n^2 x) exp(2 pi i n z),          u(0, x) = theta(x)
```

term-by-term differentiation gives `d/dx` contributing `-pi n^2` and `d^2/dz^2` contributing
`-4 pi^2 n^2`, so

```
    du/dx  =  (1/(4 pi)) · d^2u/dz^2
```

the heat equation on the circle, with a periodic delta comb as initial data at `x -> 0+`. All of
`zeta`'s good behaviour is *borrowed* from theta's heat flow through the Mellin transform (2), and
none of it survives on the `zeta` side as a differential equation. Borrowing it back, running heat
flow *on* `xi` rather than using heat flow to *build* `xi`, is the De Bruijn–Newman story in
`docs/05-de-bruijn-newman.md` and `zeta/heatflow.py`.

---

## 11. Check it yourself

The identity to test is (3): the direct product `pi^(-s/2) Gamma(s/2) zeta(s)` against the
theta-integral right-hand side. `zeta.core.theta_mellin_xi` is the documented entry point, it
computes *both* sides for a given `s`, so you can compare them anywhere you like, including inside
the critical strip and at `Re s < 0` where the left-hand side only exists *because* of the right-hand
side.

Running that comparison at 30-digit precision at `s = 3`, `2 + i`, `0.3 + 5i`, `-1.5 + 2.3i`, and
`1/2 + 14.134725...i`, the two sides agree to within `10^(-31)` in every case. The last is the most
instructive: both sides evaluate to about `2 · 10^(-12)`, the first non-trivial zero announcing
itself in a formula that never mentions zeros at all.

---

## Where to go next

- **`docs/04-explicit-formula.md`**: take `log xi` from §9, differentiate, integrate around a
  contour, and turn the zeros into a Fourier-like series for the prime-counting function. Code:
  `zeta/explicit.py`.
- **`zeta/zeros.py`**: `Z(t)` (real on the critical line, §6), `first_n_zeros`, `N_of_T`, `S_of_T`,
  `gram_points`, `verify_rh_up_to`. This is where §7's quadruples get checked, one zero at a time.
- **`zeta/statistics.py`**: once you have thousands of zeros, stop asking *where* they are and start
  asking how they are *spaced* (Montgomery's pair correlation; the GUE heuristic).
- **`docs/05-de-bruijn-newman.md`** and **`zeta/heatflow.py`**: the De Bruijn–Newman
  deformation of `xi`. RH is equivalent to `Lambda <= 0`; it is a **THEOREM** (Rodgers–Tao, 2020) that
  `Lambda >= 0`, so RH is now precisely the statement `Lambda = 0`: a knife-edge, not a margin.
- **Experiment.** Plot the tail integrand `(x^(s/2-1) + x^((1-s)/2-1)) omega(x)` for `s` on the
  critical line and watch the two terms become complex conjugates. The realness of `xi(1/2 + it)`
  stops being a computation and becomes something you can see.
