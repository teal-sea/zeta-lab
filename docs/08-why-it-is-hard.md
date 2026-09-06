# 08. Why It Is Hard: An Honest Failure Catalogue

## The short version

Every technique in this repository: Mellin transforms, the functional equation, contour integration,
the explicit formula, is genuinely powerful, and every one of them has a known ceiling that sits
*strictly below* the Riemann Hypothesis. We can prove there are no zeros in a region that hugs the
line `Re s = 1` and pinches shut as you go up; we cannot widen it to a fixed strip. We can prove that
a positive proportion, currently a bit over `5/12` of them, lie exactly on the critical line; we
cannot get to all, and the gap between "positive proportion" and "all" is not a matter of pushing
harder. Sieve and elementary methods hit the *parity problem*, which is a theorem about their limits,
not a lack of ingenuity. Numerics are useless as evidence in a way that has been demonstrated
repeatedly, most brutally by the Mertens conjecture. And two families of counterexamples,
Davenport–Heilbronn / Epstein on one side, Beurling generalised primes on the other, show that the
functional equation *alone* cannot imply RH and the Euler product *alone* cannot either. If your
argument uses only one of them, there is a concrete function it also applies to, and that function
has zeros in the wrong place.

That last point is the single most useful fact in this document. Everything else is commentary.

---

## 1. The scoreboard: what transform methods actually deliver

### 1.1 Zero-free regions

**THEOREM (Hadamard, de la Vallée Poussin, 1896).** `zeta(1 + it) != 0` for all real `t`. This gives
the Prime Number Theorem.

**THEOREM (de la Vallée Poussin).** There is `c > 0` such that `zeta(s) != 0` in

```
    sigma  >=  1 - c / log(|t| + 2)
```

**THEOREM (Vinogradov and Korobov, independently, 1958).** The region can be widened to

```
    sigma  >=  1 - c / ( (log|t|)^(2/3) (log log|t|)^(1/3) )
```

The *shape* of this region has not been improved since 1958. Only the constant has moved, the
standard explicit version is due to Ford (2002), commonly quoted with `c = 1/57.54`; check the paper
before relying on that number.

The engine behind all of these is the "3-4-1" inequality `3 + 4 cos(theta) + cos(2 theta) =
2(1 + cos theta)^2 >= 0`, applied to `log zeta(s) = sum_{p,k} p^(-ks)/k`. **That series is the Euler
product.** Remember this; §4 is about what happens without it.

Now look at the scale. RH asks for a zero-free region of *fixed* width `1/2`. What we have is a
region whose width tends to `0`. At `t = 10^12`, `1/log t ≈ 0.036` and the Vinogradov–Korobov width
is `≈ 0.073`. At `t = 10^100` they are `0.0043` and `0.015`. These are not 90% of the way to RH; in
the relevant sense they are 0% of the way, because no amount of improvement to a *shrinking* width
ever produces a *fixed* strip. This is a qualitative wall, not a quantitative one.

### 1.2 Zero-density estimates

Let `N(sigma, T)` count zeros with `Re rho >= sigma` and `0 < Im rho <= T`. RH says
`N(sigma, T) = 0` for every `sigma > 1/2`. The realistic goal is to prove there are *few*.

**THEOREM (Ingham, 1940).** `N(sigma, T) << T^(3(1-sigma)/(2-sigma)) (log T)^5` for `1/2 <= sigma <= 1`.

**CONJECTURE (Density Hypothesis).** `N(sigma, T) << T^(2(1-sigma)+eps)`.

**THEOREM (Guth–Maynard, arXiv:2405.20552, May 2024; I believe it has appeared in the *Annals of
Mathematics*, verify the venue).** `N(sigma, T) <= T^(30(1-sigma)/13 + o(1))` for `3/4 <= sigma <= 1`.
At the critical case `sigma = 3/4` this replaces Ingham's exponent `3/5 = 0.6` with
`15/26 ≈ 0.5769`: the first improvement there since 1940. The advertised arithmetic payoff is
asymptotics for primes in intervals of length `x^(17/30 + o(1))`, improving the previous `x^(7/12)`.

Note what a density estimate *is*: permission for exceptional zeros to exist, provided they are rare.
Even the full Density Hypothesis, far beyond what is known, would not exclude a single off-line
zero. And a single one is fatal for the sharpest applications: if `Theta = sup{Re rho}`, then

```
    psi(x) - x  =  Omega_pm( x^(Theta - eps) )      for every eps > 0
```

so the error term in the Prime Number Theorem is governed by the *supremum* of the real parts, which
one bad zero determines all by itself. `docs/04-explicit-formula.md` and `zeta/explicit.py` show
exactly where this `x^rho` sensitivity enters.

### 1.3 A positive proportion on the line: and why that is not "all"

**THEOREM (Hardy, 1914).** Infinitely many zeros lie on the critical line.

**THEOREM (Hardy–Littlewood, 1921).** At least `cT` of them up to height `T`.

**THEOREM (Selberg, 1942).** A positive proportion of *all* zeros lie on the line.

**THEOREM (Levinson, 1974).** More than `1/3` (about 34.7%).

**THEOREM (Conrey, 1989).** More than `2/5` (the paper's precise proportion is commonly quoted as
just under 41%; check it before citing a decimal).

**THEOREM (Pratt, Robles, Zaharescu, Zeindler; arXiv 2018, published in *Research in the Mathematical
Sciences*: 2019 or 2020 depending on which record you trust).** More than `5/12 ≈ 41.67%`.

Here is the part people misread. `N(T) ~ (T/2pi) log(T/2pi)` grows without bound, so "41.67% are on
the line" leaves *infinitely many* zeros unaccounted for, roughly 58% of an unbounded quantity. Even
a hypothetical theorem giving 99.999% would leave an infinite exceptional set, and by §1.2 the error
term in the PNT is decided by whichever exceptional zero has the largest real part. Proportion
theorems say nothing whatsoever about `Theta`. They are progress on a *different* question.

Why can't the method just be pushed to 100%? Levinson's technique is a mollified second moment: you
multiply `zeta` by a Dirichlet polynomial of length `x = T^theta` chosen to damp its fluctuations,
then count sign changes. The proportion you extract increases with `theta`. Levinson had
`theta < 1/2`; Conrey reached `theta < 4/7` by importing bounds on sums of Kloosterman sums
(Deshouillers–Iwaniec); every subsequent gain has come from new *arithmetic* input of the same kind,
not from better bookkeeping. It is generally stated: I believe the precise result is due to Farmer
in the early 1990s, and you should check the reference before quoting it, that letting
`theta -> infinity` would give 100%. That is exactly the point: `5/12` is a proxy for "how much
cancellation in twisted moments we currently know how to prove", and each increment is a hard theorem
in its own right. There is no visible route by which finitely many such increments reach
`theta = infinity`.

---

## 2. The parity problem

Sieve methods start from an axiom set: a sequence `A`, and estimates for how much of `A` survives
sifting by each prime. **Selberg's parity obstruction** is the fact that these axioms cannot
distinguish integers with an even number of prime factors from those with an odd number. Selberg
exhibited sequences satisfying perfectly good sieve axioms in which *every* surviving element has an
even number of prime factors, so no argument using only those axioms can ever produce a prime.
Bombieri's asymptotic sieve (1976) is the standard formalisation of where the limit sits.

**This is not a side issue for RH; it is central.** RH is *equivalent* to

```
    M(x) = sum_{n <= x} mu(n)  =  O( x^(1/2 + eps) )       for every eps > 0
```

and `mu(n)` on squarefree `n` is exactly `(-1)^(number of prime factors)`. Proving RH by elementary or
sieve-theoretic means requires detecting precisely the cancellation the parity problem says those
methods are blind to. It is why sieves deliver almost-primes (Chen: infinitely many primes `p` with
`p + 2` having at most two prime factors) rather than primes.

Two honest caveats. First, "elementary" does not mean "weak", the Erdős–Selberg elementary proof of
the PNT (1948–49) is a standing rebuke to that idea. Second, parity *can* be broken, but only by
injecting information the axioms do not contain: Friedlander–Iwaniec (Annals, 1998) proved there are
infinitely many primes of the form `a^2 + b^4`, and Heath-Brown (2001) did `x^3 + 2y^3`, both by
supplying bilinear ("Type II") estimates from outside the sieve. The lesson is structural: you get
past parity by adding new arithmetic, never by rearranging the sieve.

---

## 3. Why numerical verification cannot help

### 3.1 What has been checked

**THEOREM (Platt–Trudgian, *Bull. London Math. Soc.* 53 (2021), 792–797).** Every zero with
`0 < Im rho <= 3·10^12` has `Re rho = 1/2`, verified rigorously with interval arithmetic. By the
Riemann–von Mangoldt formula that is about `1.24·10^13` zeros, `zeta.zeros.riemann_von_mangoldt(3e12)`
returns `1.236·10^13` instantly; `N_of_T` computes the exact count, but only at heights your laptop
can actually reach. Gourdon's earlier (2004) computation
reached the first `10^13` zeros, at height about `2.45·10^12`, to a lower standard of rigour.
Odlyzko has computed zeros in windows far higher, around the `10^22`-nd zero.

The verification method is in `zeta/zeros.py` (`verify_rh_up_to`): count the zeros in the strip with
`N(T) = 1 + theta(T)/pi + S(T)`: an identity, not an asymptotic, so it counts off-line zeros too,
count sign changes of Hardy's `Z(t)` on the line, and check the two agree. If they do, every zero
below `T` is simple and on the line.

### 3.2 The relevant quantity crawls

Fluctuations in the zero counting function are carried by `S(T) = (1/pi) arg zeta(1/2 + iT)`.

**THEOREM (Selberg).** `S(T)` is asymptotically normally distributed with variance
`~ (1/(2 pi^2)) log log T`.

`log log` is the slowest function in serious mathematics. At `T = 10^13` the typical size of `S(T)`
is `sqrt( log log T / (2 pi^2) ) ≈ 0.415`. At `T = 10^22` it is `≈ 0.446`. To merely *double* it
relative to height `10^13`, you need `T ≈ 10^(3.5·10^5)`, a number with about 350,000 decimal
digits. Every computation ever performed lives in the first flat inch of a curve that has to climb
forever. (Three lines of mpmath; check it rather than believing me.)

You can already watch a small-scale version of this fail. Gram's law, "the `n`-th zero lies between
consecutive Gram points", holds for the first 125 Gram points and then breaks:
`zeta.zeros.gram_law_violations(0, 200)` returns `[126, 134, 195]`. A pattern with 125 consecutive
confirmations was still false.

### 3.3 Littlewood, Skewes, and the death of numerical intuition

Every computation of `pi(x)` ever performed has found `pi(x) < Li(x)`.

**THEOREM (Littlewood, 1914).** `pi(x) - Li(x)` changes sign infinitely often; more precisely
`pi(x) - Li(x) = Omega_pm( x^(1/2) (log log log x) / log x )`.

So the numerical pattern is *known* to be a lie about the asymptotics, and the first crossover is
grotesque: Skewes bounded it by `e^(e^(e^79))` assuming RH (1933) and by `e^(e^(e^(e^7.705)))`
unconditionally (1955). Modern work locates a crossing region near `1.398·10^316` (Bays–Hudson,
2000, later refined slightly by Chao–Plymen and by Demichel), still hopelessly beyond computation,
and not proved to be the *first* crossing. Compare `zeta.explicit.li` and `zeta.explicit.pi_true`:
you can see the bias in the data, and the bias is not the truth.

### 3.4 Mertens: an overwhelming numerical pattern that was simply false

The Mertens conjecture `|M(x)| < sqrt(x)` was proposed on strong numerical evidence and would have
implied RH (and the simplicity of the zeros).

**THEOREM (Odlyzko–te Riele, *J. reine angew. Math.* 357 (1985), 138–160).** It is false. The proof
is non-constructive, no explicit counterexample is known to this day. Explicit upper bounds for the
first counterexample have been pushed down to roughly `exp(1.59·10^40)` (commonly attributed to
Kotnik–te Riele, 2006).

This is the cleanest available warning. A statement *stronger* than RH, supported by everything
anyone could compute, was wrong, and wrong at a scale no computation will ever reach.

---

## 4. The counterexamples that should govern your intuition

### 4.1 Functional equation alone: Davenport–Heilbronn

**THEOREM (Davenport–Heilbronn, "On the zeros of certain Dirichlet series", *J. London Math. Soc.* 11
(1936), two papers).** There is an explicit Dirichlet series, a particular linear combination of two
Dirichlet L-functions mod 5, with coefficients chosen so the phases in the functional equation cancel,
which:

- continues analytically to the whole plane,
- satisfies a Riemann-type functional equation relating `s` and `1 - s` with the same gamma factors,
- has periodic, perfectly explicit coefficients,
- has **infinitely many zeros on the critical line**,
- and **also has zeros off the critical line, including zeros in the half-plane `Re s > 1`.**

Bombieri–Ghosh, "Around the Davenport–Heilbronn function" (*Russian Math. Surveys* 66 (2011)) study
it in depth: a positive proportion of its zeros lie on the line, and RH is still false for it.

The one thing it lacks is an **Euler product**.

**Therefore: any proposed proof of RH that uses only the functional equation, the order of growth,
the reality of `xi(1/2 + it)`, the Hadamard product, or the symmetry `rho -> 1 - rho` of the zero set,
is wrong.** All of those hold for the Davenport–Heilbronn function. This is the fastest available
test of a proposed proof, and it kills the large majority of them. If you cannot point at the step
where your argument would break for Davenport–Heilbronn, you have not proved anything.
`docs/03-functional-equation.md` derives, carefully and at length, exactly the structure that is
*not* enough.

The same lesson arrives independently from **Epstein zeta functions**. For a positive definite binary
quadratic form `Q`, the series `zeta(s, Q) = sum' Q(m,n)^(-s)` satisfies a clean Riemann-type
functional equation. When the class number of the discriminant is `1`, `zeta(s, Q)` factors as `zeta`
times an L-function, it inherits an Euler product, and it behaves. When the class number exceeds
`1`, Davenport and Heilbronn proved it has infinitely many zeros in `Re s > 1`. The functional
equation is the same in both cases; the arithmetic is not.

### 4.2 Euler product alone: Beurling generalised primes

Now run the experiment the other way. A **Beurling system** is an arbitrary sequence
`1 < p_1 <= p_2 <= ...` of "generalised primes" together with the multiplicative semigroup of
"generalised integers" they generate, with counting function `N_B(x)`. Its zeta function has an Euler
product *by construction*. What it does not have is the specific arithmetic of `Z`, in particular,
no functional equation.

**THEOREM (Diamond–Montgomery–Vorhauer, "Beurling primes with large oscillation", *Math. Ann.* 334
(2006), 1–36).** There is a Beurling system with `N_B(x) = kappa·x + O(x^theta)`, generalised
integers as regularly distributed as you could reasonably ask for, whose zeta function has
infinitely many zeros on the curve `sigma = 1 - a/log t`, and whose prime counting function
oscillates: `pi_B(x) = li(x) + Omega( x exp(-c sqrt(log x)) )`.

Read that carefully. With an Euler product and PNT-quality regularity of the integers but nothing
else, the classical de la Vallée Poussin zero-free region is **optimal**, not merely unimproved.
So the Euler product by itself cannot even deliver Vinogradov–Korobov, let alone RH.

### 4.3 The two-sided test

Put §4.1 and §4.2 together and you get a filter that costs nothing to apply:

```
    uses the functional equation only     ->  Davenport-Heilbronn / Epstein refute it
    uses the Euler product only           ->  Beurling systems refute it
    must use BOTH, entangled              ->  the actual difficulty
```

No known technique entangles them at RH strength. That, stated plainly, is why the problem is open.

---

## 5. The graveyard, stated respectfully

Claimed proofs of RH appear at a rate of dozens per year on arXiv and elsewhere; Matthew Watkins has
long maintained a public catalogue of proposed proofs and disproofs. The overwhelming majority fail
the §4.3 test within the first paragraph.

Serious mathematicians are not exempt. Louis de Branges, who proved the Bieberbach conjecture in
1984, a first-rate theorem, has announced approaches to RH repeatedly over several decades. Conrey
and Li ("A note on some positivity conditions related to zeta- and L-functions", *IMRN* 2000) gave
examples showing that the positivity conditions his method requires are not satisfied in the setting
relevant to `zeta`. De Branges has disputed the relevance
of those examples; as of this writing no proof along those lines has been accepted. Michael Atiyah
presented a claimed proof at the Heidelberg Laureate Forum in September 2018; it was not accepted by
the community.

None of this warrants mockery. It warrants internalising what specialists say a proof must contain.
Conrey's survey "The Riemann Hypothesis" (*Notices of the AMS*, March 2003) is the best short
statement of the state of play, and it is explicit that any successful method must be sensitive to
the Euler product, precisely because of Davenport–Heilbronn. Bombieri's official Clay Mathematics
Institute problem description makes the same structural point. Read both before writing anything.

---

## 6. If you want to work on this: what is actually tractable

Genuinely open, genuinely approachable, roughly ordered by how fast a non-specialist can start:

1. **Rigorous verification and explicit constants.** Interval-arithmetic zero verification
   (Platt–Trudgian style) and explicit versions of classical estimates feed directly into real
   theorems: Helfgott's proof of the ternary Goldbach conjecture (2013) relies on verified zero
   computations for Dirichlet L-functions. Unglamorous, permanently useful. Start from
   `zeta/zeros.py`.

2. **Statistics of zeros.** Montgomery's pair correlation (1973) and Odlyzko's numerics support the
   GUE **CONJECTURE**; nearly everything here is open and the numerical side is accessible.
   `docs/06-hilbert-polya-and-gue.md` and `zeta/statistics.py`.

3. **The de Bruijn–Newman constant.** `Lambda <= 1/2` (de Bruijn, 1950); `Lambda >= 0` is a
   **THEOREM** (Rodgers–Tao; announced 2018, published 2020), so RH is now exactly `Lambda = 0`.
   **Polymath15** (2018) drove the upper bound to `Lambda <= 0.22`, sharpened to `Lambda <= 0.2` by
   Platt–Trudgian (2021), see `docs/05` §3 for both, and note neither is strict. Polymath15 was a
   real, open, collaborative
   project in which a competent programmer could and did contribute compute and code. See
   `docs/05-de-bruijn-newman.md` and `zeta/heatflow.py`.

4. **The Guth–Maynard large-values method (2024).** New, actively being extended, and its analogues
   for Dirichlet L-functions and other families are open. The liveliest technical frontier on the
   density side.

5. **Moments of zeta.** The second (Hardy–Littlewood, 1918) and fourth (Ingham, 1926) moments are
   **THEOREM**s; the Keating–Snaith random-matrix **CONJECTURE** (2000) and the CFKRS refinement
   (2005) predict all of them. Sharp upper bounds under RH (Soundararajan, 2009; sharpened by Harper)
   and unconditional lower bounds (Radziwiłł–Soundararajan) exist. The sixth moment is open.

6. **Function-field analogues.** RH for curves over finite fields is a **THEOREM** (Weil, 1948;
   Deligne, 1974 for the general Weil conjectures). Its proof uses positivity from intersection
   theory with no known number-field counterpart; understanding exactly *why* it does not transfer is
   a research programme in itself. Katz–Sarnak (1999) established the random-matrix symmetry
   predictions in that setting.

7. **L-function analogues.** Test any idea against Dirichlet L-functions, modular L-functions, the
   Selberg class. If a phenomenon is about `zeta` specifically and not about the whole family, that
   is information, and if it is about the whole family, §4.1 is waiting for you.

8. **Computable equivalences.** The Nyman–Beurling criterion, and Báez-Duarte's reformulation,
   express RH as a Hilbert-space distance that can be approximated numerically. Neither has produced
   a proof, but both are concrete and programmable, `docs/07-equivalences-and-criteria.md` §5 states
   them precisely and works out, from the conjectured `C/log N` asymptotic, why the numerics are
   hopeless (no `d_N` computation is implemented in this repo; doing one and watching it refuse to
   converge is a suggested experiment there).

---

## Where to go next

- **`docs/04-explicit-formula.md`**: the mechanism by which one off-line zero would poison the prime
  count. Everything in §1.2 lives there; code in `zeta/explicit.py`.
- **`docs/03-functional-equation.md`**: reread §4.1 next to it. That doc derives precisely the
  structure Davenport–Heilbronn also has, and therefore precisely the structure that cannot suffice.
- **`docs/05-de-bruijn-newman.md`** and **`zeta/heatflow.py`**: the `Lambda = 0` knife-edge,
  and the most contributable open problem in this document.
- **`zeta/zeros.py`**: run `verify_rh_up_to` yourself, then compute how far you would have to go for
  the result to constitute evidence. By §3.2 the answer is: further than you can go.
- **Conrey, "The Riemann Hypothesis", *Notices of the AMS*, March 2003**: if you read one external
  source, read that one.
