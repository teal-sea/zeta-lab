# 07. Equivalences and Criteria

*A curated catalogue of statements exactly equivalent to RH, with honest notes on which ones have
ever gone anywhere.*

## The short version

The Riemann Hypothesis has an unusually large number of exactly equivalent reformulations, and they
look nothing like each other: an error bound on prime counting, a growth bound on a sum of Möbius
values, a positivity condition on a sequence of numbers, a least-squares approximation problem in
`L^2(0,1)`, an inequality about the sum of divisors of an integer, and the statement that a certain
heat flow has already run exactly to its critical time. Each is a **THEOREM** of the form "RH ⟺ X",
proved and published. None of them is easier than RH. That is the whole lesson of this document: an
equivalence is a *translation*, not a *reduction*, it relocates the difficulty without shrinking it,
and in every case below you can point at exactly where the difficulty went. A small number of these
criteria have nevertheless been genuinely productive (the error-term version, Speiser's theorem, de
Bruijn–Newman); most, including the famous elementary-looking ones, have produced no partial progress
whatsoever, and I say so where that is the case.

*Notation.* `rho = beta + i*gamma` runs over non-trivial zeros; `Theta = sup(beta)`; RH is
`Theta = 1/2`. `mu` is Möbius, `sigma(n)` the sum of divisors, `Lambda(n)` von Mangoldt (as in
`docs/04-explicit-formula.md`). The de Bruijn–Newman constant is written `Lambda_dBN` here to avoid
the clash; `docs/05-de-bruijn-newman.md` calls it simply `Lambda`.

---

## 0. Ground rules

Two words are used with force throughout. **THEOREM** means proved and published. **CONJECTURE** means
believed and unproved. Anything labelled **HEURISTIC** is a plausibility argument, not a proof.

Note also that "equivalent to RH" cuts both ways. If X ⟺ RH, then *disproving* X disproves RH. Nobody
has managed that either. The one instructive near-miss on this list is the Mertens conjecture, which
was a *strengthening* of an equivalence, and which turned out to be false, a standing warning that
intuition about the size of these objects is unreliable.

---

## 1. The error term in `pi(x)` and `psi(x)`: the original

**THEOREM (von Koch, 1901).**

```
    RH   <=>   pi(x)  = li(x) + O( sqrt(x) log x )
         <=>   psi(x) = x     + O( sqrt(x) (log x)^2 )
```

The mechanism is derived in `docs/04-explicit-formula.md` §6 and will not be repeated: each zero
contributes a wave of amplitude `x^beta / |rho|` to `psi(x)`, so the real part of a zero is literally
an exponent on `x`. Three cautions people get wrong:

- The bound is genuinely `epsilon`-free, `O(sqrt(x) log^2 x)`, not `O(x^{1/2+eps})`. Schoenfeld (1976)
  made the constants explicit: under RH, `|psi(x) - x| < sqrt(x) log^2(x) / (8 pi)` for `x >= 73.2`
  and `|pi(x) - li(x)| < sqrt(x) log(x) / (8 pi)` for `x >= 2657`. I am confident in the shape and the
  constant `1/(8 pi)`; check the thresholds against the paper before quoting them. (Sanity check at
  `x = 10^6`: the `pi` bound gives about 550, and the actual `li(10^6) - pi(10^6)` is about 130.)
- RH is **not** equivalent to `pi(x) < li(x)`. That statement is **FALSE**: Littlewood (1914) proved
  the difference changes sign infinitely often, despite being negative for every `x` ever computed.
  See `docs/08-why-it-is-hard.md` §3.3.
- The equivalence is two-way: `psi(x) - x` is both `O(x^{Theta+eps})` and `Omega(x^{Theta-eps})`. The
  error is *exactly* of size `x^Theta`, no more and no less.

**Productive?** Yes, by far the most productive item on the list. It is why "assume RH" appears in
thousands of papers: it converts directly into effective bounds on almost every prime-counting
quantity, and those conditional results are real mathematics. It has never suggested a route to
*proving* RH.

---

## 2. The Mertens function `M(x)`: and the conjecture that was false

Let `M(x) = sum_{n <= x} mu(n)`. The bridge to `zeta` is one partial summation:

```
    1/zeta(s)  =  s * integral_1^inf  M(x) * x^(-s-1) dx        (Re s > 1)
```

That integral converges, and so defines an analytic function, precisely as far left as `M(x)` is
small. A growth bound on `M` is therefore a zero-free region for `zeta`, zeros of `zeta` are poles
of `1/zeta`, and conversely.

**THEOREM.** For `1/2 <= theta < 1`: `M(x) = O(x^{theta+eps})` for every `eps > 0` if and only if
`zeta` has no zeros with `Re s > theta`. In particular

```
    RH   <=>   M(x) = O( x^(1/2 + eps) )    for every eps > 0
```

**Now the trap.** The *Mertens conjecture* asserted the clean `epsilon`-free bound

```
    |M(x)| < sqrt(x)     for all x > 1                         [FALSE]
```

Stieltjes claimed in 1885 to have a proof of the weaker `M(x) = O(sqrt(x))` but never produced one;
Mertens stated the strong form in 1897 on numerical evidence. It would have implied RH *and* the
simplicity of every zero.

**THEOREM (Odlyzko and te Riele, 1985, "Disproof of the Mertens conjecture").** The Mertens conjecture
is false. They showed `limsup M(x)/sqrt(x) > 1.06` and `liminf M(x)/sqrt(x) < -1.009` (these are the
values usually quoted; Kotnik and te Riele later pushed both past 1.2 in absolute value: I am hedging
on those improved constants). The proof is **non-constructive**: take a few thousand zeros to high
precision, treat `M(x)/sqrt(x)` via the explicit formula as an almost-periodic sum of waves
`cos(gamma * log x + phase)`, and use lattice basis reduction to locate a `log x` at which enough
waves align. No explicit counterexample is known and the bounds on the first one are astronomical.

Sit with this. Sieving up to `x = 10^6` I get `max M(x)/sqrt(x) = 1.0` (at `x = 1`) and
`min M(x)/sqrt(x) = -0.894` (at `x = 5`), with `M(10^6) = 212`. The numerical evidence was
overwhelming and the conjecture was wrong. `docs/08-why-it-is-hard.md` §3.4 develops this as the
cautionary tale it is. Note carefully, though, that RH itself survived the disproof untouched, only
the over-strong strengthening died.

**Still open:** whether `M(x) = O(sqrt(x))` holds without the `epsilon`. That would imply RH plus
simple zeros. It is widely believed **false**; work of Ng and others suggests, under a
linear-independence hypothesis on the `gamma`, that `M(x)/sqrt(x)` is unbounded. That is a
**CONJECTURE** and I am hedging on its precise form.

**Productive?** Not as an attack route. `mu(n)` is hard to control precisely *because* RH is what
controls it; the implication runs the wrong way for progress.

---

## 3. Riesz and Hardy–Littlewood: the same idea, smoothed

**THEOREM (M. Riesz, 1916).** Define the *Riesz function*

```
    Riesz(x)  =  sum_{k >= 1}  (-1)^(k+1) * x^k / ( (k-1)! * zeta(2k) )
```

Then `RH  <=>  Riesz(x) = O(x^(1/4 + eps))` for every `eps > 0`.

**THEOREM (Hardy and Littlewood, 1918, *Acta Mathematica* 41, as it is usually stated; verify the
exact form against the paper).**

```
    RH   <=>   sum_{k >= 1} (-x)^k / ( k! * zeta(2k+1) )  =  O( x^(-1/4) )    as x -> inf
```

These are §2 in disguise, and the disguise comes off in two lines. Expand
`1/zeta(2k) = sum_n mu(n) n^(-2k)`, swap the order of summation, and use
`sum_{k>=1} (-1)^(k+1) y^k/(k-1)! = y * exp(-y)`:

```
    Riesz(x)  =  sum_{n >= 1}  mu(n) * (x/n^2) * exp(-x/n^2)
```

and the Hardy–Littlewood series collapses the same way to `sum_n (mu(n)/n) * (exp(-x/n^2) - 1)`. I
checked both identities numerically: the Riesz power series and its Möbius form agree to 7–8 digits at
`x = 1, 10, 100` (limited by my truncation of the Möbius sum), and the Hardy–Littlewood pair agrees to
10 digits at `x = 1, 10, 50`. So these criteria are the Mertens criterion with a Gaussian-type
smoothing, and the smoothing is what buys the clean exponent `1/4`, which is `sqrt` of `sqrt(x)`
because the natural variable is `n^2`.

Values: `Riesz(1) = 0.0439818`, `Riesz(10) = -0.7806756`, `Riesz(100) = -0.1519372`.

**Productive?** No, and the reason is worth seeing concretely. Evaluating `Riesz(x)` from its defining
series is a cancellation catastrophe: at `x = 100` the largest single term is about `10^44` while the
sum is `-0.152`, so roughly 45 decimal digits cancel, and that count grows linearly in `x`. Any
numerical probe of the `x^{1/4}` growth needs working precision proportional to `x`, so the asymptotic
regime is unreachable in practice. Exactly true, computationally inert.

---

## 4. Li's criterion: positivity of a sequence

**THEOREM (Xian-Jin Li, 1997).** Define, for `n >= 1`,

```
    lambda_n  =  (1/(n-1)!) * d^n/ds^n [ s^(n-1) * log xi(s) ]  evaluated at s = 1
              =  sum_rho [ 1 - (1 - 1/rho)^n ]        (zeros paired rho <-> 1-rho)
```

Then `RH  <=>  lambda_n >= 0 for every n >= 1`.

*Why.* The Möbius map `s -> w = 1 - 1/s` sends the half-plane `Re s > 1/2` onto the open unit disk and
the critical line onto the unit circle (check: `s = 1 -> w = 0`, `s = 1/2 -> w = -1`). Since zeros come
in pairs `rho, 1-rho`, RH says every `w_rho` lies *on* the circle, rather than one strictly inside and
its partner strictly outside. Now `lambda_n = sum_rho (1 - w_rho^n)`, and if some zero is off the line
its `w` has `|w| > 1`, so the term `-Re(w^n)` oscillates with *exponentially growing* amplitude --
the delicate part of the proof is showing it cannot be forever cancelled by the infinitely many other
terms, i.e. that some `lambda_n` really does go negative. Bombieri and Lagarias (1999) distilled
exactly this into a clean statement about arbitrary multisets of complex numbers, with no zeta in it.

Checks I ran. There is a closed form for the first coefficient:

```
    lambda_1  =  1 + gamma/2 - log(4 pi)/2  =  0.0230957089661...
```

Under RH, `sum_rho 1/|rho|^2 = sum_rho 1/(rho(1-rho)) = 2*lambda_1 = 2 + gamma - log(4 pi)`. Summing
`2/(1/4 + gamma^2)` over the first 1000 zeros gives `0.0447523`; the crude density-based tail estimate
adds `0.0014397`, for `0.0461920` against the exact `0.0461914...`, agreement to about `6e-7`.
Truncated sums for `lambda_1 ... lambda_4` over those 1000 zeros are `0.0224, 0.0895, 0.201, 0.357`:
all positive, increasing, and all slight *under*estimates since the omitted tails are positive.

**Productive?** No, and the shape of the trouble is visible in the numbers. `lambda_1 = 0.023` is
*barely* positive, and it is positive only through a delicate near-cancellation between `gamma` and
`log(4 pi)`. Worse, evaluating `lambda_n` requires either the zeros themselves, in which case you have
assumed what you wanted to prove, or an arithmetic expression involving prime sums whose individual
terms grow. Under RH one expects `lambda_n` to grow like `(n/2) log n`; nobody can prove
non-negativity unconditionally for large `n`.

**How weak a detector is it?** Measurable, and the answer is discouraging. The Davenport–Heilbronn
function `F` has the same shape (`F(s) = F(1-s)`, real coefficients, real Hardy-style `Z`) and a zero
provably off the line, so some `lambda_n` for `F` must *eventually* go negative, note this leans on
the Bombieri–Lagarias multiset statement above rather than on Li's original, since `F` has no Euler
product and is outside the Selberg class, and the multiset form needs neither. Running
the same contour extraction on `F`, validated first against `zeta.li.li_coefficients` on `xi`, where
it agrees bit-identically, gives `lambda_n > 0` for every `n <= 24`, in fact uniformly *larger* than
zeta's. The reason is in the off-line zero itself: with
`rho = 0.80851718... + 85.69934848...i`, the mirror zero `1 - rho` has `Re < 1/2` and
`|1 - 1/(1-rho)| = 1.00004200616...`, so the exponentially growing term grows at rate `4.2e-5` per
step and needs `n ~ 2.4e4` merely to double, against a background growing like `(n/2) log n`.
So observing `lambda_n >= 0` for zeta over any comparable range distinguishes nothing: a function
that violates RH passes the identical test. This sharpens §11's "the equivalences restate rather than
reduce" into a quantitative statement about one of them. `scripts/18_dh_li_coefficients.py`.

---

## 5. Nyman–Beurling, and Báez-Duarte's strengthening

This is the criterion that comes closest to being a *finite* problem.

Write `{y}` for the fractional part, and define on `(0,1)`, for `0 < theta <= 1`:

```
    rho_theta(x)  =  { theta / x }
```

**THEOREM (Nyman, 1950; Beurling, 1955).** RH holds if and only if the constant function `1` lies in
the closed linear span of `{ rho_theta : 0 < theta <= 1 }` inside `L^2(0,1)`. Beurling proved the
`L^p` refinement: `zeta` has no zeros in `Re s > 1/p` if and only if that span is dense in `L^p(0,1)`.

*Why.* Take Mellin transforms along `Re s = 1/2`. The transform of `rho_theta` is essentially
`-theta^s * zeta(s)/s`, and the transform of the constant `1` is `1/s`. So approximating `1` by a
combination `sum_k c_k * rho_{theta_k}` amounts to finding a Dirichlet-polynomial-like `D(s)` with
`zeta(s) D(s) ≈ 1` in mean square on the critical line, that is, **`1/zeta` is approximable by
Dirichlet polynomials on the critical line**. If `zeta` had a zero at `beta > 1/2`, then `1/zeta` has
a pole strictly inside the relevant half-plane and no such approximation can exist. That is the whole
content, and it is a clean statement: RH ⟺ `1/zeta` is reachable from the right.

**THEOREM (Báez-Duarte, 2003).** You only need `theta = 1/k` for positive integers `k`. Define

```
    d_N^2  =  inf over c_1,...,c_N  of  || 1 - sum_{k=1}^N c_k * rho_{1/k} ||^2  in L^2(0,1)
```

Then `d_N` is non-increasing (extra basis vectors can only help), and

```
    RH   <=>   d_N -> 0   as N -> infinity
```

So RH becomes: *does this explicitly computable, monotonically decreasing sequence of least-squares
residuals tend to zero?* The Gram matrix entries are elementary integrals; not a single zero appears.

**CONJECTURE (Báez-Duarte, Balazard, Landreau and Saias, around 2000).**

```
    d_N^2  ~  C / log N       with     C = sum_rho 1/|rho|^2
```

and under RH that constant is `2 + gamma - log(4 pi) = 0.0461914...`, the same number verified in §4.
I believe they also proved a matching lower bound of this shape; hedge on the exact statement.

**Productive?** Structurally beautiful, computationally hopeless, and it is worth being precise about
why. If `d_N^2 ≈ 0.0462/log N`, then at `N = 100` you have `d_N ≈ 0.10`, nowhere near zero, and to
reach `d_N^2 = 0.001` you would need `log N ≈ 46`, i.e. `N ≈ 10^20`. No finite computation can
distinguish "tends to 0 like `1/log N`" from "tends to a small positive limit". On top of that the
Gram matrix is severely ill-conditioned, so the least-squares problem itself resists high-precision
solution. This is the sharpest illustration of the theme of this document: exactly equivalent to RH,
and it tells you nothing you can act on.

---

## 6. Robin, Lagarias, Nicolas: RH as an inequality about divisors

Unconditional background: **THEOREM (Gronwall, 1913).**
`limsup_n sigma(n)/(n log log n) = e^gamma = 1.7810724...`. So `e^gamma` is exactly the right constant
and the only question is whether the `limsup` is ever *exceeded*.

**THEOREM (Robin, 1984).**

```
    RH   <=>   sigma(n)  <  e^gamma * n * log log n      for every n > 5040
```

I computed the failures directly. For `3 <= n <= 20000` the inequality fails at exactly

```
    3, 4, 5, 6, 8, 9, 10, 12, 16, 18, 20, 24, 30, 36, 48, 60, 72, 84,
    120, 180, 240, 360, 720, 840, 2520, 5040
```

- 26 values, largest 5040 (plus degenerate `n = 1, 2`, where `log log n` is not positive). The margin
at the top is thin: `sigma(5040) = 19344` against `e^gamma * 5040 * log log 5040 = 19237.06`, a ratio
of `1.00556`. Robin also proved the unconditional companion
`sigma(n) <= n log log n * (e^gamma + 0.6483/(log log n)^2)` for `n >= 3`: I am confident in the
shape, and treat `0.6483` as "commonly cited", and that if RH is false there are infinitely many
counterexamples, occurring among the *superabundant* numbers.

**THEOREM (Lagarias, 2002, Amer. Math. Monthly, "An elementary problem equivalent to the Riemann
hypothesis").** With `H_n = 1 + 1/2 + ... + 1/n`,

```
    RH   <=>   sigma(n)  <=  H_n + exp(H_n) * log(H_n)     for all n >= 1
```

with equality only at `n = 1`. Verified: at `n = 1` both sides are exactly 1; at `n = 5040`,
`19344` against `19836.32`; at `n = 55440`, `232128` against `241179.92`.

This is Robin in elementary clothing, and the disguise comes off cleanly: `H_n = log n + gamma + O(1/n)`,
so `exp(H_n) ≈ e^gamma * n` and `log H_n ≈ log log n`. The extra `H_n` term plus the lower-order
corrections supply exactly enough slack to absorb all 26 exceptional values, which is why Lagarias'
form needs no "`n > 5040`" clause at all. That is a genuinely elegant piece of bookkeeping.

Related: **Nicolas (1983, I believe, verify the date)** proved RH equivalent to
`N_k/phi(N_k) > e^gamma * log log N_k` for every primorial `N_k = 2*3*5*...*p_k`. I checked this for
the first 17 primorials and the gap widens steadily (at `p_k = 59`: `7.4749` versus `6.9319`).

**Productive?** No, and this is the most *misleading* family on the list. These statements are
elementary to state and are routinely presented as "RH for people who don't know complex analysis".
But the proof of each equivalence runs through the explicit formula and the distribution of primes;
the elementary appearance is entirely cosmetic, and nothing about the extremal behaviour of `sigma`
is tractable by elementary means at the required precision. Be suspicious of anyone claiming an
elementary attack from this direction.

---

## 7. Weil positivity: the one with a proof in a parallel universe

Take the explicit formula of `docs/04-explicit-formula.md` in its symmetric distributional form. For a
suitable even test function `h` with Fourier transform `g`, it reads schematically

```
    sum_rho h(gamma_rho)  =  (archimedean/Gamma terms)  +  (pole terms)
                             -  2 * sum_{n >= 2} (Lambda(n)/sqrt(n)) * g(log n)
```

where `rho = 1/2 + i*gamma_rho`, so `gamma_rho` is **real exactly when `rho` lies on the critical
line**.

**THEOREM (Weil, 1952; refined 1972).** RH holds if and only if the functional
`W(h) = sum_rho h(gamma_rho)` is `>= 0` for every `h` of positive-definite type, every `h` arising as
a self-convolution `g * g~` of a nice test function.

*Why it is a criterion.* If all `gamma_rho` are real and `h >= 0` on the real line, the sum is
non-negative automatically. If some zero is off the line its `gamma_rho` is genuinely complex, `h`
extends to the complex plane, and one can engineer an `h` making that term very negative, off-line
zeros come in quadruples (`docs/03-functional-equation.md`), and the pair off the real `gamma`-axis
can be made to dominate.

*Why people care.* Weil **proved** the exact analogue for curves over finite fields (announced 1940,
full proof 1948), where the positivity is not analysis at all but the Castelnuovo–Severi / Hodge index
inequality for intersection numbers on the surface `C x C`. This is the only criterion here with a
complete proof in a genuinely parallel setting, by genuinely geometric means. Connes (1999) recast it
as a trace formula on a space of adele classes. Both stories are told properly in
`docs/06-hilbert-polya-and-gue.md` (§4 Connes, §6 function fields), including a precise account of
what is missing over `Spec Z`.

**Productive?** The most structurally suggestive item on this list, and the origin of essentially all
geometric programmes. Also the least checkable: `W(h) >= 0` admits no meaningful numerical test, and
the missing ingredient, an arithmetic surface playing the role of `C x C`, has resisted decades.
High explanatory value, zero computational value, no proof.

**Detector Power and the Gaussian/Fejér Gap.** If Weil's criterion is viewed computationally as a detector for off-line zeros, its sensitivity depends entirely on the choice of the test-function family `h`. The gap in sensitivity between admissible choices spans thousands of orders of magnitude. For the Gaussian family `h(r) = exp(-a r^2)`, an off-line zero at height `T` with shift `delta` produces a maximal negative dip bounded by `4 * exp(-pi(T^2 - delta^2)/(2T delta))`. At the height of `gamma_1 = 14.13` and `delta=0.01`, the Gaussian dip is `10^{-964}`, the detector is completely blind. In contrast, band-limited test functions like the Fejér kernel are exponentially sensitive to off-line zeros (growing as `exp(2b*delta)` off the real line by the Paley-Wiener theorem). Detector power is a property of the test-function family, not the Weil criterion itself. This is computationally demonstrated in `scripts/24_detector_power.py`.

---

## 8. Speiser's theorem: the one that actually worked

**THEOREM (Speiser; the paper is in Mathematische Annalen 110, cited variously as 1934 and 1935).**

```
    RH   <=>   zeta'(s) has no zeros in the strip  0 < Re(s) < 1/2
```

*Why, roughly.* The functional equation makes `zeta` in the left half-strip a reflected copy of `zeta`
in the right half-strip times an explicit analytic factor. Differentiating and running an
argument-principle / Rolle-type count, a zero of `zeta` strictly right of the critical line forces a
zero of `zeta'` strictly left of it. Levinson and Montgomery (1974) proved the quantitative form: up
to height `T`, the number of zeros of `zeta'` in the left half-strip `0 < Re s < 1/2` and the number
of zeros of `zeta` in that same half-strip agree to within `O(log T)`. (By the functional equation,
zeros of `zeta` off the line come in pairs mirrored across it, so the left half-strip holds exactly
half of the off-line zeros; both counts are zero precisely under RH.)

Numerically, the two zeros of `zeta'` of smallest positive imaginary part:

```
    zeta'(s) = 0   at   s = 2.4631619 + 23.29832 i
                   and  s = 1.2864968 + 31.70825 i
```

both comfortably right of `Re s = 1/2`, as RH requires. (`zeta'` also has real zeros in the left
half-plane, interleaved with the trivial zeros of `zeta`: `s = -2.7172628...`, `s = -4.9367621...`.)

**Productive? YES, uniquely so on this list.** Speiser's theorem is the engine of *Levinson's
method*: zeros of `zeta'` are easier to count than zeros of `zeta`, and Levinson (1974) used this to
prove that more than one third of the non-trivial zeros lie on the critical line, later improved by
Conrey (1989) to more than `2/5`, and further since. See `docs/08-why-it-is-hard.md` §1.3 for the
current record and, importantly, for why a positive proportion is progress on a *different* question
than `Theta = 1/2`. Still: no other criterion in this document has yielded an unconditional
quantitative theorem about the zeros. If you want a worked example of an equivalence that *paid*,
this is it.

---

## 9. De Bruijn–Newman: RH with no margin

Developed in full in `docs/05-de-bruijn-newman.md`; the statement belongs in this catalogue.

Deform `xi` by a heat flow in a time parameter `t`, producing a family `H_t` with `H_0` equal, up to
normalisation, to `Xi`.

**THEOREM (de Bruijn, 1950; Newman, 1976).** There is a finite real constant `Lambda_dBN` such that
`H_t` has only real zeros exactly when `t >= Lambda_dBN`. Hence `RH <=> Lambda_dBN <= 0`.

**THEOREM (de Bruijn, 1950).** `Lambda_dBN <= 1/2`; since improved: Polymath15 (2018-19) proved
`<= 0.22`, and `docs/05` notes a commonly-cited further refinement to `<= 0.2`.

**THEOREM (Rodgers and Tao; arXiv 2018, journal version around 2020).** `Lambda_dBN >= 0`: Newman's
conjecture, whose motivating slogan was that RH, if true, is only barely so.

Together: `RH <=> Lambda_dBN = 0` exactly. This is the most philosophically loaded equivalence here.
It says RH is not merely true-or-false but *marginally* true if true at all, so any argument carrying
slack, any inequality with a constant to spare, is provably incapable of proving RH. It also explains,
retroactively, the thin margins you keep meeting elsewhere in this document: Robin's `0.56%` at
`n = 5040`, `lambda_1 = 0.023`, the `1/log N` decay in Báez-Duarte.

**Productive?** Yes, in the specific sense that Rodgers–Tao is a hard *unconditional* theorem obtained
by working on this side of the equivalence. Code: `zeta/heatflow.py`.

---

## 10. Others, briefly (and hedged)

- **Franel and Landau (1924).** Let `a_1 < ... < a_m` be the Farey fractions of order `n`. RH ⟺
  `sum_v |a_v - v/m| = O(n^{1/2+eps})`: a statement purely about how evenly the Farey sequence is
  spread. I am confident in the attribution and the shape; check the exponent convention.
- **Redheffer's matrix.** Let `A_n` be the `n x n` 0/1 matrix with `A_ij = 1` when `j = 1` or `i | j`.
  Then `det(A_n) = M(n)` exactly, so RH ⟺ `det(A_n) = O(n^{1/2+eps})`. Charming, and it is §2 wearing
  a matrix costume; no linear algebra has ever been extracted from it. Usually credited to Redheffer
  in the 1970s.
- **Balazard, Saias and Yor (1999).** An identity of the form
  `(1/(2 pi)) * integral_R log|zeta(1/2 + it)| * dt/(1/4 + t^2)  =  sum over zeros with beta > 1/2 of log|rho/(1-rho)|`,
  so RH ⟺ that integral vanishes. Each off-line zero contributes a strictly positive amount, making
  this a *measure of failure* rather than a yes/no test, unusual and appealing. I am reasonably
  confident in this statement; verify before quoting.

---

## 11. Why so many equivalences, and still no proof

The general obstructions, the parity problem, Davenport–Heilbronn, the limits of zero-density
methods, the graveyard of failed attacks, are `docs/08-why-it-is-hard.md`'s subject and I will not
duplicate them. What belongs *here* is the narrower question: why does the sheer abundance of exact
equivalences not constitute progress?

**Difficulty is conserved, and you can watch it move.** RH is one statement about the zeros of one
function. A criterion re-encodes exactly that information in a different language, so the hardness
must reappear somewhere, and it always does, visibly:

```
    criterion              where the difficulty went
    ---------------------  ----------------------------------------------------
    Mertens (§2)           cancellation in sum mu(n); no handle on it
    Riesz / H-L (§3)       45 digits of cancellation at x = 100, growing in x
    Li (§4)                computing lambda_n needs the zeros you wanted to find
    Nyman-Beurling (§5)    d_N^2 ~ C/log N: unreachably slow, ill-conditioned
    Robin / Lagarias (§6)  extremal sigma on superabundant n, which is RH again
    Weil (§7)              the arithmetic surface that would prove positivity
                           does not exist
```

The correct reaction to a beautiful new equivalence is therefore "where did the hard part go?", and
there is always an answer. Nothing has been gained; a label has been changed.

**There is no margin to work with.** Rodgers–Tao turned a feeling into a theorem: `Lambda_dBN >= 0` is
proved and `Lambda_dBN = 0` *is* RH. Whatever proves RH must be exactly tight. That rules out an entire
style of argument, the kind where you bound something by something else with room to spare, and it
is not a soft observation but a consequence of a published theorem.

**A practical filter.** An equivalence is productive if and only if it lets you prove something new
*without* proving RH. By that test only three items in this catalogue have paid: the error-term
version (§1, an entire industry of conditional theorems), Speiser (§8, Levinson's method, and a
positive proportion of zeros unconditionally on the line), and de Bruijn–Newman (§9: Rodgers–Tao).
Robin, Lagarias, Li, Nyman–Beurling, Riesz and Mertens are exactly true, fully rigorous, genuinely
beautiful, and have to date produced no partial progress whatsoever. Saying so is not pessimism; it is
the only way to tell the two categories apart.

**And a note on what the abundance means.** It is often reported as "we're closing in". Read it the
other way: RH sits at a junction where many independent parts of mathematics meet, which is strong
evidence that it is *true and deep*, and correspondingly weak evidence that it is nearly *proved*.

---

## Where to go next

- **`docs/08-why-it-is-hard.md`**: the companion to §11, and the natural next read. The parity
  problem, the Davenport–Heilbronn counterexample (why no proof can use the functional equation
  alone), and an honest catalogue of what has failed.
- **`docs/04-explicit-formula.md`**: the machine behind §1, §2 and §7. Every criterion here is
  ultimately the explicit formula viewed from a different angle. Code: `zeta/explicit.py`
  (`psi_true`, `pi_true`, `li`, `psi_from_zeros`, `pi_from_zeros`, `prime_spectrum`). Beware a name
  clash: `zeta.explicit.R` is *Riemann's* `R(x)` from the prime-counting side, not the Riesz function
  of §3.
- **`docs/05-de-bruijn-newman.md`** and **`zeta/heatflow.py`**: §9 in full, with the current bounds on
  `Lambda_dBN` and the particle-repulsion intuition for why the flow behaves as it does.
- **`docs/06-hilbert-polya-and-gue.md`**, §7 in full: Connes' trace formula, the function-field case
  where Weil positivity is a theorem, and exactly what is missing over `Spec Z`.
- **`zeta/zeros.py`**: `first_n_zeros`, `Z`, `N_of_T`, `S_of_T`, `verify_rh_up_to`. Everything I
  computed from zeros in §4 came from the cached list in `data/zeros_1000.json`.
- **Experiments worth doing.** (i) Compute the Báez-Duarte residual `d_N` for `N` up to a few hundred
  and watch it refuse to converge, that failure *is* the point of §5. (ii) Plot `M(x)/sqrt(x)` out to
  `10^7` and note how convincingly it stays inside `±1`, then re-read §2. (iii) Compute
  `sigma(n)/(n log log n)` along the superabundant numbers and watch it creep up towards
  `e^gamma = 1.7810724...`: the quantity whose `limsup` Gronwall pinned, and whose supremum over
  `n > 5040` is what RH is really about.
