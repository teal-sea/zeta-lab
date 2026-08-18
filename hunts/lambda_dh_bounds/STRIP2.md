# The sharpened zero strip: a phase obstruction, decided

Section draft for the pre-submission hardening of WP2 (2026-08-18).
Instrument: `strip2.py`; decided values in `strip2_results.json`. This
supersedes the *constant* of `STRIP.md`, not its argument: `STRIP.md`
remains correct and is the weaker of two valid derivations, kept because a
reader should be able to see both.

Vocabulary per `MISSION.md`: *decided* means an enclosure whose exact
endpoints settle a sign, stated with backend and precision; *measured*
means one float route; *cited* means somebody else's theorem.

> **Frame.** `sigma_0'` is a point in the `s` plane and is frame-free.
> `Delta = sigma_0' - 1/2` and `Delta^2/2` are not. They are stated below
> in the narrow normalization `s = 1/2 + iz` (Stopple, arXiv:1301.3158,
> and this hunt) and in the wide one `s = (1+iz)/2` (de Bruijn as usually
> quoted, Newman, Rodgers-Tao, Polymath 15, Dobner), where
> `Lambda_wide = 4 Lambda_narrow`. Derivation and conversion table:
> `FRAME.md`.

---

## 0. The result in one line

    decided, both backends, P = 10^5:
        every zero of F lies in  1 - sigma* < Re s < sigma*
        at the exact rational   sigma* = 1.12036249819,
        so  Lambda_DH <= Delta^2/2 = 0.1924248145802688766381  (narrow)
                                   = 0.7696992583210755065522  (wide)

against `STRIP.md`'s `0.4006343708899556944469549` narrow /
`1.6025374835598228` wide. The improvement factor is **2.082030697360155**,
and the hunt's bracket ratio falls from 6.955 to **3.341**.

The lower bound is untouched, so the separation corollary
`Lambda_DH > Lambda_zeta` of `SEPARATION.md`, which rests on the floor
alone, is unaffected. In the wide frame the bracket becomes
`0.2304 < Lambda_DH <= 0.7697`.

---

## 1. Why coefficient domination is weak, quantified

`STRIP.md` proves `|f(s)| >= 1 - sum_{n>=2} |a_n| n^{-sigma}` and takes the
abscissa where the right side turns positive. That step replaces every
phase `n^{-it}` by its worst case *independently*, so it is exactly the
relaxation

    inf_t |f(sigma + it)|   >=   1 - sup over FREE phases of |sum_{n>=2} a_n n^{-sigma} e^{i theta_n}|

with `theta_n` ranging over `[0, 2 pi)^{N}` with no relation between them.
Under that relaxation the supremum is the L1 norm `sum_{n>=2} |a_n|
n^{-sigma}`, attained when every term points the same way.

The phases are not free. `n^{-it} = prod_p p^{-it v_p(n)}` is determined by
its values at the primes, and the constraint is multiplicative. `STRIP.md`
already uses that fact once, qualitatively: its section 3(c) excludes the
boundary line `Re s = sigma_0` because equality in the triangle inequality
would force `3^{-it} = 4^{-it} = 1` and `12^{-it} = -1`, which contradicts
`12 = 3 * 4`. Everything below is the same observation used
quantitatively rather than once at the boundary.

Two decided measurements of the size of the slack (Arb, 192 bits):

| what | value |
|---|---|
| `sum_{n>=2} |a_n| n^{-sigma}` at the true abscissa `sigma = 1.12036249819` | `[3.9384229985187637623766, 3.9384229985187646505552]` |
| its excess over the 1 that domination needs | `2.9384229985187637623766` |
| `Theta(sigma)` (section 3) at `STRIP.md`'s `sigma_0 = 1.3951361582351097210613589375` | `[1.5264666943583505966000, 1.5264666943583506708716]` |
| the phase a zero must supply, `pi - 2 arctan kappa` | `[2.5880182946927479869541106, 2.5880182946927479869541107]` |
| deficit factor at `sigma_0` | `1.6954305680286197` |

Read the two halves together. At the true abscissa the free-phase
relaxation is still asking for a coefficient mass of 3.94 to be below 1,
which is why it cannot conclude anything there and has to climb to 1.395.
At `sigma_0 = 1.395`, where domination finally concludes, the primes can
supply only 1.526 radians of argument against the 2.588 a zero needs, so
domination stops a factor 1.695 late. The two numbers are one fact seen
from either side, and the factor **2.082** in `Delta^2/2` is what it costs.

---

## 2. The obvious sharpening: five-term blocks. It does not decide

The coefficients sum to zero over a period, `1 + kappa - kappa - 1 + 0 = 0`,
so the series can be regrouped in blocks

    f(s) = sum_{k>=0} B_k(s),
    B_k(s) = (5k+1)^{-s} + kappa (5k+2)^{-s} - kappa (5k+3)^{-s} - (5k+4)^{-s}
           = [(5k+1)^{-s} - (5k+4)^{-s}] + kappa [(5k+2)^{-s} - (5k+3)^{-s}].

Each pair telescopes. Writing `m^{-s} - n^{-s} = s int_m^n t^{-s-1} dt` and
bounding the integrand by its value at the left endpoint,

    |B_k|  <=  |s| [ 3 (5k+1)^{-sigma-1} + kappa (5k+2)^{-sigma-1} ],       (2.1)

which is `O(n^{-sigma-1})` per block of five terms instead of the
`O(n^{-sigma})` per term that domination uses. The tail sums exactly,

    sum_{k>=K} |B_k| <= |s| 5^{-sigma-1} [ 3 zeta(sigma+1, K+1/5)
                                           + kappa zeta(sigma+1, K+2/5) ].

**The factor `|s|` is the whole story, and it is not an artifact of the
bound.** Both pairs inside a period have the *same* midpoint `5k + 5/2`,
and their first-order terms carry the same sign, so they add:

    B_k = s (3 + kappa) (5k + 5/2)^{-s-1} (1 + O(|s|/n)).

No trapezoid-style second-order correction removes the `|s|`; the next
order carries `|s|^2`. Measured directly (mpmath dps 40), the bound (2.1)
tracks the true `|B_k|` to within a factor 1.0062 at `sigma = 1.2, t = 1,
k = 100` and 1.00006 at `k = 10^4`, and overshoots by 101 at `t = 1000,
k = 10` and by 1104 at `t = 10^5, k = 100`. The crossover is `n ~ |s|`,
exactly where a first-order expansion should fail.

So the block bound cannot make a statement about a half-plane, which is
what de Bruijn's theorem consumes: it degrades as the height grows. What
it does give is a genuine height-restricted strip, from the hybrid split
that keeps `n <= 5K` under the plain triangle inequality and blocks the
rest,

    sum_{n=2}^{5K} |a_n| n^{-sigma}  +  sqrt(sigma^2 + T^2) * (block tail)  <  1 .

Decided on flint at 192 bits, with the best `K` chosen by scan and every
sign an Arb ball decision:

| every zero with `|Im s| <= T` has `Re s <` | `T = 1` | `10` | `100` | `1000` | `10^4` | `10^5` |
|---|---|---|---|---|---|---|
| `sigma_block(T)` | `1.02` (already at the search floor) | `1.19585459` | `1.33701478` | `1.37495619` | `1.38762602` | `1.39224106` |
| best `K` | - | 3 | 21 | 233 | 2584 | 28657 |

The column heads say it: as `T` grows the optimal split keeps more terms
under the plain triangle inequality, so `sigma_block(T)` climbs back toward
the coefficient-domination `sigma_0 = 1.3951361582...`, which is its limit.
Beyond `T = 10` it is already worse than the phase bound of section 3, and
at no `T` does it produce a half-plane statement.

**Verdict on the obvious sharpening: correct, decided, and useless for the
upper bound.** It is recorded because it is the natural thing to try and
because knowing why it fails is what points at the thing that works: the
mean value theorem exploits *additive* smoothness in `n`, and the
cancellation that actually matters here is *multiplicative*.

---

## 3. The phase obstruction

### 3.1 Two Euler products

Let `chi` be the odd primitive character mod 5 with `chi(2) = i` (so
`chi(1), chi(2), chi(3), chi(4) = 1, i, -i, -1`), and put

    A = (1 - i kappa)/2 .

Then `a_n = A chi(n) + conj(A) conj(chi)(n)` for every `n`, because both
sides have period 5 and they agree on a full period. Checked as a decided
statement: five acb residual balls, each containing 0 with radius below
`1e-40` at 192 bits, with `chi` taken from flint's own Dirichlet character
table rather than from a remembered list of values. Hence, for `Re s > 1`,

    f(s) = A L(s, chi) + conj(A) L(s, conj chi).                          (3.1)

This decomposition is not new here: `zeta/epstein.py` states it in the
`dh_f` docstring and the suite pins it. Measured cross-check in
`strip2.py` anyway, since it is now load-bearing in a new way:
`zeta.epstein.dh_f` against `A L_chi + conj(A) L_chi(conjugate)` at
`s = 1.6+3.5i, 2.2-11i, 3+40i`, agreeing to `1.2e-41` or better, and
`dh_f` against a truncated `sum a_n n^{-s}` inside its own truncation
allowance.

### 3.2 A zero is a phase equation

For `Re s > 1` both Euler products converge absolutely and neither vanishes,
so (3.1) gives

    f(s) = 0   <=>   R(s) := L(s, chi) / L(s, conj chi) = -conj(A)/A .     (3.2)

The right side is unimodular, since `|A| = |conj(A)|`, and

    -conj(A)/A = -(1 + i kappa)/(1 - i kappa) = exp( i (pi + 2 arctan kappa) ).

Decided as an acb ball identity to radius below `1e-40`. Its argument
modulo `2 pi` has smallest absolute representative

    tau := pi - 2 arctan kappa
         in [2.5880182946927479869541106, 2.5880182946927479869541107]
         (Arb, 192 bits, from the 500-bit kappa ball).

### 3.3 What each prime can contribute

    R(s) = prod_p (1 - conj(chi)(p) p^{-s}) / (1 - chi(p) p^{-s}) .

If `chi(p)` is real the factor is 1, so `p = 5` and `p = 1, 4 mod 5`
contribute nothing at all. If `p = 2, 3 mod 5` then `chi(p) = +-i` and
`conj(chi)(p) = -chi(p)`, so with `u = chi(p) p^{-s}`, `|u| = p^{-sigma}`,
the factor is `(1 + u)/(1 - u)`.

**Lemma.** For `|u| <= r < 1`,  `|arg (1+u)/(1-u)| <= 2 arctan r`, with
equality exactly at `u = +- i r`.

*Proof.* `u -> (1+u)/(1-u)` is a Moebius map, so it carries the disc
`|u| <= r` to a disc. That disc is symmetric about the real axis (the
domain is, and the map commutes with conjugation) and its real diameter
runs from `(1-r)/(1+r)` to `(1+r)/(1-r)`, so its centre is
`C = (1+r^2)/(1-r^2)` and its radius is `rho = 2r/(1-r^2)`. Since
`C > rho > 0` the disc misses the origin, and the largest argument on it is
`arcsin(rho/C) = arcsin(2r/(1+r^2)) = 2 arctan r`, the last step because
`2r/(1+r^2) = sin(2 arctan r)` and `2 arctan r < pi/2` for `r < 1`. The
tangency points are the images of `u = +- i r`. []

Two things fall out of that proof and both matter.

First, `C^2 - rho^2 = 1`, so the tangent length from the origin is 1: **the
argument-maximising point of each factor has modulus exactly 1**. The
constraint `|R(s)| = 1`, which (3.2) also demands, is therefore free at the
configuration that maximises the argument, and no sharper bound is
available by playing modulus against phase. This is why the phase
inequality below is not merely an improvement but is the end of this line
of argument.

Second, the bound is attained, so nothing has been thrown away. Measured
confirmation over a 4001-point circle sample at `r = 0.5, 0.25, 0.1, 0.01`
(mpmath dps 30): the observed maximum equals `2 arctan r` to printed
precision, the argmax sits at `u = i r`, and `|(1+ir)/(1-ir)| = 1` to
`1e-25`.

### 3.4 The obstruction

The product for `R(s)` converges absolutely, so its argument is the sum of
the principal arguments of its factors modulo `2 pi`, and by the lemma

    |arg R(s)|  <=  Theta(sigma) := sum_{p = 2, 3 mod 5} 2 arctan(p^{-sigma}).

A zero at `Re s = sigma` needs `arg R(s) = pi + 2 arctan kappa` modulo
`2 pi`, whose smallest absolute representative is `tau`. Therefore

> **If `Theta(sigma) < tau` then `f` has no zero on the line `Re s = sigma`.**

`Theta` is a sum of strictly decreasing positive terms, so one decided
`sigma*` closes the whole half-plane: for every `sigma >= sigma*`,
`Theta(sigma) <= Theta(sigma*) < tau`.

### 3.5 From `f` to `F`, and the strip

Identical to `STRIP.md` section 3(d), (e), and repeated only so this
section stands alone. `gamma(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2)` is
analytic and nonvanishing on `Re s >= sigma* > 1` (its only poles are at
`s = -1, -3, ...`), so `F = gamma f` has no zero with `Re s >= sigma*`.
`F` is entire with `F(s) = F(1-s)`, so it has none with `Re s <= 1 -
sigma*` either. The zeros of `F` are exactly the nontrivial zeros of `f`,
the trivial ones at `s = -1, -3, ...` being an artifact of the gamma
factor. Under `s = 1/2 + iz` the strip `1 - sigma* < Re s < sigma*`
becomes `|Im z| < Delta = sigma* - 1/2` for the zeros of `Xi_DH = H_0`,
which is what de Bruijn 1950 Theorem 13 consumes to give
`Lambda_DH <= Delta^2/2`.

### 3.6 What is used and what is not

Used: the Euler product for two Dirichlet L-functions with `Re s > 1`,
absolute convergence, one Moebius image, `F` entire with `F(s) = F(1-s)`,
and the classical facts about `Gamma`. That is all. No Bohr theory, no
Kronecker theorem, no positivity, no Euler product for `f` itself, which is
just as well since `f` has none.

Not used: any statement that the abscissa is *attained*. This argument
gives an upper bound for the supremum of the real parts of the zeros.
Whether that supremum equals the root of `Theta = tau` is Bombieri and
Ghosh's converse, and it is not needed and not claimed here.

---

## 4. Deciding `Theta`, with no prime counting

`Theta(sigma)` is a sum over primes in two residue classes, and it
converges too slowly to truncate. The head is summed exactly from a sieve;
the tail is closed by the Euler product itself, so no explicit `pi(x)`
estimate, no Chebyshev bound and no cited prime-counting inequality enters
anywhere.

### 4.1 The tail identities

Taking logarithms of the Euler products for `zeta` and for `L(., chi5)`,
where `chi5` is the quadratic character mod 5 (value `+1` on `1, 4 mod 5`,
`-1` on `2, 3 mod 5`, `0` at 5):

    T1(sigma)   := log zeta(sigma)      + sum_{p<=P} log(1 - p^{-sigma})
                 = sum_{p>P} -log(1 - p^{-sigma}),
    Tchi(sigma) := log L(sigma, chi5)   + sum_{p<=P} log(1 - chi5(p) p^{-sigma})
                 = sum_{p>P} -log(1 - chi5(p) p^{-sigma}).

Only the class `2, 3 mod 5` and `p = 5` survive in the difference, since
the two logarithms coincide when `chi5(p) = +1`:

    T1 - Tchi = log( zeta(sigma) / L(sigma, chi5) ) + log(1 - 5^{-sigma})
                + sum_{p<=P, p = 2,3 mod 5} [ log(1 - p^{-sigma}) - log(1 + p^{-sigma}) ].

Expanding both logarithms in `k`, and writing `Q := sum_{p>P, p = 2,3 mod 5}
p^{-sigma}` for the quantity actually wanted,

    T1 - Tchi = 2 Q + (E_chi - E_1),
    E_1   = sum_{p>P} sum_{k>=2} p^{-k sigma}/k,
    E_chi = sum_{p>P} sum_{k>=2} chi5(p)^k p^{-k sigma}/k.

**The `k = 2` terms cancel exactly**, because `chi5(p)^2 = 1` for every
`p > P >= 5`, and so does every even `k`. Only odd `k >= 3` survives, with
`|chi5(p)^k - 1| <= 2`, so

    |E_chi - E_1|  <=  (2/3) sum_{p>P} p^{-3 sigma} / (1 - P^{-2 sigma})
                   <=  (2/3) P^{1-3 sigma} / ((3 sigma - 1)(1 - P^{-2 sigma}))  =:  eps3,

the last step by the integral test over all integers `> P`, which is crude
and does not matter because the quantity is already `O(P^{1-3 sigma})`.
This is the point at which the estimate stops being loose: bounding
`E_chi` and `E_1` separately would leave an `O(P^{1-2 sigma})` error, larger
by a factor of order `P^{sigma}`. Numerically at `P = 10^5` and
`sigma = 1.12036249819` the separate bound is `2.52e-07` and this one is
`4.42e-13`, a factor `5.7e+05`.

### 4.2 The two bounds

With `arctan x <= x` on the tail and `arctan x >= x - x^3/3`:

    Theta_up(sigma) = head_P(sigma) + (T1 - Tchi) + eps3,
    Theta_lo(sigma) = head_P(sigma) + (T1 - Tchi) - eps3 - (2/3) W3,
    head_P(sigma)   = sum_{p <= P, p = 2,3 mod 5} 2 arctan(p^{-sigma}),
    W3              = P^{1-3 sigma}/(3 sigma - 1) .

Only `Theta_up` is load-bearing. `Theta_lo` is computed so the width can be
reported: it is the head/tail systematic, not the ball precision, and at
`P = 10^5, sigma ~ 1.12` it is `1.34e-12`.

### 4.3 Backends

* **python-flint (Arb), 192 bits.** `arb.atan`, `arb.log`, `arb.zeta`, and
  `L(sigma, chi5)` from the Hurwitz combination `5^{-s}[zeta(s,1/5) -
  zeta(s,2/5) - zeta(s,3/5) + zeta(s,4/5)]`.
* **mpmath.iv, dps 40.** The `iv` context has neither zeta nor arctan.
  `zeta` and `L` come from the Euler-Maclaurin machinery `strip.py` already
  uses for arithmetic progressions, generalised to a step: `zeta` is the
  step-1 progression, `L` the four step-5 ones. `arctan` comes from its
  Maclaurin series, which is alternating with strictly decreasing terms for
  `0 <= x < 1`, so consecutive partial sums bracket the value; the bracket
  is taken from the last odd-index and even-index partial sums, each
  evaluated in interval arithmetic, and the loop refuses rather than
  guesses if `x` is too close to 1.

Both legs run at the same sieve limit `P = 10^5`, so they bisect the same
function and their intervals must overlap. They do.

---

## 5. Decided numbers

All intervals are outward-rounded decimal strings containing the exact
rational endpoints. Full detail in `strip2_results.json`.

### 5.1 The abscissa

| quantity | python-flint (Arb), 192 bits | mpmath.iv, dps 40 |
|---|---|---|
| root of `Theta_up = tau`, `P = 10^5` | `[1.1203624981833869487276, 1.1203624981833869487332]` | `[1.1203624981833854, 1.1203624981841131]` |
| sign decisions | 65 | 38 |

Two-sided enclosure of the root of `Theta = tau` itself, from bisecting
`Theta_lo` as well (flint, `P = 10^5`):
`[1.1203624981832156488068, 1.1203624981833869487332]`, width `1.71e-13`.

### 5.2 The headline, at an exact rational

`Theta(sigma) < tau` decided on **both** backends at `sigma* =
1.12036249819` (exact rational `112036249819/100000000000`):

| | flint | iv |
|---|---|---|
| `Theta(sigma*)` | `[2.5880182946402392454052004, 2.5880182946415650528147533]` | `[2.5880182946402392, 2.5880182946415651]` |
| `tau` | `[2.5880182946927479869541106, 2.5880182946927479869541107]` | same to printed width |
| decided below | yes | yes |

margin `tau - Theta_up(sigma*) = 5.12e-11`. Consequently

    Delta = sigma* - 1/2 = 0.62036249819   (exact)
    Lambda_DH <= Delta^2/2 = 0.1924248145802688766381    (narrow)
                           = 0.7696992583210755065522    (wide)

A deliberately generous rounding is also decided on both backends and is
worth quoting because it can be reproduced at a sieve limit of only
`P = 10^4`, in seconds: at `sigma = 1.1203625`,
`Delta^2/2 = 0.1924248157031250` narrow, `0.7696992628125` wide,
margin `1.41e-8`.

### 5.3 One deep point

flint only, 320 bits, `P = 10^7`, 332442 class primes, one evaluation,
5.9 s. The `iv` leg is not run at this sieve limit because a single
evaluation there costs about a minute and nothing in the headline depends
on it.

    sigma_deep = 1.1203624981833251     (decided: Theta < tau)
    Delta^2/2  = 0.1924248145761280189989039   (narrow)
               = 0.7696992583045120759956154   (wide)

### 5.4 The improvement

| | narrow (`s = 1/2 + iz`) | wide (`s = (1+iz)/2`) |
|---|---|---|
| `STRIP.md` | `0.4006343708899556944469549` | `1.6025374835598228` |
| this section, headline | `0.1924248145802688766381` | `0.7696992583210755065522` |
| this section, deep point | `0.1924248145761280190` | `0.7696992583045120760` |
| improvement factor | **2.082030697360155** | same, the factor is frame-free |

The hunt's bracket, wide frame: `0.2304 < Lambda_DH <= 0.7697`. Bracket
ratio `6.955 -> 3.341`.

---

## 6. Controls and cross-checks, all run before anything is decided

Eight, each of which aborts the run rather than downgrading a claim.

1. **Character decomposition (decided).** `a_n = A chi(n) + conj(A)
   conj(chi)(n)` for `n = 1..5` and `-conj(A)/A = exp(i(pi + 2 arctan
   kappa))`, as six acb residual balls containing 0 with radius `< 1e-40`.
   `chi` from flint's Dirichlet character table.
2. **Series against the two L-functions (measured).** `zeta.epstein.dh_f`
   against `A L_chi + conj(A) L_chi(conjugate)` at three complex points
   with large imaginary part (`<= 1.2e-41`), and against a truncated
   `sum a_n n^{-s}` at two more, inside the truncation allowance.
3. **The phase lemma (measured).** 4001-point circle samples at four radii:
   observed max `|arg|` equals `2 arctan r`, argmax at `u = i r`, modulus 1
   there.
4. **Bombieri-Ghosh's finite claim (decided).** Their section 9 states that
   the smallest set of primes `p = 2, 3 mod 5` with `sum arctan(1/p) >
   pi/2` runs up to 6323 and has 420 elements. Recomputed here from the
   exact sieve with Arb ball sign decisions: **threshold prime 6323,
   cardinality 420**. This shares no machinery with their Theorem 7 and it
   exercises precisely this instrument's class enumeration and arctan.
5. **The Euler-product tail identity (measured).** The closed form
   `log zeta(sigma) + sum_{p<=P} log(1 - p^{-sigma})` against the explicit
   partial tail over `P < p <= P2`: the gap must be positive and below the
   integral-test allowance at `P2`. It is.
6. **`L(., chi5)` two routes (decided).** The Hurwitz combination against
   flint's `acb.dirichlet_l`, ball overlap at three sigma.
7. **`iv` special functions (decided).** The `iv` enclosures of `zeta`, `L`
   and `arctan` must contain the corresponding Arb balls, nine points.
8. **Head/tail split across sieve limits (decided).** `Theta` enclosures at
   `P = 10^3, 10^4, 10^5` must intersect. They do, common width `1.34e-12`.
   Different `P` move mass between head and tail, so this is a check on the
   split itself rather than on either half.

**Plus a control at the other Titchmarsh root.** The two roots of
`x^2 + 2 phi x - 1 = 0` multiply to `-1`, so the second Davenport-Heilbronn
parameter is `tau_- = -1/kappa`, and its phase target is
`pi - 2 arctan|tau_-| = 2 arctan kappa`. `Theta` itself does not change:
only the target moves. Running the identical head, the identical tail
bound and the identical bisection:

    1/kappa      decided [3.52014702134020199243, 3.52014702134020199244]
                 against their published tau_- = -3.520147021340
    sigma(tau_-, 1)
                 decided [2.38228610898712387152, 2.38228610898712387205]
                 against their published 2.3822861089 (ten digits)

Nothing in this instrument was built around that constant, and it hits all
ten published digits.

---

## 7. Relation to Bombieri and Ghosh, stated exactly

Their Theorem 7, quoted verbatim in `BOMBIERI-GHOSH.md` section 3.1: for
real `xi = tan(theta)`, `sigma(xi, q)` is the value of `sigma > 1` solving

    sum_{p = 2,3 mod 5, (p,q)=1} arctan(p^{-sigma}) = pi/2 - |theta| .

At `q = 1` and `xi = kappa` that is `Theta(sigma) = tau`, term for term.
Their quoted prime-sum target for `tau_+`, 1.2940091, is
`pi/2 - arctan kappa`, which this instrument decides as
`1.29400914734637399...`.

So the equation is theirs, and this is not presented as a new equation. The
division is:

* **Their necessary half is what is derived in section 3 above**, from the
  Euler product and one Moebius image, with no Bohr theory and no Kronecker
  theorem. That half is all an upper bound needs, and it is the half this
  hunt can decide by its own lights.
* **Their converse is not used.** It is what turns the upper bound into an
  exact supremum, it needs machinery this tree has not verified, and
  nothing here depends on it.
* **What is new here is the grade, not the number.** `BOMBIERI-GHOSH.md`
  set out exactly the two conditions for adopting the sharper constant at
  rung 2: check Theorem 7's hypotheses in-tree, and re-solve with
  outward-rounded enclosures. Both are now done, and the constant no longer
  needs to be adopted from the literature at all, because the inequality it
  supplies is proved here.

**A correction this instrument forces, and it is against an in-tree
artifact rather than against the paper.** `BOMBIERI-GHOSH.md` check B
re-solved both abscissae to 29 digits at mpmath dps 30. At `P = 10^7` and
320 bits this instrument decides that both re-solves sit on the wrong side
of their own root:

| | recorded re-solve | decided finding |
|---|---|---|
| `sigma(tau_+, 1)` | `1.12036249818332508773010350311` | `Theta < tau` already holds there, so the root is strictly **below** it; the re-solve is high by about `1.2e-17` |
| `sigma(tau_-, 1)` | `2.38228610898712386578711039387` | `Theta > 2 arctan kappa` still holds there, so the root is strictly **above** it; the re-solve is low by about `6e-18` |

Neither touches anything Bombieri and Ghosh published: they print 1.120362
and 2.3822861089, and this instrument reproduces both exactly. What it does
touch is `FRAME.md`'s 18-digit row `0.192424814576128011`, which is derived
from the `tau_+` re-solve rather than from the six cited decimals. The
decided replacement, from the deep point, is `0.1924248145761280190`
narrow, which agrees with it to 17 digits.

---

## 8. Honest ceiling, and where the looseness now is

**How far above the truth is the decided abscissa?** The headline `sigma* =
1.12036249819` sits `6.8e-12` above the decided lower end of the root
enclosure at `P = 10^5`, and the deep point sits about `4e-17` above it.
The sieve-limit sweep says what that costs (flint, 192 bits, full
bisection each time):

| `P` | class primes | decided `sigma_0' <=` | `Theta` systematic width | seconds |
|---|---|---|---|---|
| `10^3` | 89 | `1.1203625015845160712658` | `6.99e-08` | 0.06 |
| `10^4` | 619 | `1.1203624981978052337886` | `3.04e-10` | 0.21 |
| `10^5` | 4814 | `1.1203624981833869487332` | `1.33e-12` | 1.38 |
| `10^6` | 39287 | `1.1203624981833253279238` | `5.77e-15` | 10.9 |
| `10^7` | 332442 | `1.1203624981833251` (single point, 320 bits) | `~2.6e-17` | 5.9 |

Both error sources fall like `P^{1-3 sigma}`, so the accuracy is essentially
free and the exercise stops being interesting long before it stops being
cheap. **The strip constant is no longer where the looseness is.**

What is left, stated plainly:

1. **The converse.** This argument bounds the supremum of the real parts of
   the zeros from above and does not show it is attained. If Bombieri and
   Ghosh's converse holds, `Delta` cannot be improved at all. If it does
   not, `Delta` might still come down, and this argument would not see it.
2. **The de Bruijn engine.** With `Delta = 0.62036249819` the engine
   returns `Delta^2/2 = 0.19242481458` narrow, while the deepest measured
   Davenport-Heilbronn zeros reach `|Im z| = 0.347`, which would give
   `0.0602`, and the decided floor is `0.0576`. The remaining factor of
   3.34 in the bracket is the engine plus the sparsity of the extreme
   zeros, not the strip.
3. **Everything `GATE.md` already carries** on the other side: the `M2`
   blind spot, which this section does not touch, and de Bruijn Theorem 13
   itself, which this section still rides on exactly as `STRIP.md` did.

The one thing that has genuinely closed is the referee question `GATE.md`
listed second: *why is the sharper published constant not used?* It no
longer needs to be. The sharper constant is now derived and decided
in-tree, on both backends, from an elementary argument, and the citation
has moved from being the source of a number to being the standard the
number is measured against.

---

## 9. Grades

| claim | grade |
|---|---|
| `kappa`, `tau`, `Theta` enclosures, `sigma*`, `Delta^2/2` | decided (python-flint 192 bits and mpmath.iv dps 40, `P = 10^5`; deep point flint 320 bits, `P = 10^7`) |
| the phase obstruction of section 3 | exact elementary analysis on top of decided constants, using the Euler product, `F` entire with `F(s) = F(1-s)`, and the classical nonvanishing of `Gamma` |
| block route of section 2 | decided, and decided to be useless for a half-plane |
| `6323 / 420`, `sigma(tau_-, 1)`, `1/kappa` against published decimals | decided, against cited values |
| the correction to `BOMBIERI-GHOSH.md`'s two re-solves | decided |
| `Lambda_DH <= Delta^2/2` | cited plus decided, weakest step cited: de Bruijn 1950 Theorem 13, unchanged from `STRIP.md` and `THEOREM13.md` |

Reproduce with

    .venv/bin/python hunts/lambda_dh_bounds/strip2.py

which rewrites `strip2_results.json` and takes about a minute.
