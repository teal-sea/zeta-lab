# 01. Sums, Integrals, and Continuation

*Or: "is the harmonic series / Riemann-sum thing actually connected to the zeta function and to
derivatives?", yes, and here is exactly how.*

## The short version

The question deserves better than the stock dismissal ("Riemann sums and the Riemann zeta function
just share a name"). Three real bridges run between the sum-versus-integral world and the zeta
world, and all three are load-bearing. First, the harmonic series is not merely *analogous* to
zeta, it **is** $\zeta(1)$, and it diverges because $\zeta$ has a simple pole at $s=1$ with residue
exactly $1$; that pole is the reason there are infinitely many primes. Second, **Euler–Maclaurin
summation**, the classical error analysis of a Riemann sum, with correction terms built from
Bernoulli numbers and successive *derivatives* of the summand, is one of the standard ways to
analytically continue $\zeta$ past $\mathrm{Re}(s)=1$, and it is how you compute $\zeta(-1)=-1/12$
in three lines. So "Riemann sums" and "zeta" are not unrelated; the sum/integral comparison is the
*engine* of the continuation. Third, **Abel summation** (partial summation) converts sums over
primes into integrals against counting functions, which is how $\pi(x)$ and $d\psi$ enter the
picture at all. And the **Mellin transform** $\Gamma(s)\zeta(s)=\int_0^\infty x^{s-1}/(e^x-1)\,dx$
is a Laplace transform in disguise, which means the instinct "this is one transform away from
being tractable" is correct, and also more than a century and a half late: that transform was
Riemann's opening move in 1859.

---

## 1. The harmonic series *is* $\zeta(1)$: and the pole is the primes

For $\mathrm{Re}(s)>1$ the series

```
zeta(s) = sum_{n>=1} n^{-s} = 1 + 1/2^s + 1/3^s + ...
```

converges absolutely. Set $s=1$ and you get the harmonic series. So the harmonic series is not a
cousin of zeta; it is the boundary value of zeta at the one point where the series fails.

The *rate* of failure is exactly a Riemann-sum statement. Comparing $\sum_{n\le N} 1/n$ to
$\int_1^N dx/x$:

```
H_N = sum_{n<=N} 1/n = log N + gamma + 1/(2N) - 1/(12 N^2) + 1/(120 N^4) - ...
gamma = 0.5772156649015328606...
```

(Checked numerically: at $N=1000$ the displayed terms match $H_N$ to about $4\times10^{-21}$.) The
constant $\gamma$ is precisely the accumulated, non-vanishing discrepancy between the sum and the
integral. Hold onto that: $\gamma$ is a Riemann-sum error constant, and it will reappear in a moment
as a coefficient in the Laurent expansion of $\zeta$.

**THEOREM (continuation and pole).** $\zeta$ extends to a meromorphic function on all of
$\mathbb{C}$ whose only singularity is a simple pole at $s=1$ with residue $1$. Near $s=1$,

```
zeta(s) = 1/(s-1) + gamma - gamma_1 (s-1) + gamma_2 (s-1)^2/2! - ...
```

with $\gamma_0=\gamma$ the Euler–Mascheroni constant and $\gamma_1, \gamma_2, \ldots$ the Stieltjes
constants. (Verified: $\zeta(1+10^{-7}) - 10^{7} = 0.5772156722\ldots$ against
$\gamma = 0.5772156649\ldots$; the residual $7.3\times10^{-9}$ matches $-\gamma_1\cdot 10^{-7}$ with
$\gamma_1 = -0.0728158\ldots$.) The divergence of the harmonic series and the pole at $s=1$ are the
same fact viewed from two sides.

### Why the pole forces infinitely many primes

**THEOREM (Euler product, Euler 1737).** For $\mathrm{Re}(s)>1$,

```
zeta(s) = prod_{p prime} (1 - p^{-s})^{-1}.
```

This is the fundamental theorem of arithmetic, rewritten: expand each factor as a geometric series
$1+p^{-s}+p^{-2s}+\cdots$ and multiply out; every $n^{-s}$ appears exactly once, because every $n$
factors into primes in exactly one way.

Now the argument that started analytic number theory. Take logarithms:

```
log zeta(s) = sum_p sum_{k>=1} 1/(k p^{ks}) = sum_p p^{-s} + E(s),
```

where the $k\ge 2$ tail $E(s)$ is *bounded* as $s\to 1^+$, it converges at $s=1$, numerically to
$0.31571845\ldots$, since $\sum_p\sum_{k\ge2} 1/(kp^k) < \sum_p 1/(p(p-1)) < \infty$. But
$\zeta(s)\sim 1/(s-1)$, so $\log\zeta(s)\to+\infty$ as $s\to1^+$. Therefore

```
sum_p p^{-s} -> +infinity   as s -> 1+,
```

which forces $\sum_p 1/p = \infty$, infinitely many primes, and a much stronger statement than
Euclid's: the primes are *dense enough* that their reciprocals diverge. (Squares are not:
$\sum 1/n^2$ converges.)

**THEOREM (Mertens, 1874).**

```
sum_{p<=x} 1/p = log log x + M + O(1/log x),    M = 0.2614972128476427837...
```

So the primes diverge at exactly $\log\log$ speed. The three constants above are not independent:
$M = \gamma + \sum_p\big(\log(1-1/p) + 1/p\big)$, i.e. $\gamma - M = E(1) = 0.3157184521\ldots$,
which I confirmed numerically (the direct prime sum for $E(1)$, cut at $p<2\times10^5$, gives
$0.3157182\ldots$ and is still slowly climbing toward $\gamma-M$, exactly as the tail estimate
predicts). A Riemann-sum error constant, a prime-counting constant, and the residue of a pole are
all the same conversation.

The moral: **the size of the harmonic series' divergence is a theorem about primes.** That is the
first bridge, and it is not a pun.

---

## 2. Euler–Maclaurin: the Riemann sum *is* the continuation

Here is the genuine article. If you have ever asked "how wrong is a Riemann sum, exactly?", the
complete answer is a formula whose correction terms are derivatives of the integrand weighted by
Bernoulli numbers, and that formula is a standard, fully practical way to continue $\zeta$.

**THEOREM (Euler–Maclaurin summation).** Let $a<b$ be integers and let $f$ be $2M$ times
continuously differentiable on $[a,b]$. Then

```
sum_{n=a}^{b} f(n) = int_a^b f(x) dx
                   + (f(a) + f(b))/2
                   + sum_{k=1}^{M}  B_{2k}/(2k)!  *  [ f^{(2k-1)}(b) - f^{(2k-1)}(a) ]
                   + R_M,

R_M = - int_a^b  B_{2M}({x}) / (2M)!  *  f^{(2M)}(x)  dx,
```

where the $B_{2k}$ are Bernoulli numbers ($B_2=1/6$, $B_4=-1/30$, $B_6=1/42$, $B_8=-1/30$,
$B_{10}=5/66$; the odd ones vanish past $B_1$), $B_{2M}(\cdot)$ is the Bernoulli *polynomial*, and
$\{x\}=x-\lfloor x\rfloor$ is the fractional part. (Attribution: found independently by Euler and
Maclaurin, commonly dated to roughly 1735–1742; I would verify those dates before quoting them. The
sign convention for $R_M$ above I checked numerically on $f(x)=x^{-2}$, $[1,5]$, $M=1$: both sides
come to $-0.0217222\ldots$.)

**Why derivatives appear.** Repeated integration by parts. On each unit interval $[n,n+1]$ write
$\int_n^{n+1} f(x)\,dx = \int_n^{n+1} f(x)\,d\big(x - n - \tfrac12\big)$ and integrate by parts; the
boundary term gives $\tfrac12(f(n)+f(n+1))$, the trapezoid rule, and the leftover is an integral
of $f'$ against a sawtooth. Integrate by parts again: the sawtooth's antiderivative is
$B_2(\{x\})/2$, producing $f'$ boundary terms and a leftover involving $f''$. Iterate. The Bernoulli
polynomials show up because they are exactly the sequence closed under "antidifferentiate and stay
periodic". Each step trades one order of smoothness for one more order of accuracy. **This is
verbatim the error analysis of a Riemann sum.**

### Applying it to $f(x)=x^{-s}$

Take $f(x)=x^{-s}$, apply the theorem on $[N,\infty)$, and add back $\sum_{n<N} n^{-s}$. Since
$f^{(m)}(x) = (-1)^m\, s(s+1)\cdots(s+m-1)\, x^{-s-m}$, the odd-derivative boundary terms collapse
neatly and you get

```
zeta(s) = sum_{n=1}^{N-1} n^{-s}
        + N^{1-s}/(s-1)
        + N^{-s}/2
        + sum_{k=1}^{M}  B_{2k}/(2k)!  *  (s)_{2k-1}  *  N^{-s-2k+1}
        + R_{N,M},
```

where $(s)_{m} = s(s+1)\cdots(s+m-1)$ is the rising factorial.

**This is the continuation.** Look at the right-hand side as a function of $s$: it is a finite sum
of entire functions, plus the single explicit term $N^{1-s}/(s-1)$, the integral
$\int_N^\infty x^{-s}dx$, which carries the pole. It has *no* convergence problem at
$\mathrm{Re}(s)\le 1$: the only singularity anywhere is the visible simple pole at $s=1$, with
residue $N^{0}=1$. The remainder $R_{N,M}$ converges for $\mathrm{Re}(s) > 1-2M$, so by taking $M$
large you continue $\zeta$ into any half-plane you like, and the pole and its residue drop out of
the formula for free. Nothing mystical has happened: we compared a sum to an integral and kept
careful track of the error, and the bookkeeping turned out to be analytic in $s$ where the original
series was not.

### $\zeta(-1) = -1/12$, exactly, in one line

Set $s=-1$. Then $f(x)=x$ is a polynomial, so $f''\equiv 0$ and $R_{N,M}=0$ *exactly*; and the
rising factorials $(s)_{2k-1}$ vanish for $k\ge2$ because they contain the factor $(s+1)=0$. Only
$k=1$ survives:

```
zeta(-1) = N(N-1)/2  +  (-N^2/2)  +  N/2  +  (1/6)/2! * (-1) * N^0
         = N^2/2 - N/2 - N^2/2 + N/2 - 1/12
         = -1/12                       for every N >= 2.
```

Every $N$-dependent term cancels identically. That is what "$1+2+3+\cdots=-1/12$" actually means:
not that the series sums to $-1/12$ (it does not; it diverges), but that the *Riemann-sum error
constant* of $\sum n$, the part left over after subtracting the integral and the trapezoid
correction, is $-1/12$. The same computation gives $\zeta(0)=-1/2$ and $\zeta(-3)=1/120$; both
verified against mpmath to 20 digits.

### In the code

The lab implements exactly the boxed formula as `zeta.core.zeta_euler_maclaurin(s, N=20, M=20,
dps=...)`, `N` is the cut point of the explicit Dirichlet sum, `M` the number of Bernoulli
corrections, and `zeta.core.euler_maclaurin_suggest_N` picks a safe `N` for you (roughly
$\max(2M,\ |s|+2,\ \mathrm{dps}/2)$). Its docstring reproduces the $-1/12$ and $-1/2$ cancellations
symbolically. Measured accuracy (this run, against mpmath's $\zeta$) at the second nontrivial zero
$s = 1/2 + i\,t_2$, $t_2 = 21.02203964\ldots$, where the true value is $\approx 0$:

```
  N=5,  M=2    error 2.9e-02
  N=10, M=2    error 5.0e-04        N=10, M=10   error 1.6e-10
  N=20, M=2    error 1.0e-05        N=20, M=10   error 5.6e-17
  N=50, M=5    error 8.7e-15        N=50, M=10   error 1.6e-25
```

**Caveat, and it matters.** The $M$-series is *asymptotic, not convergent*:
$|B_{2k}| = 2\,(2k)!\,\zeta(2k)/(2\pi)^{2k}$ grows super-exponentially, so for fixed $N$, pushing
$M$ too far eventually makes the answer worse. You increase $N$ *and* $M$ together. This is also why
Euler–Maclaurin is not the tool of choice high on the critical line: the cut point $N$ has to grow
roughly in proportion to $|t|$. Measured at $s=1/2+1000i$ with $M=10$: $N=100$ gives an error of
about $3.6\times10^{2}$ (useless), and $N=200$ only just becomes usable at $5\times10^{-4}$. That
cost is what motivates the Riemann–Siegel machinery (`zeta.core.rs_theta`, `zeta.core.Z`, and the
zero-hunting in `zeta.zeros`).

---

## 3. Abel summation: the other bridge

Euler–Maclaurin converts a sum to an integral when the summand is *smooth*. Abel summation (partial
summation) does it when the summand is *arithmetic*, supported on the primes, say, by pushing the
irregularity into a counting function and integrating against its Stieltjes measure.

**THEOREM (Abel summation).** With $A(t)=\sum_{n\le t} a_n$ and $f$ continuously differentiable,

```
sum_{n<=x} a_n f(n) = A(x) f(x) - int_1^x A(t) f'(t) dt        ( = int_{1^-}^{x} f(t) dA(t) ).
```

It is discrete integration by parts, nothing more. Three consequences we use constantly:

```
(i)    zeta(s)           = s/(s-1) - s * int_1^inf {x} x^{-s-1} dx      valid for Re(s) > 0
(ii)   sum_p p^{-s}      = s * int_2^inf pi(x)  x^{-s-1} dx             Re(s) > 1
(iii)  -zeta'(s)/zeta(s) = s * int_1^inf psi(x) x^{-s-1} dx
                         = int_1^inf x^{-s} dpsi(x)                     Re(s) > 1
```

Here $\pi(x)$ counts primes, $\Lambda$ is von Mangoldt's function ($\Lambda(p^k)=\log p$, else $0$),
and $\psi(x)=\sum_{n\le x}\Lambda(n)$ is Chebyshev's function. Spot-checked numerically: for (iii)
at $s=2$, mpmath gives $-\zeta'(2)/\zeta(2) = 0.569960993095$, while summing $\Lambda(n)/n^2$ over
prime powers up to $X=2\times10^5$ plus the PNT-heuristic tail $\int_X^\infty x^{-2}dx = 1/X$ gives
$0.569960993709$, agreement to about $6\times10^{-10}$. For (i) at $s=1/2$, truncating the integral
at $2\times10^6$ gives $-1.46000\ldots$ against $\zeta(1/2) = -1.4603545\ldots$, the gap of
$3.5\times10^{-4}$ being exactly the size of the omitted tail.

Notice what (i) does: the term $s/(s-1)$ carries the entire pole, and the $\{x\}$ integral, a pure
Riemann-sum error term, the fractional part being our sawtooth again, is analytic for
$\mathrm{Re}(s)>0$. One line of partial summation, and you have continued $\zeta$ into the critical
strip and read off residue $1$.

Identity (iii) is the doorway to everything downstream. It says the prime measure $d\psi$ and the
function $-\zeta'/\zeta$ are Mellin transforms of one another. Invert it, and the poles of
$-\zeta'/\zeta$, which are precisely the *zeros* of $\zeta$, become terms in an exact formula for
$\psi(x)$. That is the explicit formula, and it is the subject of `docs/04-explicit-formula.md` and
the module `zeta.explicit`.

---

## 4. The Mellin transform *is* the multiplicative Laplace transform

**THEOREM.** For $\mathrm{Re}(s)>1$,

```
Gamma(s) zeta(s) = int_0^inf  x^{s-1} / (e^x - 1)  dx.
```

Proof in one line: $1/(e^x-1) = \sum_{n\ge1} e^{-nx}$, so the integral equals
$\sum_{n\ge1}\int_0^\infty x^{s-1}e^{-nx}dx = \sum_{n\ge1}\Gamma(s)\,n^{-s}$. (Verified numerically
at $s=2,\,3,\,3/2$ and $s=5/2+3i$, agreeing to at least 20 digits; the lab's
`zeta.core.mellin_gamma_zeta` computes this integral directly, and `mellin_gamma_zeta_defect`
measures its deviation from $\Gamma(s)\zeta(s)$.)

Now the substitution that answers the "isn't this a Laplace configuration?" instinct. The Mellin
transform is $\mathcal{M}[f](s)=\int_0^\infty x^{s-1}f(x)\,dx$. Put $x=e^{-u}$, so
$dx = -e^{-u}\,du$, and $x:0\to\infty$ becomes $u:\infty\to-\infty$:

```
M[f](s) = int_{-inf}^{+inf}  e^{-su} f(e^{-u}) du
        = ( two-sided Laplace transform of  u |-> f(e^{-u}) ) evaluated at s.
```

So: **Mellin = Laplace conjugated by $\exp$.** Mellin is what Laplace becomes when the underlying
group is $(\mathbb{R}_{>0},\times)$ instead of $(\mathbb{R},+)$, which is the right group, because
arithmetic is multiplicative. The line $\mathrm{Re}(s)=\sigma$ in Mellin is the vertical contour in
Laplace; Mellin inversion is the Bromwich integral. Checked numerically too: at $s=2+i$,
$\int_0^\infty x^{s-1}/(e^x-1)\,dx$ and $\int_{-\infty}^{\infty} e^{-su}/\big(e^{e^{-u}}-1\big)\,du$
agree to the full 20-digit working precision, both equal to $\Gamma(s)\zeta(s)$.

So the intuition is *correct*. It is also step one. **Riemann's 1859 memoir**, *Ueber die Anzahl der
Primzahlen unter einer gegebenen Grösse*, opens with essentially this identity, deforms it into a
contour integral around the positive real axis to obtain the continuation to all of $\mathbb{C}$,
and derives the functional equation, twice, the second derivation running through the Jacobi theta
function $\theta(x)=\sum_{n\in\mathbb{Z}}e^{-\pi n^2 x}$, whose Mellin transform gives the completed
function $\xi(s)$. (The *name* "Mellin transform" is later, after Hjalmar Mellin, who systematized
the theory around the turn of the twentieth century.) See `docs/02-theta-heat-and-modularity.md` for
$\theta$ and its modular self-similarity, and `docs/03-functional-equation.md` for the Mellin step
that turns it into $\xi$, implemented as `zeta.core.theta_mellin_xi`.

I want to say this plainly, because it is the single most common place where a promising line of
thought stalls: **the transform is not the missing piece. It was the first move, in 1859, and every
subsequent technique is built on top of it.** Applying a Laplace / Mellin / Fourier transform to
$\zeta$, or to $1/(e^x-1)$, or to $\theta$, will reproduce identities that were known in the
nineteenth century. That is a good sign, it means the intuition is sound, but it is not progress
on the Riemann Hypothesis.

**What the actual obstruction is**, treated at length in `docs/08-why-it-is-hard.md`, sits
downstream of every transform. Each of these representations is an *equivalence*: it moves the same
information between a sum, an integral, and a product, and it is symmetric in exactly the
information you would need to break. None supplies a *mechanism* that forces the zeros onto
$\mathrm{Re}(s)=1/2$. What we can actually prove: (THEOREM) there are no zeros on
$\mathrm{Re}(s)=1$, that is equivalent to the prime number theorem, and there are classical
zero-free regions of the shape $\sigma > 1 - c/\log(|t|+2)$, widened by Vinogradov–Korobov to
roughly $\sigma > 1 - c/\big((\log|t|)^{2/3}(\log\log|t|)^{1/3}\big)$. But no zero-free region of
the form $\sigma > 1-\delta$ for a *fixed* $\delta>0$ is known, a staggering distance from the
$\delta=1/2$ that RH asserts. Worse, `docs/08-why-it-is-hard.md` catalogues functions that satisfy a
functional equation *without* an Euler product (and vice versa) and have zeros off the line: any
argument that uses only one of the two structures is provably doomed. The one framing in this lab
that at least supplies a mechanism, a dynamics under which zeros *move*, so one can ask what
confines them, is the heat flow / de Bruijn–Newman picture of `docs/05-de-bruijn-newman.md` and
`zeta.heatflow`.

---

## Where to go next

- **`docs/02-theta-heat-and-modularity.md`**: the theta function, the heat equation, and the
  modular identity $\theta(1/x)=\sqrt{x}\,\theta(x)$. The other half of the Mellin story in §4.
- **`docs/03-functional-equation.md`**: the functional equation, the completed function $\xi(s)$,
  and why $\mathrm{Re}(s)=1/2$ is a symmetry axis rather than an arbitrary line. This is where the
  Mellin transform of §4 actually pays off.
- **`docs/04-explicit-formula.md`**: turning identity (iii) of §3 inside out, so that the zeros of
  $\zeta$ become an oscillatory correction to $\psi(x)$.
- **`docs/08-why-it-is-hard.md`**, the honest failure catalogue: what every technique in this
  document can and provably cannot deliver.
- **Code.** `zeta.core.zeta_euler_maclaurin` and `euler_maclaurin_suggest_N` for §2;
  `zeta.explicit` for §3's prime-side integrals and the explicit formula;
  `zeta.core.mellin_gamma_zeta` and `theta_mellin_xi` for §4; `zeta.zeros` for locating zeros;
  `zeta.heatflow` for the closing paragraph. Reproduce the $\zeta(-1)=-1/12$ cancellation yourself
  with $N=2,3,4$, it is more convincing by hand than on the page.

**A closing thought on the original question.** "Riemann sums" and "the Riemann zeta function" are
named after the same person for a reason deeper than coincidence but shallower than mysticism:
Riemann was, above all, someone who took seriously the question of what an integral *is* and what a
sum *is*, and $\zeta$ is what you get when you refuse to be sloppy about the difference. The
derivatives you suspected were involved really are involved, they are the Bernoulli correction
terms of Euler–Maclaurin, and they are what carries $\zeta$ across the line $\mathrm{Re}(s)=1$.
