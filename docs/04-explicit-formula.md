# 04 — The Explicit Formula: Zeros ↔ Primes

*"What do the zeros actually have to do with the primes?"*

## The short version

Everything. The connection is not an analogy, it is an **identity**. Chebyshev's prime-counting
function `psi(x) = sum_{p^k <= x} log p` — a staircase that jumps by `log p` at every prime power —
can be written exactly as a smooth main term `x` minus a sum of *waves*, one wave per non-trivial
zero of zeta:

```
    psi_0(x)  =  x  -  sum over rho  x^rho / rho  -  log(2 pi)  -  (1/2) log(1 - x^-2)
```

Each zero `rho = beta + i gamma` contributes a pure oscillation in the variable `u = log x`, of
frequency `gamma` and amplitude `2 x^beta / |rho|`. The primes are the interference pattern of these
waves; the zeros are the Fourier spectrum of the primes. Run the sum one way and the zeros rebuild
the primes; run it the other way and a bare sum of cosines over the zeros develops spikes at exactly
`u = log p^k`, and at no other point. This is why the Riemann Hypothesis is not an aesthetic
preference: `beta` is the *growth exponent of the error* in every prime count. RH says every `beta`
equals `1/2` — that the primes are as regular as they could possibly be. A single zero with
`beta > 1/2` would be a permanent anomaly in the distribution of the primes of size `x^beta`, and no
amount of averaging would ever wash it out.

---

## 1. The bridge: `-zeta'/zeta`

The Euler product (see `docs/01-sums-integrals-and-continuation.md`) is
`zeta(s) = prod_p (1 - p^-s)^{-1}` for `Re(s) > 1`. Take the logarithm to turn the product into a
sum, then differentiate:

```
    log zeta(s)  =  - sum_p log(1 - p^-s)  =  sum_p sum_{k>=1} p^(-ks) / k

    -zeta'(s)/zeta(s)  =  sum_p sum_{k>=1} (log p) p^(-ks)  =  sum_{n>=2} Lambda(n) n^-s
```

where the **von Mangoldt function** `Lambda(n)` is `log p` if `n = p^k` for some `k >= 1`, and `0`
otherwise. This is the whole reason `Lambda` exists: it is the arithmetic function whose Dirichlet
series is the logarithmic derivative of zeta. Weighting `p^k` by `log p` instead of counting primes
by `1` is not cosmetic — it is what makes the analysis clean, and `pi(x)` is recovered from `psi(x)`
afterwards by Möbius inversion (§8).

Sanity check at `s = 2 + 0.3i` (mpmath, series truncated at `n = 3·10^5`):

```
    -zeta'/zeta(s)          =  0.489626756937 - 0.240714012303 i
    sum Lambda(n) n^-s      =  0.489628660161 - 0.240716580265 i
```

The residual is the truncation tail, as it should be.

**Why this is the bridge.** The left side knows about the zeros — a logarithmic derivative has a
*simple pole with residue equal to the multiplicity* at every zero of `zeta`, and a simple pole with
residue `-1` at the pole `s = 1`. The right side knows about the primes. One function, two faces —
exactly the geometry/spectrum split you already met in `docs/02-theta-heat-and-modularity.md`, where
the windings of heat around a circle and the eigenvalues of the Laplacian were two faces of theta.
Here the windings become prime powers and the eigenvalues become zeros.

## 2. Perron: extracting a staircase from a Dirichlet series

To get from `sum Lambda(n) n^-s` to `sum_{n <= x} Lambda(n)` you need a device that turns a Dirichlet
series into a partial sum. That device is Perron's formula, and it rests on one integral:

```
    (1/2 pi i) integral over Re(s)=c of  y^s / s  ds  =  1  if y > 1,   0  if y < 1,   1/2 if y = 1
```

(`c > 0`; the integral is a principal value.) It is a sharp cutoff written analytically: close the
contour to the left when `y > 1` and pick up the pole at `s = 0`; close to the right when `y < 1` and
pick up nothing. Put `y = x/n` and sum against `Lambda(n)`:

```
    psi_0(x)  =  (1/2 pi i) integral over Re(s)=c of  (-zeta'(s)/zeta(s)) · x^s / s  ds ,    c > 1
```

The subscript on `psi_0` is the price of that `1/2` in the cutoff: at a prime power the contour
integral returns the **midpoint of the jump**, `psi_0(x) = psi(x) - Lambda(x)/2`. Away from prime
powers `psi_0 = psi`. This matters when you test the formula at `x = 8` or `x = 121`; the code handles
it (`explicit.convergence_table` reports both `psi_true` and `psi0_true`).

## 3. Hadamard: where the poles are

Now push the contour left. Everything the answer contains is a residue, so the question becomes:
*where are the poles of `(-zeta'/zeta)(s) · x^s/s`?* To answer that globally — not just where the
Euler product converges — you need the factorisation of the completed function
`xi(s) = (1/2) s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)` from `docs/03-functional-equation.md`.

**THEOREM (Hadamard, 1893).** `xi` is entire of order 1, and therefore factors over its zeros:

```
    xi(s)  =  e^(A + B s)  prod over rho  (1 - s/rho) e^(s/rho)
```

the product running over the non-trivial zeros of `zeta`, which are exactly the zeros of `xi`. The
`e^(s/rho)` factors are the genus-1 convergence factors, needed because `sum 1/|rho|` diverges while
`sum 1/|rho|^2` converges.

Take the logarithmic derivative of `xi` in both of its forms — the Hadamard product, and the
definition in terms of `zeta` and `Gamma` — and solve for `zeta'/zeta`. Out comes a global partial
fraction expansion whose content, stripped of the constants, is:

```
    -zeta'(s)/zeta(s)   has a simple pole, residue  +1,  at  s = 1        (the pole of zeta)
                        a simple pole, residue  -1,  at each  s = rho     (non-trivial zeros)
                        a simple pole, residue  -1,  at each  s = -2n     (trivial zeros)
```

That is the entire input. The rest is bookkeeping.

## 4. Collecting the residues

Sweep the contour from `Re(s) = c > 1` off to `Re(s) = -infinity`. The integrand is
`(-zeta'/zeta)(s) · x^s/s`, so a pole of `-zeta'/zeta` at `s_0` with residue `r` contributes
`r · x^(s_0)/s_0`, and the pole of the factor `1/s` at `s = 0` contributes `(-zeta'/zeta)(0)`:

| pole | contributes | value |
|---|---|---|
| `s = 1` (pole of zeta) | `+ x^1/1` | `x` — the main term, i.e. the PNT |
| `s = rho` | `- x^rho/rho` | the oscillation, one term per zero |
| `s = 0` (from `1/s`) | `(-zeta'/zeta)(0)` | `-log(2 pi)` |
| `s = -2n` | `- x^(-2n)/(-2n)` | sums to `-(1/2) log(1 - x^-2)` |

Two of these deserve a check rather than a nod:

- `zeta'(0)/zeta(0) = log(2 pi)`. Verified to 25 digits: both equal `1.837877066409345483560659…`.
- `sum_{n>=1} x^(-2n)/(2n) = -(1/2) log(1 - x^-2)`, by the Mercator series for `log(1-z)` at
  `z = x^-2`. This term is genuinely tiny: `5.03e-3` at `x = 10`, `5.00e-5` at `x = 100`. It *is* the
  trivial zeros — and they contribute almost nothing, which is exactly why nobody cares about them.

**THEOREM (von Mangoldt, 1895).** For `x > 1`,

```
    psi_0(x)  =  x  -  sum over rho  x^rho/rho  -  log(2 pi)  -  (1/2) log(1 - x^-2)
```

the `rho`-sum taken as `lim_{T -> inf} sum over |Im rho| < T`, i.e. in conjugate pairs. That symmetric
pairing is not optional: the series is only conditionally convergent, and reordering it would change
the answer.

## 5. Each zero is a wave

Pair `rho = beta + i gamma` with its conjugate. Since `x^rho = x^beta · e^(i gamma log x)` and
`1/rho = e^(-i arg rho)/|rho|`,

```
    x^rho/rho  +  x^rhobar/rhobar   =   2 Re(x^rho/rho)
                                    =   2 x^beta cos(gamma log x - arg rho) / |rho|
```

On RH, `beta = 1/2`, so `|rho| = sqrt(1/4 + gamma^2)` and `arg rho = arctan(2 gamma)`, and the working
form the code evaluates (`explicit.psi_curve`) is

```
    psi_0(x)  ≈  x  -  2 sqrt(x) · sum over gamma > 0 of cos(gamma log x - arg rho)/|rho|
                    -  log(2 pi)  -  (1/2) log(1 - x^-2)
```

Read that as music. In the variable `u = log x` each zero is a **pure tone**:

- **frequency** `gamma` — the first zero, `gamma_1 = 14.134725141…`, has wavelength
  `2 pi/gamma_1 = 0.4445` in `log x`, i.e. one full cycle every time `x` is multiplied by
  `e^(2 pi/gamma_1) = 1.5597`;
- **amplitude** `2 x^beta/|rho|` — decaying with the zero's height, so the low zeros dominate;
- **phase** `arg rho`.

Concretely at `x = 100`: the smooth part alone gives
`x - log 2pi - (1/2)log(1 - x^-2) = 98.1622`, against `psi(100) = 94.0453` — an overshoot of `4.1169`.
The single lowest zero contributes a wave worth `1.0579` there, cutting the error to `3.06`. Adding
more zeros:

```
  N zeros   gamma_N     psi estimate    error vs psi(100) = 94.0453
      0       —            98.1622        +4.1169
      1     14.135         97.1042        +3.0589
     10     49.774         95.0403        +0.9950
     50    143.112         94.4488        +0.4034
    100    236.524         93.6700        -0.3753
    500    811.184         93.9906        -0.0548
```

Reproduce it exactly:

```python
from zeta.explicit import convergence_table
for r in convergence_table(100.0, 500, counts=(0, 1, 10, 50, 100, 500)):
    print(r["n_zeros"], round(r["gamma_max"], 3), round(r["psi_est"], 4), round(r["error"], 4))
```

Note that the error is *not* monotone — 100 zeros does worse than 50. That is the signature of a
conditionally convergent Fourier series being truncated: you are watching Gibbs-type ringing, not a
bug. The truncated formula does have a rigorous error term; the standard statement (Davenport,
*Multiplicative Number Theory*, §17) has the shape `O(x log^2(xT)/T + log x)` when the sum is cut at
height `T` — I am quoting the *shape*, so check the exact statement before using it quantitatively.
The practical moral is already visible in the table: to resolve `psi` near `x` you need zeros up to
height of order `x`.

## 6. Why RH is *exactly* an error-term statement

Look at the amplitude once more: `2 x^beta / |rho|`. The real part of a zero is an **exponent on x**.
That one observation is the entire significance of RH.

**THEOREM.** Let `Theta = sup { Re(rho) }` over the non-trivial zeros. Then, for every `eps > 0`,

```
    psi(x) - x  =  O(x^(Theta + eps))     and     psi(x) - x  =  Omega(x^(Theta - eps))
```

So the size of the prime-counting error is *precisely* `x^Theta` — no more, and no less. Hardy proved
infinitely many zeros lie on the critical line, so `Theta >= 1/2`, and

```
    RH   <=>   Theta = 1/2   <=>   psi(x) = x + O(sqrt(x) log^2 x)
                              <=>   pi(x)  = li(x) + O(sqrt(x) log x)
```

The last equivalence is **von Koch's theorem (1901)**. Under RH the constants can even be made
explicit: Schoenfeld (1976) proved `|psi(x) - x| < (1/(8 pi)) sqrt(x) log^2 x` for `x >= 73.2`, and
`|pi(x) - li(x)| < (1/(8 pi)) sqrt(x) log x` for `x >= 2657`. (I am confident in the constant
`1/(8 pi)` and the shape; verify the thresholds against the paper before quoting them.)

Nor could the bound be improved much. **THEOREM (Littlewood, 1914).**
`psi(x) - x = Omega_±(sqrt(x) log log log x)`. The `sqrt(x)` is genuinely there; only logarithms are
negotiable. So RH is the statement that the error is *as small as the zeros already force it to be* —
"the primes are as regular as they could possibly be."

**What one rogue zero would do.** Suppose — counterfactually — a single zero sat at `beta = 0.6`,
`gamma = 100`. Its wave has amplitude `2 x^0.6/100`, against an RH-permitted total error of order
`sqrt(x)`. The ratio is `x^0.1/50`, which passes 1 at `x = 50^10 ≈ 9.77e16`. Beyond that point this
one zero out-shouts every other effect in the theory, forever, with a clean periodic signature of
wavelength `2 pi/100` in `log x`. It would not be a correction; it would be a permanent,
ever-growing, in-principle-detectable bias in how the primes are laid out. That is what "off the
line" costs.

## 7. The dual direction: the spectrum of the primes

Differentiate the explicit formula with respect to `u = log x`. The staircase `psi_0(e^u)` becomes a
comb of delta spikes, one at each `u = log n`, with weight `Lambda(n)`:

```
    sum_{n>=2} Lambda(n) delta(u - log n)  =  e^u  -  2 e^(u/2) sum_{gamma>0} cos(gamma u)  -  1/(e^(2u) - 1)
```

Divide by `e^(u/2)` and discard the smooth pieces. The purely oscillatory object

```
    D(u)  =  -2 sum over gamma > 0 of  w(gamma) cos(gamma u)
```

— *a bare sum of cosines over the zeros, containing no arithmetic input whatsoever* — is a spike train
with a peak at every `u = log p^k` and nowhere else; and after normalising by the window `w`, the peak
at `u = log n` has height `Lambda(n)/sqrt(n)`. That is `zeta.explicit.prime_spectrum`:

```python
import numpy as np
from zeta.explicit import prime_spectrum, spectrum_peaks
u  = np.linspace(0.2, 3.2, 4000)
sp = prime_spectrum(1000, u, window="gauss")      # 1000 zeros, Gaussian taper
for p in spectrum_peaks(u, sp, n_peaks=10):
    print(round(p["u"], 4), round(p["x"], 3), p["nearest_n"],
          round(p["height"], 4), round(p["lambda_over_sqrt_n"], 4))
```

Output, run in this repository (rows re-sorted by `u` for readability — `spectrum_peaks` returns them
in order of decreasing height; the first call computes the zeros and takes a minute, after which they
are cached to `data/`):

```
     u        x = e^u    n     peak height    Lambda(n)/sqrt(n)
  0.6931       2.000      2       0.4792           0.4901
  1.0986       3.000      3       0.6258           0.6343
  1.6094       5.000      5       0.7086           0.7198
  1.9459       7.000      7       0.7194           0.7355
  2.1972       9.000      9       0.3511           0.3662     <- the prime power 3^2
  2.3979      11.000     11       0.7078           0.7230
  2.5650      13.000     13       0.6792           0.7114
```

and between the spikes the signal is flat: `D(log 6) = -0.009`, `D(log 10) = -0.013`,
`D(log 2.5) = -0.005`. Nothing goes into this computation but a list of zero ordinates, and out come
the primes with their correct multiplicities. Note `9` appearing at roughly half the height of a
prime (`log 3 / 3` versus `log 3 / sqrt 3`): the spectrum sees prime *powers*, properly weighted,
because `Lambda` does.

The rigorous version of this duality is the **Riemann–Weil explicit formula**: for a suitable test
function `f` with Fourier transform `fhat`, a sum of `f(gamma)` over the zeros equals a sum of
`fhat(log p^k) · Lambda(p^k)/sqrt(p^k)` over prime powers, plus archimedean terms. Reading peak
*heights* off a plot the way we just did is the practical, HEURISTIC form of that theorem; the
theorem itself is a statement about smoothed sums, which is precisely why the code applies a window.

## 8. `pi(x)`, Riemann's `R`, and the `li` overestimate

Riemann's own 1859 formula was for `pi`, not `psi`. Set `J(y) = sum_{k>=1} pi(y^(1/k))/k`; then
`log zeta(s) = s · integral J(y) y^(-s-1) dy`, and the same contour argument gives

```
    J_0(y)  =  li(y)  -  sum over rho  li(y^rho)  -  log 2  +  integral from y to inf of dt/(t(t^2-1) log t)
```

Möbius inversion — a *finite* sum, since `J(y) = 0` for `y < 2` — returns
`pi(x) = sum_n mu(n)/n · J(x^(1/n))`, whose headline form is

```
    pi(x)  ≈  R(x)  -  sum over rho  R(x^rho),        R(x) = sum_{n>=1} mu(n)/n · li(x^(1/n))
```

`R` is the **Riemann R function** (`explicit.R`, evaluated via Gram's rapidly convergent series
`R(x) = 1 + sum_{k>=1} (log x)^k / (k · k! · zeta(k+1))`). It is a strikingly better approximation to
`pi(x)` than `li(x)` is, because its `-(1/2) li(sqrt x)` term subtracts off the systematic overcount
coming from the squares of primes:

```
     x          pi(x)         li(x) - pi(x)      R(x) - pi(x)
    10^6         78498             129.5              29.4
    10^8       5761455             754.4              96.9
    10^10    455052511            3103.6           -1827.7
    10^12  37607912018           38262.8           -1475.8
```

Driving the formula from the zeros works too: `pi_from_zeros(100, 500)` returns `24.9899`, against
`pi(100) = 25`.

Notice that `li(x) - pi(x)` is positive in every row — as it is in every row anyone has ever computed.
It is very tempting to conjecture that `pi(x) < li(x)` always. That conjecture is **false**.

**THEOREM (Littlewood, 1914).** `pi(x) - li(x)` changes sign infinitely often.

The mechanism is visible in the formula above. The `-(1/2) li(sqrt x)` bias is what the zero-waves
must overcome, and Littlewood showed they eventually do — but only through a delicate near-alignment
of very many waves at once, which is why it takes so absurdly long. No crossing point is known
explicitly. Skewes (1933) gave the first upper bound, `e^(e^(e^79))`, assuming RH, and in 1955 an
unconditional bound usually quoted as `e^(e^(e^(e^7.705)))`. Modern work has located a region where a
crossing provably occurs, **commonly cited as just under `1.4 × 10^316`** (Bays and Hudson, 2000,
exhibited a crossing region near `1.398 × 10^316`; later authors refined the leading digits slightly
downward). Direct computation has confirmed `pi(x) < li(x)` out beyond `10^19` with no crossing.
*Hedge:* I am confident in the order of magnitude `10^316` and in the Littlewood and Skewes
attributions; treat the leading digits, and the exact extent of the verified range, as "commonly
cited" rather than checked here.

---

## Where to go next

- **`zeta/explicit.py`** — every formula above, implemented and documented: `psi_from_zeros`,
  `psi_curve`, `psi_staircase`, `convergence_table`, `J_from_zeros`, `pi_from_zeros`, `R`,
  `prime_spectrum`, `spectrum_peaks`. `tests/test_explicit.py` is the regression suite; running it
  (`.venv/bin/python -m pytest tests/test_explicit.py`) is the fastest way to convince yourself that
  none of this is hand-waving.
- **The one plot to make.** Overlay `explicit.psi_staircase` (the true jagged staircase) with
  `explicit.psi_curve` for `N = 1, 10, 100, 1000` zeros on `2 < x < 100`. Watch a smooth line grow
  corners, then risers, then land on the steps. Nothing makes the duality as vivid.
- **`docs/03-functional-equation.md`** — the symmetry `xi(s) = xi(1-s)` that makes the zeros come in
  pairs `rho, 1 - rho` and puts the mirror at `Re(s) = 1/2`. This document explains why that mirror
  *matters*; that one explains why it exists.
- **`zeta/zeros.py`** — the supply side: `first_n_zeros`, `zeros_from_scratch`, and `verify_rh_up_to`,
  which proves — by Turing's method, not by statistics — that every zero below a given height is
  simple and on the line.
- **`zeta/statistics.py`** — one level deeper. §5 treats the zeros as a bag of independent
  frequencies; they are not. Their *spacings* follow the GUE pair-correlation law, which is a
  statement about how the waves in `psi` conspire with each other.
- **`docs/05-de-bruijn-newman.md`** and **`zeta/heatflow.py`** — the frontier: deform `Xi` by
  heat flow and ask when the zeros become real.
