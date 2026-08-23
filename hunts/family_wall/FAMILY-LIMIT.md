# The analytic limit of the n-point pressure family

> Verdict: the family **saturates short**. Its limit is exactly `H = 0.6725007036794116`,
> and its supremum over all n is at most `0.6751676` — against a configuration ceiling of
> `0.6818286874638`. The deficit is `0.0093280` in the limit and at least `0.0066611`
> at the family's best n, which is 71% of the whole distance from `H` to the ceiling.
> The n-point pressure method cannot reach the ceiling, and the obstruction is not a
> numerical accident: it is the identity
> `Phi_n <= H + H c - (n-1)/p`, in which the pressure term cancels exactly against a
> configuration of total length `(n-1)/H`.

Every figure below is labelled **VERIFIED** (recomputed here from first principles, or
matched against a published arbitrary-precision value), **MEASURED** (float optimisation,
an upper bound on an infimum), **DERIVED** (algebra, checked numerically), or
**INFERRED** (extrapolation or model, with the gap stated).

Notation throughout: `k = n - 1` gaps, `q = floor(1/c)`, `m = k + q` the cap,
`theta = 1/c - q` in `[0,1)`, `H = 3/2 - (1/sqrt2) cot(1/sqrt2)`. For a gap vector `g`,
`S(g) = sum g_i` and

    W(g) = sum_{s=1}^{k} (2/(k+1-s)) sum_{i=1}^{k+1-s} w(g_i + ... + g_{i+s-1}),
    F(g,p) = W(g) + S(g)/p.

`W` is the pressure-free part of the functional. Because the coefficient `2/(n-s)` divides
by the number of windows of length `s`, `W` is **twice the sum over s of the mean of w over
windows of length s** — that is, an *energy per point*, not an extensive energy. That single
observation is what makes the whole limit computable.

---

## 0. Reproduction control

The functional was reimplemented here from the definition
(`K(x) = int_{-1/2}^{1/2} cos(sqrt2 t) cos(2 pi x t) dt`, in the closed form
`K(x) = (1/2)[sin(u)/u + sin(v)/v]`, `u = pi x - 1/sqrt2`, `v = pi x + 1/sqrt2`,
`K(0) = sqrt2 sin(1/sqrt2) = 0.9187253698655684`) and evaluated at the three published
argmins:

| n | p | published floor | recomputed | difference |
|---|---|---|---|---|
| 7 | 3400 | 0.003469942585928755 | 0.003469942585928756 | 1e-18 |
| 8 | 3200 | 0.004177322102452557 | 0.004177322102452564 | 7e-18 |
| 9 | 4000 | 0.003927926119847278 | 0.003927926119847276 | 2e-18 |

VERIFIED. The first six positive zeros of `k` recomputed as
1.0572782910088552, 2.030067530128161, 3.0202429921714815, 4.015235607036755,
5.0122084484991545, 6.010182789398035 — VERIFIED, and matching the two zeros the
minimisers are built from.

---

## 1. The lead survives, with one correction

### 1.1 The reduction is exact only when 1/c is an integer

Clearing the cap into the fraction,

    Phi_n = [H m - k (m-1)/p] / (m - c q),     m = k + q,  q = floor(1/c).

Since `c q = 1 - c theta`, the denominator is `m - 1 + c theta`, so

    Phi_n = [H m - k (m-1)/p] / (m - 1 + c theta).                           (DERIVED)

At `theta = 0` this is exactly the lead's `Phi = H m/(m-1) - k/p`. For `theta > 0` the
lead **overstates** `Phi`; because `c q <= 1` always, the lead's form is a rigorous upper
bound on `Phi_n` for every `c`. VERIFIED at the three known peaks:

| n | theta | Phi exact | Phi from the lead | overshoot |
|---|---|---|---|---|
| 7 | 0.189206 | 0.6730297139607 | 0.6730312220417 | +1.508e-6 |
| 8 | 0.387812 | 0.6730536540671 | 0.6730581045108 | +4.450e-6 |
| 9 | 0.587273 | 0.6730713860004 | 0.6730773347280 | +5.949e-6 |

The overshoot is 6% to 31% of the *spacing between adjacent peaks* (2.4e-5 from n=7 to 8,
1.9e-5 from n=8 to 9). **The lead is safe as a bound and safe as a model, but must not be
used to rank adjacent n** — the floor defect is the same size as the effect being ranked.

Separately VERIFIED at all three peaks by exhaustive search over `m` in `[k, k+q]`:
`m` at the cap is the maximiser, so nothing is lost by taking `m = k + floor(1/c)`.

### 1.2 Monotonicity in p inside one minimiser family, in closed form

Within one minimiser family the pair `(W, S)` is essentially constant — recomputed from the
published argmins, `W` varies by less than 4.4e-7 across a family's whole pressure range —
so `c(p) = W + S/p` is a straight line in `1/p`. Writing `gain = Phi - H` and using the
`theta = 0` model,

    gain(c) = H c / (1 + (k-1) c)  -  k (c - W)/S.                            (DERIVED)

This is concave in `c` with a single stationary point

    D* = ( sqrt(H S / k) - 1 ) / (k - 1),      which exists iff  S > k/H.     (DERIVED)

`gain` rises with `p` while `c > D*` and falls while `c < D*`. So **within one family `Phi`
is monotone in `p`, in the direction fixed by the sign of `c - D*`** — the lead was right
that it is monotone, but the direction is family-dependent, and both directions actually
occur in the existing sweep:

| n | family | S | W | H S / k | D* | own stationary p | sweep range | direction |
|---|---|---|---|---|---|---|---|---|
| 7 | 1-2-2-1-2-1 | 9.085068 | 7.97892e-4 | 1.018286 | 1.82029e-3 | 8886 | 2000–3400 | rising |
| 7 | 1-2-2-2-2-1 | 10.083965 | 5.06925e-4 | 1.130246 | 1.262602e-2 | 832 | 3600–6400 | falling |
| 8 | 1-2-1-2-1-2-1 | 10.089202 | 1.025696e-3 | 0.969285 | none (`HS<k`) | — | 2000–3000 | rising |
| 8 | 1-2-2-1-2-2-1 | 11.086837 | 7.12690e-4 | 1.065129 | 5.33954e-3 | 2395 | 3200–4000 | falling |
| 9 | 1-2-1-2-2-1-2-1 | 12.091715 | 9.05026e-4 | 1.016461 | 1.17097e-3 | 45466 | 2400–4000 | rising |
| 9 | 1-2-2-2-1-2-2-1 | 13.089156 | 6.60104e-4 | 1.100308 | 6.99369e-3 | 2067 | 4400–4800 | falling |

MEASURED (`W`, `S` from the published argmins), DERIVED (`D*`, direction). In every case the
family's *own* stationary pressure lies outside the pressure interval on which that family is
the floor. That is the lead's second claim, and it holds.

### 1.3 The optimal pressure is exactly a family crossover — closed form

Two families `(W1,S1)` and `(W2,S2)` exchange the floor at

    p_x = (S2 - S1) / (W1 - W2).                                             (DERIVED)

Evaluated on the sweep's own argmins:

| n | crossover | p_x | sweep bracket | Phi(p_x) | best grid Phi | gain |
|---|---|---|---|---|---|---|
| 7 | 1-2-2-1-2-1 -> 1-2-2-2-2-1 | 3433.0 | 3400 → 3600 | 0.6730299840 | 0.6730297140 | +2.70e-7 |
| 8 | 1-2-1-2-1-2-1 -> 1-2-2-1-2-2-1 | 3187.3 | 3000 → 3200 | 0.6730537132 | 0.6730536541 | +5.91e-8 |
| 9 | 1-2-1-2-2-1-2-1 -> 1-2-2-2-1-2-2-1 | 4072.5 | 4000 → 4400 | 0.6730728477 | 0.6730713860 | +1.46e-6 |

Every predicted `p_x` lands inside the exact grid interval in which the sweep's winning word
changes, and the peak value at `p_x` exceeds the best gridded value. **The lead's peak
condition is confirmed**: the optimum sits at a crossover, not at a stationary point, and the
crossover is given in closed form by the two families' `(W,S)`.

MEASURED. Caveat: `p_x` is computed from `(W,S)` averaged over each family's sweep rows;
the gaps relax slightly with `p`, which moves `p_x` by order 1 in absolute pressure.

### 1.4 What the peak condition *means*

Both `1.2` and `1.3` collapse into one statement. Order the minimiser families by mean gap
`gbar = S/k`. The crossover chosen by the maximisation is the one that brackets

    gbar = 1/H = 1.4869872919 ,

and the peak value is `H` times the **chord** of the (mean gap, energy-per-point) ladder
evaluated at `gbar = 1/H`, damped by `1/(1+(k-1)c)`:

| n | rung below | rung above | chord at 1/H | H x chord | damped model | exact Phi(p_x) - H |
|---|---|---|---|---|---|---|
| 7 | gbar 1.51418, W 7.979e-4 | gbar 1.68066, W 5.069e-4 | 8.454136e-4 | 5.685413e-4 | 5.293273e-4 | 5.292803e-4 |
| 8 | gbar 1.44131, W 1.026e-3 | gbar 1.58383, W 7.127e-4 | 9.253879e-4 | 6.223240e-4 | 5.531845e-4 | 5.530096e-4 |
| 9 | gbar 1.51146, W 9.050e-4 | gbar 1.63614, W 6.601e-4 | 9.531082e-4 | 6.409659e-4 | 5.721765e-4 | 5.721440e-4 |

The damped model reproduces the exact excess to 4.7e-8, 1.7e-7 and 3.3e-8 — the residual is
the `theta` floor defect of section 1.1. DERIVED, checked MEASURED.

So the whole reach of the family above `H` is: *H times the convexified minimal energy per
point of a one-dimensional configuration at density H.* Section 2 turns that sentence into a
bound.

---

## 2. The barrier

### 2.1 The chain

For `k >= 2`, with `c` any valid uniform floor for `F_k` and `m` at the cap:

    Phi_n  =  [H m - k(m-1)/p] / (m - c q)
           <= H m/(m-1) - k/p                            (A)   since c q <= 1
           <= H + H c/(1 + (k-2) c) - k/p                (B)   since m-1 = k-1+q >= k-2+1/c
           <= H + H c - k/p                              (C)
           <= H + H W(g) + (H S(g) - k)/p                (D)   since c <= F(g,p) for all g >= 0

Step (A) needs the numerator nonnegative; when it is negative `Phi_n < 0` and every bound
holds trivially. Step (D) holds **for every nonnegative gap vector `g`**, because `c` must be
a floor for `F_k` everywhere, hence at `g`.

VERIFIED: the four inequalities were evaluated on all 36 rows of the existing n=7,8,9 sweep
using each row's own argmin as `g`. Zero violations.

### 2.2 Two consequences, and the barrier they make

**(i) The trivial leg.** For `m >= k`, `H m/(m-1) <= H k/(k-1)` and `-k/p < 0`. For
`1 <= m < k` the denominator `1 - c(1-k/m) = 1 + c(k/m - 1) >= 1` while the numerator is at
most `H`, so `Phi_n <= H` there. Either way

    Phi_n  <=  H (n-1)/(n-2)      for every n >= 3 and every m >= 1.         (DERIVED)

This alone is already below the ceiling from `n = 75` onward: `H*74/73 = 0.6818409912`
is above `0.6818286874638`, and `H*75/74 = 0.6817130421` is below. VERIFIED.

VERIFIED separately, at five `(n, p, c)` triples including `n = 20`: maximising `Phi` over
the whole range `m in [1, k+floor(1/c)]` puts the maximiser at the cap every time, and every
`m < k` gives `Phi < H`. So taking `m` at the cap loses nothing, and the `m < k` branch is
never the one that matters.

**(ii) The witness leg.** In (D), choose `g` with `S(g) <= k/H`. Then `H S(g) - k <= 0`, the
pressure term is nonpositive for every `p`, and

    Phi_n  <=  H (1 + W(g))      for every gap vector g with sum(g) <= (n-1)/H.   (DERIVED)

This is the heart of it. The pressure `p` is the family's only free dial for buying gain, and
a configuration of total length exactly `(n-1)/H` makes the dial cancel itself. What is left
is `H` times an energy per point at density `H` — a quantity of order `10^-3`, while reaching
the ceiling would need

    W(g) >= (0.6818286874638 / H) - 1 = 0.0138706 ,

an order of magnitude more, for *every* admissible `g` simultaneously. It is not close.

**(iii) The sharp form.** Using (B) instead of (C), and any finite set of witnesses `g_j`
(`c <= min_j F(g_j, p)` pointwise),

    Phi_n  <=  H + max_{p>0} min_j [ H c_j(p)/(1 + (k-2) c_j(p)) - k/p ],  c_j(p)=W_j+S_j/p.

Rigorous whatever the witnesses are; better witnesses only tighten it.

### 2.3 The numbers

Witness ladder used for (iii): for each `j = 0..k`, the balanced (Sturmian) word with `j`
long letters among `k`, its total length scaled by 0.90, 0.94, 0.97, 1.00, 1.03, 1.06, 1.10,
and `W` minimised at that fixed length by SLSQP. `7(k+1)` witnesses per `n`.

| n | sharp bound (iii) | best measured Phi_n | headroom | ceiling minus bound |
|---|---|---|---|---|
| 3 | 0.6730263561 | — | — | +0.0088023 |
| 5 | 0.6735202493 | — | — | +0.0083084 |
| 7 | 0.6732471047 | 0.6730299840 | 2.17e-4 | +0.0085816 |
| 8 | 0.6731728344 | 0.6730537132 | 1.19e-4 | +0.0086559 |
| 9 | 0.6731887414 | 0.6730728477 | 1.16e-4 | +0.0086399 |
| 10 | 0.6733940587 | 0.6730802503 | 3.14e-4 | +0.0084346 |
| 14 | 0.6731493536 | 0.6730911872 | 5.82e-5 | +0.0086793 |
| 15 | 0.6731332649 | — | — | +0.0086954 |
| 20 | 0.6731099910 | 0.6730928938 | 1.71e-5 | +0.0087187 |
| 25 | 0.6730765652 | — | — | +0.0087521 |
| 30 | 0.6730523698 | — | — | +0.0087763 |
| 35 | 0.6730051199 | — | — | +0.0088236 |

MEASURED (the bound is rigorous given the witnesses; the witnesses are explicit and the
`W` values are ordinary floating-point evaluations of a finite sum).

For larger `n` a single tiled witness suffices, with no optimisation in the loop: take the
`k = 27` constrained minimiser as a period, tile it, rescale to total length `k/H`, and
evaluate `W`. At **every** `k` from 35 to 400 — not a sample, every integer — this gives a
bound whose worst value is **0.6751676068** (at `k = 55`, i.e. `n = 56`); for `k >= 401` the
trivial leg alone gives `H*400/399 = 0.6741861691`. MEASURED.

(Restricting the tiling to `k >= 74` the worst is `0.6749544944`, at `k = 82`. Running the
section-2.3 envelope over `37 <= n <= 74` as well — it was run to `n = 51` here and every
value came in under `0.67310` — would replace the 0.6751676 figure by that one. The number
quoted below is the one that holds without that extension, so it stands on the tiled witness
alone over `36 <= n <= 401`.)

### 2.4 The barrier, stated

**Every n is covered, with no gaps:**

| range | instrument | bound |
|---|---|---|
| n = 3 .. 36 | sharp witness envelope (iii), computed at every n | max 0.6735202493 (at n=5) |
| n = 36 .. 401 | tiled explicit witness (ii), computed at every n | max 0.6751676068 (at n=56) |
| n >= 402 | trivial leg (i) | max 0.6741861691 |

    sup_n Phi_n  <=  0.6751676068  <  0.6818286874638 = the configuration ceiling.

**Deficit at the family's best: at least 0.0066611** — 71% of the whole distance from `H`
to the ceiling.

This is a **BARRIER**. The n-point pressure certificate family, at any n and any pressure
and with any valid floor `c`, cannot reach the configuration ceiling. Increasing `n` does not
help; the family's own supremum is short by more than 0.0066, which is 71% of the whole
distance from `H` to the ceiling.

### 2.5 The limit

Upper: `Phi_n <= H(n-1)/(n-2) -> H`.
Lower: for any `n`, sending `p -> infinity` sends the floor `c*(p) -> 0`, hence `m -> infinity`,
`H m/(m-1) -> H` and `k/p -> 0`; so `sup_p Phi_n >= H` for every `n`.

    lim_{n -> infinity} Phi_n  =  H  =  0.6725007036794116     (DERIVED, exact)

There is **no uncertainty in `Phi_inf`**: it is the constant `H` itself, not an estimate.
The family does not merely stall below the ceiling — it climbs a little, turns over, and
comes back down to `H`. The measured climb from n=7 to n=9 (+4.3e-5) is the front edge of a
bump of total height at most `0.6751676 - H = 0.0026669`, on a curve that ends at `H`.
The measured climb so far, best floor of the two independent searches at each pressure:
`0.6730300` (n=7), `0.6730537` (n=8), `0.6730728` (n=9), `0.6730803` (n=10),
`0.6730912` (n=14), `0.6730929` (n=20) — increments `2.4e-5, 1.9e-5, 7.5e-6, 1.1e-5, 1.7e-6`
against a grid that gets coarser relative to the peak as `n` grows, so each is a lower bound
on that `n`'s true peak.

The rate of the decay is `Phi_n - H <= H/(n-2)`, which is the trivial leg; the *actual*
decay is faster, because the witness envelope in 2.3 already falls below `H/(n-2)` from
`n = 7` on. INFERRED: from the envelope's behaviour the excess appears to decay like
`C/n` with `C` of order `10^-2`, but the constant is not pinned here.

### 2.6 Why `W` stays of order 1e-3: the infinite-chain energy, exactly

The witness bound is only decisive because the minimal `W` at density `H` is small but
bounded away from anything like `0.0139`. That quantity has an exact form. Write
`f(t) = cos(sqrt2 t) 1_{[-1/2,1/2]}(t)`, so `K = Fourier transform of f` and
`w = FT(G)/K(0)^2` with `G = f * f` supported on `[-1,1]`:

    G(u) = (1-|u|) cos(sqrt2 u)/2 + sin(sqrt2 (1-|u|))/(2 sqrt2),   |u| <= 1,  else 0.

Poisson summation over a period-`T` lattice therefore terminates at a **finite** Fourier
order — only `|nu| <= T` survives, because `G(nu/T) = 0` beyond that — and the energy per
particle of an infinite configuration with `P` points per period is

    W_inf = (1/(P T K(0)^2)) sum_{|nu| <= T} G(nu/T) |sum_j exp(-2 pi i nu x_j / T)|^2  -  1.

DERIVED. VERIFIED against a brute-force lattice sum over 800001 images: agreement `7.9e-9`,
which is the brute force's own truncation error, not the formula's.

Minimising this over `P <= 6` and the positions gives the `W_inf(gbar)` curve in
`artifacts/periodic-energy-curve.json`. It is violently non-monotone in `gbar` — commensurability
with the kernel zeros — which is exactly why the finite-`n` ladder's convex envelope, not the
curve itself, is what section 1.4 evaluates at `gbar = 1/H`. MEASURED, and an upper bound on
the true minimum since the period is capped at 6.

The finite-`n` `W` values are substantially *below* the infinite-chain ones (7.98e-4 at
`k = 6, gbar = 1.514` against 4.37e-3 for the corresponding infinite chain), because
`W_k` truncates the sum over window lengths at `s = k`. That is a real finite-size effect,
not a numerical discrepancy, and it is the reason the measured peaks rise with `n` at all:
`W_k` grows toward `W_inf` while the `k/p` charge and the `1/(1+(k-1)c)` damping grow too,
and the second pair eventually wins. INFERRED as the mechanism; the two rigorous legs of
section 2.2 are what actually bound the outcome.

---

## 3. Independent numerical check

`modal_family_limit.py` re-derives the floor by multistart global minimisation, independently
of any prediction in this file, at `n = 7, 10, 14, 20` over a wide pressure grid
`1200 .. 20000` (the existing sweep only covers 2000..6400, so this also tests whether the
peak leaves that window at larger n). Control: `n = 7, p = 3000` must return the published
arbitrary-precision floor `0.0038262312115073`.

`modal_family_limit.py` re-derives the floor by multistart global minimisation, independently
of any prediction in this file, at `n = 7, 10, 14, 20` over the pressure grid
`1200, 1800, 2600, 3000, 3400, 4400, 6000, 8500, 13000, 20000` (the existing sweep covers only
2000..6400, so this also tests whether the peak leaves that window at larger n). 320 cells,
8 shards per cell, 2 CPU each; well inside the compute budget.

**Control passed.** `n = 7, p = 3000` returned `0.0038262312113044716` against the published
arbitrary-precision floor `0.0038262312115073` — agreement to `2.0e-13`. VERIFIED.

**Agreement with the predicted floors.** The prediction under test is
`c_pred(p) = min_j [W_j + S_j/p]` over this file's witness ladder, which by construction is an
*upper* bound on the true floor. At `n = 7, 10, 14` the Modal search came in below the
prediction at every one of the thirty pressures, by `4.5e-6` to `4.2e-4` — the prediction is
valid as a bound and loose by the expected amount (the ladder is Sturmian and balanced; the
true minimisers relax off it).

**Disagreement at n = 20, and it goes the informative way.** At `n = 20` and
`p = 3400, 4400, 6000, 8500` the *ladder* came in **below** Modal, by up to `2.4e-4`:

| n | p | Modal floor | ladder floor | ladder minus Modal |
|---|---|---|---|---|
| 20 | 3400 | 0.0095045403 | 0.0094228403 | -8.17e-5 |
| 20 | 4400 | 0.0077967045 | 0.0076104882 | -1.86e-4 |
| 20 | 6000 | 0.0062095306 | 0.0059672889 | -2.42e-4 |
| 20 | 8500 | 0.0046292979 | 0.0045500172 | -7.93e-5 |

At `k = 19` the Modal job could only enumerate 16000 of the `2^19` two-letter words per
shard, and its multistart missed basins the ladder reaches directly. Modal's raw
`Phi_20 = 0.6731391381` is therefore built on a floor that is not a floor, and is not a
valid certificate value; with the better of the two searches at each pressure the n=20 peak
is `0.6730928938` at `p = 8500`. **That correction matters**: the raw Modal number sits
*above* this file's envelope bound for n=20 (0.6731099910), and the corrected one sits below
it. The apparent violation was a search failure, and the bound caught it — which is exactly
the use a bound of this kind has.

**Peaks, best floor of the two searches at each pressure** (MEASURED; grid-limited, so each
is a lower bound on that n's true peak):

| n | best floor | p | Phi_n | envelope bound at that n |
|---|---|---|---|---|
| 7 | 0.0034699426 | 3400 | 0.6730297140 | 0.6732471047 |
| 10 | 0.0040292603 | 4400 | 0.6730802503 | 0.6733940587 |
| 14 | 0.0043128406 | 6000 | 0.6730911872 | 0.6731493536 |
| 20 | 0.0045500172 | 8500 | 0.6730928938 | 0.6731099910 |

Every measured value lies below the corresponding bound. The climb continues past n=9 but is
decelerating hard: +5.1e-5 from n=7 to 10, +1.1e-5 from 10 to 14, +1.7e-6 from 14 to 20. INFERRED
from that deceleration and from the bounds above it: the bump tops out in the low
`0.67310`s. Not pinned; the envelope bound is what is rigorous here, and it is `0.6751676`.

Artifacts: `artifacts/family-limit-modal.json`, `artifacts/compare.json`.

---

## 4. What would refute this

The claims here fail if any of the following is exhibited.

1. **A configuration below a claimed floor.** The witness bound (ii) is only as good as the
   arithmetic in `W(g)`. Exhibit a `g` with `sum(g) <= (n-1)/H` whose `W(g)` this file reports
   too high — the bound then moves, though in the *safe* direction (a smaller `W` makes the
   barrier stronger, never weaker). The dangerous direction is the opposite: if `W(g)` is
   reported too *low*, the bound is invalid. Recompute `W` in interval arithmetic to close
   this; the sum is finite and exactly the kind of thing Arb settles.
2. **A failure of the chain.** Steps (A)–(D) are elementary but they rest on `m` being capped
   at `k + floor(1/c)` and on `c` being a floor for `F_k` on *all* nonnegative gap vectors.
   If the proved theorem admits an `m` above that cap, or admits an `c` valid only on a
   restricted set of gap vectors, (A) and (D) respectively fail and the barrier goes with them.
   This is the single load-bearing assumption and it should be checked against `n_point_bound`
   line by line.
3. **A direct minimisation returning `Phi_n` above the barrier.** Any `(n, p, g)` with the
   resulting `Phi_n > 0.6751676` refutes section 2.4 outright. The Modal job in section 3 is
   exactly this test, run at four values of `n` and ten pressures; a wider or deeper run is
   the cheapest way to attack the claim.
4. **A different `n`-dependence in the theorem.** Everything here is driven by the two
   `n`-dependent pieces `(n-1)(m-1)/(pm)` and the cap `m <= (n-1)+floor(1/c)`. A variant of
   the certificate with a cap growing faster than `floor(1/c)`, or with the pressure term
   charging less than `(n-1)/p`, breaks the cancellation in (ii) and would have to be
   re-analysed from scratch. The barrier is a statement about *this* family, not about
   pressure certificates in general.
5. **The exact-arithmetic tail.** All optimisation here is float. The floors are upper bounds
   on infima, so the `Phi` values built from them are *optimistic*; that direction is safe for
   the barrier (a true floor is lower, so the true `Phi` is lower). But the `W` values used as
   *witnesses* are also float, and there the safe direction is the other one. The margin is
   0.0066 against float errors of order 1e-12, so this is not a live risk — but it is the
   right thing to certify if the barrier is ever leaned on.

## 5. What is not claimed

- No claim that `H` is the limit of any *other* certificate family. Section 2 is about the
  formula in `n_point_bound` and nothing else.
- No claim about how to *reach* the configuration ceiling. This file says one route does not,
  and says why. It proposes no replacement.
- No claim of exact-arithmetic status for any number in this file. Everything is float, with
  the reproduction control of section 0 and the direction-of-error analysis of section 4.5.
- The `n = 10 .. 16` sweep running in parallel is a different measurement and is not
  duplicated or pre-empted here; its measured peaks should land below the section-2.3 bounds
  at the same `n`, which is a further check on both.
