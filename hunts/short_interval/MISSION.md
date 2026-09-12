# Mission: the bandwidth dial was physical all along

**Opened 2026-09-12.** Nothing in this directory is a result. Nothing here
bears on RH (`docs/08-why-it-is-hard.md`).

Read `CLAUDE.md` and `ALIGNMENT.md` first. Then read §3, §4 and §5, which are
three findings established on the day the hunt opened, before any compute was
spent, and which between them killed the plan the hunt was opened for and
reordered everything else. The live routes are §6 and §7, ranked; §8 is a priced door that the literature shuts.

```huntspec
id: short_interval
question: Wang's short-interval bound is the laboratory's own bandwidth landscape evaluated at lambda = theta. Given that, what does this tree hold on that axis that nobody else does, and what is the band edge worth?
frontier: the zeta landscape 2 - lambda/2 - (1/sqrt 2) cot(lambda/sqrt 2) is already computed in hunts/frontier_map/frontier.py from the source paper's eq. (7.4), agrees with Wang's c(theta) to 1e-16 and dies at 0.5501939647441547; the xi-prime landscape is computed on the same grid, sits 0.11 to 0.20 higher at every bandwidth, dies at 0.51332, and has no short-interval counterpart in the literature; the bandwidth-one configuration ceiling is 0.6818286874638 against a window optimum of 0.6725007036794116, and the bandwidth-theta ceiling is computed nowhere
proposed_attack: the gate passed, so write the short-interval xi-prime theorem along the eight-step outline in AUDIT-dyadic.md section 6, localizing the kernel-checked xi-prime second moment by Wang's Montgomery-Vaughan and grid-end arguments, with the bandwidth-theta constants enclosed by ball arithmetic before any number is stated; the bandwidth-theta configuration ceiling needs the PairCeiling construction rebuilt with the band as a parameter, since the measure-level LP in this tree reproduces the window optimum and not the ceiling
dead_routes:
  - substituting c(theta) into the affine bridges Phi_3 and Phi_4: the certificate's cost is proportional to the second moment, which diverges like 1/theta, so the gain is negative below theta 0.808 and no re-optimization repairs it; the bridges are also band-width-one and dyadic (section 4)
  - re-optimizing the certificate's window shape at each bandwidth: measured worth about lambda^3/180, and at the vacuity threshold the whole optimal-versus-flat advantage is 3.2e-4 (section 5)
  - deriving the closed form of the landscape as new work: it is the source paper's eq. (7.4), already in the tree, and independently Wang's Proposition 4.1
  - proving the landscape optimal at bandwidth theta: Wang's Proposition 4.1 already is that statement, since the Euler-Lagrange condition differentiates to f'' + 2f = 0 at every interval length
  - converting out-of-band POSITIVITY into an unconditional certificate: closed by hunt #118 on 2026-09-06; positivity is a lower bound on F and this method needs an upper one, so it is wrong-signed information
  - closing the cycle_moments quartic route on second and third moments alone: a matched finite fourth-moment bound is required and is not established
  - buying bandwidth beyond one with an upper bound on F past the band edge: priced in section 8 and closed by literature search the same day; the only T-independent bounds are RH-conditional integrated bounds that tend to 7/8 rather than to zero as the sliver shrinks, because delta spikes in F beyond the band cannot be ruled out, and the sieve route is blocked by parity at second order
required_oracles:
  - the published statements of arXiv:2609.07918 and arXiv:2609.02882, read directly
  - Alpoge-Furman Remark 7.1's two published xi-prime figures, as the calibration for any F_1 landscape computed here
  - independent numerical solve of the window variational problem by a discretization not shared with the closed form it checks, with the zeta control run at the same settings so method error is visible
  - interval or ball arithmetic for any constant entering a claimed inequality
  - Lean 4 kernel with zero sorrys, for anything stated as a theorem
kill_conditions:
  - the xi-prime derivation's deterministic corrections turn out to have been established by a dyadic average that does not survive a T^theta block: CHECKED 2026-09-12 and did not fire, the corrections enter through a range-free arithmetic identity, see AUDIT-dyadic.md
  - the bandwidth-theta configuration ceiling collapses onto the landscape, leaving no room for any certificate: NOT TESTABLE with any instrument in this tree, the measure-level LP measures the window optimum and the PairCeiling certificate is not public, see section 7
  - the n-point family rebuilt at bandwidth theta does not exceed the landscape anywhere in (0.5501939647441547, 1)
  - no unconditional constant upper bound on F beyond the band is reachable: FIRED 2026-09-12 on literature search, section 8
agents_may:
  - search
  - derive
  - code
  - measure
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - edit zeta/, ontology/ or harness/
  - claim the reserved word
```

## 1. Why this hunt exists

Biao Wang (Yunnan University) posted arXiv:2609.07918 on 2026-09-07: zeros in
`(T, T + T^theta]` are simple and on the critical line in proportion at least
`c(theta)`, and distinct in proportion at least `d(theta) = (1 + c(theta))/2`,
unconditionally, for every fixed `0 < theta < 1`. The laboratory did not
notice for five days and then heard about it from a stranger's email. The
companion brief `meta/literature-monitor.md` covers that half.

Provenance, because this tree is in it: an internal research version of Claude
produced the original argument, Alpöge and Furman verified and published it
(arXiv:2608.13637), Lamzouri reproved it more simply (arXiv:2609.02882),
Wang extended it to short intervals. This tree's `Phi_3` and `Phi_4` are built
on `anthropics/zeta-23-lean`, which is arXiv:2608.13637.

## 2. What the papers prove

**Wang, Theorem 1.1.** Unconditional, fixed `0 < theta < 1`, on
`I = (T, T + T^theta]`:

    liminf N_0^s(I)/N(I) >= c(theta) = 2 - theta/2 - (1/sqrt 2) cot(theta/sqrt 2)
    liminf N^d(I)/N(I)   >= d(theta) = (1 + c(theta))/2

`c` strictly increasing with `c'(theta) = (1/2) cot^2(theta/sqrt 2)`, zero at
`theta_0 = 0.550193964744154`; `d` zero at `theta_d = 0.346658926139761`.
`theta = 1` is **not** in the stated range; the global constants are the
`theta -> 1^-` limits.

**Wang, Theorem 2.2**, the actual technical contribution. For fixed
`0 < lambda < theta < 1` and `g` real, even, `C_c^infinity`, `supp g` in
`[-lambda, lambda]`:

    sum_{gamma, gamma' in I} ghat(i(rho - rho')L/2pi) w(rho - rho')
        = (HL/2pi)(g(0) + integral |alpha| g(alpha) dalpha) + O_g(H + T^lambda L^2)

`w(z) = 4/(4 - z^2)`, `H = T^theta`, `L = log T`. Unconditional. The
counterpart of Lemma 5 of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh (Acta Arith. 214 (2024), arXiv:2306.04799), built from
their Lemmas 1, 3 and 4. **The error is `o(HL)` precisely because
`lambda < theta`**, and the proof of Theorem 1.1 closes by letting
`lambda -> theta`. So the bandwidth available in a short interval of exponent
theta is theta, and the band is the open interval `(-theta, theta)`.

**Wang, Proposition 4.1.** Over real `f` in `L^2(J)` with `integral_J f = 1`,
`J = [-lambda/2, lambda/2]`, the functional
`C(f) = integral f^2 + double-integral |u - v| f f` has unique minimizer
`f_lambda(u) = cos(sqrt 2 u)/(sqrt 2 sin(lambda/sqrt 2))` and minimum
`C_lambda = lambda/2 + (1/sqrt 2) cot(lambda/sqrt 2)`, so `c = 2 - C_theta`.
Uniqueness by Dirichlet-Poincaré. The Euler-Lagrange condition is
`f(u) + integral_J |u - v| f(v) dv = const`, differentiating to
`f'' + 2f = 0`, **at every interval length**. That last clause matters: it
means Proposition 4.1 already is the bandwidth-theta optimality statement, so
the method class "Lamzouri's inequality plus in-band pair correlation" is
capped at `c(theta)` for every theta, and there is nothing to prove there.

**Lamzouri, Proposition 2.1.** For `Z` a finite conjugation-invariant
multiset and `K = Fourier(eta^2)` with `eta` real, even, supported in
`(-lambda, lambda)`, `K(0) = 1`: simple real elements at least
`2|Z| - sum K(z-s)^2`, distinct at least `(3/2)|Z| - (1/2) sum K(z-s)^2`.
**No positivity hypothesis on `K`** and, importantly for §8, **no cap on
`lambda`**. The cap lives entirely in the analytic input. The window density
is `f = eta^2` and is therefore nonnegative, which §8 depends on.

## 3. Finding one: Wang's curve is already in this tree

**Measured, agreement to 1e-16.** `hunts/frontier_map/frontier.py` computes
the unconditional proportion as a function of bandwidth, from the source
paper's eq. (7.4):

```python
def zeta_H_closed(lam):
    theta = lam / math.sqrt(2.0)
    t = math.tan(theta)
    c = math.sqrt(2.0) * t / (1.0 + theta * t)
    return 2.0 - 1.0 / c
```

Since `(1 + t tan t)/(sqrt 2 tan t) = (1/sqrt 2) cot(lambda/sqrt 2) + lambda/2`,
this **is** `c(lambda)`. It agrees with Wang at every bandwidth tested and
crosses zero at `0.5501939647441547`, his `theta_0` to every digit he prints.
The same module computes `Hd = (1 + H)/2`, his `d(theta)`. **Both constants in
Wang's Theorem 1.1 were already being computed here.**

**So what Wang adds is that the dial is physical.** `frontier.py` records
bandwidth as "exactly one dial, lambda, capped at 1 by the Rudnick-Sarnak /
Montgomery support restriction", and notes the source paper's remark that "the
certificate is empty for lambda <= 1/2". The tree held the low-bandwidth
regime as a hypothetical, because the whole game was pushing the dial up.
Theorem 2.2 says bandwidth theta is exactly what counting in an interval of
length `T^theta` buys. The lab's dial and Wang's exponent are the same number,
so the landscape's interior carries an unconditional theorem.

That is a reading of existing material, not a new result. State it that way.

## 4. Finding two: the transplant is dead, and the reason is the second moment

Substituting `c(theta)` for `H` in the two kernel-checked bridges fails, and
the sharp diagnosis is not the one an earlier draft of this file gave.

Rewrite `Phi_3` in the coordinate the problem is actually affine in,
`R = 2 - c`, which is the normalized second moment `C_theta`:

    R -> 1.001343 R - 0.002019

The certificate buys a fixed absolute `0.002019` and pays a **relative
0.134% of whatever second moment it consumes**. Since
`R(theta) = C_theta = 1/theta + theta/3 - theta^3/180 - ...` diverges like
`1/theta`, the proportional penalty grows without bound while the gain stays
fixed. Break-even is at `R = 1.5037`, that is `theta = 0.8082`. So the
overhead is intrinsic in the worst possible way: **it is proportional to the
one quantity that blows up in a short window.**

The cheapest kill, and the thing to do if anyone wants to revisit this:
locate the single step in the `Phi_3` derivation whose loss is a multiple of
the input rather than an additive constant. If it is a truncation tail bounded
by a fraction of the second moment, the transplant is dead at every
`theta < 0.81` and no re-optimization rescues it.

Independently, the transplant has no analytic footing at all, for two
reasons. **The band is `(-theta, theta)`, open and strict**, so a certificate
needing the band edge cannot take the endpoint even in a limit without care;
the bridges read `[-1, 1]`, and `hunts/family_wall/famlib.py` holds `H` as a
module constant with a kernel that is the closed form of
`integral_{-1/2}^{1/2} cos(sqrt 2 t) cos(2 pi x t) dt` with no free
half-length. **And the bridges are dyadic**: 21 occurrences of `2 * T` in
`Bridge/Main.lean` alone, with `S8` concluding in `N(T, 2T)`, `S9` absorbing
deleted end strips of width `2 pi L` against it, and `S15`'s span bound being
`LT/2pi = N(T,2T) + o(N(T,2T))`. A per-block error absorbed against
`N(T,2T)` and reappearing against `HL = T^theta log T` **carries a hidden
`T^(1-theta)`**. Check that before anything else on any route here.

## 5. Finding three: window shape is worth nothing in a short interval, so there is nothing to re-optimize

**Measured; `landscape.py` reproduces all of it.** Substituting
`v(u) = phi(u/lambda)` into the laboratory's functional gives

    R(lambda, phi) = A(phi)/lambda + lambda B(phi),
    A = integral phi^2/(integral phi)^2,
    B = double-integral |u-v| phi phi/(integral phi)^2

and `A >= 1` by Cauchy-Schwarz with equality iff `phi` is constant. So the
`1/lambda` cost is a pure L2-against-L1 defect of the window and the only way
to cheapen it is to be flat. The flat window gives `R = 1/lambda + lambda/3`
exactly, verified, whose threshold is the root of `theta^2 - 6 theta + 3`,
that is `3 - sqrt 6 = 0.5505102572`.

Against Wang's optimal-window `theta_0 = 0.5501939647`, **the entire value of
the Montgomery-Taylor window over a flat one is 3.2e-4 of threshold**, and the
flat-minus-optimal gap is about `lambda^3/180` (measured `0.00122` at
`lambda = 0.6` against `0.00120`; `0.00583` at `lambda = 1` against
`0.00556`). The optimal window flattens as the bandwidth shrinks.

Be precise about what that does and does not say. At full bandwidth the flat
window gives `2 - 4/3 = 0.6667` and the optimal one `0.6725`; that `0.0058` is
**exactly the Montgomery-Taylor improvement over Montgomery's two thirds**, so
at bandwidth one the window shape is the whole famous step. The point is that
its worth decays as bandwidth cubed, so it is the full-range game and not the
short-interval one.

Consequence, and it kills a recommendation an earlier draft of this file made:
at `theta = 0.55` the whole window-shape game is worth about `9e-4`, and an
n-point family whose bandwidth-one share of it is `2.4e-4` is worth roughly
`4e-5`. **There is nothing to re-optimize. Wang's `c(theta)` already is the
re-optimization.**

## 6. Route one: the xi-prime arm, and the search that says it is open

**The best bet here, and the only place the tree holds something the field
does not. A literature search was run on 2026-09-12 and is recorded in
`RESULTS.md` §4; its verdict and its one near-miss are below.**

`hunts/frontier_map/frontier.py` computes the landscape for **two** kernels:
Montgomery's `F(x) = |x|` for zeta, and Farmer-Gonek-Lee's

    F_1(x) = |x| - 4x^2 + sum_{k>=1} ((k-1)!/(2k)!) (2|x|)^(2k+1)

for `xi'`, which is this tree's own line of work. **Wang does only zeta.** His
paper contains no derivative of any kind.

Measured in `landscape.py`, with the `F_1` implementation calibrated against
**two published figures** from Alpöge-Furman Remark 7.1 (flat window at
bandwidth 1 giving `0.858384` against their `0.85838`, and `0.929192`
against their `0.92919`), so a mis-transcribed series would have been caught:

| bandwidth | zeta | xi-prime | difference |
|---|---|---|---|
| 1.00 | +0.672513 | +0.868660 | +0.1961 |
| 0.80 | +0.486277 | +0.682554 | +0.1963 |
| 0.60 | +0.134562 | +0.281718 | +0.1472 |
| 0.55 | -0.000570 | +0.130262 | +0.1308 |
| 0.50 | -0.165957 | -0.052054 | +0.1139 |

**Vacuity thresholds: zeta `0.55019`, xi-prime `0.51332`.** The zeta control
at the same settings is off by `+1.2e-5` from a value known exactly, which is
the error bar on every `xi'` figure above; the `xi'` solve's `0.868660`
against the laboratory's quartic-certificate `0.8686415005` is a `+1.9e-5`
gap that is **method error, not a free gain**, and the control proves it.

### 6.1 What the literature holds (searched 2026-09-12)

Thirty-four query strings, four citation-graph lookups, and about twenty-five
papers opened; the full log is in `RESULTS.md` §4. **Verdict: no paper states
a proportion of simple, or critical, zeros of `xi'` (or of any `xi^(k)` or
`zeta^(k)`) in `(T, T + T^theta]` as a function of theta, conditional or
unconditional.** Specifically:

- Farmer, Gonek and Lee (JLMS 90 (2014), arXiv:0803.0425) assume RH
  throughout, state `F_1` for the cumulative range `0 < gamma <= T` only, and
  mention short intervals once, in a bibliography entry. Semantic Scholar
  lists nineteen papers citing them; none concerns short intervals for `xi'`.
- Alpöge-Furman's `xi'` result is Remark 7.1 (the lab's own
  `hunts/wide_search/RESULTS-xiprime.md` says 7.3, which is the subsection it
  sits under; see §11), is dyadic `(T, 2T)`, and cites Farmer-Gonek-Lee only
  as the RH-conditional comparator, never as an input.
- Chirre, Gonçalves and de Laat (arXiv:1810.08843, Corollary 7) give `0.8825`
  simple and `0.9412` distinct for `xi'` **under RH**, full range. Any
  conditional short-interval `xi'` curve is compared against that at
  `theta -> 1`.
- Of the 191 `math.NT` listings from 2026-09-05 to 2026-09-12, Wang's is the
  only short-interval zero paper and none concerns derivatives. Semantic
  Scholar reports zero citations of Wang and one of Lamzouri (Wang).

**The near-miss that fixes the wording.** Conrey (JNT 17 (1983), as restated
by Rezvyakova) and Rezvyakova (Izv. Math. 69 (2005) and 70 (2006)) already
work in **sub-dyadic windows** `(T, T + U]` with `U = T (log(T/2 pi))^(-10)`:
on-line proportion of `xi^(k)` zeros above `1 - (3/5) k^(-2)`, and
**simple on-line proportion above `1 - ((e^2 + 2)/16) k^(-2)`**, uniformly in
`k` up to `(1/2) log log T / log log log T`. At `k = 1` that is about `0.413`.
So "first short-interval statement for `xi'`" would be **false**. The correct
claim, if the route succeeds, is **"first power-length statement, `T^theta`
with `theta < 1`, and first as a function of theta"**, with Rezvyakova's
`0.413` in log-power windows and Conrey's `0.79874` at full range as the
comparanda. Write it that way from the start.

Also absent, and worth knowing: Steuding (Acta Math. Hungar. 96 (2002)) and
Karatsuba (1984) give positive proportions of simple critical zeros
(`H >= T^0.552`) and odd-order zeros (`H >= T^(27/82+eps)`) of **zeta** in
power-length intervals by Levinson and Selberg methods, with no explicit
theta-curve; no Levinson-method `xi'` analogue in short intervals was found.
Ki and Lee (2012) and Das and Pujahari (arXiv:2104.10243) treat `zeta^(k)` in
`(T, T + T^a]`, `a > 1/2`, but only horizontal-distribution sums, not on-line
or simple proportions.

### 6.2 The gate, run 2026-09-12: passed with conditions

The audit is `AUDIT-dyadic.md` in this directory, kept verbatim. It read
every statement the headline theorem `xiDeriv_simple_on_line` depends on in
`anthropics/formal-math` at commit `fbdc36bb`, listed every place the dyadic
range enters (35 proof steps, 10 interface statements, 7 definitions),
classified each, and compared each against how Wang localized the same step
for zeta. **Verdict: PASS WITH CONDITIONS. No step uses the dyadic structure
to produce a main term.** Every use is cosmetic or an error absorption with a
named exponent, and the hidden `T^(1-theta)` this brief warned about lives in
exactly two places, both of which are the conditions below rather than
obstructions.

**A correction to the way this brief framed the route.** An earlier draft
said Wang's Theorem 2.2 supplies the arithmetic `|x|` term of `F_1` on the
narrowed band and the rest is a deterministic transfer from zeta zeros. That
is not how the kernel-checked development is built. **It uses no zeta
pair-correlation input and no transfer at all.** It treats the zeros of `xi'`
directly, with its own explicit formula (`XiEF`), its own second moment
(`CoeffMoments`), its own zero count, and the density
`D_1(s) = s - 4s^2 + sum d_k s^(2k+3)` enters through one range-free
arithmetic identity, hypothesis (H3), where the `s` and the corrections are
one object. So Wang's Theorem 2.2 is the **template** for the localization,
not an input to it: the `xi'` second moment must itself be localized, by
Wang's Montgomery-Vaughan and grid-end arguments, and the audit shows every
one of those steps has an exact counterpart that localizes for the same
reason. Write the paper as "localization of the kernel-checked `xi'` second
moment along Wang's route".

**The hazard this brief named is refuted.** The corrections in `D_1` reach
the certificate only through (H3), an arithmetic identity for
`sum_{N <= e^y} |C(N; L_T)|^2 / N` whose only `T`-dependence is the scalar
`l(T)` inside `L_T`. No height average, no interval, no `2T` anywhere under
`Coeff/`. They carry no hidden factor.

**The seven conditions**, each with what it costs:

1. **Bandwidth `lambda < theta`.** Wang's own condition, appearing in seven
   places through one mechanism, the Montgomery-Vaughan and grid-end
   remainders of size `l^4 X`, absorbed against `H l` iff `lambda < theta`.
   Theorem at every fixed `lambda < theta`, constant by `lambda -> theta`
   via continuity of `kappaXi`, exactly as the tree does at 1.
2. **End strips.** With the padding `D0 = sqrt T` the surrendered strips cost
   `sqrt T log T`, absorbed iff `theta > 1/2`; free in the whole range
   `theta > 0.51332`. Or take `D0 = T^beta` with `lambda/4 < beta < theta`,
   which changes one frozen constant.
3. **Short-window zero count.** `N_xi'(T, T+H) = H L/2pi + O(H + log T)` is
   not stated in the tree, but every intermediate is: the half-contour
   identity at good heights, the `Y` bound, the gamma side, the local count.
   Two new lemmas, the window count and the short-window `mu`-integrals, are
   corollaries. A statement is missing, not an argument.
4. **Grid bookkeeping.** `d_H = floor(L H/2pi)`, the end strips at `T` and
   `T + H`, and `T <= tau_k <= T + H`; every downstream use is an upper bound
   and holds a fortiori.
5. **Constants.** The tree's decimals are fixed at bandwidth near 1 and do
   not transfer. Bandwidth-theta decimals come from `landscape.py`
   (`0.130262` at `0.55`, `0.281718` at `0.60`, `0.682554` at `0.80`) and
   **must be enclosed by ball arithmetic before any number is stated**.
6. **Denominator.** The natural statement is against `N_xi'(T, T + T^theta)`.
   Against the zeta count it needs Wang's (1.2). The cumulative
   `N_xi'(T) = N(T) + O(log T)` appears only in docstrings and is not a
   theorem here; do not quote it as one.
7. **Framing**, as above.

**The eight-step proof outline**, mirroring Wang's sections and naming the
Lean lemma each step localizes, is §6 of `AUDIT-dyadic.md`. The
formalization footprint is about forty touch points across the files listed
there, with `Coeff/`, `Window.lean`, `ZeroSide.lean`, `MV/` and `WeilEF/`
untouched; the audit suggests making the range a second parameter `(T, U)`
with `U = 2T` recovering the current tree, so "never hard-code `2T`" becomes
enforced by the type.

**What the gate does not claim.** That the Lean localization is small; any
constant, since none is enclosed at bandwidth theta; novelty beyond §6.1's
search; anything about RH.

Hardy's `Z'` is formalized in the same tree (`hardyW_simple_on_line`,
`0.85838 / 0.92919`) and is equally absent from the short-interval
literature; it is a second target of the same shape and should be mentioned
in the same paper if the first succeeds.

**Do not conflate the two constants both called `c*`.** The zeta one has
kernel `|alpha|`, `1/c*_1 = 1.3274992963205884`, and is Wang's. The `xi'` one
in `lean/ZetaLean/Pub1/Setting.lean` has kernel `F_1` and gives
`H* = 0.8686415005`. An earlier draft of this brief claimed
`PALOMAR-2026-08-21-000004` was the `lambda = 1` case of Wang's Proposition
4.1. It is not, and that claim is withdrawn here rather than quietly deleted.

## 7. Route two: the bandwidth-theta configuration ceiling, as a stopping criterion

The window class is capped at the landscape by Wang's Proposition 4.1 (§2).
That caps **windows**, not **certificates**: the bandwidth-one configuration
ceiling is `0.6818286874638` against a window optimum of `0.6725007036794116`,
a headroom of `0.00933` that no window reaches, and `Phi_3`, `Phi_4` and the
`0.675142509660254` family saturation all live inside it.

**The bandwidth-theta configuration ceiling is computed nowhere**, and the
search in §6.1 confirms it: Alpöge-Furman §7.2 and `Zeta23/PairCeiling/`
certify a ceiling only for bandwidth-one certificates for zeta
(`p_0 <= 0.6818287`), nothing below one, nothing for `xi'`, and Wang has no
ceiling or optimality remark at all.

**Built 2026-09-12, and the control revealed the brief pointed at the wrong
instrument.** `ceiling_theta.py` parameterizes `configuration_lp.py` by band
width; the band edge was a literal `1` in exactly two places, both now
`theta`. At `theta = 1` it reduces to the original to the last bit and
reproduces all six recorded in-band rungs to `1e-12`. But its ladder
extrapolates to `0.6740762`, which is the Montgomery-Taylor window optimum
within the method error, **not** the configuration ceiling `0.6818287`, and
it is `0.0078` short of it. `hunts/frontier_math/RESULTS-frontier-math.md`
§1 already says why: this LP is the measure-level dual, its type structure
eliminates exactly, and the `0.0093` gap to the ceiling "measures what
configuration realizability adds beyond measure positivity". The ceiling is
the simple fraction of an extremal law on marked periodic configurations
(`Zeta23/PairCeiling/LawN256.lean`), whose exact-rational certificate is not
public, and **nothing in this tree recomputes it**
(`hunts/wide_search/RESULTS-pair-ceiling.md`). So a theta sweep of this LP
can only measure convergence to `c(theta)`, which §3 has in closed form; at
`theta = 0.55` it descends to the `p_1 >= 0` floor, consistent with zero
headroom over the landscape, as it must. The workflow
`hunt-short-interval-ceiling.yml` is written and **deliberately not
dispatched**, because it would spend free compute to confirm a closed form.
The estimate is in `RUNS.md` regardless, as the compute discipline requires.

**What measuring the real bandwidth-theta ceiling needs.** A column-generation
primal over realizable configurations with the form-factor data cut at
`theta N`, that is, the `PairCeiling` construction itself rebuilt with the
band as a parameter. That is a different and larger build than the one this
brief asked for, and it starts from a certificate that is not public. The
`theta^3` headroom prediction is therefore **untestable with any instrument
in this tree today** and stays open. It is still the stopping criterion for
the n-point program on this axis, and still the most valuable formalization
target, for the reason given before: a cap is what this laboratory produces
and nobody else does. But it is a build, not a run, and §6 does not wait on
it.

## 8. The band edge: priced, then closed by the literature

**Status: the kill condition for this route fired on 2026-09-12, on a
documented literature search, before any compute.** The pricing stands as a
measured fact about what a constant upper bound on `F` beyond the band would
be worth. The bound does not exist, and the search says why.

**The price.** `hunts/outband_certificate/RESULTS.md` states the reason for
bandwidth one: "`F` has no unconditional upper bound outside the band, so
bandwidth one is forced". That names the input without pricing it. Priced in
`landscape.py` by minimizing
`integral f^2 + double-integral_{|u-v|<=1} |u-v| f f + B double-integral_{|u-v|>1} f f`
over `f` on `[-L/2, L/2]` with `integral f = 1`, checking the minimizer's sign
because a sign-changing minimizer is outside Lamzouri's class:

| F <= B | L = 1.05 | L = 1.10 | L = 1.20 |
|---|---|---|---|
| 2 | 0.702950 | 0.726768 | 0.760859 |
| 3 | 0.701549 | 0.721863 | 0.746779 |
| 6 | 0.697810 | 0.710023 | 0.718168 |
| 20 | 0.686561 | sign-changing | sign-changing |

Baseline `0.672508`. A constant `B` of any finite size on any sliver beyond
the band would be worth more than the whole bandwidth-one headroom of
`0.00933`, because the shadow price of bandwidth is linear,
`c'(1) = (3/2 - H)^2 = 0.6847550854111`, while the out-of-band mass of a
stretched window is quadratically small. **That is what the input would buy.
Here is why it is not available.**

**What the literature holds, searched 2026-09-12.** Twenty-one query strings
and twenty-three papers, listed in `RESULTS.md` §4.

*Unconditionally:* nothing past `alpha = 1` beyond `F >= 0` (positive
definiteness) and `F(alpha) <= F(0) ~ log T`. Baluyot, Goldston, Suriajaya
and Turnage-Butterbaugh (arXiv:2306.04799) stop at `alpha = 1` and state
nothing beyond it. No paper found even states an unconditional averaged bound
past 1.

*Under RH:* integrated bounds exist and are `T`-independent. Goldston's Notes
(math/0412313) Lemma 1: `integral_B^{B+1} F <= 3` for any `B`. Carneiro,
Chandee, Chirre and Milinovich, arXiv:2108.09258 ("a tale of three
integrals"), Theorem 10: `integral_1^{1+delta} F <= 7/8 + (5/4) delta + O(delta^2) + o(1)`.
**But that bound tends to `7/8`, not to zero, as `delta -> 0`.** In their own
words, equation (2.27): "we cannot rule out the existence of delta spikes in
`F(alpha)` for `|alpha| >= 1`". Every known upper-bound argument drops the
phases `T^{i alpha (gamma - gamma')}` by absolute value and is therefore
location-blind, so it cannot see below the spike mass. The pricing above
needs a bound of the shape `B delta`, and no bound of that shape exists under
any hypothesis short of Hardy-Littlewood itself. Pointwise, even
`F(alpha) << 1` just past 1 is carried as an unproved hypothesis by
Heath-Brown (Acta Arith. 41 (1982)) and by Goldston and Suriajaya
(arXiv:2205.06503), who write of it "there is probably no hope of proving
any of these conjectures at present".

*Chirre, Goncalves and de Laat's `0.6792` under RH* (arXiv:1810.08843, Lemma
8) uses **only** `F >= 0` beyond the band plus the Cohn-Elkies constraint
`ghat <= 0` for `|x| >= 1`. No upper bound on `F` beyond 1 is assumed or used
there, nor in Carneiro-Chandee-Littmann-Milinovich (arXiv:1406.5462).

**The precise obstruction, and it is not RH.** Past `alpha = 1` the quantity
`F(alpha) - alpha` is the difference of two terms each of size about
`T^alpha`, whose cancellation to within `O(T log T)` requires the prime-pair
correlations `sum_n Lambda(n) Lambda(n+h)` to relative error
`O(T^{1-alpha} log T)`, uniformly in `h`. Montgomery said so in 1973. A sieve
upper bound gives those correlations to a constant factor `c` (4 by
Bombieri-Davenport, 3.2996 by Lichtman arXiv:2109.02851, and never below 2 by
parity), which leaves a residual `(c - 1) T^alpha` against a main term
`T log T`: for `alpha = 1.05` and `log T = 100` the residual is already 1.4
times the main term at `c = 2`. So the sieve route fails unconditionally and
under RH alike, and BGSTB's technique cannot cross `alpha = 1` in the
upper-bound direction because what it needs there is not a zero-free-region
fact but a prime-pair fact at second order. The same shape appears on the
prime side: every unconditional variance bound for primes in short intervals
(Brun-Titchmarsh, Zaccagnini) is of the `H^2 x` shape, and what the form
factor needs is `H x log(x/H)`.

**The one-line kill for any future attempt.** Any argument that never uses
the phases beyond `|alpha| <= 1` proves the same bound at `b = 0` as at
`b = 1`. But `integral_{-delta/2}^{delta/2} F >= 1 + o(1)` for every fixed
`delta` by Montgomery's theorem. So no phase-dropping argument can give
`B delta < 1`. Apply this to any draft before reading further.

**Assessment, marked as such:** probability that an unconditional
`T`-independent bound `integral_1^{1+delta} F <= B delta` appears by known
methods within a lab-scale effort, about 2%; a pointwise `F <= B` on
`(1, 1+delta)` under RH, about 1%. Feeding the RH-conditional CCCM bound back
into a simple-zero argument cannot exceed the Chirre-Goncalves-de Laat
optimum, since it is derived from the same three facts that certificate
already optimizes over.

**One definitional note the tree should carry.** BGSTB's Theorem 1 is about a
*modified* form factor, summed over complex zeros with weight
`w(u) = 4/(4 - u^2)`, which agrees with Montgomery's only under RH. Lamzouri
and Wang use exactly that modified object, so the lab's certificates are
consistent; but "BGSTB proved `F >= 0` unconditionally" should be read as
being about the modified `F`, and for Montgomery's own `F` the nonnegativity
is the older positive-definiteness fact.

## 9. Leads

- **Higher trace moments are near-dead, with one live corner.** The
  Rudnick-Sarnak support condition means the k-th moment needs bandwidth
  `lambda <= 2/k`, so the band cost `1/lambda = k/2` is linear in `k` while
  the payoff is bounded, and `k = 2` stays optimal. The live corner: **below
  `theta_0` the `k = 2` bound is vacuous, so any positive certificate wins by
  default**, and `hunts/cycle_moments`'s quartic family is the tool, with its
  blocker (a normalized fourth-moment bound) unconditionally available at
  bandwidth below 1/2 by Rudnick-Sarnak. Cheapest test: evaluate the quartic
  certificate at bandwidth `theta/2` for `theta` in `(0.45, 0.55)` and ask
  only whether it is positive. Low expectation. Note it competes with §6 for
  the same headline and loses, since `xi'` reaches `0.5133` with machinery
  that already exists.
- **Alpöge-Furman Remark 6.1 already states the flat-window landscape**,
  `H(lambda) = 2 - 1/lambda - lambda/3`, with the sentence "no `lambda < 1`
  improves the constants". That is §5's flat-window identity in the source
  paper, and it is the sentence Wang's Theorem 2.2 gives a second reading to:
  no `lambda < 1` improves the constants *for the full range*, and every
  `lambda < 1` is exactly what a shorter range costs.
- **Two unread unconditional moment-bound papers** that may bear on
  `cycle_moments`'s blocker: arXiv:2609.11619 (Hagen) and arXiv:2609.01101
  (Durkan, Karak, Mahatab). Shape unchecked.
- **The distinct-zero track.** The lab computes `Hd = (1 + H)/2` and has never
  chased it. Lamzouri's Proposition 2.1 gives both bounds from the same kernel
  sum via *different* elementary inequalities, so the distinct constant is not
  a corollary of the simple one.
- **`T^theta` already appears in the tree, unrun.**
  `hunts/rogue_frontier/IDEA_PORTFOLIO.md` carries "rigorize the hybrid
  q-aspect Theorem E: `q <= T^vartheta` with proportion `H(1/(1+vartheta))`",
  flagged by the source as unchecked. Same landscape, second physical axis.
  The narrow-box `b` curve in `FRONTIER_MAP.md` is a third.
- **Wang's Theorem 2.2 is reusable beyond this hunt.** Anything here that
  consumes full-range pair correlation now has a short-interval counterpart.
- **Lamzouri is at v2; the tree cites v1.** Check what changed.
- **Read `github.com/AxiomMath/ZetaZeros` before writing any Lean.**
  Lamzouri's Appendix A records that AxiomProver produced a formal certificate
  for his Proposition 2.1 unconditionally, and for his Theorem 1.1 modulo
  BGST's Lemma 5 and Riemann-von Mangoldt. A second verification venue
  alongside Palomar, possibly already holding what a formalization here would
  build.

## 10. Closed. Do not re-enter.

**Out-of-band positivity.** Hunt #118 closed it on 2026-09-06: worth zero to
any certificate whose positivity input is Weil's Hermitian form, which is
every unconditional one, and what hunt #110 priced was the RH-conditional
pointwise class. The closure rests on a proved edge lemma, that a real even
spectral profile's autocorrelation is strictly positive just inside its
support edge, so it can never be nonpositive on the strip; false for odd
factors, giving a dichotomy where an even factor is Gram-able and strip-blind
and an odd factor is strip-capable and never a Gram kernel. §8 above is the
**upper-bound** question, which is a different object and is open; do not let
the two blur.

The measured `+0.0068` is best read as the price of removing RH rather than as
an unclaimed gain: under RH one drops off-diagonal terms using pointwise
`W >= 0`, which is compatible with a sign-indefinite transform.

`docs/35` predates the closure and reads as an open opportunity. See §11.

## 11. Corrections this hunt owes the tree

Small, real, none of them this hunt's mathematics:

1. **`docs/35` is stale.** It is hunt #110's front door and does not record
   hunt #118's closure. Add it.
2. **`docs/35` and `hunts/outband_intake/RESULTS.md` disagree numerically.**
   The doc says `+0.0068` with method error `2.2e-3`; the hunt and case log
   say `+0.0065` with `1.8e-3`. Find out which is right.
3. **`references/papers.md` has no entry for Baluyot, Goldston, Suriajaya and
   Turnage-Butterbaugh at all.** Not arXiv:2306.04799, whose Lemma 5 is the
   arithmetic engine of this entire line of work, and not arXiv:2501.14545.
   Add both, plus Lamzouri and Wang, in the file's annotated format.
4. **`hunts/frontier_map/RESULTS-frontier-map.md` should record that its
   landscape now has a theorem attached at each bandwidth**, citing Wang. One
   paragraph, not a new claim.
5. **`hunts/wide_search/RESULTS-xiprime.md` cites the `xi'` figures as
   Alpöge-Furman "Remark 7.3".** They are Remark 7.1, which sits under
   subsection 7.3; the paper's own §1.3 and the Lean `formalization.yaml` both
   say 7.1. Fix the citation.
6. **The Lean dependency has moved.** `lean/bridge/README.md` and `BRIDGE.md`
   cite `anthropics/zeta-23-lean`; the development now lives at
   `anthropics/formal-math`, subdirectory `zeta23/`. Update the citation and
   check the pinned revision still resolves.

## 12. Scope

May: build instruments under `hunts/short_interval/`, record measurements
here, read anything in the tree, make the four corrections in §11, write one
new `docs/NN-*.md` with the number from `scripts/science_preflight.py` and the
heading in the enforced form `# NN. Title`, and open GitHub issues for
observations it is not chasing (§8 is the first candidate).

May not: edit `zeta/`, `ontology/` or `harness/`; write a verdict into
`README.md`, `ROADMAP.md` or `HANDOFF.md`; use the reserved word; claim
novelty; or assign its own claims a status. Use *measured*, *observed*,
*derived*, *consistent with*.

Per `CONTRIBUTING.md` and `scripts/71_contribution_check.py`: `MISSION.md`
with a valid `huntspec`, `RUNS.md` with at least one `runmanifest` including
runs that produced nothing, `RESULTS.md` stating the bounded outcome, a
case-log entry naming the directory in `hunts/README.md`, and a numerical test
or explicit hedge for every quantitative claim.

Compute goes to GitHub Actions, never to the operator's machines, with an
estimate in `RUNS.md` before launching and a checkpoint per unit above twenty
minutes. `CLAUDE.md`'s compute discipline was written after a day that cost
roughly a third of a month's budget and crashed the operator's laptop
repeatedly. It is not advisory.

## 13. The doors

Preliminary: this hunt has measured no ceiling of its own yet, so the
inventory is what §3 to §8 expose. Whoever runs §7 replaces this with the
measured version, ranked by shadow price.

**Active constraint.** One: **bandwidth**. Its shadow price is known in closed
form, `(3/2 - H)^2 = 0.6847550854111` per unit at bandwidth 1, and §3 is the
news that it is a physical parameter rather than a free dial. Its door is §8,
and §8 is shut.

**Frozen-constant inventory**, with what relaxing each trades against.

1. **The band edge at 1.** Frozen by the absence of an unconditional upper
   bound on `F` beyond it, not by choice. Priced in §8 as worth more than
   everything else here combined, **and shut by the literature the same day**:
   the required input is a prime-pair fact at second order, blocked by
   parity, and even under RH the best integrated bound tends to `7/8` rather
   than to zero. The price is recorded so the next person to derive this door
   knows what is behind it and why it will not open.
2. **The kernel.** The zeta arm is fixed to `F(alpha) = |alpha|`. The tree also
   computes the `F_1` landscape and Wang does not, so this is the frozen choice
   where the tree holds something the field does not. §6. Changes the
   information class.
3. **The dyadic counting range.** Frozen in the Lean development by what
   was available to formalize. For the `xi'` arm the audit in
   `AUDIT-dyadic.md` prices the door exactly: two named exponent conditions,
   two missing statements whose proofs already exist, and about forty
   bookkeeping touch points, with no mathematics in the way. For the n-point
   bridges (`S8`, `S9`, `S15`) it remains unaudited and §4 stands. Same
   information class.
4. **The window shape.** Measured in §5 to be worth about `lambda^3/180`, and
   `3.2e-4` at the threshold. **This door is closed by measurement**, and it is
   listed so nobody opens it again.
5. **The window's single frequency `sqrt 2`.** `hunts/amtopa_ceiling`
   established that the `2 j pi` harmonics are exactly M-orthogonal to the
   `sqrt 2` term at bandwidth one, so the window maximum over the whole
   coefficient space is the pure `sqrt 2` value. Whether that orthogonality
   survives at bandwidth theta is unchecked and cheap to check, though §5
   bounds the prize.

**Information class.** Door 1 would leave the class and is shut. Door 2
leaves the class and is open. Doors 3, 4 and 5 stay inside it and are
therefore under the configuration ceiling, which is itself a bandwidth-one
number and unmeasured at bandwidth theta. That measurement is §7 and it is
the stopping criterion for the whole axis.
