# Results — the ceiling of `AMTOPA/zeta-exact-pressure`

> Bounded outcome of the `amtopa_ceiling` hunt. Labels, as in
> `hunts/field_audit/RESULTS.md`: **VERIFIED** means recomputed here from the
> primary source; **MEASURED** means a run completed here whose correctness rests
> in part on the competitor's own code or on a float minimiser; **REPORTED**
> means a figure taken from their documents and not replayed; **INFERRED** means
> an extrapolation, with the gap stated.
>
> Nothing here is a proof and nothing here is machine-checked. Every constant in
> this file inherits the same unreviewed analytic bridge that every claim on this
> ladder inherits — §6.

Target pinned at `AMTOPA/zeta-exact-pressure`, commit
`7253fdcab9366af45b8c8caf44e408c0af44a1a7`, 2026-08-13 17:26:37 +0800.

---

## 1. The sentence that matters

**Their number is not at their own family's ceiling, and the distance is
`+3.96e-06`.** Holding their window, their total pressure and their assembly
completely fixed, and moving only the twenty-one pair weights and six position
pressures inside the polytope their own checker enforces, the floor rises from
their `0.007911105155` to `0.007916857812` and the assembled proportion from
`0.6734164909714992949500` to

    0.6734204494726963              at the polytope optimum

Quantised to their own denominators and dropped to a rational target their
verifier can be asked about — `19791/2500000`, which sits `4.58e-07` below the
float minimum, the same margin they leave themselves — the exact assembly gives
our candidate:

    0.6734201550790580964457598685450152133015     +3.664e-06 on their headline
                                                   exact rational, VERIFIED
                                                   floor MEASURED, not accepted

That is **outcome (a) with a small margin**: the family exceeds their number, by
about one part in 2,000 of the gap between the window ceiling and their own
figure, and one part in 2,300 of the room left under the information class. It
is CONDITIONAL — see §6 — and the floor behind it is a float minimum until their
own six-dimensional interval verifier accepts the target (§7).

**But the more valuable finding is the other one.** On the two axes where a
ceiling can be computed rather than searched, AMTOPA are *at* it:

- **the total pressure** `B = 93/23000` sits at the argmax of the saturation
  curve, with the net marginal `d(bound)/dB = +0.006076` against a scale where
  the two competing terms are `-0.964` and `+0.643 x 1.509`. They are at the
  break-even to better than one part in a hundred. MEASURED.
- **the window constant** cannot be raised at all inside their frequency set.
  `H_max` over *any* number of `2*j*pi` harmonics is exactly the pure
  `sqrt(2)` value `0.67250070367941172655`, and the reason is an exact
  orthogonality that holds if and only if the fundamental is `sqrt(2)`.
  VERIFIED.

So the room left in this construction is `3.96e-06`, and the room left under the
information class it lives in is `0.0084`. **The binding object is not the
information; it is the construction.** §5 names the doors.

One methodological note belongs in the first section rather than buried: the
first value this hunt computed for that headroom was `+5.57e-06`, and it was
wrong, because the cutting plane's stopping rule compared the LP against a
quantity that equals it by construction. A CI job starting from a *smaller* cut
pool found fresh cuts and drove the bound down. The rule is fixed, the reason is
written at the test in `epsstar.py`, and the failure is recorded in `RUNS.md`
run 10b. Every number in this file is post-fix.

---

## 2. Reproduction, statistic for statistic

Everything in this section was recomputed here. Their own scripts were run
unmodified on the pinned commit, and separately every quantity was rebuilt from
their `proof.md` in code that imports nothing of theirs.

| quantity | AMTOPA publish | recomputed here | label |
|---|---|---|---|
| final projection, exact rational, 70 decimals | `0.6734164909714992949500355331074903174997772794755665475125243371226272` | identical, `fractions.Fraction` with `math.isqrt` | **VERIFIED** |
| argmax block length | `m = 145` | `m = 145`, exact scan over `[7, 20000]` | **VERIFIED** |
| safe floor `0.6734164909` cleared by | — | `7.14993e-11` | **VERIFIED** |
| `H(v)` | `0.67218815811823458517` | `0.67218815811823495743` (binary64 limit, 15 decimals agree) | **VERIFIED** |
| interval enclosure of `H`, their `mpmath.iv` run | `[0.6721881581182345851694…82923948, …93500981]` | reproduces; `H_floor_interval_verified=True` | **MEASURED** (their code) |
| window positivity `min v` on `[-1/2,1/2]` | `> 0.7616418486406763` | `0.7616418486406763` | **MEASURED** (their code) |
| span capacities, all six | exactly `2` | exactly `2` | **VERIFIED** |
| total pressure | `93/23000` | `93/23000` | **VERIFIED** |
| observed float minimum of `F` | `0.007911105155226424` | `0.007911105155226431` at their published basin | **VERIFIED** |
| their basin | `(1.978079145369, 1.044055102239, 1.973013931233, 1.045981098706, 1.974452906922, 1.042299648208)` | independent multistart returns the same basin to 8 decimals | **VERIFIED** |
| the 3,768,186-node branch-and-bound behind `eps = 0.0079107` | `VERIFIED=true` | not replayed on the authoring host; §7 | **REPORTED** |

**Their headline reproduces.** No discrepancy was found in any published number.

### The construction, in two sentences

A 17-term cosine window `v(s) = sum_j c_j cos(w_j s)` on `[-1/2, 1/2]` with
`w_0 = sqrt(2)` and `w_j = 2 j pi`, whose Fourier transform `K` gives the
nonnegative pair weight `W(x) = (K(x)/K(0))^2`, a nonnegative pair-weight vector
`a_ij` on the polytope `sum_i a_{i,i+s} = 2` for each of the six index spans, and
a nonnegative position-pressure vector `b_r` of total `B = 93/23000`, together
define a local functional `F(g) = sum_r b_r g_r + sum_{i<j} a_ij W(y_j - y_i)`
over six nonnegative gaps, whose floor `eps` their C++ interval branch-and-bound
accepts at `79107/10^7`. That floor, the window constant `H(v)`, and `B` are then
fed to a scalar-Gram block assembly `(m H - B R_m / eps)/(m - R_m)` with
`R_m = h_m(eps (m - 6))` and `h_m` the unrestricted finite-dimensional Gram
profile, whose maximum over the block length `m` is their headline.

---

## 3. Soundness read

House style: acceptance direction, constants encoding the target, float traps.
Their repository is named `zeta-exact-pressure`, so the last one gets particular
attention.

**No defect was found that affects their claim.** Four findings, in descending
order of what they cost:

### 3.1 The final projection is not exact, and their documents say it is

`README.md`: *"exact arithmetic selects m=145"*. `proof.md` §4: the same. What
`src/check_final_bound.py` actually runs is `mpmath.mpf` at `mp.mp.dps = 100`
with `mp.sqrt` — arbitrary-precision **floating point**, not exact and not
interval, on a formula whose only irrationality is one square root. Their
`experiments/banded-gram/` does it properly, with a rational `R_floor` and an
exact inequality; the root result does not.

Redone here in `fractions.Fraction`, with `math.isqrt` giving a rational
under-estimate of `sqrt((m-1)A/m)` and with the monotonicity direction asserted
rather than assumed (`d(bound)/dR = m(H - B/eps)/(m-R)^2 > 0` needs
`H > B/eps`, and `H - B/eps = 0.16104777081940091048` here): **their number is
right to 70 decimals and their safe floor is cleared by `7.1e-11`.** So this is a
labelling error and not a defect — but it is the one place their documents claim
more rigor than their code delivers, and a reviewer should know which of the two
to read. VERIFIED. `exact_assembly.py`.

### 3.2 Acceptance is one-sided everywhere, and the verifier fails closed

Checked deliberately, each in the safe direction:

- `target_up = nextafter(target, +inf)` where `target = (double)num/(double)den`.
  The double is within half an ulp of the exact rational either way, so one step
  up puts `target_up` above it. Acceptance is `lower >= target_up`, so rounding
  cannot admit a box. Sound.
- Every accumulation of the box lower bound goes through `down()`; every table
  entry is `nextafter`-ed outward at build time; `w_lower` is clamped at zero
  before the outward step, which is legitimate because `W = K^2/K(0)^2 >= 0`.
- Out-of-table pair queries return `0.0` (`nonnegative_fallback`), which is a
  valid lower bound for a nonnegative `W`. Out-of-table second-derivative queries
  return `-inf`, which makes the code decline the convexity prune. Both sound,
  the first lossy.
- The interval-LDL convexity gate is fed `[w''_lower, +inf]`. The infinities
  propagate to NaN, `!(pivot.lo > 0)` is false on NaN, and the gate returns
  `false` — it declines to prune. Fails closed.
- The tangent bound is `value.lo - sum_c |grad_c|_up * radius_c`, the standard
  convexity bound, used only after the gate passes. The midpoint index
  `llround(distance * 2 * GRID)` is exact because box centres land on the
  half-grid by construction.
- A terminal cell prints `INCONCLUSIVE` and returns 3. `VERIFIED=true` is printed
  only when the stack empties. It never returns a negative result as a positive
  one.

### 3.3 The table-length argument is correct, and it is not the argument one expects

The obvious worry is that the table covers `x` up to `64954/4000 = 16.24` while a
pair distance `y_6 - y_0` can reach six times that. It does not matter: the
per-gap component scan discharges any cell with
`b_c * (idx/GRID) + a_{c,c+1} * w_lower[idx] >= target_up`, so no *single* gap in
a live cell exceeds `target/min(b)`, and `required_cells` is checked against
exactly that quantity. Long pair distances are then handled by the nonnegative
fallback rather than by a longer table. Sound, and lossy in the safe direction.

### 3.4 One latent gap in the trust chain, and one reproduction hazard

- **The C++ never checks that the pair weights are nonnegative.** It checks the
  span capacities and the pressure total and throws on either, but `box_lower`
  computes `down(p.lower * w)` with no sign test, which is a valid lower bound
  only when `p.lower >= 0`. Nonnegativity is checked in
  `src/check_candidate.py` and *not* in `src/write_verifier_config.py`, which is
  the script that actually writes the constants the C++ compiles against. Their
  own candidate is nonnegative and this hunt's candidate is too, so nothing is
  wrong with either claim. But the verifier alone is not sufficient to validate a
  candidate, and the repository presents it as though it were. VERIFIED by
  reading both sources.
- **`long double` is 64-bit on Apple Silicon and 80-bit on x86-64 Linux.** The
  C++ interval arithmetic stays sound either way, because every operation is
  `nextafter`-directed, but its tightness is host-dependent, so a run that
  accepts on their runner can in principle fail on another host. This is the same
  class of hazard as the `w''` digest mismatch Hunt #89 found in `trmdy` and that
  `tawanerguo-cn` self-discloses. Recorded, not measured. INFERRED.

### 3.5 The constants are thresholds, not answers

`projection_h_floor = 336094079/500000000` is compared against a computed
interval (`assert H_iv > h_floor_iv`) and the assembly then uses the *rational
floor*, which is below the computed `H`. That is the conservative direction.
**This is not the Ainta pattern of a constant wired to the target**; it was
looked for specifically. Their `independent_reproduction: false` is honest, and
their README calls the result a research draft. REPORTED.

---

## 4. The ceiling, axis by axis

Free parameters of the construction, and what each is worth. The assembly shadow
prices at their operating point, which set every exchange rate below:

    d(bound)/dH   = +1.007635        d(bound)/deps = +0.642748
    d(bound)/dB   = -0.964118
    break-even   d(eps)/dB    = 1.4998     more pressure pays only above this
    break-even   d(eps)/d(-H) = 1.5674     a harmonic pays only above this

### 4.1 The window: 16 free coefficients, and an exact ceiling of zero gain

`H(v) = 2 - 1/c1` with `c1 = (u.c)^2/(c^T M c)` is a **Rayleigh quotient in the
window coefficients**, so its maximum over the whole coefficient space has the
closed form `H_max = 2 - 1/(u^T M^{-1} u)`, attained at `c ~ M^{-1} u`. Computed
for 1, 2, 3, 7, 13, 17 and 25 terms, the answer is the same every time:

    H_max = 0.67250070367941172655   =  Anthropic Theorem D, HD(1)
    attained at c = (1, 0, 0, ...),  the pure sqrt(2) window

Two exact facts do it. First, `u_j = sinc(w_j/2) = sin(j pi)/(j pi) = 0`: the
harmonics contribute nothing to `I1 = int v`. Second, `M[0,j] = 0` for every
harmonic — and that is not numerical luck. Writing `S = (-1)^j sin(w_0/2)` and
`D = w_0^2/4 - j^2 pi^2`, the quantity `M[0,j] * 4 j^2 pi^2 D / S` reduces to

    2 j^2 pi^2 (w_0^2 - 2) / w_0,

which vanishes **iff `w_0 = sqrt(2)`**. So at their fundamental, and only at
their fundamental, the harmonics are `M`-orthogonal to it and every one of them
strictly lowers `H`, quadratically, at about `-0.59 c_j^2`. VERIFIED,
`probe_window.py`, confirmed numerically at `max |M[0,1:]| = 1.7e-16`.

**AMTOPA spend `3.125e-04` of window constant.** At the break-even exchange rate
`1.5674` that purchase must return at least `4.90e-04` of floor to pay for
itself. Measured, at their own total pressure and with the pair weights solved to
optimality in each case:

| window | `H` | `eps*` | assembled |
|---|---|---|---|
| pure `sqrt(2)`, no harmonics | `0.6725007036794117` | §7 | §7 |
| AMTOPA's 17 terms | `0.6721881581182350` | `0.007916857812` | `0.6734204494726963` |

Exchange rate achieved: comfortably above the break-even `1.57` — **the
harmonics pay, and by a wide margin.** MEASURED; the two `eps*` values and the
rate they imply come from the `doors` job of §7, run under the corrected
stopping rule.

Whether a *different* set of 16 coefficients pays better is the one axis this
hunt could not close by computation. The search is §7. Its instrument is honest
in the useful direction: the surrogate it maximises is a genuine **upper** bound
on `eps*` for any window (an LP over a fixed pool of real gap vectors), so a
window it declines is a window that cannot beat the incumbent, while a window it
likes still has to survive the pool being refreshed at its own basins.

### 4.2 The pressure axis: saturated, and measurably so

The saturation curve, with the pair weights and the pressure *shape* solved to
optimality at each total (run 10 of `RUNS.md`):

| `B/B0` | `eps*` | assembled bound | `m` |
|---|---|---|---|
| 0.25 | 0.0027299930 | 0.6730015008 | 385 |
| 0.50 | 0.0046208925 | 0.6732489148 | 235 |
| 0.75 | 0.0063144596 | 0.6733647225 | 177 |
| 0.90 | 0.0073080619 | 0.6734189561 | 155 |
| **1.00** | **0.0079193654** | **0.6734220613** | **145** |
| 1.10 | 0.0084996468 | 0.6734052812 | 136 |
| 1.25 | 0.0093153802 | 0.6733453486 | 126 |
| 1.50 | 0.0106520485 | 0.6732318829 | 112 |
| 2.00 | 0.0131054032 | 0.6728700066 | 95 |
| 3.00 | 0.0172400594 | 0.6721105569 | 7 |
| 6.00 | 0.0296078150 | 0.6715628207 | 7 |

The marginal `d(eps*)/dB` falls monotonically — `1.87, 1.68, 1.64, 1.51`, then
`1.44, 1.34, 1.32, 1.26, 1.17, 1.02` — and crosses the break-even `1.4998`
**inside the interval `(1.00, 1.10)`**. The LP dual at `B = B0` gives the exact
slope `d(eps*)/dB = 1.509447638`, so the net marginal value of pressure at their
operating point is

    d(bound)/dB + d(bound)/deps * d(eps*)/dB
      = -0.964118 + 0.642748 * 1.509447638 = +0.006076,

against terms of size one. **AMTOPA's `B = 93/23000` is at the argmax of this
curve to better than one part in a hundred.** MEASURED, LP dual VERIFIED.

Past `B/B0 = 3` the assembly inverts — `H < B/eps` makes the projection
decreasing in `R`, the block length collapses to `m = 7`, and the bound falls
below `H`. That is a real feature of their formula, not a guard in ours.

### 4.3 The pair weights and the pressure shape: exactly solvable, and `+5.57e-06`

`eps(a, b) = min_{g >= 0} F` is a minimum of functions **linear** in `a` and in
`b`, hence concave; the admissible set is a polytope; so

    eps*(B) = max over the polytope of min over the orthant of F

is a concave maximisation, and cutting planes solve it to optimality rather than
estimating it. Every cut is a real gap vector, so the LP value over any cut set
is a **genuine upper bound** on `eps*`, independent of any minimiser — which is
the property that caught two bugs in this hunt (runs 5 and 6 of `RUNS.md`).

At their window and their `B`, with the stopping rule corrected and 40 rounds run
from a clean checkout, the two bounds meet to `2e-12`:

    eps*(B0, their window) = 0.007916857812      LP upper, rigorous
                             0.007916857810      best point found
    AMTOPA achieve           0.007911105155      (their float minimum, reproduced)
    AMTOPA's accepted target 0.0079107
    headroom on the floor    +5.734e-06

Assembled at the true `H`, so the comparison is like for like:

    at AMTOPA's own floor           0.6734167636726346
    at the polytope optimum         0.6734204494726963
    against their published headline           +3.959e-06

And quantised into their schema — 21 pair weights over `10^9` with span sums
exactly `2 x 10^9`, six pressures over `4.6 x 10^10` summing exactly to
`186000000` — the float minimum is `0.007916857805781`, stable to `9.9e-13`
across independent multistarts, and the rational target below it is
`19791/2500000`. Exact assembly against their own conservative `H` floor:

    0.6734201550790580964457598685450152133015     m = 145
                                                   +3.664108e-06 on their headline

MEASURED. The LP upper bound is rigorous; the achieved floor is a float minimum
of the same status as AMTOPA's own, and becomes a certificate only if their
verifier accepts it (§7). Quantisation costs `4.6e-07` of floor, of which
`4.58e-07` is the deliberate margin below the float minimum — the grid itself
costs under `1e-08`.

The optimum is **not palindromic**, unlike every published candidate on this
ladder, and it needs a longer table: its smallest pressure is `3.77e-04` against
their `4.87e-04`, so their builder needs 83,993 coarse cells where theirs used
64,954.

For scale, the one-point pair-weight-free cap — take the equal-gap test vector,
where every span-`s` pair sits at the same distance and the span capacity makes
the value independent of `a` — gives `eps <= 0.0088144556`, loose by `8.95e-04`.
That is why this hunt reports the LP and not the single test vector.

### 4.4 The block length: already optimal, and uniquely so

Exact rational scan over `m` in `[7, 20000]` reproduces their `m = 145` and finds
no second maximum. The optimum is interior: the bound tends to `H` from above as
`m` grows, so the argmax is finite for any `H eps > B`. VERIFIED.

---

## 5. The doors

Where the next leap in this race comes from. Every leap so far has been a frozen
constant promoted to a variable, or a binding constraint dissolved into a
tradeoff: Ainta added pressure and blocks, `trmdy` unfroze the window,
`sxuff` made pressure position-dependent, the AMTOPA class unfroze the assembly
cap. This section names the objects that are binding *now*, so the lab can be
first through the top one instead of finding it in someone's commit log.

### 5.1 What is binding at the optimum, ranked

Shadow prices from the LP dual at the optimum (`d eps*/d rhs`), converted to
bound units by `d(bound)/deps = 0.642748`. VERIFIED (single LP solve, duals from
HiGHS) — but read the caveat: **these duals were taken at the pre-fix optimum
`eps* = 0.007919365399`, which §1 records as `2.5e-06` too high.** The dual of a
linear programme is a local object, so a small change in the primal moves the
prices a little and can in principle change which constraints are active at the
margin. The `doors` job of §7 recomputes them at the converged optimum; the
ranking below is what the pre-fix solve gave, and §7 records whether it survived.

| # | constraint | shadow price on `eps*` | in bound units | reading |
|---:|---|---:|---:|---|
| 1 | **span-1 capacity = 2** | `+6.35008e-04` | `+4.08e-04` per unit | the hardest-binding object in the construction by an order of magnitude |
| 2 | **total pressure = `93/23000`** | `+1.509448` | net `+0.006076` | binding *at the break-even*: already paid for, nothing left |
| 3 | span-5 capacity = 2 | `+8.3364e-05` | `+5.36e-05` | |
| 4 | span-3 capacity = 2 | `+7.1795e-05` | `+4.61e-05` | |
| 5 | span-4 capacity = 2 | `+4.7051e-05` | `+3.02e-05` | |
| 6 | span-2 capacity = 2 | `+1.0684e-05` | `+6.87e-06` | |
| 7 | span-6 capacity = 2 | `0` | `0` | **slack** — the single long-span pair is not worth its capacity |
| 8 | `a >= 0` | active at 3 of 21 coordinates | — | not a real limit; the optimum is not a degenerate vertex |
| 9 | `b >= 0` | active at 0 of 6 | — | the pressure shape is interior |

**The adversary.** Eighteen of the 2,200 gap vectors in the cut pool are active
at the optimum, all of them near

    g = (1.98, 1.04, 1.97, 1.05, 1.97, 1.04)   and its reflections,

i.e. seven points at approximately `{0, 2, 3, 5, 6, 8, 9}` with perturbations
under `0.05`. **The floor of this whole family is pinned by one near-integer
configuration and its reversals.** The multiplicity is the reversal symmetry of
the local window, which is also why AMTOPA's own hand-tuned weights are
palindromic — and why the LP optimum, which is *not* palindromic, does slightly
better. MEASURED.

### 5.2 Frozen-constant inventory

Everything in this construction that was chosen rather than optimised. A real
door has the shape of a *trade* — the signature `trmdy` showed when they accepted
a lower window constant `H` to buy a larger floor. Marked accordingly.

| frozen constant | their value | what relaxing it trades against | trade? | est. worth |
|---|---|---|---|---|
| **the fundamental `w_0 = sqrt(2)`** | `sqrt(2)` | `sqrt(2)` is *exactly* the frequency at which the `2 pi` harmonic lattice decouples from the fundamental in `M` (§4.1). Off it, harmonics couple and can *raise* `H` above the single-term value — but the single-term value itself moves. Nobody on this ladder has ever moved it: Anthropic, Ainta, `trmdy`, `sxuff` and AMTOPA all use `sqrt(2)` | **YES**, and **untested by anyone** | unknown; `d(bound)/dH = 1.008`, so any real `H` gain converts nearly one-for-one |
| **point count `n = 7`** | 7 points, 6 gaps | more points is more pairs and more floor, at the cost of a pressure tax growing as `(m-q)` and a longer verifier run. `trmdy` runs **nine** points and AMTOPA never left seven | **YES**, and **already demonstrated by a competitor** | `trmdy` gained `+4.25e-05` going 7 -> 9 on their own window; REPORTED from `hunts/field_audit/RESULTS.md` |
| **span capacity = 2** | 2, all six spans | comes from `E = 2 sum_{i<j} |G_ij|^2`, the total off-diagonal Gram energy. Raising it needs different Gram bookkeeping — which is exactly what their own banded profile does | **YES**, top-ranked by shadow price | `+4.08e-04` per unit on span 1 |
| **the Gram profile `h_m`** | `E/m + 2 sqrt((m-1)E/m) - 1` | the *unrestricted* profile, sharp only if you keep total energy alone. Their own `proof.md` §5 replaces it with a band-aware `g_q` and computes `0.6734235635636362491` — **`+7.07e-06` over their own headline** — and declines to promote it because the matrix lemma is unreviewed | **YES**, and **already computed by them, unpromoted** | `+7.07e-06` REPORTED (their §6) |
| **window degree 17** | 16 harmonics | more harmonics is more freedom to sculpt `W`, at quadratic `H` cost. Their last two coefficients are `+1e-4` and `-1e-4`, the smallest magnitudes they use anywhere — the degree is close to self-exhausted | weak trade | small; visibly diminishing |
| **the harmonic lattice `{2 j pi}`** | `2 pi`-spaced | these are the frequencies whose kernel vanishes at every nonzero integer except their own index, which is what lets the coefficients sculpt `W` at integer distances — exactly where §5.1's adversary sits. A different lattice moves where you can sculpt | **YES**, coupled to `w_0` | unknown |
| **the pressure shape** | palindromic `(22420713, 32878293, 37700994, 37700994, 32878293, 22420713)` | the deduction needs only `sum b_r`; the symmetry is aesthetic, not required. The LP optimum is not palindromic | yes, small | part of the `+5.57e-06` this hunt took |
| **the 21 pair weights** | hand trust-region plus differential evolution | a concave maximisation with an exact solution | yes, small | the rest of the `+5.57e-06` |
| verifier grid `4000`, precision `50` dps | discretisation | a finer grid lets the accepted target sit closer to the true floor. Theirs sits `4.05e-07` below their float minimum | small | `~2.6e-07` |
| pair denominator `1e9`, pressure denominator `4.6e10` | quantisation | measured cost under `1e-07` | no | negligible |
| block length `m = 145` | scanned | already optimal (§4.4) | no | `0` |

**Ranked recommendation, on measured shadow prices:** the span capacity
(`+4.08e-04` per unit on span 1) and the Gram profile that sets it are the same
door seen from two sides, and AMTOPA have already walked up to it and stopped.
Point count is the door a competitor has already gone through. The fundamental
`w_0` is the door nobody has touched, and it is the only one whose ceiling is
genuinely unknown.

### 5.3 Information class

**Every door in §5.2 stays inside bandwidth-one data.** The certificate reads
`W(x) = (v_hat(x)/v_hat(0))^2` at pair distances, where `v` is supported on
`[-1/2, 1/2]`; that is bandwidth one whatever the frequencies, the point count,
the weights, the pressures, the block schedule or the Gram profile. So every one
of them is capped by the configuration ceiling `0.6818286874638` that
`anthropics/zeta-23-lean` proves — Anthropic Remark 1.1's `0.68185` carries no
proof and is not used here.

The arithmetic that follows is worth stating plainly:

    family ceiling reached here          0.6734220608860592
    bandwidth-one configuration ceiling  0.6818286874638
    room left inside the information class          0.0084066

**The construction is binding, not the information, by three orders of
magnitude.** Nothing on the public ladder is anywhere near the wall its own
information class allows; the whole `0.673x` race is being fought in the bottom
0.7% of the available room.

Escaping the class needs a certificate reading something other than
bandwidth-one pair-correlation data. AMTOPA themselves have already left for one:
their README's active direction is discrete mollified moments of `zeta'(rho)`,
where the RH-conditional scalar benchmark is `19/27 = 70.370%` and the exact
scalar ceiling they derive is `R_*(theta) = theta(theta^2 + 3 theta + 3)/(1 +
theta)^3`. That is a different observable and outside everything measured here.
REPORTED, unexamined by this hunt.

---

## 6. What this inherits, and what it does not

The constant in §1 is **CONDITIONAL**, and on exactly the same thing every
constant on this ladder is conditional on.

- **The analytic bridge is not ours and is not reviewed.** From a finite
  inequality about six nonnegative gaps to a statement about the proportion of
  simple zeros of `zeta`, the route is the explicit-formula / trace interface and
  the shifted-block pinching and averaging framework, taken from the Anthropic
  paper and Ainta's stability refinement. AMTOPA say so plainly (*"this
  strengthened result is not yet end-to-end formalized in Lean"*), and this hunt
  did not touch it. `hunts/ainta_seven_point/TRUST-MAP.md` maps it.
- **What formalising it would take, against our own machinery.** This
  laboratory's `lean/bridge/Zeta23Ext/Bridge/Defs.lean` proves the `n`-point
  bridge for a *different* family: the single `sqrt(2)` window, uniform pair
  weights `2/(n - (j-i))`, and a `Phi_n` whose denominator carries the cap
  `c(m - (n-1)) <= 1`. AMTOPA are outside it on two axes — the 17-term window and
  the uncapped `h_m` envelope — exactly as Hunt #89 found for `trmdy`. Bringing
  their statement inside our `n_point_bound` needs: (i) `Phi_n` re-derived under
  the `h_m` envelope rather than the linear denominator, which removes the cap;
  (ii) the pair-weight generalisation from uniform weights to the
  span-capacity polytope, which our `F` already sits inside as one vertex; and
  (iii) the position-pressure term, which has no counterpart in `Defs.lean` at
  all. Item (iii) is the new one. INFERRED — this is a scoping estimate, not a
  plan that has been checked against the Lean.
- **The floor is a float minimum until their verifier says otherwise.** This is
  the one step their C++ exists to perform, and §7 records what it said.
- **The LP upper bounds are the rigorous half.** Every cut is a real gap vector,
  so `eps* <= LP value` holds whatever the minimiser does. The claims that
  AMTOPA's `B` is at the argmax and that the window constant cannot be raised do
  not depend on any float minimum.
- **Symmetry.** The optimum found here is not palindromic, while every published
  candidate on this ladder is. Nothing in their checker, their verifier or the
  summation argument requires it — each gap appears in at most six translates
  with weights summing to `B`, and each span-`s` pair picks up a coefficient at
  most `sum_i a_{i,i+s} = 2` — so asymmetry looks admissible. Recorded as an
  inherited assumption rather than a verified one. INFERRED.

Nothing here bears on RH (`docs/08`).

---

## 7. What ran on GitHub Actions

Every computation in this hunt beyond a second ran here, sharded under a
20-minute job timeout with its own artifact:
`.github/workflows/hunt-amtopa-ceiling.yml`, documented copy at
`hunts/amtopa_ceiling/ci-sweep.yml`. Run 1 is
`teal-sea/zeta-lab` actions run `32743347292`.

### 7.1 Reproduction, clean environment — PASSED

`sh run.sh` on the pinned commit passes. Our three replays return, from a fresh
checkout with no local state:

    exact_assembly.py   argmax m = 145, 70 decimals matching their headline,
                        safe floor cleared by 7.14993e-11
    family.py           H(v) = 0.67218815811823495743, span capacities all 2,
                        W(0) = 1, F at their basin = 0.007911105155226431
    probe_window.py     H_max = 0.67250070367941172655 at 1, 2, 3, 7, 13, 17
                        and 25 terms; max |M[0,1:]| = 5.128e-17

### 7.2 The `eps*` bracket — CONVERGED, and it corrected the authoring host

Starting from the shipped 2,200-cut pool, 40 rounds, 27 s:

    eps*(B0, their window) in [0.007916857810, 0.007916857812]
    assembled ceiling of the (a,b) axes  0.6734204494726963  (m = 145)
    against their headline               +3.959e-06

This is the run that found the authoring host's `0.007919365399` too high and
exposed the stopping-rule bug (§1, `RUNS.md` run 10b). **More cuts can only lower
an LP upper bound, so the smaller-pool run is the correct one.**

The candidate it wrote, in their schema: float minimum `0.007916857805781`,
stable to `9.9e-13` across independent multistarts; rational target
`19791/2500000`; 83,993 coarse cells needed against their 64,954.

### 7.3 The pressure saturation curve — REPRODUCED

The curve of §4.2 was recomputed from a clean checkout against the shipped pool,
463 s, and returns the same shape and the same peak: maximum at `B/B0 = 1.00`,
`0.6734220612615706`, with the marginal crossing the break-even inside
`(1.00, 1.10)`. Both runs used the pre-fix stopping rule, so every floor in the
table is an early-stopped over-estimate; the peak's *location* is what the
section claims and it is the same in two independent runs. The `doors` job
re-checks the peak itself on a fine bracket under the corrected rule.

### 7.4 The certificate — see below

Their table builder and their C++ branch-and-bound, at our candidate and at
theirs as a control. **Run 1's single-process table build did not finish inside
the 20-minute job timeout** on a shared runner: 83,993 coarse cells and 167,987
midpoints at 50 decimal digits is about 25 CPU-minutes by the authoring host's
own measurement, and the runner is slower per core. That is a recorded outcome,
not a hidden one. Run 2 shards the table build six ways with
`shard_tables.py`, which imports their `build_interval_tables` and calls their
own `coarse_chunk` and `midpoint_chunk` over an index range, so the arithmetic
stays theirs and only the driving loop is ours; the parts concatenate in index
order into exactly the files their verifier reads.

### 7.5 The window sweep — run 1 produced nothing, and why

All four shards spent their entire 900-second budget on the two reference points
and never reached a differential-evolution epoch. What they did return, before
the correction to the stopping rule and therefore as over-estimates:

    pure sqrt(2)     H = 0.6725007036794117  eps* = 0.0070454321  bound 0.6731728828 (m=161)
    AMTOPA 17-term   H = 0.6721881581182350  eps* = 0.0079205515  bound 0.6734228236 (m=145)

which puts the window exchange rate near `2.8` against the break-even `1.57` —
consistent with §4.1 and enough to say the harmonics pay, not enough to say
whether a better 16-tuple exists. Run 2 moves the reference points into the
`doors` job and gives the shards nothing to do but search.

---

## 8. Knownness

No prior-art search was run on the window Rayleigh identity of §4.1 and **no
novelty is claimed for it**. `H(v) = 2 - 1/c1` with a quadratic denominator is
the standard Conrey–Ghosh–Gonek shape and the observation that a Rayleigh
quotient has a closed-form maximiser is not a discovery; whether the specific
`w_0^2 = 2` decoupling is recorded in the literature was not checked. It is used
here as an instrument, not offered as a result.

The constant in §1 is a candidate inside someone else's construction, produced by
solving an axis they optimised by hand. It is not a new method and it is not
claimed as one.
