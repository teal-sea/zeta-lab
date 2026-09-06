# Results: the ceiling of `AMTOPA/zeta-exact-pressure`

> Bounded outcome of the `amtopa_ceiling` hunt. Labels, as in
> `hunts/field_audit/RESULTS.md`: **VERIFIED** means recomputed here from the
> primary source; **MEASURED** means a run completed here whose correctness rests
> in part on the competitor's own code or on a float minimiser; **REPORTED**
> means a figure taken from their documents and not replayed; **INFERRED** means
> an extrapolation, with the gap stated.
>
> Nothing here is a proof and nothing here is machine-checked. Every constant in
> this file inherits the same unreviewed analytic bridge that every claim on this
> ladder inherits, §6.

Target pinned at `AMTOPA/zeta-exact-pressure`, commit
`7253fdcab9366af45b8c8caf44e408c0af44a1a7`, 2026-08-13 17:26:37 +0800.

---

## 0. The finding that outranks the rest

**The leading public claim does not replay at its own repository tip.** Run
through AMTOPA's own pipeline on the pinned commit, their table builder, their
verifier, their candidate, their target, the finite inequality behind
`0.6734164909714992949` returns `INCONCLUSIVE=true reason=terminal_cell` with a
rigorous lower bound `1.19e-07` short of the target.

The tables are not at fault: **all six reproduce byte for byte against the
digests in their own `candidate.json`.** The cause is their own convexity gate.
Their recorded run reports `convex=2030240`; here it fires **zero** times in 72
million nodes. Between `b3b7784`, the commit their `candidate.json` names as the
source of that run, and the tip, the gate's curvature entries changed from thin
points to intervals with `+inf` upper bounds, and the interval LDL that follows
cannot certify positive definiteness of a matrix that is unbounded above. A
70-line reproduction is in `ldl_probe.cpp`.

**Direction: fail-closed.** The tip refuses what the earlier revision accepted and
never the reverse, so this is not evidence their number is wrong, it is evidence
that the one runnable artifact carrying the top claim on a fifteen-claim public
ladder does not run as shipped. Full account, both directions, in §3.0.

> **CORRECTED 2026-09-06.** The sentence that stood here said *"the same defect blocks our
> candidate at the tip too, by `2.70e-08`"*. The `2.70e-08` was really printed, but it is the
> verifier's plain corner bound, about `2e-05` loose, and the causal claim is false: at
> `b3b7784`, with their gate demonstrably alive, our candidate is refused on 4 of 8 shards
> anyway (§7.7). It was not blocked by their defect. Its target sat above the true floor,
> because the float oracle behind it over-reported. Their number replays; ours never held.
> §7.7 and §7.8.

---

## 1. The sentence that matters

> **WITHDRAWN 2026-09-06.** The `+3.96e-06` below rests on a float floor of
> `0.007916857812` that was never the floor: the LP's cut oracle missed a basin,
> and the functional at the candidate's own weights bottoms at `0.0078960`,
> `1.5e-5` under the leader's floor. Found by running the candidate through the
> leader's own verifier three times and reading the cells it refused. The
> sentence is kept as written because it was written. **Scope, corrected 2026-09-06:** an
> earlier version of this notice exempted "the second finding (the two axes at their
> ceiling)". Only half of that exemption holds. The window-constant claim is a closed form and
> is untouched (§4.1, VERIFIED). The total-pressure argmax is not: its curve is built from the
> same oracle's floors (§4.2, qualified there). The correction, the
> arithmetic and the re-solve with a stronger oracle are in §7.7; the wide-box re-measurement
> that puts this candidate's assembled bound `1.03e-05` **below** the record, and closes the
> window axis with it, is in §7.8. Everything in this section from here to §1's second finding
> is what the withdrawn floor implied.

**Their number is not at their own family's ceiling, and the distance is
`+3.96e-06`.** Holding their window, their total pressure and their assembly
completely fixed, and moving only the twenty-one pair weights and six position
pressures inside the polytope their own checker enforces, the floor rises from
their `0.007911105155` to `0.007916857812` and the assembled proportion from
`0.6734164909714992949500` to

    0.6734204494726963              at the polytope optimum

Quantised to their own denominators and dropped to a rational target their
verifier can be asked about, `19791/2500000`, which sits `4.58e-07` below the
float minimum, the same margin they leave themselves, the exact assembly gives
our candidate:

    0.6734201550790580964457598685450152133015     +3.664e-06 on their headline
                                                   exact rational, VERIFIED
                                                   floor MEASURED, not accepted

That is **outcome (a) with a small margin**: the family exceeds their number, by
about one part in 230 of the `9.158e-04` their whole construction gained over
Anthropic's Theorem D constant, and one part in 2,100 of the room left under the
information class. It
is CONDITIONAL, see §6, and the floor behind it is a float minimum until their
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

> **WITHDRAWN 2026-09-06, §7.8.** The paragraph that stood here said the window's sixteen
> coefficients were "the live door", worth gains near `+3.5e-05`. All five windows the sweep
> produced were re-priced with an oracle that seeds the region AMTOPA's verifier pointed at,
> and every one of them lands **below** their number, by `1.8e-05` to `3.7e-05`. Every one of
> those windows opens a low basin at a gap near `2.91` that no float search in this hunt was
> sampling; AMTOPA's own window does not. The door is shut.

**And one axis looked open: the window's sixteen coefficients.** `H` cannot rise, but the
coefficients also shape the kernel, and a search over them (§7.5) walked away from AMTOPA's
window on five independent seeds, every one toward lower `H` and lower `B`, reporting gains
near `+3.5e-05`. Those figures rested on a deliberately cheap inner solve. Re-priced properly
they are negative (§7.8), and the note in §7.5 that they were "direction, not magnitude" was
the right caveat attached to the wrong sign.

So the room left in this construction is **none that this hunt can find**, on any of the five
axes, while the room left under the information class it lives in is `0.0084`. **The binding
object is not the information; it is the construction, and the construction is at its own
ceiling.** §5 named the doors and §7.8 closes the last one.

One methodological note belongs in the first section rather than buried: the
first value this hunt computed for that headroom was `+5.57e-06`, and it was
wrong, because the cutting plane's stopping rule compared the LP against a
quantity that equals it by construction. A CI job starting from a *smaller* cut
pool found fresh cuts and drove the bound down. The rule is fixed, the reason is
written at the test in `epsstar.py`, and the failure is recorded in `RUNS.md`
run 10b. **"Every number in this file is post-fix" was the sentence that followed, and it is
false**: §4.2's `B/B0 = 1.00` row still carries the pre-fix `0.0079193654`. Corrected in place
there on 2026-09-06. The wider version of the same mistake is §7.8: three oracles in a row
were declared fixed and each was still biased, so a warranty of that shape does not belong in
this file at all.

---

## 2. Reproduction, statistic for statistic

Everything in this section was recomputed here. Their own scripts were run
unmodified on the pinned commit, and separately every quantity was rebuilt from
their `proof.md` in code that imports nothing of theirs.

| quantity | AMTOPA publish | recomputed here | label |
|---|---|---|---|
| final projection, exact rational, 70 decimals | `0.6734164909714992949500355331074903174997772794755665475125243371226272` | identical, `fractions.Fraction` with `math.isqrt` | **VERIFIED** |
| argmax block length | `m = 145` | `m = 145`, exact scan over `[7, 20000]` | **VERIFIED** |
| safe floor `0.6734164909` cleared by |, | `7.14993e-11` | **VERIFIED** |
| `H(v)` | `0.67218815811823458517` | `0.67218815811823495743` (binary64 limit, 15 decimals agree) | **VERIFIED** |
| interval enclosure of `H`, their `mpmath.iv` run | `[0.6721881581182345851694…82923948, …93500981]` | reproduces; `H_floor_interval_verified=True` | **MEASURED** (their code) |
| window positivity `min v` on `[-1/2,1/2]` | `> 0.7616418486406763` | `0.7616418486406763` | **MEASURED** (their code) |
| span capacities, all six | exactly `2` | exactly `2` | **VERIFIED** |
| total pressure | `93/23000` | `93/23000` | **VERIFIED** |
| observed float minimum of `F` | `0.007911105155226424` | `0.007911105155226431` at their published basin | **VERIFIED** |
| their basin | `(1.978079145369, 1.044055102239, 1.973013931233, 1.045981098706, 1.974452906922, 1.042299648208)` | independent multistart returns the same basin to 8 decimals; **re-checked 2026-09-06** with the wide-box oracle of §7.8, which finds no lower basin anywhere at their weights and returns their floor to `2e-13` | **VERIFIED** |
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

**Nothing was found that makes their claim unsound.** One thing was found that
makes it unreplayable at their own repository tip, and it is §3.0.

### 3.0 Their published certificate does not replay at HEAD, and the reason is a dead convexity gate

Run through their own pipeline on the pinned commit, their table builder, their
verifier, their candidate, their target, **AMTOPA's own finite inequality
returns `INCONCLUSIVE` at a terminal cell.** VERIFIED, `hunts/amtopa_ceiling`
Actions run `32752160099`:

    target=0.0079107  table_cells=64954  initial_boxes=64  accelerated=true
    shard 2/8  INCONCLUSIVE=true reason=terminal_cell
               lower=0.0079105811209911128
               box=[4136,4136][4140,4140][7856,7856][4187,4187][7837,7837][4157,4157]
               nodes=21063162  convex=0  tangent=0
    shard 3/8  SHARD_VERIFIED=true nodes=47945570 convex=0 tangent=0
    shard 7/8  SHARD_VERIFIED=true nodes=3201488  convex=0 tangent=0

The rigorous lower bound at that single grid cell is short of their target by
`1.19e-07`.

**The tables are not the problem, they reproduce perfectly.** All six
outward-rounded tables built here join to byte-identical streams: `w_lower`
`b5acdeea…ba2c8e`, `w_second_lower` `fbac961c…c355d0`, `w_mid_lower`
`4c4c010a…e878a47`, `w_mid_upper` `cb8163fa…3ccde8e`, `w_prime_mid_lower`
`6190bc24…9ed30a`, `w_prime_mid_upper` `b221e296…bf65c915`: **every one matching
the digests in their `candidate.json`.** That is a stronger table reproduction
than Hunt #89 obtained for `trmdy`, where the `w''` stream was host-dependent.

**`convex=0` is the tell.** Their own recorded run reports `convex=2030240` and
`tangent=936616`; here the convexity gate fires **zero** times in 72 million
nodes across three shards, so the tangent pruner never runs, the search explodes,
and the plain interval bound at grid `1/4000` is left to clear the target on its
own, which at one cell it cannot.

**The cause is a change in their own source, and their `candidate.json` records
it.** That file names `source_commit: b3b7784ed0089c3c2197d740aaae1a424d142e44`
as the origin of the recorded `VERIFIED=true` run. Between `b3b7784` and the
pinned tip `7253fdca`, `src/verify_local_tables.cpp` changed by **173 lines**,
and the convexity gate was rewritten:

    b3b7784   const double scalar = s >= 0 ? down(p.lower*s) : down(p.upper*s);
              const Interval term = point(scalar);          // THIN entry

    7253fdca  const Interval curvature =
                  mul(p.exact, {sec, std::numeric_limits<long double>::infinity()});

The lower bound is the same in both. What changed is the upper: it became `+inf`.
The interval LDL that follows is unchanged, and it **cannot certify positive
definiteness of a matrix whose entries are unbounded above**, the first Schur
update drives a pivot's lower endpoint to `-inf` and the gate returns false.
`ldl_probe.cpp` in this directory is a 70-line reproduction: on a matrix with
`10` on the diagonal and `1` off it, positive definite by any test, the tip's
shape returns `false` and `b3b7784`'s returns `true`. VERIFIED.

Note that the old thin-entry version was **sound**, and not by luck: the Hessian
is `sum_p (a_p W''_p) J_p` with `J_p` the all-ones block on `[i, j)`; every `J_p`
is PSD, so lowering the scalar coefficients gives a PSD lower bound, and an LDL
on the lowered matrix certifies the true one. The rewrite did not fix a hole; it
closed the gate.

**Direction: fail-closed, and this is the whole point.** The tip's verifier
refuses what the earlier one accepted and never the reverse. So this is **not
evidence that their number is wrong**, it is evidence that a reviewer who clones
the repository and runs the documented pipeline gets `INCONCLUSIVE` on the
headline. For a claim whose entire trust rests on one runnable artifact, at the
top of a fifteen-claim public ladder, on a repository asking for independent
reproduction, that is the finding worth reporting.

**It does not bite our own candidate identically, though this file said so until
2026-09-06.** At the tip our target `19791/2500000` also hits a terminal cell, short by
`2.70e-08` on the plain corner bound. The verifier at `b3b7784` has since been run (§7.7):
their candidate is accepted on 8 of 8 shards with the gate firing 34,780 to 459,982 times a
shard, and ours is refused on 4 of 8 at that revision too. So their refusal at the tip was
the gate and it disappears when the gate works; ours does not. The two cases are not the same
defect, and ours is not a defect of theirs at all: the target was above the true floor.

### The other findings, in descending order of what they cost:

### 3.1 The final projection is not exact, and their documents say it is

`README.md`: *"exact arithmetic selects m=145"*. `proof.md` §4: the same. What
`src/check_final_bound.py` actually runs is `mpmath.mpf` at `mp.mp.dps = 100`
with `mp.sqrt`, arbitrary-precision **floating point**, not exact and not
interval, on a formula whose only irrationality is one square root. Their
`experiments/banded-gram/` does it properly, with a rational `R_floor` and an
exact inequality; the root result does not.

Redone here in `fractions.Fraction`, with `math.isqrt` giving a rational
under-estimate of `sqrt((m-1)A/m)` and with the monotonicity direction asserted
rather than assumed (`d(bound)/dR = m(H - B/eps)/(m-R)^2 > 0` needs
`H > B/eps`, and `H - B/eps = 0.16104777081940091048` here): **their number is
right to 70 decimals and their safe floor is cleared by `7.1e-11`.** So this is a
labelling error and not a defect, but it is the one place their documents claim
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
  `false`: it declines to prune. Fails closed.
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
harmonic, and that is not numerical luck. Writing `S = (-1)^j sin(w_0/2)` and
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
| pure `sqrt(2)`, no harmonics | `0.6725007036794117` | `0.0070454321` † | `0.6731728827729097` † |
| AMTOPA's 17 terms | `0.6721881581182350` | `0.007916857812` | `0.6734204494726963` |

† from the window-sweep shards of §7.5, computed under the **pre-fix** stopping
rule and therefore an over-estimate; the `doors` job recomputes both ends under
the corrected rule and §7 records the result.

Exchange rate achieved: `8.75e-04 / 3.125e-04 = 2.80` on those figures,
comfortably above the break-even `1.57`, **the harmonics pay, and by a wide
margin.** MEASURED. Note that the two floors are over-estimated in the same
direction and by a similar mechanism, which is why the *ratio* survives the
correction better than either number does.

Whether a *different* set of 16 coefficients pays better is the one axis this
hunt could not close by computation. The search is §7. Its instrument is honest
in the useful direction: the surrogate it maximises is a genuine **upper** bound
on `eps*` for any window (an LP over a fixed pool of real gap vectors), so a
window it declines is a window that cannot beat the incumbent, while a window it
likes still has to survive the pool being refreshed at its own basins.

### 4.2 The pressure axis: saturated, and measurably so

> **QUALIFIED 2026-09-06.** Every `eps*` in the table below is `eps_star`'s achieved floor,
> which is `harvest`'s output, and §7.7 and §7.8 show that oracle over-reports by `2e-05` to
> `8e-05` at points away from AMTOPA's own. The `B/B0 = 1.00` row is also the pre-fix value
> `0.0079193654`, from before the stopping rule of run 10b, which contradicts §1's "every
> number in this file is post-fix"; the post-fix value at that row is `0.0079111052`. So the
> curve's *heights* are unreliable and its `1.00` row is stale. What the section claims is the
> *location* of the argmax, and that is a comparison between rows computed the same way,
> which the errors do not obviously reorder; but "obviously" is not a measurement, and this
> curve has not been recomputed with the oracle of `wide_floor.py`. That recomputation, one LP
> re-solve per row, is the open item. Until then read §4.2 as MEASURED with a known-biased
> instrument, not as the computable half of §1's second finding.

The saturation curve, with the pair weights and the pressure *shape* solved at each total by
the cutting plane (run 10 of `RUNS.md`). "Solved to optimality" is how this line read until
2026-09-06 and it was wrong: the cutting plane terminates when its float oracle stops
separating, which is not the same thing, and §7.8 is what that difference cost.

| `B/B0` | `eps*` | assembled bound | `m` |
|---|---|---|---|
| 0.25 | 0.0027299930 | 0.6730015008 | 385 |
| 0.50 | 0.0046208925 | 0.6732489148 | 235 |
| 0.75 | 0.0063144596 | 0.6733647225 | 177 |
| 0.90 | 0.0073080619 | 0.6734189561 | 155 |
| **1.00** | **`0.0079193654`, STALE: this is the pre-fix value. Post-fix and wide-box, `eps*(B0)` is bracketed `[0.0079111052, 0.0079111939]` (§7.8), and the assembled bound is `0.6734167516` at the lower end, `+2.6e-07` on the record, not `+5.6e-06`** | ~~`0.6734220613`~~ | **145** |
| 1.10 | 0.0084996468 | 0.6734052812 | 136 |
| 1.25 | 0.0093153802 | 0.6733453486 | 126 |
| 1.50 | 0.0106520485 | 0.6732318829 | 112 |
| 2.00 | 0.0131054032 | 0.6728700066 | 95 |
| 3.00 | 0.0172400594 | 0.6721105569 | 7 |
| 6.00 | 0.0296078150 | 0.6715628207 | 7 |

The marginal `d(eps*)/dB` falls monotonically, `1.87, 1.68, 1.64, 1.51`, then
`1.44, 1.34, 1.32, 1.26, 1.17, 1.02`: and crosses the break-even `1.4998`
**inside the interval `(1.00, 1.10)`**. The LP dual at `B = B0` gives the exact
slope `d(eps*)/dB = 1.509447638`, so the net marginal value of pressure at their
operating point is

    d(bound)/dB + d(bound)/deps * d(eps*)/dB
      = -0.964118 + 0.642748 * 1.509447638 = +0.006076,

against terms of size one. **AMTOPA's `B = 93/23000` is at the argmax of this
curve to better than one part in a hundred.** MEASURED, LP dual VERIFIED.

Past `B/B0 = 3` the assembly inverts, `H < B/eps` makes the projection
decreasing in `R`, the block length collapses to `m = 7`, and the bound falls
below `H`. That is a real feature of their formula, not a guard in ours.

### 4.3 The pair weights and the pressure shape: exactly solvable, and `+5.57e-06`

`eps(a, b) = min_{g >= 0} F` is a minimum of functions **linear** in `a` and in
`b`, hence concave; the admissible set is a polytope; so

    eps*(B) = max over the polytope of min over the orthant of F

is a concave maximisation, and cutting planes solve it to optimality rather than
estimating it. Every cut is a real gap vector, so the LP value over any cut set
is a **genuine upper bound** on `eps*`, independent of any minimiser, which is
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

And quantised into their schema: 21 pair weights over `10^9` with span sums
exactly `2 x 10^9`, six pressures over `4.6 x 10^10` summing exactly to
`186000000`: the float minimum is `0.007916857805781`, stable to `9.9e-13`
across independent multistarts, and the rational target below it is
`19791/2500000`. Exact assembly against their own conservative `H` floor:

    0.6734201550790580964457598685450152133015     m = 145
                                                   +3.664108e-06 on their headline

**What justifies the candidate, and what does not.** The linear programme is how
the point was *found*; it is not what makes the claim. The LP value over a cut
set is a rigorous upper bound on `eps*`, and it can only fall as cuts accumulate,
so if a future run finds cuts we did not, our headroom shrinks and can vanish.
The claim itself is narrower and does not depend on the LP at all: **at the
`(a, b)` this hunt produces, `min_g F` is at least `19791/2500000`**, and that is
a statement their own six-dimensional interval branch-and-bound either accepts or
refuses at a terminal cell. Until it answers, the floor is a float minimum with
exactly the status AMTOPA give their own. §7 records the answer.

Its termination is also a heuristic and is worth saying so: cutting planes stop
when the separation oracle stops separating, and this one's oracle is a float
multistart. A weak multistart halts the loop early at whatever the incoming pool
carried, that is precisely the failure of `RUNS.md` run 10b, and raising the
patience does not remove it, it only makes it less likely.

Quantisation costs `4.6e-07` of floor, of which `4.58e-07` is the deliberate
margin below the float minimum, the grid itself costs under `1e-08`.

The optimum is **not palindromic**, unlike every published candidate on this
ladder, and it needs a longer table: its smallest pressure is `3.77e-04` against
their `4.87e-04`, so their builder needs 83,993 coarse cells where theirs used
64,954.

For scale, the one-point pair-weight-free cap, take the equal-gap test vector,
where every span-`s` pair sits at the same distance and the span capacity makes
the value independent of `a`, gives `eps <= 0.0088144556`, loose by `8.95e-04`.
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
HiGHS), but read the caveat: **these duals were taken at the pre-fix optimum
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
| 7 | span-6 capacity = 2 | `0` | `0` | **slack**, the single long-span pair is not worth its capacity |
| 8 | `a >= 0` | active at 3 of 21 coordinates |, | not a real limit; the optimum is not a degenerate vertex |
| 9 | `b >= 0` | active at 0 of 6 |, | the pressure shape is interior |

**The adversary.** Eighteen of the 2,200 gap vectors in the cut pool are active
at the optimum, all of them near

    g = (1.98, 1.04, 1.97, 1.05, 1.97, 1.04)   and its reflections,

i.e. seven points at approximately `{0, 2, 3, 5, 6, 8, 9}` with perturbations
under `0.05`. **The floor of this whole family is pinned by one near-integer
configuration and its reversals.** The multiplicity is the reversal symmetry of
the local window, which is also why AMTOPA's own hand-tuned weights are
palindromic, and why the LP optimum, which is *not* palindromic, does slightly
better. MEASURED.

### 5.2 Frozen-constant inventory

Everything in this construction that was chosen rather than optimised. A real
door has the shape of a *trade*, the signature `trmdy` showed when they accepted
a lower window constant `H` to buy a larger floor. Marked accordingly.

| frozen constant | their value | what relaxing it trades against | trade? | est. worth |
|---|---|---|---|---|
| **the fundamental `w_0 = sqrt(2)`** | `sqrt(2)` | `sqrt(2)` is *exactly* the frequency at which the `2 pi` harmonic lattice decouples from the fundamental in `M` (§4.1). Off it, harmonics couple and can *raise* `H` above the single-term value, but the single-term value itself moves. Nobody on this ladder has ever moved it: Anthropic, Ainta, `trmdy`, `sxuff` and AMTOPA all use `sqrt(2)` | **YES**, and **untested by anyone** | unknown; `d(bound)/dH = 1.008`, so any real `H` gain converts nearly one-for-one |
| **point count `n = 7`** | 7 points, 6 gaps | more points is more pairs and more floor, at the cost of a pressure tax growing as `(m-q)` and a longer verifier run. `trmdy` runs **nine** points and AMTOPA never left seven | **YES**, and **already demonstrated by a competitor** | `trmdy` gained `+4.25e-05` going 7 -> 9 on their own window; REPORTED from `hunts/field_audit/RESULTS.md` |
| **span capacity = 2** | 2, all six spans | comes from `E = 2 sum_{i<j} |G_ij|^2`, the total off-diagonal Gram energy. Raising it needs different Gram bookkeeping, which is exactly what their own banded profile does | **YES**, top-ranked by shadow price | `+4.08e-04` per unit on span 1 |
| **the Gram profile `h_m`** | `E/m + 2 sqrt((m-1)E/m) - 1` | the *unrestricted* profile, sharp only if you keep total energy alone. Their own `proof.md` §5 replaces it with a band-aware `g_q` and computes `0.6734235635636362491`, **`+7.07e-06` over their own headline**, and declines to promote it because the matrix lemma is unreviewed | **YES**, and **already computed by them, unpromoted** | `+7.07e-06` REPORTED (their §6) |
| **window degree 17** | 16 harmonics | more harmonics is more freedom to sculpt `W`, at quadratic `H` cost. Their last two coefficients are `+1e-4` and `-1e-4`, the smallest magnitudes they use anywhere, the degree is close to self-exhausted | weak trade | small; visibly diminishing |
| **the harmonic lattice `{2 j pi}`** | `2 pi`-spaced | these are the frequencies whose kernel vanishes at every nonzero integer except their own index, which is what lets the coefficients sculpt `W` at integer distances, exactly where §5.1's adversary sits. A different lattice moves where you can sculpt | **YES**, coupled to `w_0` | unknown |
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
`anthropics/zeta-23-lean` proves: Anthropic Remark 1.1's `0.68185` carries no
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
  `c(m - (n-1)) <= 1`. AMTOPA are outside it on two axes, the 17-term window and
  the uncapped `h_m` envelope, exactly as Hunt #89 found for `trmdy`. Bringing
  their statement inside our `n_point_bound` needs: (i) `Phi_n` re-derived under
  the `h_m` envelope rather than the linear denominator, which removes the cap;
  (ii) the pair-weight generalisation from uniform weights to the
  span-capacity polytope, which our `F` already sits inside as one vertex; and
  (iii) the position-pressure term, which has no counterpart in `Defs.lean` at
  all. Item (iii) is the new one. INFERRED, this is a scoping estimate, not a
  plan that has been checked against the Lean.
- **The floor is a float minimum until their verifier says otherwise.** This is
  the one step their C++ exists to perform, and §7 records what it said.
- **The LP upper bounds are the rigorous half, and only that half.** Every cut is a real gap
  vector, so `eps* <= LP value` holds whatever the minimiser does, and adding cuts can only
  lower it. That is what carries §7.7's "headroom at most `8.9e-8`", and it survives §7.8
  untouched. The sentence that followed here until 2026-09-06 did not: it said the `B` argmax
  and the window-constant claim "do not depend on any float minimum". The window-constant
  claim does not, and is VERIFIED by a closed form (§4.1). **The `B` argmax does.** The
  saturation curve of §4.2 is built from `eps_star`'s achieved floors, which are `harvest`'s
  output, and the shadow price `d(eps*)/dB = 1.509447638` behind the break-even is a dual of
  an LP whose cut set that same oracle generated. The argmax is a comparison between rows
  computed the same way, so it is more robust than any row of it; robust is not rigorous, and
  §4.2 now says so.
- **Symmetry.** The optimum found here is not palindromic, while every published
  candidate on this ladder is. Nothing in their checker, their verifier or the
  summation argument requires it, each gap appears in at most six translates
  with weights summing to `B`, and each span-`s` pair picks up a coefficient at
  most `sum_i a_{i,i+s} = 2`, so asymmetry looks admissible. Recorded as an
  inherited assumption rather than a verified one. INFERRED.

Nothing here bears on RH (`docs/08`).

---

## 7. What ran on GitHub Actions

Every computation in this hunt beyond a second ran here, sharded under a
20-minute job timeout with its own artifact:
`.github/workflows/hunt-amtopa-ceiling.yml`, documented copy at
`hunts/amtopa_ceiling/ci-sweep.yml`. Run 1 is
`teal-sea/zeta-lab` actions run `32743347292`.

### 7.1 Reproduction, clean environment: PASSED

`sh run.sh` on the pinned commit passes. Our three replays return, from a fresh
checkout with no local state:

    exact_assembly.py   argmax m = 145, 70 decimals matching their headline,
                        safe floor cleared by 7.14993e-11
    family.py           H(v) = 0.67218815811823495743, span capacities all 2,
                        W(0) = 1, F at their basin = 0.007911105155226431
    probe_window.py     H_max = 0.67250070367941172655 at 1, 2, 3, 7, 13, 17
                        and 25 terms; max |M[0,1:]| = 5.128e-17

### 7.2 The `eps*` bracket: CONVERGED, and it corrected the authoring host

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

### 7.3 The pressure saturation curve: REPRODUCED

The curve of §4.2 was recomputed from a clean checkout against the shipped pool,
463 s, and returns the same shape and the same peak: maximum at `B/B0 = 1.00`,
`0.6734220612615706`, with the marginal crossing the break-even inside
`(1.00, 1.10)`. Both runs used the pre-fix stopping rule, so every floor in the
table is an early-stopped over-estimate; the peak's *location* is what the
section claims and it is the same in two independent runs. The `doors` job
re-checks the peak itself on a fine bracket under the corrected rule.

### 7.4 The doors, at the converged optimum: the §5 ranking survives

Run 2's `doors` job re-solves everything of §5 under the corrected stopping rule,
at `eps* = 0.007916857812` over 3,190 cuts. **The ranking is unchanged and the
numbers move in the fourth significant figure:**

| constraint | run-2 `d eps*/d rhs` | in bound units | §5.1 (pre-fix) |
|---|---:|---:|---:|
| span-1 capacity | `+6.29270e-04` | `+4.04483e-04` | `+6.35008e-04` |
| span-5 capacity | `+8.5326e-05` | `+5.4846e-05` | `+8.3364e-05` |
| span-3 capacity | `+7.2331e-05` | `+4.6493e-05` | `+7.1795e-05` |
| span-4 capacity | `+4.8894e-05` | `+3.1428e-05` | `+4.7051e-05` |
| span-2 capacity | `+9.693e-06` | `+6.230e-06` | `+1.0684e-05` |
| **span-6 capacity** | **`0`** | **`0`** | `0` |
| total pressure | `+1.508643906` | net `+0.005600` | `+1.509448` |

Assembly prices: `d(bound)/dH = +1.007633`, `d(bound)/deps = +0.642782`,
`d(bound)/dB = -0.964129`, break-even `d(eps)/dB = 1.499932`,
`d(eps)/d(-H) = 1.567613`. Active set: 4 of 21 pair weights at zero, 2 at the
cap, 0 of 6 pressures at zero, and **24 of 3,190 gap vectors active**, all of
them the near-integer configuration of §5.1 and its permutations. VERIFIED (LP
duals).

**The pressure argmax, rechecked under the corrected rule** on a fine bracket:

    B/B0  0.94  eps* <= 0.0075531404   bound 0.6734205573759323 (m=151)
    B/B0  0.97  eps* <= 0.0077362610   bound 0.6734213137767857 (m=148)
    B/B0  1.00  eps* <= 0.0079188588   bound 0.6734217356598431 (m=145)
    B/B0  1.03  eps* <= 0.0080997560   bound 0.6734210670372676 (m=142)
    B/B0  1.06  eps* <= 0.0082819025   bound 0.6734212017525835 (m=139)

argmax at `B/B0 = 1.00` exactly. **AMTOPA's `B = 93/23000` is at the peak.**

**The window trade, both ends under the same rule:**

    pure sqrt(2)     H = 0.6725007036794117  eps* <= 0.0070401956  bound 0.6731694905 (m=161)
    AMTOPA 17-term   H = 0.6721881581182350  eps* <= 0.0079168578  bound 0.6734204495 (m=145)
    they spend 3.125456e-04 of H and buy 8.766622e-04 of floor
    exchange rate 2.8049 against break-even 1.5676

### 7.5 The window sweep: **the window axis is not saturated**, and it is worth ten times the rest

> **REVERSED 2026-09-06, §7.8.** Every floor in this section came from an inner solve at 14
> rounds and a 40,000-point multistart, and all five are over-estimates by `4.9e-05` to
> `8.1e-05`. Re-priced, all five windows land below AMTOPA's number. The section is kept as
> written; its own caveat, "direction, not magnitude", was correct about the confidence and
> wrong about the sign.

Run 1's four shards produced nothing: they spent their entire 900-second budget
on the two reference points and never entered the search. Run 2 moved the
reference points into `doors` and gave the shards nothing to do but search.
Three of the four returned, and **all three beat the incumbent by an order of
magnitude more than the pair-weight axis did:**

| run | shard | best bound | `H` | `B/B0` | `eps*` | `m` | vs AMTOPA |
|---|---|---|---|---|---|---|---|
| 3 | 0 | `0.6734536055358651` | `0.6721654027522228` | `0.9081` | `0.0074464746` | 153 | **`+3.711e-05`** |
| 2 | 0 | `0.6734531219043779` | `0.6721765258757710` | `0.8708` | `0.0072022744` | 157 | `+3.663e-05` |
| 2 | 3 | `0.6734509899705670` | `0.6721609604662047` | `0.9415` | `0.0076519730` | 149 | `+3.450e-05` |
| 2 | 2 | `0.6734492182109082` | `0.6721776934457142` | `0.8645` | `0.0071559747` | 158 | `+3.273e-05` |
| 3 | 3 | `0.6734471805237648` | `0.6721412064054275` | `0.9654` | `0.0078219798` | 146 | `+3.069e-05` |

Five independent seeds across two runs, every one of them starting from AMTOPA's
own window, every one of them walking away from it, every one reporting a gain
between `+3.07e-05` and `+3.71e-05`.

**Read this carefully, because it is the least settled number in this file.**
Each shard's inner `eps*` solve is deliberately cheap: 14 rounds, a 40,000-point
multistart, patience 3, so every one of those floors is an early-stopped
over-estimate of the same kind §1 describes, and the bounds inherit that. What
the sweep establishes is *direction*, not magnitude: five independent seeds all
walk away from AMTOPA's window toward **lower `H` and lower `B`**, and all report
gains near `+3.5e-05`. The window axis is open. Settling how far it is open needs
each candidate window run through the converged pipeline and then through their
verifier, which this hunt did not do.

Note the shape of what the search wants: `H` *below* AMTOPA's, and `B` at
`0.87` to `0.94` of theirs. The optimiser is spending more window constant to buy
more floor, the same trade `trmdy` made against Anthropic, one level further
in.

### 7.6 The certificate: not obtained, and the cost is the finding

Their table builder and their C++ branch-and-bound, at our candidate and at
theirs as a control.

- **Run 1**: the single-process table build, 83,993 coarse cells and 167,987
  midpoints at 50 decimal digits, took about 17 of the 20 available minutes, and
  the branch-and-bound was cancelled two minutes in. The estimate that put the
  build at 6 minutes came from the authoring host's 0.0225 CPU-s per cell and did
  not carry the runner's slower cores.
- **Run 2**: the build was sharded six ways with `shard_tables.py`, which imports
  their `build_interval_tables` and calls their own `coarse_chunk` and
  `midpoint_chunk` over an index range, so the arithmetic stays theirs and only
  the driving loop is ours. All twelve shards passed and the parts joined into
  tables of exactly the right lengths, digests recorded. **The branch-and-bound
  then ran out the clock anyway, for our candidate and for AMTOPA's own.**

That second sentence is worth stating plainly, because it is a fact about their
result and not only about ours: **AMTOPA's own published finite inequality did not
replay inside a 20-minute job on a free runner.** Their own
`local-certificate-pilot.yml` budgets `timeout-minutes: 120` for exactly this
step, so this is consistent with their record rather than in tension with it,
but it means the load-bearing computation behind the leading public claim costs
on the order of an hour of runner time, and any reviewer should budget for that.

- **Run 3** shards the search itself. The verifier's outer loop is
  `for (const auto& root : initial)` over independent initial boxes, every one of
  which must verify; partitioning it by `root_index % 8` is the same decomposition
  `trmdy`'s Python driver uses and is sound in the same way. The patch is
  `root-shard.patch`, 15 added lines, and it touches **only** the loop bounds and
  the final print: no arithmetic, no acceptance test, no fail-closed path. It is
  applied in CI with `git apply` against the pinned commit so a reader can see
  exactly what changed, and AMTOPA's own candidate runs through the same patched
  binary as a control.

  **This worked, and what it returned is §3.0.** The shards run: 24 s to 343 s
  each, node counts from 3.2M to 47.9M. But at the pinned tip the convexity gate
  is dead, so both candidates hit terminal cells:

  | candidate | target | shard | result | nodes | wall |
  |---|---|---|---|---|---|
  | AMTOPA | `0.0079107` | 2/8 | **INCONCLUSIVE**, `lower=0.0079105811209911128` | 21,063,162 | 147 s |
  | AMTOPA | `0.0079107` | 3/8 | SHARD_VERIFIED | 47,945,570 | 343 s |
  | AMTOPA | `0.0079107` | 7/8 | SHARD_VERIFIED | 3,201,488 | 24 s |
  | ours | `19791/2500000` | 1/8 | **INCONCLUSIVE**, `lower=0.0079163729648852113` | 5,571,088 | 30 s |
  | ours | `19791/2500000` | 7/8 | SHARD_VERIFIED | 3,517,672 | 99 s |

  every one of them with `convex=0 tangent=0`. Ours falls short by `2.70e-08`,
  theirs by `1.19e-07`, both at a single width-zero grid cell, both by less than
  a part in fifty of the target, and both because the tangent bound that used to
  close those cells no longer exists at this revision.

**So the answer this hunt has, precisely.** Our candidate's floor is **not
accepted at the repository tip**, and neither is AMTOPA's own, for the same
reason and by the same mechanism. Settling either needs the verifier at
`b3b7784ed0089c3c2197d740aaae1a424d142e44`: their own code, the revision their
own `candidate.json` names, which is one more Actions cycle of the shape run 3
already demonstrates: six table shards at about four minutes each, then eight
search shards at 24 to 343 seconds each. That is the cost, and it is written here
rather than run, because the hunt's budget went to finding out why the tip does
not work.

Until then, **the floor behind §1's constant is a float minimum and nothing
more**, and this hunt does not claim otherwise.

---

### 7.7 The certificate, obtained: at `b3b7784` their headline replays and ours is refused

**2026-09-06, Actions run `34024309937`, workflow `hunt-amtopa-ceiling` with the new
`verifier_commit` input.** Exactly the cycle §7.6 priced: tables at the pinned tip (six
shards each for both candidates, all passed), the C++ verifier and its config writer built
from `b3b7784ed0089c3c2197d740aaae1a424d142e44` in a second clone, `root-shard.patch` applied
there (offsets 34 and 7 lines), the tip's `candidate.json` as the baseline since it is the
headline's certificate and `b3b7784`'s own file carries an older target, eight search shards
per candidate.

**Their headline: `SHARD_VERIFIED` on 8 of 8, with the gate alive.** `convex` per shard
34,780 to 459,982, `tangent` 14,972 to 214,264, and every shard done in 1 to 19 seconds
against the tip's minutes and non-termination. So §3.0 was exactly right: the one thing wrong
at the tip is the gate, and their published finite inequality is accepted by their own
verifier at the revision their own `candidate.json` names. **VERIFIED.** Their number stands
at that revision.

**Ours, target `19791/2500000`: `INCONCLUSIVE` at a terminal cell on 4 of 8 shards.**

| shard | verdict | rigorous lower bound at the cell | the cell, in gap units (box / 4000) |
|---|---|---|---|
| 0 | SHARD_VERIFIED | | |
| 1 | INCONCLUSIVE | `0.0078933207` | `1.03975, 1.95625, 1.03825, 1.03325, 1.9595, 1.03775` |
| 2 | INCONCLUSIVE | `0.0078989953` | `1.03975, 1.97525, 1.04775, 1.968, 1.044, 1.971` |
| 3 | SHARD_VERIFIED | | |
| 4 | INCONCLUSIVE | `0.0078943512` | `1.95025, 1.0475, 1.96625, 1.03325, 1.02475, 1.02775` |
| 5 | INCONCLUSIVE | `0.0078942963` | `1.033, 1.0395, 1.965, 1.041, 1.96425, 1.03775` |
| 6 | SHARD_VERIFIED | | |
| 7 | SHARD_VERIFIED | | |

**First reading, wrong, kept because it was written down.** Those four bounds sit `2.2e-5`
below our target and below the leader's own floor too, so the first reading was that the
functional at our `(a, b)` genuinely reaches `0.00789` at gap vectors of a different shape
(two large gaps out of six) from the reported basin (three large), the minimiser missed a
basin, and kill condition 2 fires. A cutting-plane round on that reading (the four cells
added to the pool, LP re-solved, Actions run `34024961426`) returned a point `5e-9` from the
first and the identical refusal to twelve digits, which is what forced the second look.

**What the verifier actually said.** The LP's own functional, evaluated at the four cells at
their midpoints `(2k + 1)/8000`, is `0.0079175` to `0.0079185`: **above** the target, by
`1e-6` to `2e-6`, and it reproduces the reported float minimum `0.0079168578` at its location
exactly. The number the verifier prints at a terminal cell is its plain corner bound (each gap
at its left edge, `W` minimised over a span-wide range of table cells), about `2.5e-5` loose
and never the deciding quantity. What decides is the tangent bound, midpoint value minus
`sum_c |dF/dg_c| / 8000`; at these cells `sum|grad|` is `0.009` to `0.017`, the slack `1e-6`
to `2e-6`, and the tangent bound `0.0079163` to `0.0079164`, a hair under the target
`19791/2500000 = 0.0079164`. The target left a margin of `4.6e-7` over the float minimum; at
grid `1/4000` these cells cost `1e-6` to `2e-6`. **Not a missed basin; a margin.** The leader's
point certifies with the same `4.6e-7` margin because its basin is flatter there. Their
verifier is fail-closed at a terminal cell and prints the loose bound, which is what sent the
first reading the wrong way. `artifacts/verifier_cells.json` carries both rounds and the
arithmetic.

**Round 3, and the second reading was wrong about the candidate.** The same point, target
backed off to `19786/2500000 = 0.0079144` (Actions run `34025675594`). The four round-1 cells
were passed, exactly as the margin arithmetic said they would be. The search then went deeper
and the same four shards stopped at four new cells a few grid steps away, and the midpoint
values there are `0.0079153` to `0.0079162`: **below the LP's reported float minimum
`0.0079168578`**. So the reported floor was not the floor. Descending the LP's own functional
from each refused cell, and from the reported location itself, reaches five distinct local
minima at `0.0078960`, `0.0078988`, `0.0078993`, `0.0079015`, `0.0079020`; a 400,000-seed
multistart on `[0.9, 2.3]^6` finds nothing lower. The reported location is not a stationary
point at all (gradient `1e-2` in sum): it is an active cut of the LP, which is why its value
equals the LP value, not a minimum of `F`. The floor of `F` at this `(a, b)` is
`0.00789598574667553` at gaps `(1.038654, 1.963484, 1.038887, 1.035361, 1.961736, 1.039690)`,
confirmed at 40 digits with mpmath independently of the numpy code. That is `2.09e-5` under
the claimed floor and `1.51e-5` under the leader's floor `0.0079107`. (**Lower still, 2026-09-06,
§7.8:** the oracle used here seeds `[0.9, 2.3]^6` and misses a basin at a three-unit gap. With
that region seeded the floor at this same point is `0.0078946642`, and the assembled bound at
it is `-1.03e-05` **below the record**. The withdrawal below is right and understated.) The same descent at the
leader's own `(a, b)` gives `0.0079111052`, `3e-7` above the target their verifier accepts,
so the method reproduces their floor and the gap is real.

**The candidate is withdrawn. Kill condition 2 fires, with the number.** The first reading
had the right conclusion for the wrong reason (the round-1 cells were a margin, as the second
reading said), and the second reading had the wrong conclusion: the oracle that generated the
LP's cuts (`harvest`: 90,000 seeds on `[0, 6]^6` and `[0.6, 3.2]^6`, 48 descents, `maxiter`
300) never found the basin at `(1.04, 1.96, 1.04, 1.04, 1.96, 1.04)`, which is exactly the
failure the stopping-rule comment in `epsstar.py` warned of: *a float multistart is a fallible
oracle, and a later run with a better oracle can only push `upper` down*. Every number in §1
that rests on `0.0079168578` rests on that oracle. No target change rescues a point whose
functional dips `1.5e-5` under the leader's floor. The leader's verifier was fail-closed and
right all three times; the plain bounds it printed, about `0.00789`, happened to land near
the truth for the wrong reason. `artifacts/verifier_cells.json` carries all three rounds with
the arithmetic.

**What is left of hunt #90's question.** Whether AMTOPA are at the ceiling of the pair-weight
and pressure axes at their window is now open again, with the LP's previous answer
(`+5.9e-6` of headroom on `eps`) withdrawn along with the point. The honest re-solve is the
same cutting-plane LP with an oracle that finds these basins: 400,000 seeds on `[0.9, 2.3]^6`,
300 descents plus 200 warm starts from the pool, `gtol 1e-14`. Recorded below when it lands.
The LP value is an upper bound on `eps*` whatever the oracle does, because every cut is a real
gap vector; only the claimed floor was ever soft.

**The re-solve: AMTOPA are at the ceiling of these two axes, to within `8.9e-8`.** Same LP
(`epsstar.eps_star`), same polytope, same window and `B`, started from the committed
2,200-cut pool plus the five minima above, with `harvest` replaced by the oracle in
`resolve_strong_oracle.py` (the seeding and descent settings named above). On the authoring
host, about 13 s a round:

| round | LP value (upper bound on `eps*`) | oracle floor at that `(a, b)` | cuts |
|---|---|---|---|
| 0 | `0.0079186025` | `0.0078899279` | 2,205 |
| 5 | `0.0079139952` | `0.0079073808` | 3,514 |
| 10 | `0.0079125137` | `0.0079065114` | 4,815 |
| 15 | `0.0079117826` | `0.0079098676` | 6,135 |
| 20 | `0.0079113976` | `0.0079103453` | 7,443 |
| 25 | `0.0079113315` | `0.0079110292` | 8,780 |
| 30 | `0.0079112599` | `0.0079108102` | 10,108 |
| 35 | `0.0079112090` | `0.0079110420` | 11,412 |
| 40 | `0.0079112036` | `0.0079110811` | 12,731 |
| 45 | `0.0079111939` | `0.0079106294` | 14,060 |

The LP value never rises, and at every round it is an upper bound on `eps*`. After round 45
(578 s) the next HiGHS solve failed on the 14,000-row model (status 15, `model_status`
Unknown, primal feasible) and the run ended there, so this is **not a converged solve**; the
patience rule never fired. It is a bound that stands. Against the leader's floor
`0.0079111052` (§1's `0.007911105155`, reproduced by the same descent at their `(a, b)`),
`eps*` on the pair-weight and position-pressure axes at their window lies in

    [0.0079111052, 0.0079111939]        MEASURED (float LP and float descents)

Headroom at most `8.9e-8` in `eps`, which by §1's assembly ratio (`+3.96e-6` on the headline
per `+5.75e-6` in `eps`) is under `7e-8` on the headline. §1's `+5.75e-6` of headroom was the
oracle's, not the polytope's. The hunt's own second finding, the two computable axes at their
ceiling, now extends to the two searchable ones: **four of AMTOPA's five axes are at the
ceiling, and the window axis (§7.5) is the only one left, with a lead whose floors came from
the same weak oracle.** (**Closed too, §7.8**: re-priced, all five of that lead's windows are
below their number. Five axes, all at the ceiling.) Whether `eps*` sits at `0.0079111052` exactly (their point optimal)
or up to `8.9e-8` above it is what a converged re-solve with a numerically steadier LP would
settle; it is worth nothing on the headline either way.

---

### 7.8 The window axis, re-priced and closed: five windows, all of them below the record

§7.5 read five windows off a differential-evolution sweep and reported gains of `+3.07e-05`
to `+3.71e-05`, with the caveat that its inner solve was cheap and the figures were
"direction, not magnitude". §7.7 then showed the oracle behind every floor in this hunt
over-reports. Re-pricing the five windows took three passes, and the answer changed sign
between the second and the third.

**Pass one, at each window's own saved weights.** Every `window_search_N.json` records the
`(a, b)` its inner solve settled on, so the claim can be tested by descending at that exact
point. Every floor was over-reported, by `2.6e-05` to `3.0e-05`; all five windows still
cleared the record. That pass was itself optimistic: a second seed of the same oracle
disagreed with the first by `1.8e-05` at a fixed point.

**Pass two, the LP re-solved at each window** from a fresh pool with the oracle of
`resolve_strong_oracle.py`, 40 rounds, 18,400 to 18,800 cuts, about 40 s a round. Upper and
achieved met to `5e-08` at every window, so `eps*` looked pinned:

| window | source | sweep claimed | pass-two floor | LP upper | assembled | vs record |
|---|---|---|---|---|---|---|
| 1 | run `32752160099` shard 0 | `0.0074464746` | `0.0074164707` | `0.0074165292` | `0.6734342829` | `+1.779e-05` |
| 4 | run `32746772911` shard 3 | `0.0076519730` | `0.0076266744` | `0.0076267231` | `0.6734347155` | `+1.822e-05` |
| 5 | run `32752160099` shard 3 | `0.0078219798` | `0.0077999542` | `0.0078000298` | `0.6734330263` | `+1.654e-05` |
| 3 | run `32766484386` shard 2 | `0.0071780293` | `0.0071452504` | `0.0071453076` | `0.6734318428` | `+1.535e-05` |
| 2 | run `32746772911` shard 0 | `0.0072022744` | `0.0071609470` | `0.0071609918` | `0.6734264824` | `+9.991e-06` |

On those numbers the window axis survived at half its reported size, and two candidates were
built at window 1 and put through AMTOPA's verifier, differing only in how far the target sat
below the floor. Their own checks at `b3b7784` pass on both here: `check_candidate.py`
(consistency, span capacity, pressure total), `check_final_bound.py` (`m = 154` and the
bound), and `check_window.py`, which verifies the interval enclosure of `H` above the
`projection_h_floor` computed at *our* window and returns interval positivity lower bound
`0.7619130192389083`. That last one matters on its own: **a window that is not theirs is
admissible to their pipeline**, because `build_interval_tables.py` is "driven entirely by
candidate.json, supports a variable window term count", `check_window.py` recomputes the
window constant rather than trusting it, and `write_verifier_config.py` reads the rest from
the candidate. The interval table for our window is 86,787 coarse cells against their 83,993.
`make_window_candidate.py` is the generator.

| candidate | target | margin below the pass-two floor | assembled | vs record | Actions run | verdict |
|---|---|---|---|---|---|---|
| A | `9263/1250000` | `6.07e-06` | `0.67343037148559612098` | `+1.388e-05` | `34030214675` | 6 of 8 shards accepted, refused on 2 and 4 |
| B | `18533/2500000` | `3.27e-06` | `0.67343217406253723406` | `+1.568e-05` | `34030138950` | 6 of 8 shards accepted, refused on 2 and 4 |

Baseline in both runs: 8 of 8, gate alive, 2 to 19 s a shard.

**Pass three, and it reverses the section.** The cells the verifier refused are not in the
region any oracle in this hunt has ever sampled. Both runs stopped at gap vectors with **one
gap near 2.91** and the rest near `1.04` and `1.97`, for instance
`(1.02612, 1.04787, 2.91613, 1.04262, 1.03838, 1.96788)`. Every float search here, theirs and
ours, seeded gaps in a box around the known minima: `harvest` uses `[0, 6]^6` and
`[0.6, 3.2]^6` but concentrates its 48 descents where its 90,000 samples are lowest, and the
"strong" oracle of §7.7 seeds 400,000 points on `[0.9, 2.3]^6`. A 2.91 gap is outside the
second box and vanishingly sampled in the first. Descending from the refused cells:

| candidate | shard | `F` at the cell midpoint | vs target | tangent bound | descends to | vs target |
|---|---|---|---|---|---|---|
| A | 4 | `0.0074118836` | `+1.48e-06` | `0.0074103765` | `0.0073822070` | `-2.82e-05` |
| A | 2 | `0.0074128857` | `+2.49e-06` | `0.0074102513` | `0.0073523448` | `-5.81e-05` |

The interval Hessian is positive definite at both cells (smallest eigenvalue `0.171` and
`0.153`), so the gate is not the obstruction; the functional simply goes far below the target
a short walk from where the verifier stopped. **The floor was wrong again, by `6.4e-05`.**

Re-measured with a seeding that includes the 2.91 cluster and `[0.9, 4.2]^6`, every window
collapses, and all five land **below** AMTOPA's number:

| window | pass-two floor | wide floor | over-reported by | floor needed to hold the record | assembled | vs record |
|---|---|---|---|---|---|---|
| 1 | `0.0074164707` | `0.0073523448` | `+6.41e-05` | `0.0073888408` | `0.6733929776` | **`-2.35e-05`** |
| 2 | `0.0071609470` | `0.0071119605` | `+4.90e-05` | `0.0071454531` | `0.6733948914` | `-2.16e-05` |
| 3 | `0.0071452504` | `0.0070644452` | `+8.08e-05` | `0.0071214411` | `0.6733797232` | `-3.68e-05` |
| 4 | `0.0076266744` | `0.0075579822` | `+6.87e-05` | `0.0075983518` | `0.6733905077` | `-2.60e-05` |
| 5 | `0.0077999542` | `0.0077457626` | `+5.42e-05` | `0.0077742352` | `0.6733981817` | `-1.83e-05` |

Every wide argmin has exactly one gap in `[2.911, 2.927]`. **The window axis is closed on the
evidence this hunt has: §7.5's `+3.71e-05` is withdrawn, and every window the sweep produced
is worse than AMTOPA's, not better.**

**The control, which is why the above is a measurement and not a scare.** The same wide oracle
run at AMTOPA's own window and their own weights returns `0.0079111052`, identical to the
narrow-box value to `2e-13`, at their published basin
`(1.97808, 1.04406, 1.97301, 1.04598, 1.97445, 1.04230)`. **No 2.91 basin exists at their
point.** Their floor clears the value needed to hold their own headline by `+4.05e-07`, which
is the margin they left themselves, and their verifier accepts 8 of 8. The wide oracle does
not find lower numbers everywhere; it finds them exactly where the verifier said to look, and
agrees with everyone at the one point their own verifier has independently accepted.

Run at *our* withdrawn pair-weight point (§7.7, same window as theirs, our weights) it returns
`0.0078946642`, again at a 2.91 basin, `2.22e-05` under `harvest`'s claim and `1.60e-05` under
what the record needs. So §7.7's withdrawal was right and understated: that candidate is not
merely below AMTOPA's floor, its assembled bound is `-1.03e-05` **below the record**.

**What this says about the whole hunt.** Three oracles were used here, each built to fix the
last one, and all three over-reported the same quantity in the same direction:

| oracle | at our pair-weight point | error |
|---|---|---|
| `harvest`, 90,000 seeds, 48 descents, `maxiter` 300 | `0.0079168578` | `+2.22e-05` |
| §7.7's strong oracle, 500,000 seeds on `[0.9,2.3]^6`, 300 descents, `gtol 1e-14`, 3 seeds, an 18,705-cut pool | `0.0078959857` | `+1.32e-06` |
| the wide oracle, cluster mixture plus `[0.9,4.2]^6` | `0.0078946642` | (the value the verifier's cells confirm) |

The failure was never the descent, the tolerance or the number of starts. It was the seeding
box, every time, and it was inherited every time because each new oracle was built by looking
at where the previous one's minima were. **AMTOPA's interval branch-and-bound is the only
instrument in this hunt that searches the whole box, and it caught all three.** That is the
methodological result, and it is worth more than the arithmetic: on this family, a float
minimum is evidence of nothing until their verifier has seen it, and the right use of a
refusal is to read the cell it names rather than to move the target.

Which also explains the ceiling. AMTOPA's configuration is the one at which the low basin at
a three-unit gap does not open; every direction the LP moves in buys floor among the near-`1`
and near-`2` gaps and pays for it at `2.91`, where no oracle here was looking. That is why
four axes measured as saturated (§4, §7.7) and the fifth now does too.

**The capstone: the LP re-solved at their own window with the wide oracle cannot beat them.**
Same polytope, same window, same `B = 93/23000`, 40 rounds, 13,387 cuts, the oracle of
`wide_floor.py` as the separation routine (`lp_wide.py` in the session record):

| quantity | value | against AMTOPA's floor `0.0079111052` |
|---|---|---|
| LP value, an upper bound on `eps*` over the whole polytope | `0.007912132524` | `+1.03e-06` |
| floor achieved at the `(a, b)` the LP settles on | `0.007909735797` | `-1.37e-06` |

**The LP's own best point is worse than theirs.** Taking the smaller of the two independent LP
upper bounds (`0.0079111939` from §7.7's run, `0.0079121325` from this one, both valid because
every cut is a real gap vector) against their wide-box-confirmed floor:

    eps* on the pair-weight and pressure axes, at their window, in
    [0.0079111052, 0.0079111939]        headroom at most 8.9e-08

which is the §7.7 bracket, now with its lower end measured by the instrument that broke every
candidate this hunt produced. Assembled, even the top of that bracket is worth `+8.4e-07` on
the headline. **AMTOPA's configuration is the optimum of its own polytope, to within a
millionth of their published constant.**

**Grade.** MEASURED. Float LP and float descents on our side, their code for the interval half,
their verifier for every acceptance and refusal, and the analytic bridge inherited and
unreviewed (§6). The one VERIFIED statement in this section is negative: our windows do not
beat their number.

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
