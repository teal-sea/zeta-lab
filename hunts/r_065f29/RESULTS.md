# R-065F29: white-box attack on `urms2-0.51`

**Outcome: the attack ran, the claim is not withdrawn, and it found three
things about the record that a reader leaning on this claim should know.**

The mathematics of the load-bearing new step survives direct numerical
attack in the regime the old proof forbade. What does not survive is the
supporting apparatus: the "independent" audit route for one gate is a second
arithmetic assembly of the same numbers, the recorded rational witness does
not select `51/100`, four of the six obligations the theorem lists have no
gate, and the record's own falsification control runs on a coefficient family
that violates the hypothesis of the step it is offered as evidence for.

Nothing here is evidence for or against RH (`docs/08`).

Reproduce: `python3 hunts/r_065f29/probe.py` (numpy and sympy only; no
`zeta` import, no mpmath, no network). Numbers below are from
`results.json`, written by that run.

## The table

| # | Checklist entry attacked | What was tested | Result |
|---|---|---|---|
| A1 | non-realizable extremizers | does `urms2_051_witness()`'s four-margin system select `α = 51/100`? | **No.** At the published `(δ,γ,ε)` it admits `α` up to `257/500 = 0.514`; with `(δ,γ,ε)` free it admits `α = 0.9` with all four margins positive. |
| A2 | non-independent independent checks | mutate the layer the two window routes share; do they diverge? | **No.** Both move by exactly `4.426081703885579e-27`. Tail terms are bit-identical; the JSON fixture reproduces `corrected_coefficients(40)` exactly. |
| A3 | hidden approximations | evaluate `∫_U^{2U}|P|²dt` exactly at `W/U` from 1.3 to 9.9 | **Claim survives.** The block second moment saturates: `17.2964 → 17.3455 → 17.3593 → 17.3642`, a move of 0.39% while `W/U` grows 7.5×. |
| A5 | finite-grid artifacts | does the record's control family satisfy `A(y) ≪ y log y`? | **No.** `A(y)/(y log y)` climbs by a factor of **88** from its trough (0.0231 at `y=400`) to the top of the array (2.036 at `y=22026`). |
| A4 | correlated assumptions | cross §7's obligation list against the audit's six gates | **4 of 6 ungated**: infinite tail, initial height interval, height commutator, contour localization. |

## A3: the load-bearing step holds where it was attacked

`URMS2-051.md` §3 replaces the worst-spacing majorant with the
spacing-sensitive Montgomery–Vaughan estimate, and §4 concludes the
off-diagonal error is `O(x log x)` independent of the upper length `W`. The
whole half-band crossing rests on this: it is what converts the old
`γ < δ < 1` condition, which is infeasible at `α = 0.51`, into `α < δ`, which
is not.

The probe evaluates the exact block second moment

    ∫_U^{2U} |Σ_{n≤W} c_n n^{-it}|² dt
      = U Σ|c_n|² + Σ_{m≠n} c_m c̄_n K_U(log(m/n)),  K_U(θ) = ∫_U^{2U} e^{-itθ}dt

as a closed-form double sum on the author's own frozen level-two coefficient
array, with the two-range weights `√n/x` and `x/n^{3/2}` of §1, at `U = 300`,
`x = e^{0.51·8} = 59.1`, and `W` swept to 2980. This is the regime
`W ≫ U` that the old proof's `W/U = o(1)` forbade.

The integral saturates to four significant figures. That is the
`W`-independence the claim asserts, measured rather than argued, and it is
the strongest positive result of this attack. The deviation from `U Σ|c_n|²`
also stays inside the claimed `O(Σ n|c_n|²)` throughout, with ratio in
`[0.400, 0.883]`.

One caveat, stated because the number invites a wrong reading: that ratio
*falls* across the sweep, which looks like a widening safety margin but is
partly its denominator inflating on this particular coefficient family (see
A5). The saturation of the integral does not depend on the denominator and
is the observation to lean on.

A second caveat: at `U = 300` the off-diagonal is the same order as
`U Σ|c_n|²`, so this test confirms the *bound* and the `W`-independence, not
the asymptotic main-term dominance, which lives at `U → ∞`.

## A5: the record's own control does not satisfy its own hypothesis

This is the finding with the most consequence for how the claim should be
read.

§4 derives the `W`-independence from `A(y) = Σ_{n≤y}|a_{2,U}(n)|² ≪ y log y`,
supplied by RAMS2, via partial summation on `x² Σ_{x<n≤W}|a(n)|² n^{-2}`.
The probe checks that mathematics twice.

**The mathematics is correct under its hypothesis.** On a surrogate family
built to satisfy the law exactly (`|b(n)|² = log n`), the upper-range sum
saturates as `W` grows 67×: `441.6 → 691.3 → 830.4 → 907.1 → 984.7`. §4's
step does what it says.

**The record's control family does not satisfy the hypothesis.** On the
frozen level-two array from `dirichlet_recurrence.py`, the family
`half_band_crossing.finite_height_spacing_experiment` runs on, and the source
of §9's `ℓ = 6, 8, 10` table, `A(y)/(y log y)` is not bounded. It falls to a
trough of 0.0231 at `y = 400` and then climbs to 2.036 at `y = e^10`, a factor
of 88. Swept at fixed `x`, the upper-range sum on that family grows like
`W^{0.825}` (32.1× over the same sweep) instead of saturating.

**Why §9's table cannot see this.** The `ℓ` ladder moves `x = e^{0.51ℓ}` and
`W = e^ℓ` together, holding the effective `γ` at 1. It therefore reports the
ratio `spacing cost / (x log x)` along a single ray and never varies `W` at
fixed `x`, which is precisely the quantity §4 claims is `W`-independent. Its
reassuring decreasing sequence (0.409, 0.282, 0.185) is consistent with
`W`-independence and equally consistent with `W^{0.825}` growth. The probe
reproduces that table's `ℓ = 8` entry to five digits (0.28176 against the
recorded 0.28174), so this is the same object, read along a second axis.

What this does **not** show: `dirichlet_recurrence.py` says in its own
docstring that it is "a frozen finite model, not a tail theorem", and RAMS2,
not the frozen model, is the actual analytic input to §4. So this is not a
counterexample to RAMS2 and not a kill. It is narrower and still worth
recording: **§9's falsification control has no power over the step it is
attached to**, because the family it runs on violates that step's hypothesis
and the ladder is structurally blind to the failure mode. A reader who took
that table as numerical support for the `W`-independence took support that
is not there.

## A2: gate 6's "independent route" is arithmetic, not independence

`URMS2-051-AUDIT.md`'s verdict table lists six gates, each with an
"independent route". For the `0.51` window functional the route is given as
"JSON coefficient fixture and rebuilt tail sum", and
`urms2_051_audit.py`'s docstring says it "does not call
`constant_window_bound`". Both statements are true. Neither delivers
independence.

- The fixture `C2_EXTENDED.json` reproduces `corrected_coefficients(40)`
  exactly, index for index. It is a snapshot of the function the primary
  route calls, not a second derivation.
- Both routes import `fock_upper_coefficient`, `coarse_upper_coefficient`,
  `MAJORANT_CUTOFF` and `TWO_STEP_RATIO` from `corrected_form_factor`. The
  tail terms come out bit-identical as exact rationals.
- Perturbing `fock_upper_coefficient(41)` by one part in `10⁶` moves both
  `denominator_upper` values by the identical amount,
  `4.426081703885579e-27`.

A check that cannot diverge from what it audits has no power against a fault
there. This is `WHITEBOX_CHECKLIST` entries 2 and 5 verbatim, and the same
shape as the `docs/25` shared-parsing-layer incident the checklist was built
from. The honest description of gate 6 is *a second arithmetic assembly of
the same numbers*, which catches assembly errors and nothing upstream of
them. The five decimal digits of `0.0147728663285376` are therefore
single-sourced through `corrected_form_factor`.

## A1: the witness does not derive `0.51`

`half_band_crossing.urms2_051_witness()` records four margins at
`α = 51/100, δ = 3/4, γ = 21/20, ε = 1/100`. All four are positive, as
recorded. But they do not bind at `51/100`:

- At the published `(δ, γ, ε)`, the binding margin is `far_tail_margin` and
  the system stays feasible to `α = 257/500 = 0.514`.
- `γ` is bounded above by nothing in the recorded system, §4's whole point
  is that the upper length may cross `U`, so `far_tail_margin` can be made
  positive at any `α` by raising `γ`. `δ` is bounded only by
  `initial_interval_margin > 0`, i.e. `δ < 1`. The probe exhibits feasible
  witnesses at `α = 0.6, 0.7, 0.74, 0.8, 0.9`.

So the four margins as encoded permit every `α < δ < 1`. `51/100` is not
derived from them.

Reading `hunts/higher_xi/MISSION.md` confirms this is by intent rather than
by error: the target comes from downstream, where "the downstream window
problem has exact bounds `0.5 ≤ β_useful ≤ 0.51`" and "bandwidth optimization
stops at this first corrected theorem". `0.51` is the first rational past the
half band that makes the window functional useful. The claim as worded, that
the bandwidth "extends past the half band to 0.51", is a lower bound and is
not overstated.

The finding is about the record, and it is sharp: **if the encoded margins
permitted `α` up to `δ < 1`, the method would prove far more than `0.51`, and
it does not.** Something binds that is not written down. A4 says where to
look.

## A4: where the unrecorded constraint most likely lives

§7 rests URMS2-051 on six obligations. The audit gates two of them. The other
four,

- infinite tail `o(U log U)` by the `9/1000` exponent margin,
- initial height interval,
- height commutator,
- contour localization

- are carried by the sentence "retain their earlier bounds". Those earlier
bounds were established under `γ < δ < 1`. This proof's entire novelty is
`γ = 21/20 > 1`. Inheriting a bound across the regime change that the proof
itself introduces is the correlated-assumption shape the checklist names,
and it is the one place this attack could not close: it is a claim about
prior derivations that are not in `hunts/higher_xi/` in a form the probe can
evaluate.

If a constraint genuinely caps the band below `δ`, the probe's reading is
that it is in one of these four, most plausibly the height commutator or
contour localization at `γ > 1`.

## What this attack did not settle

- Whether RAMS2 in fact supplies `A(y) ≪ y log y` for the true `a_{2,U}(n)`.
  The probe measured the frozen model, which is explicitly not the analytic
  object. Settling this needs the RAMS2 statement itself, not a finite model.
- Whether the four ungated §7 obligations survive at `γ > 1`. This needs the
  earlier derivations, which are not in this tree in evaluable form.
- The asymptotic regime. `U = 300` confirms a bound and a saturation, not a
  main-term asymptotic.
- The claim is **not withdrawn**. No fault was found in the mathematics of
  the half-band crossing itself.

## Loose threads

1. **The `α < δ < 1` gap.** If §4's mean-value gain is as general as the
   encoded margins suggest, the recorded system proves URMS2 well past
   `0.51`, up to `δ < 1`. Either the result is substantially understated or a
   real constraint is missing from the record. *Why it matters:* the
   difference between "bandwidth 0.51" and "bandwidth approaching 1" for a
   level-two pair statistic is not a rounding of the same result.
   *First step:* re-derive the height commutator and contour localization
   bounds at `γ = 21/20` rather than inheriting them, and see which one
   caps `α`.

2. **`docs/25`-shaped shared-layer risk across `hunts/higher_xi/`.** A2 found
   one gate whose independence is arithmetic re-derivation over a shared
   fixture. The same import pattern (`from corrected_form_factor import ...`)
   appears in `bandwidth_forensics.py`, `urms2_051_audit.py` and
   `dirichlet_recurrence.py`. *Why it matters:* if any other "independent"
   gate in that hunt shares the same substrate, the audit's six-of-six pass
   rate overstates the coverage. *First step:* run the same one-part-in-`10⁶`
   mutation against each of the six gates and record which ones move.

3. **A `W`-at-fixed-`x` axis for `finite_height_spacing_experiment`.** The
   existing function sweeps `ℓ` only. Adding a `W` parameter would let the
   record's own control test the quantity §4 actually claims. *Why it
   matters:* this is a two-line change that converts a control with no power
   into one with power. *First step:* add `W: int | None = None` to
   `finite_height_spacing_experiment` and truncate `integers` accordingly.
   (Not done here: `hunts/higher_xi/` is outside this hunt's write scope.)

4. **The frozen model's second-moment blow-up may itself be interesting.**
   `A(y)/(y log y)` on the level-two recurrence is not merely unbounded, it
   has a clean trough near `y ≈ e^{0.55ℓ}` and then climbs with a stable
   slope. *Why it might matter:* if that trough location tracks `ℓ`
   predictably it is a property of the level-two coefficient family, not an
   artifact, and would say something about where the frozen model stops
   proxying the real object. *First step:* locate the trough at
   `ℓ = 8, 10, 12` and check whether `log(y_trough)/ℓ` is stable.
