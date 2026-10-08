# Hunt #122: the tracked pair lands at t_c = 1.0876360002295869..., and the lower endpoint reaches 1.0876359

Status: exploratory probe, complete. Nothing here is a result (`hunts/README.md`).
Narrow frame `s = 1/2 + iz` throughout; the parent hunt's wide-frame values
are the narrow ones times four. Numbers are in `results.json` and pinned by
`test_dh_minus_landing.py`. Reproduce from the repository root:

    .venv/bin/python hunts/dh_minus_landing/probe.py            # about 35 s, one core
    .venv/bin/python -m pytest -q -n0 hunts/dh_minus_landing     # 15 tests, under 3 s

## 1. The question and the answer

`hunts/dh_minus_heat` left `217/200 < Lambda_minus <= 567009/320000` and named
as its first door a later rational heat time for the same conjugate pair, the
one its scout followed from `z = 8.918 + 1.809i` at `t = 0` to depth `0.0726` at
`t = 1.085`. The question here: where does that pair land, and how close to
that time can the parent hunt's own disk instrument still decide a non-real
zero?

**Measured landing time** (two independent routes):

    t_c = 1.087636000229586932217964154453984835461141904   (route A, 50 digits)
    x_c = 7.539944242167335224755075792589912656790177113   (the double real zero)

Route A (mpmath tanh-sinh quadrature, Newton on the double-zero system with
analytic Jacobian) gives the same `t_c` at 30 and 50 digits to `4.6e-26`, with
residuals `8e-53` and `2.7e-54` in `H` and `H'`. Route B (float64 Gauss-Legendre
grid, contour-moment discriminant `Delta(t) = (z_1 - z_2)^2`, winding number
required to be exactly 2) gives `1.0876360002296344` on 480 nodes with a
128-point contour and `1.0876360002296646` on 960 and 256, both within
`5e-14` of route A: the float64 limit, since `H''` at the double zero is only
`0.0395`. Grade of `t_c`: **hardened** (two independent float routes agree); it
carries no enclosure and no claim about any other pair.

**Enclosure-carrying lower endpoint.** Five rational heat times below `t_c`,
each with the pair's upper zero polished to 14 digits and the parent hunt's
Taylor/Rouche disk (`odd_ball.rouche`, radius `1/10^7`) decided positive on all
four of its configurations (96/128/160 bits, theta cutoffs 24/26/28, integration
cutoffs 4 and 7/2):

| rational `t` | `t_c - t` | centre (upper zero) | `abs H(c) <` | `abs H'(c) >` | `M2 <` | written margin |
|---|---|---|---|---|---|---|
| 87/80 = 1.0875 | 1.4e-4 | 7.540109386921 + 0.016492879184804 i | 9e-18 | 13/20000 | 19/10 | 6.4990491e-11 |
| 2719/2500 = 1.0876 | 3.6e-5 | 7.5399879569351 + 0.0084853687310273 i | 1.3e-17 | 33/10^5 | 19/10 | 3.2990487e-11 |
| 108763/10^5 | 6.0e-6 | 7.539951528183 + 0.003464171993609 i | 5.9e-18 | 13/10^5 | 19/10 | 1.29904941e-11 |
| 217527/200000 | 1.0e-6 | 7.5399454567353 + 0.0014143761747912 i | 2.9e-19 | 11/200000 | 19/10 | 5.49049971e-12 |
| **10876359/10^7** | **1.0e-7** | 7.539944363875 + 0.00044772668202446 i | 5.7e-19 | 17/10^6 | 19/10 | 1.69049943e-12 |

The written margin is the exact rational
`r abs H'(c) - abs H(c) - M2 r^2/2` from the coarse column bounds, which are in
the safe direction of every configuration's dyadic endpoints (test). The
Taylor/Rouche argument and its tail accounting are the parent hunt's RESULTS
sections 2 and 3, unchanged; the disk at `10876359/10^7` therefore places one
simple non-real zero of `H_t` at that time, and the parent's section 5 (the set
of real-rooted times is a closed upper ray, Dobner/de Bruijn) turns that into

    10876359/10000000 = 1.0876359 < Lambda_minus <= 567009/320000   (narrow),
    10876359/2500000  = 4.3505436 < Lambda_minus_wide <= 567009/80000  (wide).

Grade of the lower endpoint: enclosure-carrying at the numerical step (Arb
balls with every theta and integration tail charged, exact rational margin
comparison); the surrounding argument is ordinary and model-reviewed only, as
the parent hunt states.

**Pricing the door.** The pair moves the recorded lower endpoint by
`t_c - 217/200 = 2.636e-3`, which is `0.38%` of the recorded gap
`567009/320000 - 217/200 = 0.6869`. The ladder stops `1.0e-7` below `t_c`;
nothing in the instrument stops it earlier (section 4), and nothing below
`t_c` is worth more than that `1.0e-7`. For this pair the door is shut.

## 2. What the pair does after landing, and the other pilot pair

Measured, float route only. After `t_c` the discriminant is positive and the
two real zeros keep separating: `Delta = 0.0080` at `t_c + 10^-3`, `0.098` at
`t = 1.1`, `0.49` at `t = 1.15` (separation `0.70`), with the mean moving
slowly left from `7.5399`. Near `t_c` the measured `Delta` grows like
`8 (t - t_c)`, which is the isolated-pair law. This is a measured absence of
re-merging on `[t_c, 1.15]`, not the no-creation step; the parent hunt's
argument never needed that step for the lower bound and this hunt does not
supply it.

The pilot's second zero, `s = 1.9437 + 18.899i` (depth `1.444` at `t = 0`),
tracked by the same two routes, lands at

    t*_2 = 0.63095343954 (route B, 480 nodes), 0.63095343961 (route A, 30 digits),

the routes differing by `6.7e-11` and the 960-node grid by `1.0e-10`: the
float conditioning is 1600 times worse here because `H''` at that double zero
is `2.45e-5`. It lands `0.457` before the first pair, so among the two pilot
zeros the first is the binding one. The pilot used four seeds below height 20
and is not a census; whether a pair at greater height lands later than
`1.0876360` is the open question that bounds this hunt's reach (section 4).

## 3. Controls, in the four roles of the standing checklist

1. **Rival.** Not applicable in the battery's sense: the subject is itself the
   second Davenport-Heilbronn rival, and no structural statement about zeta or
   RH is made. The structure-matched comparison is the parent hunt's: the plus
   function's threshold is at most `1/2` and has no pair above it to track.
2. **Decoy.** No arithmetic effect is claimed, so no null is owed.
3. **Lesions, each caught by a named check.** A contour of radius `0.05` at
   `t = 1.08` (pair depth `0.124`) returns winding `0` and the tracker refuses.
   A centre displaced by `10^-4` (a thousand radii) at `217/200` is not
   decided. A theta cutoff of `nmax = 2` is not decided. **The shared-layer
   fault:** scaling the residue-2 coefficient by `1.01` in both routes moves the
   landing time to `1.0206817207544` (a shift of `0.067`), and the two routes
   still agree with each other to `1.4e-13`; the zero-time Hurwitz identity
   `H_0(z) = -i F(1/2 + iz)`, which shares no theta integral with either route,
   reports defect `1.2e-3` against `4.9e-31` for the true kernel. Agreement of
   the two routes is therefore evidence about the integrators, and the identity
   is what vouches for the kernel; both ran.
4. **Precision response.** Route A: `4.6e-26` between 30 and 50 digits. Route B:
   `3.0e-14` between the two grids. Disks: every margin is decided at 96, 128
   and 160 bits and at both integration cutoffs, with identical dyadic margins
   across the four configurations at each rung.

Positive controls on known values, through the same libraries: `zeta(2)`
against `pi^2/6` (defect `0`), `gamma_1` against `14.134725141734694`
(`2.1e-16`), `Xi(0)` against `0.4971207781` (`8.8e-11`, the reference's own
precision). The recorded `217/200` disk is rerun at 128 bits and meets its
coarse bounds (`abs H < 10^-14`, `abs H' > 28/10000`, `M2 < 19/10`). The
tracker on exact polynomial heat flows returns `y_0^2/2 = 0.18` for an isolated
pair to `0` and the quartic closed form `0.10041797146407168` to `1.4e-17`
(docs/37, four-root control). The `t = 0` gate reproduces both pilot zeros to
`1.8e-13` and `7.4e-11`.

## 4. Kill conditions and what was not done

None of the five kill conditions fired: the routes agree (`4.7e-14`, threshold
`1e-10`); `t_c` is stable under refinement (`4.6e-26`, threshold `1e-20`); the
`t = 0` gate passes; five rational times above `217/200` are decided; the
second pair lands earlier.

Not done, and why:

- **No census of non-real zeros** of `D_minus` at greater height, so no
  statement that this pair is the last to land. `Lambda_minus` is at least the
  supremum of all landing times (docs/37, "Landing times are unconditional
  lower bounds"), and the pilot found two zeros from four seeds. A census is a
  different information class (section 5) and was outside this hunt's budget.
- **No enclosure of `t_c` itself.** A ball enclosure of the double zero would
  need an interval Newton step on the 2x2 system; the parent's disk instrument
  encloses simple zeros only. The ladder makes this unnecessary for the lower
  bound: any rational `t < t_c` with a decided disk is a bound, and the last
  rung is `1.0e-7` below.
- **No change to the upper endpoint.** The parent's second door is priced in
  section 5 from a number already decided in `hunts/lambda_dh_bounds`; it was
  not rerun here.
- **No novelty search beyond the tree.** The landing-time instruments are
  docs/37 entries from `flow_repair` and `lambda_dh_exact`; the disk is the
  parent's. Bombieri and Ghosh (2011, section 6) publish the minus-function
  phase abscissa to ten digits, which `strip2_results.json` records; no
  published heat constant for this function was searched for here.

Nothing here bears on RH (`docs/08`); the subject is a rival function.

## 5. The doors

### Active constraints at the optimum

The quantity is the strict lower endpoint of the `Lambda_minus` bracket, and
"optimum" means the last rung the ladder can decide. Ranked by what binds:

1. **The landing time `t_c = 1.0876360002295869...` of this pair.** Binding
   absolutely: no disk at `t >= t_c` can decide a non-real zero of this pair
   because it has none. Shadow price of the whole door for this pair:
   `2.636e-3`, now spent to within `1.0e-7`.
2. **Centre accuracy against the pair's depth.** At `t_c - delta` the depth is
   measured as `y = 1.42 sqrt(delta)` (`0.1238` at `delta = 7.6e-3`, `4.5e-4`
   at `1.0e-7`), `abs H'(c)` falls in proportion (`0.00286` to `1.8e-5` on the
   ladder), and the margin `r abs H'(c) - abs H(c) - M2 r^2/2` falls with it:
   `2.9e-10` at `217/200`, `1.8e-12` at the top rung. The saturation slope is
   linear in `sqrt(delta)`; at `delta = 10^-9` the margin would be about
   `1.8e-13` against a remainder `9.5e-15`, still decidable with a 14-digit
   centre. The instrument does not bind before `t_c` does.
3. **Every other pair.** The second pilot pair lands at `0.631` and binds
   nothing. A pair landing after `1.0876360` would move the endpoint, and the
   hunt has no instrument that says whether one exists.

### Frozen-constant inventory

| constant | value | what relaxing it trades |
|---|---|---|
| disk radius `r` | `1/10^7` | larger `r` raises the linear term and the `M2 r^2/2` remainder together; the margin is maximised near `r = abs H'/M2`, about `10^-5` at the top rung, and the choice `10^-7` is the parent's, kept so the two ladders compare; no genuine trade shape below `t_c - 10^-9` |
| ladder times | `87/80, 2719/2500, 108763/10^5, 217527/200000, 10876359/10^7` | chosen as decimal rationals at `delta = 1.4e-4` to `1.0e-7`; finer rungs buy at most `10^-7` |
| disk configurations | 96/128/160 bits, `nmax` 24/26/28, `upper` 4 and 7/2 | the parent's four; identical margins across them say the theta and integration tails are far from binding |
| centre polish | 14 significant digits, mpmath 30 digits | enough for `abs H(c) < 10^-17` at every rung; 12 would do at the top |
| route A precisions | 30 and 50 digits, `nmax = 24`, `upper = 4` | the parent's quadrature window; `t_c` agrees to `4.6e-26` so neither binds |
| route B grid | 480 nodes on `[0, 4]`, `nmax = 14`, contour radius `0.3`, 128 points | float64 limits `t_c` at `5e-14`; doubling both moves it `3e-14` |
| second-pair contour | centre at the last off-axis `x`, radius `0.4`, bracket step `0.01` | a fixed contour fails the winding gate once the real zeros separate past the radius (seen at `t = 0.7` in the prototype) |
| kernel lesion factor | `1.01` on residue 2 | the fault size only sets how far the wrong landing time moves (`0.067`); the reading does not depend on it |
| frame | narrow `s = 1/2 + iz` | the wide frame multiplies every time by four, derived in the parent |
| upper endpoint | `567009/320000` | not touched; see the information class below |

### The information class of each door

- **This door (same pair, later time)** stays inside local analytic data: one
  value, one derivative, one disk-wide majorant of `H_t` near a known zero.
  Its ceiling is `t_c`, measured and hardened, not enclosed. **Shut for this
  pair** to within `1.0e-7`; a kernel-checked or enclosed `t_c` would change
  the grade, not the number.
- **Other pairs (a census).** Requires reading more: the non-real zeros of
  `D_minus(s)` in a box of the critical strip, by an argument-principle count
  (`lambda_dh_bounds` has the chord-tube winding instrument), then each one's
  landing time by the two routes here. The strip half-width `1.882` says how
  deep a pair can sit at `t = 0`; de Bruijn's `y_max(t) <= sqrt(Delta^2 - 2t)`
  gives no useful cap here since `Delta^2/2 = 1.77` exceeds every landing seen.
  Cost unknown; the minus function's zeros at height 9 and 19 were found in
  `0.15 s` each at 40 digits, so a census to height 100 or so is cheap to
  scout, and its reach, not its cost, is the question.
- **The upper endpoint.** Its information class is the strip half-width alone,
  which de Bruijn's Theorem 13 turns into `Delta^2/2`. The parent's second
  door, a sharper strip, is already decided in the tree and not consumed:
  `hunts/lambda_dh_bounds/strip2_results.json` (`control_tau_minus`) decides
  the minus-function phase abscissa `sigma* <= 2.38228610898712387205` at
  `P = 10^5` on both backends (Bombieri and Ghosh 2011 give `2.3822861089`),
  so the upper endpoint can drop to `(sigma* - 1/2)^2/2 = 1.77150049804...`,
  from `1.771903125`: worth `4.03e-4`, `0.06%` of the gap, and STRIP2 section
  3.3 proves the phase lemma is the end of that line (the modulus constraint
  is free at the argument-maximising point). **Repriced, not rerun.** Anything
  further for the upper endpoint needs a different class: either a theorem
  sharper than `Delta^2/2` for a strip of known zero density, or the
  Polymath-15 route of tracking every zero below some height plus an
  unconditional argument above it. Both are larger than this bracket.
