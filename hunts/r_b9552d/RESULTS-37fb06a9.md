# Where T1 resists, measured

**Hunt r_b9552d, run `37fb06a9-44a6-42d5-abc3-4c1342b1287b`, 2026-08-18.**
Instrument: `probe.py` (runs end to end in ~6 minutes; `--quick` in ~10 s).
Data: `results.json`.

**Status: not settled, as expected.** `k >= 3` is not closed, T1 is not
proved, and nothing here moves the reading of record. What this run has is a
restatement that makes T1's difficulty explicit, one exact constant that was
previously a measurement, a sharper search for the gas extremum with its
power stated, and one recorded number that did not reproduce. Nothing here is
evidence for or against RH (`docs/08`). The reserved certification word is
not used.

Grade: **measured**. Every sup in section 3 is a scan in double precision
over a finite search space; section 1 is an identity checked to rounding;
section 2's constant is exact but its use as a ceiling inherits the
measurement that `P = 0` on the critical lattice out to `d = 4000`.

---

## 1. T1, restated against the budget that is already proved

`gram_form.budget_gram` computes the true `k`-pair budget
`B = (1/2)[G_T(2y) + G_T(0)] - k A^2`, and `B >= 0` is the one piece of the
`k >= 2` frame that already follows from a kernel-checked theorem
(`Retention.energy_F_ge`, plus `cosh^2 >= 1`, plus `c2 >= 0`). Splitting the
two Gram sums into diagonal and off-diagonal parts gives

    2 B(T,y)  =  k Shq(y)  +  sum_{p!=q} [ Kpair(tau_pq) - D(2y, tau_pq) ],

and since `Dam = max(0,D) = D + [-D]^+`, writing
`GAS(T,y) := sum_{p!=q}[Dam(2y,tau_pq) - Kpair(tau_pq)]` (so T1 reads
`GAS <= k Shq(y) (1-rho)`):

> **(R)**  `GAS(T,y)  =  k Shq(y)  -  2 B(T,y)  +  P(T,y)`,
> where `P(T,y) := sum_{p!=q} [ -D(2y, tau_pq) ]^+  >=  0`.

Checked over 300 random configurations (`k` in 1..7, `y` in (0.01, 0.5],
centres spread over 90 units): worst absolute residual **7.99e-15**. This is
an identity, not a bound, and it is what the rest of the page is built on.

Two things fall straight out, and they are the reason (R) is worth writing.

**(1a) The signed form of T1, with `rho = 0`, is already a consequence of a
kernel-checked theorem.** Replace `Dam` by `D`, i.e. drop `P`, and T1
becomes exactly `2B >= 0`. So the entire content of T1 is (i) the strict
positivity of `rho`, and (ii) the positive-part loss `P`, which is precisely
the credit thrown away by the `D <= Dam` step that every cap-mode accounting
in this tree performs. Naming the two halves separately is the point:
`K2-TWO-SPECIES.md` §5 states T1 as one obligation, and it is two.

**(1b) An exact ceiling on the atom reserve.** T1 holds with reserve `rho`
if and only if `rho k Shq(y) <= 2B - P`, hence for every configuration

    rho  <=  (2B - P)/(k Shq(y))   <=   2B/(k Shq(y)).

## 2. The ceiling, in closed form

On the critical `2*pi` lattice `B/k -> c2(0) - A^2` exactly, by Poisson
summation with the endpoint aliases vanishing because `c2(+/-1) = 0` (defect
#24; `counting_lemma.CRITICAL_LATTICE_LIMIT`). Measured here, `P = 0` on that
lattice out to `d = 4000`: **every multiple of `2*pi` up to 25000 lies inside
a depth-1 damage window**, so the positive-part credit is not merely small
there, it is absent. Therefore

> **the atom reserve can never exceed**
> `rho*  <=  2 (c2(0) - A^2) / Shq(1/2)  =  0.153216295...`

| quantity | value |
|---|---|
| `c2(0) = 1/2 + sin(sqrt2)/(2 sqrt2)` | 0.8492279993183042 |
| `A^2` | 0.8440563052346255 |
| `lim_k B/k` on the `2*pi` lattice (exact) | 0.0051716940836786796 |
| `Shq(1/2)` | 0.06750840786062762 |
| **`rho` ceiling, against the true `Shq`** | **0.153216295497762** |
| `rho` ceiling, against Lean's proved floor `2 Shq y >= 0.51944 y^2` | **0.119590024745568** |

The second row of that pair is the one a proof has to live with. A proof may
only spend the proved floor `2 Shq(1/2) >= 0.12986` on the right of T1 while
the honest `GAS` sits on the left, and the 3.8% the floor concedes comes
straight out of the reserve: `[(2B-P)/k - (Shq - F/2)]/(F/2) = 0.11959`.

**What this replaces.** `K2-TWO-SPECIES.md` §5 records the gas as eating
"87.8% of the per-centre budget" on the worst uniform lattice, a scan. The
complement of that ratio *is* the reserve, and it now has a closed form. Any
atom argument (T2/A) must fit inside `0.1196` of the per-centre budget, not
inside the `0.122` the scan suggested, and never inside more than `0.1532`
however the budget floor is later improved.

The finite-`k` ladder approaching it, recomputed here in the `O(k)`
translation-invariant form:

| `k` | `B/k` on the `2*pi` lattice |
|---:|---|
| 64 | 0.006638323790 |
| 256 | 0.005624461221 |
| 1024 | 0.005306413510 |
| 4096 | 0.005210755854 |
| 16384 | 0.005182805005 |
| `-> inf` | 0.005171694084 (exact) |

## 3. The gas extremum, searched three ways

The row reported is the `k -> inf` per-centre `GAS/k`; T1 is the statement
that it stays below `Shq(1/2) = 0.0675084`. `two_species.centre_gas_row`
prints twice this; the `x2` column is given where it helps comparison.

**(C) Periodic occupancy.** For every period `p <= 14` and every one of the
`2^(p-1)` occupancy subsets of `Z_p` containing 0, at every base spacing
`lam` on a grid of 230 values from 5.30 to 13.0, with the exact `k -> inf`
row computed by cyclic autocorrelation against a lattice-sum vector truncated
at `|d| <= 3000`; then the winning pattern's `lam` refined by 45 golden
sections. **65,533 patterns x 230 spacings.**

**(D) Free periodic.** The same limit without any lattice: `m <= 8` free
positions inside a free period, Powell-refined from the uniform lattice, from
the recorded irregular pattern, and from 8 random cells per `m`.

**(D') Free finite `k`.** `k` in {6, 10, 16, 24}, 12 restarts, positions
entirely free.

| search | best row | `x2` | ratio to `Shq(1/2)` | implied `rho` |
|---|---|---|---|---|
| (C) occupancy, `p <= 14` | 0.0571559 | 0.114312 | 0.8466 | 0.1534 |
| (D) free periodic, `m <= 8` | 0.0571077 | 0.114215 | 0.8459 | 0.1541 |
| (D') free finite `k = 24` | 0.0509769 | 0.101954 | 0.7551 | 0.2449 |
| (D') free finite `k = 16` | 0.0486155 |, | 0.7201 | 0.2799 |
| (D') free finite `k = 10` | 0.0448429 |, | 0.6643 | 0.3357 |
| (D') free finite `k = 6` | 0.0390832 |, | 0.5789 | 0.4211 |

**Every one of the three searches returned the uniform `2*pi` lattice.** The
occupancy search's winner at `p = 13` is the all-ones pattern at
`lam = 6.283267`; the free periodic search collapses to `lam = 6.2837` from
every seed at every `m`; the residual spread across (C) and (D), 4.8e-5, is
the lattice-sum truncation, not a different configuration. Finite `k`
approaches the same row from below, monotonically, as the boundary deficit
shrinks.

So, within this search's reach: **the gas extremum sits at the uniform `2*pi`
lattice and the extremal reserve equals the ceiling of section 2.** That is
the sharpened measurement asked for, and it is a *measurement about a search*,
not a theorem: the search is finite in period, in spacing grid, in restarts,
and in `m`.

**Power (control F).** Inflating only the damage half of the per-pair charge
by a factor `c` and re-running the occupancy search:

| `c` | best row | ratio | reports T1 violated |
|---|---|---|---|
| 1.00 | 0.057147 | 0.8465 | no |
| 1.05 | 0.060262 | 0.8927 | no |
| 1.10 | 0.063378 | 0.9388 | no |
| 1.15 | 0.066494 | 0.9850 | no |
| **1.20** | **0.069609** | **1.0311** | **yes** |
| 1.30 | 0.075841 | 1.1234 | yes |
| 1.50 | 0.088303 | 1.3080 | yes |

The ladder first fires between 1.15 and 1.20, against a measured relative
margin of `1/0.8465 = 1.181`. The detector fires exactly where the margin
says it should, so the "no violation found" verdict above is a verdict from a
search with demonstrated power rather than from a search that cannot fail.

Two further controls: the numpy kernel used by the searches agrees with
`gram_form`'s scalar `cmath` path to **2.22e-16** over 4000 points on
`[0, 400]`; and the identity of section 1 is the null, an accounting error
anywhere in the row computation would show there first.

## 4. The recorded irregular-occupancy pattern did not reproduce

`two_species.NAMED_GAPS` G4 records the one reason on file to believe the gas
extremum is *not* the lattice:

> "the centre-gas extremum over CONFIGURATIONS is not the uniform lattice:
> the 1,1,2,1,1,2,3 pattern at step 2*pi gives a per-row 0.1200 > 0.1140."

The pattern's reading is not stated. All three natural readings were
evaluated, in the `x2` normalisation `centre_gas_row` prints, with the
lattice sums carried to `|s| <= 6000`:

| reading | `x2` row |
|---|---|
| entries are gaps in units of `2*pi`, averaged over the 7 centres | 0.066560 |
| entries are gaps, **maximum** over the 7 centres | 0.090247 |
| entries are site multiplicities on the `2*pi` lattice | −1.359947 |
| uniform `2*pi` lattice, same instrument | **0.114263** |
| the recorded claim | 0.1200 |

**None of them exceeds the uniform lattice, and none of them reproduces
0.1200.** The multiplicity reading is far negative because coincident centres
pay `f(0) = -Kpair(0) = -A^2 = -0.844` per ordered coincident pair, which is
the largest single number in the problem.

This is a failure to reproduce, and it is reported as exactly that. Three
outcomes are consistent with it: the pattern means something this run did not
try; the recorded number is a per-centre maximum or some other non-average
quantity, in which case it is not a counterexample to T1 at all (T1 is an
average statement, it sums over all ordered pairs and divides by `k`); or
the recorded number is wrong. **This run cannot distinguish them and does not
claim to.** It matters because G4 is the stated ground for calling the gas
extremum "an optimisation obligation, not a formula", and if the lattice is
in fact extremal on the average, that obligation is materially smaller than
recorded. Resolving it is the first thread below and, on this run's reading,
the single highest-value cheap follow-up in the whole T1 area.

## 5. The certificate route, assessed and not settled

The natural proof route for T1 is a Cohn–Elkies-style certificate: a function
`G` with `G >= f := Dam(2y,.) - Kpair(.)` pointwise and `Ghat <= 0`
everywhere. Then `sum_{p,q} G(tau_pq) = int Ghat |That|^2 <= 0` for **every**
configuration, so `GAS <= -k G(0)`, and T1 follows for all `k` at once
whenever `-G(0) < Shq(1/2)`. This is not on the recorded dead list, and it is
not any of the five routes there: it is not per-pair (it bounds the whole
quadratic form), it assumes no separation, it relaxes nothing about the
atoms, and it is not Cauchy–Schwarz.

Parametrising `G(s) = -int mu(w) cos(sw) dw` with `mu >= 0` piecewise
constant makes `Ghat <= 0` structural, and minimising `int mu` subject to
`G >= f` on a grid is a linear program whose value is what the route can
deliver. **Truncating the constraint set to `s <= s_max` only relaxes the
program**, so the truncated value is a *lower* bound on the untruncated one:
if it ever exceeded `Shq(1/2)`, no certificate of this form could prove T1,
and the route would be dead with a witness.

It did not get there at this cost. The horizon ladder:

| `s_max` | constraints | HiGHS status | LP value |
|---:|---:|---|---|
| 60 | 1500 | optimal | 0.0472509 |
| 120 | 2000 | optimal | 0.0521864 |
| 200 | 3000 | optimal | 0.0541015 |
| 400 | 5000 | numerical failure |, |
| 600 | 7000 | infeasible (reported) |, |

At `s_max = 200` (3000 constraints, 200
measure cells) the value is **0.054102**, which is 80.1% of `Shq(1/2)`, and
also *below* the achievable row 0.05716 of section 3, which proves the
truncation is still biting and the number therefore carries no upper-bound
content at all. Pushing the horizon to 400 and 600 returned solver failure
(HiGHS status 4 and 2) rather than a value.

So: **the certificate route is neither established nor killed here.** What is
established is the shape of the question, the LP value must rise above
0.05716 before it means anything, and it must stay below 0.06751 for the
route to work, so the whole verdict lives in a 15% window that this
discretisation could not resolve. That is a narrow enough target to be worth
one properly conditioned attempt. The reported infeasibility at `s_max = 600`
is **not** read here as the route being dead: the same discretisation had
already failed numerically at 400, and an infeasibility certificate from a
solver that has just lost conditioning is not a witness.

## 6. What this does and does not settle

* **Does not** close `k >= 3`, `k >= 2`, or T1. The blocker stands.
* **Does not** prove `rho > 0`. It proves `rho <= 0.1532` (and `<= 0.1196`
  against the proved floor), which is a ceiling, not a floor. The two are
  opposite statements and this run only has the useless-for-a-proof one.
* **Does** reduce T1 exactly to `2B - P >= rho k Shq`, splitting it into a
  part that follows from a kernel-checked theorem (`B >= 0`) and a part that
  is entirely the `D <= Dam` loss (`P`).
* **Does** give the gas extremum an exact value under this search, replacing
  the measured 87.8%.
* **Does** record that the one on-file reason to doubt lattice extremality
  did not reproduce.
* Every number here is double precision, no enclosures, no Lean.

## Loose threads

1. **The G4 pattern.** *What:* `two_species.NAMED_GAPS` G4's
   `1,1,2,1,1,2,3` row of 0.1200 did not reproduce under any of three
   readings (§4), all of which come in below the uniform lattice.
   *Why it might matter:* G4 is the recorded ground for treating the gas
   extremum as an open optimisation rather than a one-parameter formula. If
   the uniform lattice really is extremal on the average, T1 reduces to a
   one-parameter question with an exact answer already in hand (§2), which
   is a materially different obligation from the one on file.
   *First step:* recover the code path that produced 0.1200, it is not in
   `two_species.py`, which has no irregular-occupancy function, and state
   the pattern's reading and its normalisation in G4.

2. **The LP horizon.** *What:* the certificate LP (§5) needs its value to
   pass 0.05716 before it carries upper-bound content, and the solver failed
   above `s_max = 200`. *Why it might matter:* a value in (0.05716, 0.06751)
   would still leave the route open, but a value above 0.06751 would kill it
   with a witness, which is a clean (d)-grade result on a route not yet on
   the dead list. *First step:* replace the uniform `s` grid with one
   concentrated on the damage windows (where the constraint actually binds,
   `f <= 0` elsewhere), rescale `mu` by cell width, and re-solve with
   `highs-ipm`; the constraint count should drop by an order of magnitude
   and with it the conditioning problem.

3. **`P = 0` on the critical lattice is a measurement, not a lemma.** *What:*
   §2's ceiling uses `[-D(1, 2 pi d)]^+ = 0` for all `1 <= d <= 4000`, i.e.
   every multiple of `2*pi` out to 25000 sits inside a depth-1 damage window.
   The depth-1 window ladder has spacing ~6.23 against `2*pi = 6.2832`, so it
   drifts, and the windows are ~1.9 wide, the drift should eject a lattice
   point eventually. *Why it might matter:* if it never does, that is a
   statement about the damage windows worth proving; if it does at some
   `d`, the ceiling is very slightly loose and the exact `rho*` is smaller
   than 0.153216. *First step:* locate the window edges as a function of `s`
   at depth 1 out to `s ~ 10^5` and check whether the drift is genuinely
   linear or whether the window centres track `2*pi` asymptotically.

4. **Mixed depths in the gas.** *What:* everything here is `y = 1/2` (the
   deepest, and the worst for the budget). `K2-TWO-SPECIES.md` §5 records
   that mixed depth *relieves* the gas (ratio 0.878 -> 0.578 at `y = 0.3`),
   and (R) is depth-general, but the search was not run at other depths.
   *Why it might matter:* T1 must hold for all `y in (0, 1/2]` and for
   per-pair depths; if the equal-depth `y = 1/2` case really is extremal that
   is one v-convexity argument away from covering the rest, exactly as in the
   `k = 2` closure. *First step:* re-run search (C) at `2y in {0.2, 0.5, 1.0}`
   and check that the row over `Shq(y)` is maximised at `y = 1/2`.
