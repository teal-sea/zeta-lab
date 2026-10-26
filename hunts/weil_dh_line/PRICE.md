# PRICE: the out-of-band reduction at the Davenport-Heilbronn line

Hunt #146 (`weil_dh_line`), opened 2026-10-21, items 3 to 6 completed or priced on
2026-10-26 after the owner resumed the lane. Question, windows and rules: `MISSION.md`.
Every number below comes from a JSON artifact in this directory and is pinned by
`test_price.py`, or is hedged where it stands. Grades follow `CLAUDE.md`:
*measured* (one float route), *hardened* (ball enclosures carry every step, or
independent routes agree). Nothing here is kernel-checked, and nothing here bears on
RH (`docs/08`).

## 1. Summary

1. **Floor.** The comb-operator floor `S*_L = λ_max(P)` (the least envelope constant
   any out-of-band `H` can reach, oob_envelope theory Theorem 2) lies in
   `[3.708999, 3.715978]` at `L = 7/5`, `[4.588862, 4.595259]` at `31/20`,
   `[5.637302, 5.643859]` at `L_DH = 1.71079` and `[5.678833, 5.685405]` at
   `L_31 = 1.71699`. Both ends are ball arithmetic: a Rayleigh quotient below and a
   Schur test evaluated on every sub-interval of the window above. *Hardened.*
2. **Per-prime.** `S_sep = Σ_p λ_max(T_p)` is `5.470224`, `6.832880`, `8.930519`,
   `8.930519` (balls of width below `1e-8`, *hardened*); the evaluable sine-kernel
   envelopes at degree 16 give `5.619106`, `7.002783`, `9.157718`, `9.157718`
   (enclosure-carrying, by the oob_envelope code).
3. **Joint, evaluable.** At `L = 7/5` the two-cluster envelope `{3,7,13}`,
   `{2,5,11}` (`joint_1.4.json`, 1190 cosine terms) gives `S <= 4.117981`
   (`S_exact = 18545735548437699/2^52`). At `L_DH` the four clusters `{2,17,29}`,
   `{3,13,23}`, `{5,11,19}`, `{7}` give `S <= 6.418111` (`joint_L_DH.json`; the
   `{7}` cluster is the LP build, `U = 0.736057`, which replaced the earlier
   `0.756960`). No joint envelope was built at `31/20` or `L_31`. Each cluster's
   `U` is the branch-and-bound bound of `joint.sup_bound` over the whole torus:
   rigorous under the IEEE 754 rounding model stated in `joint.py`, with every
   frequency decided in Arb at or above `2L`, Arb re-evaluation of 60 centre
   values and 12 whole boxes per cluster as a second route on samples, and a
   second run of the bound at merge time that reproduced every `U` exactly. Not
   every step is a ball, so the grade is *measured, with an a priori float error
   bound*; not reviewed. Both sit between the floor and the per-prime limit, as
   weak duality and the cost of the build require.
4. **Go/no-go at the DH line: NO-GO for the searched envelopes.** The gate was
   `S <= about 6.2` at `L_DH`. The best evaluable envelope found gives `6.418111`,
   and the construction's own lower bound `LB` (a value at a dyadic point minus
   its error, within `tau = 5e-4` of `U` in each cluster) shows that these `H`
   cannot do better than about `6.416` (the logarithms of distinct primes are
   linearly independent over the rationals, so by Kronecker the line is dense in
   the torus and the sum of the cluster suprema is attained in the limit). Disposition under `ALIGNMENT.md`
   section 5: **attempt unresolved (category 3)** for the searched set, not an
   obstruction. Weak duality allows the gate: the floor `S*_L` lies in
   `[5.637302, 5.643859]`. What does bind is the partition: the Arb lower bound
   for any envelope whose clusters partition the primes into blocks of at most
   three is `6.174396` (`partition_lower.json`: exact search over partitions,
   Arb Rayleigh lower ends of each cluster's floor; Galerkin `6.1744` in
   section 2). The four clusters used are that best partition, so a block-3 envelope must land within `0.026` of its floor to
   pass. Blocks of four primes lower that floor to `5.8989`, at the cost of
   four-dimensional box bounds (the three-prime clusters already took 5.8 to 16.5
   million boxes). By the recorded rules of `price.py` (estimates, not measured),
   `S = 6.418111` means `T# = 2 pi e^{S + 1/2}`, about `6349`, `N` about 9100
   (the stage-B calibration) and about `7e4` core-hours of assembly; the gate
   value `6.2` would mean about `5104` and `3.5e4` core-hours. The composite
   no-go takes the grade of its weakest step: measured.
5. **Scout at `L = 7/5`** (`scout_L140.json`, *measured*). Envelope
   `joint_1.4.json`, even sector, `N = 560`, 640 bits, Gauss-Legendre `q = 64` on
   panels of width `1/2`, `T#` up to 640. `beta* > 0` from `T# = 400`. The
   midpoint LDL of `R(T#)` has 2 negative pivots at `T# = 400`
   (`beta* = 0.033`), 1 at 420 and 440, and none at every checkpoint from 460 to
   640, where the eigenvalue nearest 0 grows from `3.62e-78` to `6.71e-78`. At
   400 and 640 the leading `N = 517` block and the same data at 512 bits keep both
   the pivot count and `lambda_min`, so no sign changed under refinement (kill
   condition 4 not met). This is the `N`-mode block alone: no quadrature error,
   Legendre tail or coupling bound is computed, so it is a scout and not a bound
   on `R_H`. The scout units were built on `parts/provisional_1.4.json`, whose two
   clusters are coefficient for coefficient those of `joint_1.4.json`; the merge
   reproduced its `S` exactly (`RUNS.md`).
6. **K2** (`k2_scouts.json`, *measured*, stage-A blocks as in item 5).
   Epstein `(1,1,6)` at `L_DH` even (form known negative, `c >= 29.304199`) and at
   `L = 1.6615` odd (known negative, `c >= 27.741699`): one negative pivot at
   every checkpoint with `beta* > 0`, with the `N` and precision responses
   agreeing, so the pipeline refuses both. Epstein at `1.6615` even and DH at
   `7/5` even, where the forms are not known negative, show no negative pivot.
   `MISSION.md` task 3 asked that K2 on DH at `7/5` "must return no bound";
   at `7/5` the DH form is not known negative (`c = 16.44 < 30.617188`), so a
   positive stage-A block there contradicts nothing, and the binding kill
   condition is the huntspec's narrower one, DH at `L_DH` (dated correction 3 in
   `MISSION.md`). **DH at `L_DH` was not run** (category 4, paused by
   allocation): its merge is about 1 core-hour and its stage-A run about 19
   core-hours of units plus 3 to 6 of reduction, with 40 unit files of about
   140 MB each (`RUNS.md`, decision of 2026-10-26). Until it runs, K2 at the DH
   line is open. The transfer witness (`price.py --transfer`) was not produced.

## 2. Partition floors

`price_table.json` gives, per window, the best comb-operator floor over
partitions of the primes into clusters of at most `b` primes (Galerkin values,
the lower ends in `partition_lower.json` are Arb):

| `b` | `L = 7/5` | `31/20` | `L_DH` | `L_31` |
|---|---|---|---|---|
| 1 | 5.4663 | 6.8325 | 8.9291 | 8.9288 |
| 2 | 4.3527 | 5.3505 | 6.9802 | 6.9817 |
| 3 | 3.8917 | 4.9639 | 6.1744 | 6.1926 |
| 4 |  | 4.7440 | 5.8989 | 5.9142 |
| 5 |  |  | 5.7508 | 5.7872 |

The per-prime sine-kernel envelopes at degree 64 give `5.481097` (`7/5`),
`6.845298` (`31/20`) and `8.947147` (`L_DH`, `L_31`).

## 3. The doors

1. **Active constraints at the optimum.** At `L_DH` the bound is held by the
   partition into three-prime blocks (floor `6.1744`, `0.026` under the gate)
   and, inside each block, by the gap between the built `H` and that block's
   floor: `6.418111 - 6.1744`, about `0.24`, spread over three large clusters. The
   box count of the three-dimensional bound (5.8 to 16.5 million boxes, 11 to 64
   minutes each) prices every attempt to close that gap.
2. **Frozen constants.** Cluster size (at most three primes; four lowers the
   floor by `0.28` at a much larger bound cost), the coefficient box `D` per
   prime (`[12,4,4]`, `[9,6,6]`; genuine trade against LP size and box count),
   the bound's tolerance `tau = 5e-4` (trade against box count), the LP
   oversampling and rounds, and the dyadic rounding of `h`.
3. **Information class.** Every door above stays inside the data the current
   family reads: the prime comb on `[-L, L]` and out-of-band frequencies at least
   `2L`. Overlapping clusters (`overlap_L_DH.json`) are the same class. None reads
   more arithmetic.

This is a measured optimum over a searched family, not a proved ceiling.
