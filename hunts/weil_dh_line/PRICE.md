# PRICE: the out-of-band reduction at the Davenport-Heilbronn line

Hunt #146 (`weil_dh_line`), opened 2026-10-21, items 3 to 6 completed or priced on
2026-10-26 after the owner resumed the lane. Question, windows and rules: `MISSION.md`. Item 7, the dated corrections
and doors 5 and the additions to doors 2 to 4 were added on 2026-10-27.
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
   (Correction 2026-10-27, the text above left as written. The sentence "At
   400 and 640 the leading `N = 517` block and the same data at 512 bits keep both
   the pivot count and `lambda_min`, so no sign changed under refinement (kill
   condition 4 not met)" overstates both responses. Neither is a refinement: the
   leading block is a principal submatrix, whose least eigenvalue Cauchy
   interlacing puts at or above the full block's, and the "same data at 512
   bits" were the 640-bit midpoints copied unrounded (`arb(x.mid())` does not
   round), so that response re-ran only the reduction's arithmetic. Kill
   condition 4 was therefore not tested at `7/5`, rather than not met; for a
   positive block the refinement that matters is a larger `N`, which can only
   lower `lambda_min`, and none was run. `scout.responses_of` now rounds the
   data.)
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
   `MISSION.md`). **DH at `L_DH`** (run B, streamed on 2026-10-26: envelope
   `k2env_dh_L_DH.json`, `S = 6.039785`, every cluster re-bounded at merge time;
   `N = 856` even modes, 1280 bits, `T#` to 800): `beta* > 0` from `T# = 540`,
   and at all 14 checkpoints from 540 to 800 the midpoint LDL has exactly one
   negative pivot and no undecided one, with `lambda_min` from `-6.687e-30` to
   `-4.152e-30` (inverse-iteration residuals below `1e-83`). At 540 and 800 the
   leading `N = 791` block and the 1152-bit reduction keep the pivot count and
   `lambda_min` to 12 digits. So the pipeline refuses DH at the DH line at every
   checkpoint it reached, and the binding kill condition (a positive bound for
   DH at `L_DH`) **did not fire**. Scope and grade: *measured*, the `N`-mode
   block of stage A on `T# <= 800`, with no quadrature error, Legendre tail or
   coupling bound, so it is evidence about the pipeline at these parameters and
   not a soundness theorem for it. The negative eigenvalue is tiny, as expected
   just past the DH line (`c = 30.6178` against `30.617188`), and its magnitude
   shrinks as `T#` grows (by about 38% from 540 to 800); whether it stays below
   0 beyond `T# = 800` is not measured. Item 6 therefore leaves category 4: the
   check ran and passed at its stated scope, and the full soundness statement
   (stage B with its error terms) remains **attempt unresolved (category 3)**.
   The run cost about 16.9 core-hours with the merge (`RUNS.md`), with no unit
   files written. The transfer witness (`price.py --transfer`) was not produced.
   (Corrections 2026-10-27, the text above left as written. (a) "At 540 and 800
   the leading `N = 791` block and the 1152-bit reduction keep the pivot count
   and `lambda_min` to 12 digits": the same two responses as in item 5, with the
   same limits; the 1152-bit one reduced the 1280-bit data unrounded. Re-run
   with the data rounded (`scout.responses_of`) from the stored state at
   `T# = 800`, both keep one negative pivot and `lambda_min =
   -4.15160674834e-30`. (b) "The negative eigenvalue is tiny, as expected just
   past the DH line": tininess alone says little, since the form's whole
   near-null spectrum is on that scale (the leading 100-mode block's eigenvalue
   nearest 0 is `+4.06e-32`); the comparison that matters is with the limit
   form, whose least eigenvalue `-1.943e-30` is about half the stage-A value at
   800 (item 7). (c) "whether it stays below 0 beyond `T# = 800` is not
   measured. Item 6 therefore leaves category 4": item 7 settles it for every
   `T#`: the limit of `R(T#)` is the 856-mode DH form, which has a negative
   eigenvalue (hardened), so the stage-A block refuses at every `T#` given a
   valid `S`, the composite measured at that assumption; and the `T# = 800`
   eigenvector itself is not a witness, its refusal at 800 coming from the
   frequency tail the split discards. Item 6 leaves category 4 on that ground,
   not on the checkpoint record.)
7. **The raise (2026-10-27): K2 at the DH line at every `T#`** (`witness.py`,
   `witness_q856.json`, `witness_v856.json`, `witness_v101.json`,
   `stage_a_v800.json`, `stage_a_witness.json`, the `lesion_S` record of
   `k2_scouts.json`; runs in `RUNS.md`). The stage-A block is `R(T#) = C(T#) +
   beta*(T#)(I - G(T#))`, and `R(T#) <= Q_N` in the Loewner order, increasing to
   `Q_N` as `T#` grows, whenever `S` bounds `P_DH - H` on the whole line (the
   archimedean bound the scout uses beyond `T#` is derived below, unreviewed,
   link 4 of the chain). Here `Q_N` is the `N`-mode DH form `(1/pi) int_0^inf
   Psi_DH(t) F(t) F(t)^T dt` on the scout's even Legendre basis, with no split.
   So the pipeline refuses DH at every `T#` exactly when `Q_N` has a negative
   eigenvalue. `witness.py` assembles `Q_856` through the explicit formula in
   position space (for `g = f * f~`: `(log(5/pi) + digamma(3/4) + W_tail) g(0) +
   int_0^{2L} w(x)(g(0) - g(x)) dx - sum_n c_n g(log n)`, `w(x) = e^{-x/2}/sinh x`,
   the comb of the scout), in Arb at 256 bits: every correlation `g` is an exact
   Gauss sum (it is a polynomial), the archimedean integral is Gauss-Legendre in
   `x` with an Arb-bounded error (`6.2e-92`), the radii dropped by the
   midpoint matrix products are carried as a bound, and the error budget gives
   `Q_856` in the computed ball matrix plus `[-eps, eps] I` with `eps = 6.0e-64`.
   - *Calibration, derived and not remembered.* On vectors whose transform
     decays like `t^-9`, the position-space form exceeds the hunt's own stored
     `u^T C(800) u` by `2.7e-40` to `1.0e-38`, which is the tail beyond 800: about
     `6.2` times the stored tail mass `1 - u^T G(800) u`, against
     `log(5 * 800 / 2 pi) = 6.46`. Against the CCM closed-form DH assembly
     (`rogue_frontier/weil_trunc/galerkin.py`, an independent derivation on the
     trigonometric basis) the forms agree to below `4e-60` on the modes
     `k <= 3` (to `6e-44` at `k = 6`, the size of the 40-mode Legendre
     truncation of `cos(6 pi x / L)`). Each
     planted fault (comb sign, comb halved, conductor 1, zeta's `Gamma(s/2)` in
     place of `Gamma((s+1)/2)`) moves the form by `0.012` to `1.6`.
   - *The witness.* `Q_856` has one negative eigenvalue (midpoint LDL: one
     negative pivot, 855 positive), `lambda_min = -1.94308362498e-30`, and the
     stored 40-digit eigenvector `v` (`witness_v856.json`) has
     `Q_856(v)/|v|^2 <= -1.9430836249e-30`, every numerical step enclosed (the
     enclosed quantity is the position-space form, equal to `Q_856` by the
     identity of link 2 below, a derivation). The
     negativity sets in at the 101st mode: the leading 100-mode block has no
     negative pivot (eigenvalue nearest 0 `+4.06e-32`; midpoint LDL, so
     measured), the leading 101-mode
     block has `Q_101(v)/|v|^2 <= -4.4900037e-32` for the stored vector of
     `witness_v101.json`, and every leading block tested from 101 to 856 modes
     has one negative eigenvalue, falling from `-4.49e-32` (101) through
     `-1.17e-30` (150) and `-1.84e-30` (400) to `-1.94e-30` (856). A
     re-assembly of `Q_101` by the same code at its own size (201 Gauss nodes in
     `y` instead of 1711, 291 in `x` instead of 1801, 320 bits instead of 256)
     reproduces the 101-mode quotient to 15 digits: a check of nodes and
     precision, not of the code. The independent check (added 2026-10-27, after
     review) is the reviewer's separate implementation (its own Gauss nodes by
     Newton, its own Legendre-to-Chebyshev conversion, `f` evaluated at `u` and
     at `u - s` without the mirror pairing, its own comb and constants;
     midpoint arithmetic, so a cross-check and not an enclosure), which
     reproduced the position-space form at the 856-mode witness as
     `-1.943083624983854853685878e-30`, at `v_800` as
     `+6.366138862397569e-30`, and at the 101-mode witness as
     `-4.4900037007714099e-32` (at 260 and 320 bits).
   - *The `T# = 800` eigenvector is not a witness.* `Q_856(v_800) =
     +6.36613886240e-30`, enclosed and positive, while `R(800)(v_800) =
     -4.15160674834e-30` (the stored row, reproduced). The difference
     `1.05177e-29` is the frequency tail beyond 800 that the split discards:
     `v_800` has the boundary value `f(L) = 4.35e-14`, a jump whose tail
     `(2 f(L)^2 / (pi T#)) (S + 1)` is `1.06e-29`, against `9.0e-15` for the
     witness. So the refusal recorded at `T# <= 800` was carried by the
     truncation; the refusal at every `T#` is carried by the form.
   - *Soundness of `R(800) <= Q_856`, checked.* With `D = Q_856 - R(800)` (the
     stored state), `D + 1e-66 I` has no negative pivot, so `D` is positive
     semidefinite to within `1e-66`, 36 orders below the eigenvalue scale
     (measured; `D` itself has near-null directions, smooth functions with no
     frequency content above 800, at that noise floor).
   - *The reasoning chain and the grade of each link* (written for an
     adversarial reader; nothing here is kernel-checked).
     1. *What `Q_N` is.* For `v` in `R^N`, `f_v = sum_i v_i T_{2i}` on
        `[-L, L]` (the scout's orthonormal even Legendre functions) with
        transform `F_v(t) = sum_i v_i sigma_{2i} j_{2i}(tL)`, and
        `Q_N(v) = (1/pi) int_0^inf Psi_DH(t) F_v(t)^2 dt`, `Psi_DH(t) =
        Re digamma(3/4 + it/2) + log(5/pi) - P_DH(t)`, `P_DH` the scout's comb
        (`price.dh_comb`). This is the DH Weil quadratic form on the `N`-mode
        space (by DH's explicit formula, which nothing below uses); here it is
        defined by the integral, the `T# -> inf` limit of the scout's `C(T#)`
        with `H = 0`.
     2. *The position-space formula equals `Q_N`.* `witness.py` evaluates
        `E_N(v) = (log(5/pi) + digamma(3/4) + W_tail) g(0) + int_0^{2L} w (g(0)
        - g) - sum_n c_n g(log n)`, `g = f_v * f_v~`. `E_N = Q_N` is an exact
        identity (Gauss's integral `digamma(z) = int_0^inf (e^{-u}/u -
        e^{-zu}/(1 - e^{-u})) du` for `Re z > 0`, Fourier inversion of `g`, the
        cosine transform of the comb), derived in the module docstring: a
        derivation, ordinary and **unreviewed**. Its numerical calibration is
        **measured**: on three smooth 20-mode vectors `E_N` exceeds the hunt's
        stored `u^T C(800) u` by `2.7e-40` to `1.0e-38`, the sign and size of
        the tail beyond 800; it agrees with the CCM closed forms (an
        independent derivation of the same form) to below `4e-60`; each planted
        fault moves it by `0.012` to `1.6`.
     3. *`E_856` has a negative eigenvalue*, **enclosure-carrying**: for the
        stored vector, `E_856(v)/|v|^2 <= -1.9430836249e-30`, and every step is
        enclosed or bounded by a stated inequality: each correlation `g` is an
        exact Gauss sum in Arb (a polynomial integrand, Arb's enclosed nodes and
        weights); the archimedean integral carries an Arb-evaluated
        Gauss-Legendre bound (`6.2e-92`: Chebyshev truncation in a Bernstein
        ellipse avoiding `+-i pi`, `M_rho` from Arb on a covering of the
        ellipse, `sup|q| <= ||f||_inf^2 + ||f||_2 ||f'||_2`); `W_tail` is a
        series with its geometric remainder; the comb is Arb's (`Lambda_f` from
        the Dirichlet-series recursion with `kappa` in Arb), with its dropped
        mass (`1.6e-76`) added; the radii dropped by the midpoint products are
        carried as a bound (`E_psi`); `eps = 6.0e-64` collects these and is
        applied doubled to cover the float roundings of its own bookkeeping.
        **Grade: hardened**, resting on the enclosures; the reviewer's separate
        implementation reproduces `E_856` and `E_101` (midpoint, a
        cross-check).
     4. *A negative `Q_N(v)` means refusal at every `T#`.* Because every
        frequency of `H` is at least `2L` (decided in Arb) and `g` vanishes
        outside `(-2L, 2L)`, `int_0^inf H F_v^2 = 0`, so
        `v^T R(T#) v = Q_N(v) - (1/pi) int_{T#}^inf [Psi_DH + H - beta*(T#)]
        F_v^2 dt`. For `t >= T#` the bracket is the sum of `[Re digamma(3/4 +
        it/2) - log(t/2) + 1/t]`, `[log(5t/2pi) - 1/t - log(5T#/2pi) + 1/T#]`
        and `[S - (P_DH - H)(t)]`. The second is at least 0 (an increasing
        function). The first is at least 0 for `t >= 27/16`: Binet's second formula
        gives `digamma(z) = log z - 1/(2z) - 2 int_0^inf s ds / ((s^2 + z^2)
        (e^{2 pi s} - 1))`, and for `z = 3/4 + it/2`, `|s^2 + z^2| >= |Im z^2| =
        3t/4` and `int_0^inf s/(e^{2 pi s} - 1) ds = 1/24`, so `Re digamma >=
        log(t/2) - 3/(2t^2) - 1/(9t)`, which is at least `log(t/2) - 1/t` exactly
        when `t >= 27/16` (a derivation, ordinary and unreviewed, checked in Arb
        at 14 points from `t = 2` to `1e9` in `test_witness.py`; this replaces
        the grid check of `scout.py`). The
        third is at least 0 exactly when `S` is a valid envelope bound. Then
        `v^T R(T#) v <= Q_N(v) < 0` at every `T#`, where `R(T#)` is the block
        of exact integrals. The scout's discrete rule (`q = 64` on panels of
        width 1/2) differs from it by the Gauss-Legendre error, bounded only at
        `T# = 800`, by `8.0e-89` in all, about `5e-92` a panel (item 7, stage
        A); every factor of that per-panel bound except the digamma bound is
        independent of `T#`, and the digamma bound grows like `log T#`, so the
        discrete rule stays far inside `|Q_N(v)|` of the exact block for `T#`
        far beyond any run (a scaling argument, not computed beyond 800).
        Below about `T# = 528`, `beta* <= 0` and the pipeline claims nothing,
        so "every `T#`" is vacuous there. And and since the leading 101
        modes of `R_N(T#)` are `R_101(T#)`, the same holds for every
        `N >= 101` with the 101-mode witness (padded by zeros). (A derivation,
        unreviewed.)
     5. *The one assumption: `S` is valid*, `S >= sup(P_DH - H)` on the whole
        line. It comes from the branch-and-bound of `joint.py` over the torus,
        re-run at merge time: **measured, with an a priori float error bound**
        (not every step a ball). It is the same assumption under which `R(T#)`
        bounds anything. If it fails by `delta`, link 4 gives
        `v^T R(T#) v <= Q_N(v) + delta m_{T#}(v)`, `m_{T#}(v) = (1/pi)
        int_{T#}^inf F_v^2 <= m_800(v)` for `T# >= 800`. At the 856-mode
        witness `m_800 = 1.4220221e-31` (enclosed, `stage_a_witness.json`), so
        the refusal at every `T# >= 800` survives an `S` too low by any
        `delta < 1.9430836e-30 / 1.4220222e-31 = 13.66`, for every `N >= 856`
        (the margin uses the 856-mode witness); for `101 <= N < 856` no margin
        was computed. It does not depend on `S` being exactly right, only on
        its error being below that.
     6. *`S` bounded in Arb* (added 2026-10-27, after the review of ee06df8af).
        `price.arb_envelope_bound` runs `joint.arb_sup_bound` on every cluster
        of `k2env_dh_L_DH.json`: a branch-and-bound over the cluster's half
        torus whose centre values, gradients and second-order Taylor remainder
        `(1/2) r^2 sum_k |a_k| |k|_1^2` are all in Arb at 128 bits, with the
        weight cover checked in exact rationals and the dropped comb mass
        added. It proves `sup_t (P_DH - H)(t) <= S_used + 34/5`
        (`arb_S_delta6.8.json`, every cluster at target `U_c + (5/2, 1, 23/10,
        1)`; also `<= S_used + 12`, `arb_S_delta12.json`), with no float
        rounding model. So `delta <= 6.8` in link 5. The witness's tail mass
        from 540 is `m_540 <= m_800 + 1.0294516e-31 = 2.4514738e-31`
        (`stage_a_witness_540_800.json`: panels 540 to 800 by the single-vector
        route, enclosed, with their t-quadrature bound), and `m_{T#} <= m_540`
        for `T# >= 540`, so `v^T R(T#) v / |v|^2 <= -1.9430836e-30 + 6.8 x
        2.4514738e-31 = -2.76e-31 < 0` at every `T# >= 540`, the first
        checkpoint with `beta* > 0` (no margin was computed for
        `527.5 < T# < 540`), and every `N >= 856`. There link 5 is
        **enclosure-carrying**: the refusal no longer assumes that `S` is
        valid, only that it is within 6.8 of `sup(P_DH - H)`, which is proved.

     So: "`E_856` (and every leading `E_N`, `N >= 101`) has a negative
     eigenvalue" is **hardened**; "`Q_856` has one" adds link 2, a derivation
     with measured calibration; "the stage-A block refuses DH at `L_DH` at every
     `T#` and every `N >= 101`" adds links 4 and 5 and is **measured** at link
     5, the validity of `S`.

     Regraded 2026-10-27 after link 6 (the paragraph above is left as
     written): every numerical step of "the stage-A block (exact integrals)
     refuses DH at `L_DH` at every `T# >= 540` and every `N >= 856`" is now
     enclosed or bounded (links 3, 5 and 6), and the claim rests on the two
     derivations, links 2 and 4, which stay **unreviewed** (an independent
     review of ee06df8af re-derived both and found no error; that is not
     outside review). For `101 <= N < 856`, and for `527.5 < T# < 540`, the
     refusal still assumes a valid `S`, measured as before. Nothing is
     kernel-checked.
   - *Stage A at `T# = 800` with honest radii.* The stored block's entries
     carry no radius from the fast Bessel column, so the block was recomputed at
     one vector instead (a full recompute with enclosed columns would cost more
     than run B): `witness.stage_a_form` evaluates `v^T R(800) v` for the
     scout's own discrete rule (Gauss-Legendre `q = 64` on panels of width 1/2,
     the snapped nodes inside the balls) with every step in Arb at 256 bits, from
     data independent of the stored state and of the Bessel column: `F_v(t) = 2
     int_0^L f_v(y) cos(ty) dy` by 1500-node Gauss in position space with a
     Bernstein-ellipse bound, and `Psi + H` from `scout.Symbol`. At `v_800`:
     `R(800)(v)/|v|^2 = [-4.15160674833728e-30 +/- 1.0e-72]`
     (`stage_a_v800.json`), the stored row to all its 12 digits, so the
     `T# = 800` stage-A block is **not positive semidefinite, enclosure-carrying**
     (its least eigenvalue is at most `-4.1516067483e-30`). The exact integrals
     of `R(800)` differ from the discrete rule by at most `8.0e-89` at this
     vector (a per-panel ellipse bound through `+-i`, inside the digamma poles
     at `+-3i/2`), so the quadrature claim of the review (about 65 orders below
     `|lambda|`, measured) is now a bound. The tail mass above 800 is
     `1.4883465e-30`. At the 856-mode witness the same route gives
     `R(800)(v)/|v|^2 = [-2.83155721280920e-30 +/- 1.0e-72]`
     (`stage_a_witness.json`), the value the analysis found from the stored
     state (`-2.83155721281e-30`), below the witness's `Q_856`, as `R <= Q`
     requires, with tail mass `1.4220221e-31`. (The `F_v` balls of these two runs were
     not widened for the scout's node snapping, a shift below `2^-1268`;
     `|F_v'| <= 2 L sqrt(L/2) |v|` moves `F_v` by less than `1e-370` under it, far
     inside the recorded radii, and `witness.py` now widens them.) The count of negative
     eigenvalues (one) stays measured: a ball LDL without pivoting loses its
     radius after about 50 pivots here.
   - *Controls replaced.* The `prec - 128` response now rounds the data
     (`scout.responses_of`); at `T# = 800` from the stored state the rounded
     1152-bit block and the leading 791-mode block both keep one negative pivot
     and `lambda_min = -4.15160674834e-30`, as they must (the rounding is about
     300 orders below `lambda`, and the 791-mode block keeps a negative direction
     by interlacing). A true re-assembly at another precision and with an
     independent quadrature is the single-vector route above (256 bits against
     1280, position-space transforms against the Bessel column) and, for the
     form itself, the re-assembly of `Q_101` by the same code (320 bits, other
     nodes) and the reviewer's separate implementation. A
     real larger-`N` stage-A run is not needed for a refusal: by interlacing a
     larger `N` can only lower `lambda_min`. Its price is that of the mode-rule
     stream in door 5.
   - *K2 does not test `S` (the lesion).* `R(T#)` depends on `S` only through
     `beta*`, so understating `S` by `dS` adds `dS (I - G(T#))`. At `T# = 800`
     from the stored state, the stage-A block keeps one negative pivot for every
     `dS` tested up to 43 (`lambda_min` `-4.152e-30` at 0, `-1.892e-30` at
     7.085, `-4.487e-31` at 29.585, `-2.0e-32` at 43) and has none at 44 and
     above (`+7.0e-33` at 44). So at the DH line K2 is insensitive to `S` up to
     about the measured margin, 43 in units of `S`: an envelope bound wrong by
     less than that leaves the verdict unchanged, and K2 as run does not test the
     one number through which (`MISSION.md`) the arithmetic enters. As `T#`
     grows the dependence on `S` vanishes altogether, because `beta*(T#)(I -
     G(T#))` tends to 0: what K2 at the DH line tests is the sign of the rival's
     own `N`-mode form. (At 7.085, about `S + 1`, the average excess of the true
     tail multiplier over `beta*`, the lesioned block's `lambda_min`, `-1.89e-30`,
     already sits near the form's `-1.94e-30`; measured, one point.)

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
   oversampling and rounds, and the dyadic rounding of `h`. (Added 2026-10-27.) The K2 run at
   the DH line (run B) also froze: `T#max = 800`, which stopped at
   `beta* = 0.415`, short of the `beta = 1/2` operating point `T# = 870.8`
   (each further 20 of `T#` costs one unit and one checkpoint, door 5; item 7
   makes the verdict at every `T#` a consequence of a valid `S`, so more `T#` now
   buys a measured confirmation, not reach); `N = 856` (`2N/x = 1.25` at 800; a
   larger `N` can only lower `lambda_min`, and the form is negative from 101
   modes); 1280 bits (the bits rule; the form and the single-vector enclosures
   of item 7 run at 256 and 320 bits); `q = 64`, `h = 1/2` (bounded at the
   vectors of item 7); and the response choices `N - N//13` and `prec - 128`,
   the first uninformative for a refusal by interlacing, the second now rounding
   the data (`scout.responses_of`). For the witness: `Nx = 2N - 1 + 90` and the
   ellipse parameter `7/2` (trade: quadrature bound against nodes; the bound,
   `6.2e-92`, is far from binding).
3. **K2 margin.** At `L_DH` the DH refusal rests on one eigenvalue of size
   about `5e-30` whose magnitude falls as `T#` grows. The doors above that
   lower `S` (larger clusters, a tighter `H`), applied to the same pipeline on
   DH, also raise DH's `beta*`, which pushes this eigenvalue up. The refusal is
   not known to survive such a change, so an envelope method that passes the
   gate has to be re-run through K2 at the DH line.
   (Added 2026-10-27; the text above is left as written, and its conclusion is
   superseded.) What binds the refusal is the negative eigenvalue of the DH form
   on the first 101 or more even modes (item 7), which no valid envelope can
   move: a lower `S` raises `beta*` and so `R(T#)` at each `T#`, but every valid
   envelope leaves `R(T#) <= Q_N` with the same limit. A tighter envelope can
   shrink the refusal at a finite `T#` but cannot end it, at any `T#`, while it
   is valid: the block's least eigenvalue stays at or below
   `lambda_min(Q_N) < 0`. What a lower `S` does change is how much of the
   refusal at a finite `T#` is truncation: at `T# = 800` the eigenvector's
   refusal is all tail (item 7), and the margin in `S` is 43 (the lesion). So K2
   at the DH line is a test of the rival's form and of `R(T#) <= Q_N`, not of
   the size of `S`.
4. **Information class.** Every door above stays inside the data the current
   family reads: the prime comb on `[-L, L]` and out-of-band frequencies at least
   `2L`. Overlapping clusters (`overlap_L_DH.json`) are the same class. None reads
   more arithmetic. (Added 2026-10-27.) The witness of item 7 reads the same
   data (the DH comb and Gamma factor on `[-L, L]`) and no new class.

5. **Two runs priced, not launched** (2026-10-27, from timed slices in
   `RUNS.md`; funded separately). *The stream past `T# = 800`* at run B's
   settings (`N = 856`, 1280 bits, `q = 64`): a timed slice at `T# = 1198` to
   1200 costs `31.8 s` a panel, as in run B (31.5 to 33.9), so a unit of 20 in
   `T#` is about 1270 s and a checkpoint about 500 s. To the operating point,
   `T# = 880`: about 2.0 core-hours, about 1 h wall (4 units in parallel, then
   4 checkpoints in series). To `T# = 1600` with a
   checkpoint every 100: about 15 core-hours, 2 h wall on 8 workers (20
   core-hours and about 6 h wall, bound by the serial reduction, with a
   checkpoint every 20). Item 7 predicts its outcome (refusal at every
   checkpoint, under the pipeline's inputs). With the mode rule `2N/x = 1.25`
   instead, `N = 1711` at `T# = 1600` and the assembly restarts from 0: a timed
   panel costs `123.5 s` at 2.2 GB, so about 110 core-hours of units and 9 of
   reduction, 15 h wall on 8 workers. *The below-the-line discrimination
   control*: DH at `L' = 8503/5000` (`c = 30.0006`, below the measured
   continuum crossing near 30.61; the comb is the same 22 terms, `n <= 29`, and
   every frequency of `k2env_dh_L_DH.json` is at least `2 L_DH > 2L'`, so the
   same envelope and `S` are valid there), run B's settings to `T# = 800`: a
   timed slice costs `32.0 s` a panel, so about 16.2 core-hours, 5.5 h wall on
   3 workers or about 2.5 h on 7. Its decisive companion, `Q_856` at `L'` by
   `witness.py` (what a perfect stage A must say there), costs 5.6 core-hours,
   48 min wall on 8 processes, as measured at `L_DH`.

This is a measured optimum over a searched family, not a proved ceiling.
