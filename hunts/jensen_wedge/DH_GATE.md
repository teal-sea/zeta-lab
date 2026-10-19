# DH_GATE: hunt #135's Davenport-Heilbronn rival gate

**Nothing here bears on RH.** The Davenport-Heilbronn function (DH) satisfies a functional
equation of Riemann type and has zeros off the critical line. `MISSION.md` ("The rival
gate, with its expected outcome stated in advance") predicted that the wedge construction
reads only the weight's double-exponential decay, which DH shares, and so succeeds for DH
as for zeta. A pass shows, measured in this tree, that the construction is shared structure
with no RH content. Grade: **measured** throughout.

Reproduce:

```bash
.venv/bin/python hunts/jensen_wedge/dh_gate.py --time-unit   # about 25 s
.venv/bin/python hunts/jensen_wedge/dh_gate.py               # about 8 min, writes results_dh.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge/test_dh_gate.py
```

## 0. Verdict: the prediction held

The prediction, written in `MISSION.md` on 2026-10-18 before any DH number existed and
restated item by item in the brief of 2026-10-19 before this probe ran: *the construction
succeeds for DH exactly as for zeta. That means Holland's sign facts at R_3 and R_4, the
sign map of E_F(5), and the [2/2] Pade match of R_5 with all parameters positive.*

**Graded: held, on every item, on both routes.**

| item | DH, route A (all 3151 n in 50..3200) | DH, route B (subgrid and n = 1e4..1e20) | zeta (phases 0, 1) |
| --- | --- | --- | --- |
| Laguerre defect at R_3 positive | 3151 of 3151, no sign change | agrees and resolves the sign at all 21 subgrid n; positive at all 8 large n | 3151 of 3151 |
| Jacobi defect at R_4 negative | 3151 of 3151 | the same | 3151 of 3151 |
| E_F(5) at Holland's theta = 1/2 negative | 3151 of 3151 | the same | 3151 of 3151 |
| sign map of E_F(5) in theta: negative below theta_star(n), positive up to theta_inf(n), A < 0 beyond | at all 21 subgrid n, no failed walk | theta_star equal to route A's to 4.7e-13 at 6 n; found at all 8 large n | the same shape at 21 n and 8 large n |
| [2/2] Pade match of R_5, all parameters positive, A > B, C > D | 3151 of 3151 | all 8 large n | 3151 of 3151 and 8 large n |
| theta_star is the Pade point (D/B_J of the direct solve) | to all 12 printed digits at all 21 subgrid n | | to 12 digits |
| *further:* R_6 defect of the Pade model negative | 3151 of 3151 | agrees and resolves at 21 n; negative at 8 large n | 3151 of 3151 |

Route B (Laplace series, no quadrature) sits inside its stated error at all 21 subgrid
points; at those points two routes that share no quadrature agree in sign and resolve it,
which is the shape of a hardened reading. This file grades it measured, as phases 0 and 1
did. The contrast holds as required: DH's Jensen non-hyperbolicity was found only at n = 0
(section 7), and at every wedge cell measured here (n = 50 and 3200) DH's Jensen
polynomials are real-rooted. The two regions do not overlap.

## 1. The table, and a floor in jensen_clock's `omega_dh` (the bug check came first)

The brief named `hunts/jensen_clock/probe.py`'s DH table (`dh_nodes`, `gammas_from_nodes`).
Built literally at this hunt's precision, jensen_clock's node sets disagreed with each other
by 6 to 19 percent at n = 1600 in the scoping runs (`RUNS.md`). The cause is `omega_dh`'s cutoff: it drops each theta term below an **absolute**
floor of 10^-(dps+8), so the weight becomes exactly 0 once e^(-pi x/5) is below the floor.
At the working precision here (dps 75) that is u > 2.859, and 1001 of the 3072 nodes of
jensen_clock's default node set carry weight 0. The peak of the n = 3200 integrand sits at
u = L_DH/2 = 3.62.

| m | 50 | 100 | 200 | 400 | 800 | 1600 | 3200 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| log gamma, literal minus relative cutoff, dps 75 | -4.7e-55 | -3.9e-40 | -1.6e-21 | -1.7e-4 | -17.9 | -193 | -832 |

`dh_gate.py` keeps jensen_clock's construction (its weight, `make_nodes` and both of its
node sets) and changes only the cutoff to a relative one (`omega_dh_rel`). With it the two
node sets, (U, segments, Gauss-Legendre level) = (4.2, 16, 7) and (3.9, 13, 8), agree on log
gamma to 4.5e-72 over m = 50..3296, and `gammas_from_nodes` on the same nodes is reproduced
to 7.1e-74.

jensen_clock's own numbers are not touched by the floor in the ranges it used: at its dps 130
and j <= 328 the literal and relative-cutoff tables agree to 1.6e-39, and every contrast cell
of section 7 gives the same Delta to 10 digits on both. Its largest table (stage pair2, dps
180, j <= 400, node set (4.2, 18, 7)) agrees with the relative-cutoff table to 1.6e-63. Its
stage `precision` also ran at dps 110 (j <= 280) and dps 160 (j <= 360); those two tables
were not checked here. jensen_clock is outside
this hunt's write scope, so the floor is recorded here as an observation, not fixed there.

How much accuracy the construction needs: an alternating error of 1e-12 in log gamma at
n = 400 already leaves Holland's system with no solution in the positive class, and 1e-14
flips the sign of the Pade model's R_6 defect (`test_dh_gate.py`, planted faults). The
literal table's 1.7e-4 at n = 400 would not have produced a wrong sign; it would not have
solved at all.

## 2. Holland's sign facts on DH (phase 0, sections 4 and 5)

L_DH is the saddle of DH's leading moment, (pi/5) e^L = 3/4 + 2n/L. It plays the part of
Holland's L_n because log gamma_DH(x) = -log Gamma(x + 1/2) + log I_1(x) + (linear in x) has
Holland's eq. (14) shape, and phase 1's reduction (RESULTS.md 11.1) reads the weight only
through h''(x) ~ (2/L)/x. At equal n, L_DH is larger than zeta's L_n (7.25 against 5.85 at
n = 3200), so DH sits further along every 1/L approach.

| n | L_DH | zeta L_n | D_n (DH) | D_n (zeta) | E_J(4) (DH) | E_F(5), theta = 1/2 (DH) | n^2 L D_n/2 | -n^3 L E_J(4)/2 | n^4 L E_F(5) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 3.771 | 2.503 | 6.6175e-5 | 5.8374e-5 | -1.1493e-6 | -6.9136e-8 | 0.3119 | 0.2708 | -1.629 |
| 100 | 4.317 | 3.025 | 1.7250e-5 | 1.6387e-5 | -1.5772e-7 | -5.5274e-9 | 0.3723 | 0.3404 | -2.386 |
| 400 | 5.457 | 4.118 | 1.0751e-6 | 1.1099e-6 | -2.5769e-9 | -2.6714e-11 | 0.4694 | 0.4500 | -3.732 |
| 1600 | 6.644 | 5.264 | 6.3725e-8 | 6.8221e-8 | -3.8875e-11 | -1.0962e-13 | 0.5419 | 0.5289 | -4.773 |
| 3200 | 7.249 | 5.852 | 1.5400e-8 | 1.6637e-8 | -4.7197e-12 | -6.8431e-15 | 0.5715 | 0.5605 | -5.201 |

Every fitted parameter is positive and C > D at every n; the largest matching residual of
any fit is 7.8e-67. Route B against route A on log R_j: at most 8.0e-14 against a stated
1.0e-10 at n = 50, and 3.7e-26 against 1.3e-20 at n = 3200. Route B's m >= 2 theta terms
are 2.6e-20 of the total at n = 50 and 9.8e-34 at n = 100, and are carried anyway.

## 3. The sign map of E_F(5) over (theta, n) (phase 1, section 10)

With D = theta B_J and phase 1's solver (`family_map`, unchanged), route A:

| n | theta_star | theta_inf | (1 - theta_star) L | (1 - theta_inf) L | (theta_inf - theta_star) L | n^4 L E_F(5) at 0.125 / 0.25 / 0.5 / 0.7 | zeta theta_star |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 0.846623447 | 0.889249280 | 0.578 | 0.418 | 0.161 | -7.41 / -3.96 / -1.63 / -0.73 | 0.794052342 |
| 100 | 0.863346355 | 0.901082939 | 0.590 | 0.427 | 0.163 | -11.88 / -5.95 / -2.39 / -1.12 | 0.819287720 |
| 400 | 0.888916010 | 0.919232155 | 0.606 | 0.441 | 0.165 | -20.11 / -9.43 / -3.73 / -1.87 | 0.858347706 |
| 1600 | 0.907111619 | 0.932207533 | 0.617 | 0.450 | 0.167 | -26.02 / -11.98 / -4.77 / -2.50 | 0.885407627 |
| 3200 | 0.914295156 | 0.937348786 | 0.621 | 0.454 | 0.167 | -28.28 / -12.99 / -5.20 / -2.77 | 0.895770429 |

The shape is zeta's: negative below theta_star, a positive window of width about 1/(6 L)
(zeta: 0.145/L to 0.166/L), A passing infinity at theta_inf, and theta_star rising to 1 like
1 - 2/(3L). Route B, by direct saddle evaluation, finds theta_star equal to route A's to
2.3e-13 to 4.7e-13 at n = 100, 200, 400, 800, 1600 and 3200.

## 4. The [2/2] Pade point (phase 1, sections 11.3 and 11.4)

At every subgrid n the crossing theta_star equals D/B_J of the direct four-parameter solve to
all 12 printed digits, so on DH too phase 0's crossing is the Pade point. Route A, every n:
the solve succeeds with A > B > 0 and C > D > 0, and its R_6 defect E_S(6) is negative at all
3151 n, with route B agreeing in sign and resolving it at all 21 subgrid n.

| n | A/(nL) | (D - n) L/n | (B - C) L/n | rho_CD | gap total x L | n^5 L E_S(6) | A/B |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 5.566 | 0.628 | 3.938 | 0.299 | 1.591 | -0.496 | 7.75 |
| 400 | 4.482 | 0.495 | 4.038 | 0.342 | 1.693 | -1.010 | 10.20 |
| 3200 | 4.052 | 0.443 | 4.217 | 0.374 | 1.758 | -1.270 | 12.91 |
| 1e20 (route B) | 3.162 | 0.349 | 5.069 | 0.476 | 1.955 | -1.877 | |
| leading order | 3 | 1/3 | 16/3 | 1/2 | 2 | -2 | |

## 5. Large n, route B alone

Working precision 5 log10 n + 50 digits, as in phases 0 and 1. The spread between six and
five Laplace corrections is at most 1.5e-22 relative on any defect quoted (n = 1e4) and
falls fast with n.

| n | L_DH | n^2 L D_n/2 | -n^3 L E_J(4)/2 | A/A_J | (B - B_J) L/n | (C - D) L/n | n^4 L E_F(5) at 1/2 | (1 - theta_star) L | (1 - theta_inf) L | n^5 L E_S(6) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1e4 | 8.257 | 0.6131 | 0.6044 | 1.2496 | 0.3952 | 0.04463 | -5.808 | 0.6268 | 0.4593 | -1.360 |
| 1e6 | 12.45 | 0.7243 | 0.7199 | 1.2320 | 0.3724 | 0.04352 | -7.483 | 0.6402 | 0.4721 | -1.573 |
| 1e8 | 16.76 | 0.7873 | 0.7846 | 1.2235 | 0.3617 | 0.04301 | -8.471 | 0.6469 | 0.4789 | -1.682 |
| 1e12 | 25.55 | 0.8550 | 0.8537 | 1.2152 | 0.3515 | 0.04252 | -9.565 | 0.6537 | 0.4859 | -1.791 |
| 1e16 | 34.46 | 0.8904 | 0.8896 | 1.2112 | 0.3466 | 0.04229 | -10.15 | 0.6570 | 0.4894 | -1.845 |
| 1e20 | 43.44 | 0.9120 | 0.9115 | 1.2089 | 0.3438 | 0.04216 | -10.51 | 0.6590 | 0.4916 | -1.877 |
| limit | | 1 | 1 | 6/5 | 1/3 | 1/24 | -12 | 2/3 | 1/2 | -2 |

Every column moves monotonically toward the limit Holland states or phase 1 derives. At
n = 1e20 the DH values sit within 0.5 percent of zeta's at the same n (zeta: 0.9088, -10.46,
0.6587, -1.872 in the matching columns), and the O(1/L) coefficient of the first column,
(1 - n^2 L D_n/2) L, is 3.822 for DH against 3.816 for zeta. Measured on eight points, not
derived.

## 6. DH's Jensen polynomials at the wedge's measured cells

Phase 1's root-geometry instrument (`root_geometry`, unchanged) on DH, from a dps-260 block
of the same table (node set (4.2, 16, 8), agreeing with the dps-60 table to 7.8e-72 at
n = 3200 and 1.2e-73 at n = 50), each polynomial evaluated at dps 60 + 2d:

| n, model | d | real roots (model / Jensen / first factor) | max over j <= d of abs(c_j - 1) | c_j = 1 through j |
| --- | --- | --- | --- | --- |
| 3200, Holland | 6 / 24 / 96 | all real at each d | 4.1e-14 / 2.9e-10 / 3.9e-7 | 4 |
| 3200, Pade | 6 / 24 / 96 | all real at each d | 5.2e-19 / 6.9e-14 / 4.6e-10 | 5 |
| 50, Holland | 6 / 12 / 24 | all real at each d | 4.0e-7 / 4.2e-5 / 1.5e-3 | 4 |
| 50, Pade | 6 / 12 / 24 | all real at each d | 4.2e-10 / 3.1e-7 / 3.1e-5 | 5 |

(d = 12 and 48 at n = 3200 are in the JSON and sit between their neighbours.) Every DH
Jensen polynomial checked here is hyperbolic, and the multiplier the stability step needs
small is small. These J^{d,n} are hyperbolic for zeta by GORTTW Cor. 1.3; for DH nothing
guarantees them, and they are measured.

## 7. The contrast: DH's non-hyperbolicity sits at n = 0

From `hunts/jensen_clock/results.json`: the pair of DH zeros at height 85.7 lands in J^{d,0}
at d* = 20785.13 (relative spread 8.9e-5 over four quadratures), the pair at height 114.2 at
d* = 146365.5, and at n = 1 the first pair is already on the real axis at d = 3e4, 1e6 and
1e8 (contour count 1, stage map2). Recomputed here with jensen_clock's instrument
(`pair_delta` on the damped series) on both tables at dps 130:

| (d, n) | contour count | Delta = (x_1 - x_2)^2 | complex pair (non-hyperbolic) |
| --- | --- | --- | --- |
| (20000, 0) | 2 | +403.13 | no |
| (22000, 0) | 2 | -571.47 | yes |
| (30000, 1) | 1 | +57.44 | no |

So the measured non-hyperbolic cells of DH have n = 0; the wedge cells measured here have
n >= 50, and every DH Jensen polynomial checked there is real-rooted (section 6). **No
overlap.** It is structural: Holland's wedge n^3 log^2(n+2) >= K d^5 excludes n = 0 for every
K > 0 and d >= 1, and so does every wedge of this shape, which is exactly why it cannot see
the region where DH fails.

## 8. What this shows and what it does not

- **Shows (measured):** every step that phases 0 and 1 built for zeta goes through for DH,
  over the same shift ranges, on two routes, with the same leading constants once L is read
  from DH's own weight. In this range the construction cannot tell an RH-true function from
  an RH-false one. That is a measured, in-tree form of Farmer (Adv. Math. 411 (2022)
  108781) and GORTTW Remark 3, for this construction.
- **Does not show:** anything about phase 1's conditional chain (H1, H3) for DH, though its
  Lemmas A to C use no property of the weight; any proof; any statement about RH. A finite
  computation is not a uniform statement. The gate is not one of `MISSION.md`'s kill
  conditions and changes none of their statuses.
- **Certainty ladder.** The result is the expected one, and it still got the bug checks
  first: the table's own failure (section 1) was found and worked around before any
  construction number was read, the two node sets and route B check the table, and the
  planted faults of `test_dh_gate.py` (the floor put back, an alternating error in log gamma
  at two sizes, sign flips in the record) each turn the gate red.

## 9. Files

- `dh_gate.py`: the DH table (route A), the Laplace route B with DH's constants, the
  construction and the theta map reused from `probe.py` and `probe_phase1.py` unchanged, the
  root geometry, the n = 0 contrast and the verdict function.
- `results_dh.json`: every number above, with the floor record and the verdict.
- `test_dh_gate.py`: instrument tests, a live recomputation at n = 400 on both routes,
  planted faults (the floor put back, an alternating error in log gamma, sign flips in the
  record), and the pins.
- `RUNS.md`: unit timing, estimate and one manifest per run.
