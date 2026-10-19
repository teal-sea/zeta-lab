# jensen_wedge: RESULTS

**Nothing here bears on RH.** Phase 0 of hunt #135 reproduces two sign facts from
Holland's construction (arXiv:2608.08682v1) on a finite range of shifts n, and measures
one further quantity that phase 1 needs. A finite computation is not a uniform statement,
and a wedge of this shape would not touch RH even if proved (`MISSION.md`, "What success
would mean"). Grade: **measured** throughout. At the 21 subgrid points two independent
routes agree, which is the shape of a hardened reading; this file still grades it
measured.

Phase 1 is sections 9 to 14: Holland's PDF checked line by line, the R_5 defect mapped,
the sixth coefficient matched by his own family at the [2/2] Pade point, and a conditional
six-point stability derivation. Its verdict is section 13.

Reproduce:

```bash
.venv/bin/python hunts/jensen_wedge/probe.py --time-unit   # about 5 s
.venv/bin/python hunts/jensen_wedge/probe.py               # about 9 min, writes results.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge
```

The probe validates route A against `zeta/li.py`'s cached tables and against an
independent quadrature, and raises if either disagrees, before it prints any large-n
number.

---

## 0. Phase 0 verdict

| kill condition (`MISSION.md`) | status |
| --- | --- |
| Holland's sign facts at R_3 (positive) and R_4 (negative) fail to reproduce from the exact table | **not met.** D_n > 0 and E_J(4) < 0 at all 3151 integers n = 50..3200 on route A, with no sign change; route B agrees in sign at all 21 subgrid points and resolves each sign |
| the saddle expansion of log R_j disagrees with the exact table beyond its stated error at any n <= 3200 | **not met under the rule finally used, met once under the preset rule.** Checked at the 21 subgrid points, not at every n. Section 3 records the miss at n = 150 and why it is the error estimator, not the expansion |
| the R_5 defect after the five-coefficient match changes sign within the measured n range, on both routes | **not met** at Holland's choice D = B_J/2: E_F(5) < 0 at all 3151 n on route A, at all 21 subgrid points on route B, and at every n to 1e20 on route B. Its sign does change with the free parameter D (section 6) |

The reading of Holland's sections 4 to 6 is also confirmed from the other end: his stated
asymptotic constants are approached as n grows (section 5).

## 1. The objects, as read

Holland, arXiv:2608.08682v1, read on 2026-10-18 from the arXiv HTML rendering of v1
through a summarising fetch, **not line by line from the PDF**. What protects the reading
is internal: each fit below recovers its own exact coefficient sequence to working
precision (`test_jensen_wedge.py`, first four tests), and the limits in section 5
reproduce the constants Holland states. Neither is a line-by-line check of the source.
(Phase 1 made that check against the PDF: section 9, no formula here disagrees.)

Normalise R_j(n) = gamma(n+j)/gamma(n), R_0 = 1, and q_k = R_{k+1}^2/(R_k R_{k+2}). The
coefficient sequence S^j (U)_j/(U^j (V)_j) has quotients
qq_k(U, V) = (U+k)(V+k+1)/((V+k)(U+k+1)); U = infinity gives the Laguerre sequence
S^j/(V)_j.

| model | parameters | matches | defect measured here |
| --- | --- | --- | --- |
| Laguerre (Lemma 4.3) | B_L = 1/(q_0 - 1), S_L = B_L R_1 | R_0..R_2 | D_n = log(R_3/R_3^L) = log(qq_1(inf, B_L)/q_1) |
| Jacobi (Lemmas 5.1 to 5.4) | T = (q_0-1)/(q_1-1), A_J = 2q_0/(T - q_0), 1/B_J = q_0(1 + 1/A_J) - 1, S_J = B_J R_1 | R_0..R_3 | E_J(4) = log(R_4/R_4^J) = log(qq_2(A_J, B_J)/q_2) |
| finite-free (Lemmas 6.1, 6.2) | D = B_J/2 fixed; (A, B, C) from qq_k(A,B) qq_k(C,D) = q_k, k = 0, 1, 2; S = B R_1 | R_0..R_4 | E_F(5) = log(R_5/R_5^F) = log(qq_3(A,B) qq_3(C,D)/q_3) |

Holland's statements: D_n = 2/(n^2 L_n)(1 + O(1/L_n)) > 0, and
Q_n := -E_J(4) = 2/(n^3 L_n)(1 + O(1/L_n)) > 0, with L_n = L_{2n-2} and
x = L_x(pi e^{L_x} + 3/4) (eq. 16). He matches nothing past R_4; E_F(5) is this hunt's
quantity, and it depends on his free choice of D. His gamma is ours divided by 8, which
cancels in every R_j (checked by hand from eq. 15 as read: his M_z continuation reduces
to n!(J_{n-1} - J_n/4)), and his L_x is the saddle in the variable t = e^u, so L_n and
the u* above differ by about 1e-3 at n = 3200 (5.8516 against 5.8527).

## 2. Two routes to log R_j

**Route A, the exact table.** `zeta/li.py`'s Mellin route, gamma(m) = 8 m! (J_{m-1} -
J_m/4), J_k = I_k/(4^k (2k)!), I_k = int_0^inf u^{2k} e^{u/4} omega(e^u) du, for every
k = 49..3205 (3157 moments). Each block of 64 consecutive k shares one grid spanning the
union of the windows where the integrand is within dps + 25 decades of its peak, with step
sigma_min/8 (sigma = 1/sqrt(-Psi'') at the narrowest peak). The weight is evaluated once per
node and u^{2k} advanced by one multiplication per index; the trapezoid rule converges
geometrically here because the integrand is entire in a strip and negligible at both ends.

| check on route A | result |
| --- | --- |
| against `zeta/li.py`'s cached dps-50 table, gamma(17..47) | max abs log difference 5.1e-49 |
| against its cached dps-30 table, gamma(17..127), which reaches into the main range | 9.0e-32 |
| coarse (step 2h) against fine (step h), all 3157 moments | max relative 3.8e-74 |
| against tanh-sinh over `zeta.core.omega` at dps 80, the 147 moments of the subgrid windows | max relative 5.6e-74; max abs log R_j difference 6.8e-72 |

The check route shares no node, no rule and no omega implementation with route A. The
trapezoid needs the integrand negligible at the window's lower end, which u^{2k} supplies
only once k is moderate; that is why the comparison with `zeta/li.py` starts at m = 17.
Where below that it would fail was argued, not measured.

**Route B, the saddle.** Up to a relative O(e^{-3 pi e^u}), I_y is the Laplace integral of
Psi(u) = 2y log u + u/4 - pi e^u, with saddle pi e^{u*} = 1/4 + 2y/u* (the instrument of
`hunts/gauss_positivity` section 3). Route B carries the Laplace series to M = 6
corrections, each one more power of u*/y, generated by exponentiating the weighted
perturbation and taking Gaussian moments. This makes log gamma(x) analytic in real x, and
the saddle expansion of log R_j is its Taylor polynomial in j,

```
    log R_j(n) = sum_{i=1}^{7} g_i(n) j^i,    g_i = (d/dn)^i log gamma(n) / i!,
```

with n^{i-1} g_i of order one, as GORTTW's g_i = O(n^{1-i}) says: at n = 3200 the scaled
coefficients are -7.31, -0.354, 0.112, -0.0542, 0.0317, -0.0207, 0.0145. The derivatives
come from `mp.taylor` with a step relative to n and 60 extra bits; with the defaults the
ninth derivative of log Gamma at n = 1e20 kept 13 digits, and with these options it is
exact to working precision at n = 50, 3200 and 1e20 (`differentiation_check`). Route B
uses no quadrature.

**Stated error of route B**, at each j: |g_8| j^8 + |g_9| j^9 (Taylor truncation) plus the
larger of the last two Laplace increments, |M6 - M5| and |M5 - M4|, each evaluated
directly at n + j.

## 3. Route B against the table, and a preset rule that missed

With the rule above, route B sits within its stated error at all 21 subgrid points and
all j = 1..5: the worst ratio of deviation to stated error is 0.90 (n = 100), and it falls
to 0.15 at n = 3200. The deviation itself runs from 1.6e-9 (n = 50, j = 5, where the Taylor
truncation dominates) to 1.2e-21 (n = 3200).

**The preset rule missed once, and it is kept here.** The run was planned with M = 4 and
the Laplace part of the stated error set to |M4 - M3|. That rule held at 20 of 21 points
and failed at n = 150, at j = 1 and 2, by factors 1.7 and 1.3 (deviation 2.1e-14 against a
stated 1.2e-14). The Laplace ladder at n = 150, j = 1, shows why:

| M | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- |
| \|log R_1 route A - route B\| | 2.2e-10 | 8.9e-15 | 2.1e-14 | 2.7e-16 | 3.5e-20 |

M = 3 lands accidentally close to the table at n = 150, so the increment |M4 - M3| is
small exactly where M = 4's own error is not. The deviation falls by four to six decades
per two added corrections, which is what a truncation error does and what a disagreement
between the expansion and the table would not do. The rule was changed after the miss,
to more corrections and the larger of two increments; that is a revision after seeing the
data, and both rules' results are in `results.json` (`preset_rule_M4`). Whether the
second kill condition counts as tripped by the preset rule is for the reviewer; this file
reads it as an estimator failure.

## 4. The two sign facts, n = 50..3200

Route A at the subgrid (all 3151 integers n were computed; signs never change):

| n | L_n | D_n | n^2 L_n D_n / 2 | E_J(4) | -n^3 L_n E_J(4) / 2 | E_F(5) | n^4 L_n E_F(5) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 2.5033 | 5.83742e-5 | 0.1827 | -9.45239e-7 | 0.1479 | -4.46004e-8 | -0.698 |
| 100 | 3.0251 | 1.63871e-5 | 0.2479 | -1.42790e-7 | 0.2160 | -4.13087e-9 | -1.250 |
| 200 | 3.5640 | 4.34325e-6 | 0.3096 | -1.97788e-8 | 0.2820 | -3.29325e-10 | -1.878 |
| 400 | 4.1181 | 1.10993e-6 | 0.3657 | -2.59715e-9 | 0.3423 | -2.38707e-11 | -2.517 |
| 800 | 4.6851 | 2.77185e-7 | 0.4156 | -3.29982e-10 | 0.3958 | -1.62925e-12 | -3.127 |
| 1600 | 5.2635 | 6.82209e-8 | 0.4596 | -4.10772e-11 | 0.4428 | -1.07013e-13 | -3.691 |
| 3200 | 5.8516 | 1.66367e-8 | 0.4984 | -5.04840e-12 | 0.4840 | -6.85594e-15 | -4.207 |

Route B reproduces D_n to relative 4e-7 at n = 50 and better than 1e-14 from n = 2000,
E_J(4) to 2e-4 at n = 50 and 3e-11 at n = 3200. Every fitted parameter is positive and
C > D at every n. The matching residuals of all three fits are below 1e-63.

The normalised ratios sit well below 1 in this range. That is the O(1/L_n) term, and it is
not small here: L_n = 2.5 to 5.9. Section 5 follows them to n = 1e20.

## 5. Holland's constants at large n (route B alone)

Route B needs no table, so it runs to any n; the working precision grows with n (dps =
5 log10 n + 50). The spread between Taylor orders 7 and 9 and between M = 5 and 6 is at
most 2e-9 relative to any defect quoted (E_F(5) at n = 1e4) and falls fast with n.

| n | L_n | n^2 L_n D_n / 2 | -n^3 L_n E_J(4) / 2 | A/A_J | (B - B_J) L_n/n | (C - D) L_n/n | n^4 L_n E_F(5) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1e4 | 6.836 | 0.5526 | 0.5412 | 1.2608 | 0.4099 | 0.04533 | -4.951 |
| 1e6 | 10.969 | 0.6931 | 0.6877 | 1.2366 | 0.3782 | 0.04379 | -7.005 |
| 1e8 | 15.245 | 0.7687 | 0.7655 | 1.2259 | 0.3647 | 0.04315 | -8.177 |
| 1e12 | 24.001 | 0.8463 | 0.8449 | 1.2162 | 0.3527 | 0.04258 | -9.424 |
| 1e16 | 32.896 | 0.8854 | 0.8847 | 1.2118 | 0.3473 | 0.04232 | -10.067 |
| 1e20 | 41.866 | 0.9088 | 0.9083 | 1.2092 | 0.3442 | 0.04218 | -10.456 |
| Holland | | 1 | 1 | 6/5 | 1/3 | 1/24 = 0.04167 | (not stated) |

Each column moves monotonically toward Holland's value, with a gap that shrinks like
1/L_n: (1 - n^2 L_n D_n/2) L_n stays between 2.9 and 3.9 from n = 3200 to 1e20. This is
the evidence that the construction is read correctly, and it is measured, not a proof of
his lemmas.

## 6. The R_5 defect after the five-coefficient match (the phase 1 question)

Measured, not claimed.

**At Holland's D = B_J/2** the defect is negative at every n measured: all 3151 integers
in 50..3200 on route A, the 21 subgrid points on route B, and n = 1e4..1e20 on route B. Its
local exponent d log|E_F(5)|/d log n runs from -3.33 (n = 50..60) to -3.98
(n = 2800..3200). The product n^4 L_n E_F(5) is still growing in magnitude at n = 1e20
(-4.2 at 3200, -10.5 at 1e20), while n^4 E_F(5) falls (-0.72 at 1e4, -0.25 at 1e20).
That is consistent with E_F(5) ~ -c/(n^4 L_n) with c of order ten and an O(1/L_n)
correction, but the limit is not resolved and no constant is claimed.

**Its sign is not a property of the data alone.** D is a free choice in Holland's
construction, made for his proof. Writing D = theta B_J and following the solution by
continuation from theta = 1/2:

| n | E_F(5) at theta = 1/8, 1/4, 1/2 | crossing theta* | (C - D)/D at theta* | A/B at theta* | walk stalls at |
| --- | --- | --- | --- | --- | --- |
| 100 | -2.24e-8, -1.10e-8, -4.13e-9 | 0.81929 | 0.362 | 6.59 | 0.86 < theta < 0.88 |
| 400 | -1.35e-10, -6.25e-11, -2.39e-11 | 0.85835 | 0.440 | 8.18 | 0.88 < theta < 0.90 |
| 1600 | -6.00e-13, -2.75e-13, -1.07e-13 | 0.88541 | 0.508 | 9.90 | 0.90 < theta < 0.92 |
| 3200 | -3.82e-14, -1.74e-14, -6.86e-15 | 0.89577 | 0.538 | 10.79 | 0.92 < theta < 0.95 |

So the same five-parameter family also matches R_5 when D = theta* B_J, with theta*
rising slowly in n. At the crossing (C - D)/D is 0.36 to 0.54, above the C - D <= D/4 of
Holland's parameter window (eq. 57), which his own choice theta = 1/2 meets with room
((C - D)/D = 0.013 at n = 3200). Past the crossing the continuation stalls, after 30
consecutive step halvings in log theta, between the last solved grid point and the next,
where (C - D)/D has already reached 0.60 to 0.91. Whether the branch folds there or C runs
off to infinity is not resolved, and the stalls are recorded in `results.json`, not
hidden. An earlier version of the solver, Newton in (A, B, C) with fixed steps, stalled at
different theta on different grids, which is how the stall was found to be partly the
solver's; the recorded run uses Newton in (log A, log B, log(C - D)) with adaptive steps.
Two further measured facts about the window: A >= 8B (also eq. 57) holds at theta = 1/2
only from n between 2400 and 2800 (A/B = 7.98 and 8.13), and the per-factor conditions of
eq. (77) involve d, which this phase does not touch.

What this sharpens for phase 1, stated as a question: whether the D/4 bound in eq. (57)
is needed for real-rootedness and for the stability lemma, or is a convenience of the
proof. If it is a convenience, the sixth coefficient may need no third factor at all.
Nothing here decides it.

## 7. What this is and is not

- A reproduction, in a finite range of n, of two sign facts Holland proves for large n,
  plus his parameter limits read off numerically to n = 1e20. It is not a new result and
  makes no novelty claim.
- Not a statement about any (d, n) wedge: no degree d enters phase 0.
- Not RH. See `MISSION.md`, "What success would mean".
- No ceiling is measured in phase 0, so "The doors" is owed at phase 3, not here.

## 8. Files

- `probe.py`: both routes, the three fits, the theta scan, the large-n table.
- `results.json`: every number above, with the preset-rule record.
- `test_jensen_wedge.py`: instrument tests on exact sequences with planted signs, live
  recomputation of both routes at n = 100, a planted moment fault, and the pins.
- `RUNS.md`: unit timing, estimate, and one manifest per run.

---

# Phase 1 (2026-10-18): the sixth coefficient, MISSION question Q1

**Nothing in phase 1 bears on RH either.** Sections 9 to 14 add to phase 0's record and
change none of its numbers. Grades are stated per item: computations are measured;
sections 11.1 to 11.5 and 12 contain ordinary derivations that are self-reviewed only,
not externally reviewed, and say so where they stand. No novelty search was run, and
nothing here claims novelty or theorem status.

Reproduce:

```bash
.venv/bin/python hunts/jensen_wedge/probe_phase1.py --time-unit   # about 2 s
.venv/bin/python hunts/jensen_wedge/probe_phase1.py               # writes results_phase1.json
.venv/bin/python -m pytest -q -n0 hunts/jensen_wedge
```

## 9. Step 0: Holland's PDF, line by line (dated correction, 2026-10-18)

Phase 0 read Holland through a summarising fetch of the HTML rendering (section 1). Phase
1 downloaded arXiv:2608.08682v1 as PDF (25 pages, SHA-256
`3fc31ba84fb113bc0b3109fb0e569bd1d7183018485aca1eb1dab565c839b49d`), extracted it with
`pdftotext -layout` into a scratch directory outside the tree, read the extraction as
data, and checked each formula this hunt relies on.

| item | where in the PDF | status |
| --- | --- | --- |
| R_j, q_k (eq. 1); families L_j, J_j, F_j (eqs. 2 to 4); F_j = J_j(A, B, S) J_j(C, D, D) | sections 2 and 6 | agrees with section 1 |
| B_L = (q_0 - 1)^(-1), S_L = B_L R_1, q_1^(L) = (B_L + 2)/(B_L + 1) = 2 - 1/q_0, D_n = log(q_1^(L)/q_1) = 2/(n^2 L_n)(1 + O(1/L_n)) | Lemma 4.3, eq. (30) | agrees |
| T = (q_0 - 1)/(q_1 - 1), A_J = 2 q_0/(T - q_0), 1/B_J = q_0 (1 + 1/A_J) - 1, S_J = B_J R_1; A_J ~ n L_n, B_J = n + (n/L_n)(1 + O(1/L_n)); Q_n := -E_J(4) = 2/(n^3 L_n)(1 + O(1/L_n)) | eqs. (37), (38), (41), (42), (48); Lemmas 5.1 to 5.4 | agrees |
| qq_k(U, V) = (U+k)(V+k+1)/((V+k)(U+k+1)); D = B_J/2; system qq_k(A,B) qq_k(C,D) = q_k, k = 0, 1, 2; S = B R_1; matching through R_4 | eqs. (49), (51), (52), (66); Lemma 6.2 | agrees |
| A = (6/5) A_J (1 + O(1/L)), B - B_J = (n/(3L))(1 + O(1/L)), C - D = (n/(24L))(1 + O(1/L)) | Lemma 6.1, eqs. (53) to (55) | agrees |
| x = L_x (pi e^(L_x) + 3/4); script L_x := L_(2x-2) | eq. (16); Lemma 4.2 | agrees |
| Holland's gamma is this tree's divided by 8 | eqs. (14), (15) and the paragraph after (20) | agrees: with F(2k) = I_k, gamma_H(m) = Gamma(m+1) M_m/Gamma(2m+1) and M_m = 2^(-2m-2)(32 C(2m,2) F(2m-2) - F(2m)) give 8 gamma_H(m) = 8 m! (J_(m-1) - J_m/4) |
| after R_1..R_4 the multiplier vanishes at five indices with fifth derivative O(1/(n^4 log n)), r_F ~ sqrt(nd), error O(d^(5/2)/(n^(3/2) log n)) | section 12; Lemma 8.1 | agrees |

No formula of section 1 disagrees with the PDF. Four statements in this hunt's record are
looser than the source and are corrected here:

1. **Proposition 2.2 as `MISSION.md` paraphrases it** ("cannot move the zeros off the
   axis when sup |c - 1| is small on a neighbourhood of radius r ~ sqrt(nd)"). The
   proposition's threshold is sup over Omega_r of |c - 1| <= eps < 16, not "small", on
   Omega_r = {z : dist(z, [0, d]) <= 2r}, with c(0) = ... = c(4) = 1 and c(d) > 0, for a
   model p with d simple positive zeros. It has a second hypothesis, (6): at every
   critical point y of p, |y^k p^(k)(y)/p(y)| <= r^k for 0 <= k <= d. The radius enters
   only through (6). Holland verifies (6) with r_F = K_6 sqrt(Bd) in Lemma 9.1; the
   smallness he uses, sup |E_F| <= 1/2 so that |c_F - 1| <= 1, belongs to Lemma 8.1 and
   section 10, not to Proposition 2.2.
2. **Eq. (57) as section 6 cites it** ("C - D <= D/4"). The window is A >= 8B,
   B >= K_r d, D >= K_r d and 4d <= C - D <= D/4, with an absolute K_r >= 32; the lower
   bound 4d is what makes the second factor a Jacobi polynomial with positive zeros
   (eq. 77).
3. **What Lemma 9.1 consumes**, which section 6 did not name. Its proof treats the 3F2
   equation as a perturbation of the first factor's Jacobi equation with
   eps_p = (C - D)/C = O(1/L_n), and closes only once eps_p is small enough that
   theta_(n,d) <= 1/4. Section 6's question "whether the D/4 bound in eq. (57) is needed"
   has a sharper form: the D/4 bound is used in (80) and is easily replaced; eps_p -> 0 is
   what the stability step uses.
4. **Section 1's caveat** that the reading was "not line by line from the PDF" is
   superseded for the items in the table above.

## 10. Q1(a): the R_5 defect of Holland's family over (theta, n)

With D = theta B_J, phase 1 follows Holland's family from his theta = 1/2 in the unknowns
(w_A = n/A, log B, log(C - D)), so that it passes through A = infinity instead of
stalling there. Route A, 21 values of n, theta from 0.05 to 0.995 in steps of 0.01 above
0.8; the walk stops at the first grid point past A = infinity. Both crossing points are
bisected to 40 halvings. Measured (`results_phase1.json`, `theta_map_route_A`):

| n | L_n | n^4 L E_F(5) at theta = 0.125 | 0.25 | 0.5 | 0.7 | theta_star | theta_inf | (theta_inf - theta_star) L_n |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 2.503 | -3.591 | -1.850 | -0.698 | -0.236 | 0.79405234 | 0.85192261 | 0.145 |
| 100 | 3.025 | -6.779 | -3.314 | -1.250 | -0.486 | 0.81928772 | 0.86987890 | 0.153 |
| 200 | 3.564 | -10.48 | -4.956 | -1.878 | -0.801 | 0.84060463 | 0.88498213 | 0.158 |
| 400 | 4.118 | -14.20 | -6.585 | -2.517 | -1.145 | 0.85834771 | 0.89754391 | 0.161 |
| 800 | 4.685 | -17.63 | -8.103 | -3.127 | -1.491 | 0.87309346 | 0.90799452 | 0.163 |
| 1600 | 5.264 | -20.70 | -9.476 | -3.691 | -1.824 | 0.88540763 | 0.91673853 | 0.164 |
| 3200 | 5.852 | -23.41 | -10.70 | -4.207 | -2.138 | 0.89577043 | 0.92411382 | 0.166 |

Route B (direct saddle evaluation, no quadrature; spread between six and five Laplace
corrections below 2e-24 relative at every entry) carries the same map to n = 1e20:

| n | L_n | n^4 L E_F(5) at 0.125 | 0.25 | 0.5 | 0.7 | (1 - theta_star) L | (1 - theta_inf) L |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1e4 | 6.836 | -27.20 | -12.45 | -4.951 | -2.603 | 0.6184 | 0.4515 |
| 1e6 | 10.97 | -37.13 | -17.10 | -7.005 | -3.945 | 0.6366 | 0.4686 |
| 1e8 | 15.25 | -42.62 | -19.71 | -8.177 | -4.740 | 0.6450 | 0.4769 |
| 1e12 | 24.00 | -48.37 | -22.44 | -9.424 | -5.603 | 0.6528 | 0.4850 |
| 1e16 | 32.90 | -51.30 | -23.84 | -10.07 | -6.053 | 0.6566 | 0.4889 |
| 1e20 | 41.87 | -53.06 | -24.68 | -10.46 | -6.328 | 0.6587 | 0.4913 |
| leading order (section 11.2) | | -60 | -28 | -12 | -7.43 | 2/3 | 1/2 |

The map, as measured:

- **E_F(5) < 0 for theta < theta_star(n)** at every n measured, with all parameters
  positive and C > D. In particular it is negative for theta <= 0.79 at every n from 50
  to 1e20, and at fixed theta its normalized size n^4 L E_F(5) grows toward the leading
  order value -4 (2 - theta)/theta derived in section 11.2 (at n = 1e20 the measured values
  are 85 to 88 percent of it; the gap closes like 1/L, as every other constant here does).
- **E_F(5) > 0 on (theta_star(n), theta_inf(n))**, a window of width about 1/(6 L_n)
  (measured 0.145/L at n = 50 to 0.166/L at n = 3200). Both edges rise to 1: theta_star
  like 1 - 2/(3L), theta_inf like 1 - 1/(2L).
- **At theta_inf, A = infinity**: w_A crosses 0, the first factor becomes Laguerre, and
  past it A < 0, outside the positive-root class; a few hundredths further B runs to
  infinity. That is the stall phase 0 recorded between theta = 0.86 and 0.95; it was A
  passing infinity, not a fold of the branch.
- theta_star(n) agrees with phase 0's four bisected crossings to all 12 printed digits.

So the sign of the R_5 defect is definite on each side of a curve theta_star(n) that
rises to 1, and the "sign change" phase 0 found is the family passing through one
particular point, identified in section 11.3.
## 11. Q1(b): the sixth coefficient is a Pade problem, and Holland's family already solves it

### 11.1 The leading-order reduction (derivation, self-reviewed)

Take any model that is a product of Jacobi factors J_j(U_i, V_i, .) (a Laguerre factor is
U_i = infinity) times a scale S, and let E(z) be the logarithm of target over model, as in
Holland's (44) and (82). Matching R_0..R_(m-1) means E(0) = ... = E(m-1) = 0, so
E(m) = E^(m)(xi) for some xi in (0, m). By his (14), log gamma(n+z) is h(n+z) -
log Gamma(b+z) plus a linear function of z, b = n + 1/2, so for k >= 2

    E^(k)(z) = h^(k)(n+z) - psi^(k-1)(b+z) + sum_i psi^(k-1)(V_i+z) - sum_i psi^(k-1)(U_i+z).

Insert psi^(k-1)(p) = (-1)^k (k-2)!/p^(k-1) (1 + O(k/p)) and Holland's
h^(k)(x) = (-1)^k (k-2)! (2/L)/x^(k-1) (1 + O(1/L)) (his (21) to (23) for k = 2, 3, 4,
and (28) differentiated beyond), write w = n/p for every parameter p and eps = 2/L_n:

    E^(k)(0) = ((-1)^k (k-2)!/n^(k-1)) [beta_(k-1) + O(1/L^2) + O(1/n)],
    beta_s = sum_i w_(V_i)^s - sum_i w_(U_i)^s - (1 - eps).

So at leading order, matching R_0..R_(m-1) is beta_1 = ... = beta_(m-2) = 0, and the first
defect is E(m) ~ (-1)^m (m-2)! beta_(m-1)/n^(m-1). It determines parameters and defects to
leading order in 1/L, not their O(1/L) corrections. Two rewritings make it usable.

- **Moments.** beta_s = s * int t^(s-1) (mu - tau) dt, with mu = sum_i 1_[w_(U_i), w_(V_i)]
  and tau = (1 - eps) 1_[0, 1]. Each factor is an interval, and a factor in the
  positive-root class has w_U < w_V (U > V). Matching is moment matching of an
  integer-valued density against a constant density slightly below 1.
- **Pade.** sum_s beta_s z^s/s = log prod_i (1 - w_(U_i) z)/(1 - w_(V_i) z) - log f_eps(z),
  f_eps(z) = (1 - z)^(eps - 1). Matching R_0..R_(m-1) is agreement of a rational function
  with f_eps through z^(m-2), and f_eps is a Stieltjes function:
  f_eps(z) = int_0^1 dlambda(x)/(1 - x z) with lambda the Beta(1 - eps, eps) law.

Holland's constants come out. Laguerre, one interval [0, 1 - beta]: beta = eps and
D_n ~ eps/n^2 = 2/(n^2 L), his (30). Jacobi, [alpha, 1 - beta]: alpha = beta = eps/2, so
A_J ~ nL and B_J ~ n(1 + 1/L), his (41) and (42), and E_J(4) ~ -eps/n^3 = -2/(n^3 L), his
(48). Each first defect's sign is a sign-change count: mu - tau is -(1 - eps) on uncovered
points of [0, 1], at least eps on covered ones and at least 0 beyond 1; being orthogonal to
polynomials of degree m - 3 it changes sign at least m - 2 times, and with exactly m - 2
changes the sign of int t^(m-2) (mu - tau) is the sign of mu - tau at the right end.

### 11.2 Holland's D-fixed family at leading order

With w_D = omega fixed and every deviation of order eps (omega - 1 much larger than eps),
the first-order solution is gamma := w_D - w_C = eps/(6 omega (omega - 1)),
beta = eps/2 + eps/(6 (omega - 1)), alpha = eps (3 omega - 1)/(6 omega), and the R_5
coefficient beta_4 = eps (2 omega - 1)/3 (pinned in the tests at three values of omega).
At omega = 2 (theta = 1/2) this is Holland's (6/5, 1/3, 1/24) exactly, and it predicts
n^4 L E_F(5) -> -4 (2 omega - 1) = -4 (2 - theta)/theta: -12 at theta = 1/2. His two
intervals, [alpha, 1 - beta] and [w_C, w_D] near w = 2, give three sign changes where four
are needed, which is why E_F(5) < 0 there.

The exact leading-order family (any eps) follows from truncating Q f_eps (probe:
`lo_family`). Along it, as theta grows, the second interval slides from w ~ 2 into [0, 1]
and widens; E_F(5) changes sign at theta_star; then w_A falls through 0 (A = infinity,
the Laguerre limit) at theta_inf and turns negative, and soon after B runs to infinity.
That is phase 0's stall, which was A passing infinity and not a fold. As eps -> 0,
theta_star -> 1 - 2/(3L) and theta_inf -> 1 - 1/(2L) (section 10's table).

### 11.3 Two factors: the [2/2] Pade point

With D free the four-parameter system matching R_0..R_5 is square, and at leading order it
is the [2/2] Pade approximant of f_eps. For a Stieltjes function this approximant exists,
is unique, and has real interlacing zeros and poles: here 0 < a1 < b1 < a2 < b2 < 1, two
disjoint intervals in [0, 1], so both factors are in the positive-root class with U - V of
order n. As eps -> 0 it tends to the Lobatto (Simpson) configuration: uncovered gaps of
length eps/6 at 0, 2 eps/3 at 1/2 and eps/6 at 1, the three-node rule exact for cubics. At
every eps tested the nodes satisfy a1 + b2 = b1 + a2 = 1 to 12 digits, a reflection
symmetry measured and not derived here.

What the leading-order model predicts about the parameters, and what it does not. The gaps
at the pinned nodes 0 and 1 fix A ~ 3nL and D ~ n (1 + 1/(3L)); the interior gap's length
fixes B - C ~ 16n/(3L); the total uncovered length is eps, so the L^1 distance of section
12.4 is 2/L. The interior node itself sits at w = 1/2 only to leading order: the true
target density is not constant but about 1 - 2/L(n/t), since L varies across the scales
n/t, and that profile moves an interior node by O(1/L), which shifts B and C individually
by O(n/L). The constant-density model does not see this, so it misses B + C - 4n at order
n/L, and this file claims nothing about it. (C - D)/D -> 1 and the second factor's
relative gap rho_CD = 1 - D/C -> 1/2 are unaffected.

Measured, route A (every n from 50 to 3200 was solved; a selection) and route B:

| n | A/(nL) | (D - n) L/n | (B - C) L/n | (B - 2n) L/n | (C - 2n) L/n | rho_CD | gap total x L | D/B_J | n^5 L E_S(6) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 50 | 7.392 | 0.706 | 3.628 | 2.867 | -0.761 | 0.244 | 1.366 | 0.794052342 | -0.258 |
| 200 | 5.546 | 0.584 | 3.755 | 2.442 | -1.313 | 0.287 | 1.539 | 0.840604630 | -0.614 |
| 800 | 4.763 | 0.515 | 3.914 | 2.216 | -1.698 | 0.322 | 1.641 | 0.873093456 | -0.907 |
| 3200 | 4.343 | 0.473 | 4.064 | 2.085 | -1.979 | 0.350 | 1.706 | 0.895770429 | -1.112 |
| 1e4 | 4.122 | 0.449 | 4.173 | 2.015 | -2.158 | 0.367 | 1.744 | 0.909546900 | -1.235 |
| 1e8 | 3.473 | 0.380 | 4.677 | 1.813 | -2.864 | 0.434 | 1.877 | 0.957692497 | -1.651 |
| 1e12 | 3.297 | 0.362 | 4.883 | 1.758 | -3.125 | 0.457 | 1.920 | 0.972799818 | -1.778 |
| 1e20 | 3.169 | 0.350 | 5.060 | 1.719 | -3.341 | 0.475 | 1.953 | 0.984265818 | -1.872 |
| leading order | 3 | 1/3 | 16/3 | (not predicted) | (not predicted) | 1/2 | 2 | 1 - 2/(3L) | -2 |

Every parameter is positive and A > B, C > D at all 3151 n on route A and at every n on
route B; the matching residuals are below 1e-60. The predicted columns approach their
limits like 1/L. B and C individually drift with n, as the paragraph above says they may,
and their deviations from 2n stay of order n/L (each column stays within [-3.4, 2.9]).

**Phase 0's crossing is this point.** Started from the Pade guess, a direct solve of
(A, B, C, D) reproduces phase 0's bisected theta_star to all 12 printed digits at
n = 100, 400, 1600 and 3200, and the theta map of section 10 finds the same point at every
n. Phase 0's question, whether the D/4 bound of eq. (57) is needed, therefore has a
definite consequence: the sixth coefficient needs no third factor, and the configuration
that supplies it has a second factor far from the identity.

### 11.4 The R_6 defect of the Pade model

At first order beta_5 = -eps/24 (Simpson's error on t^4), so
E_S(6) ~ 4! beta_5/n^5 = -2/(n^5 L). Its sign is forced twice: mu - tau has exactly four
sign changes and ends in a gap, and the Gauss-quadrature remainder of the Stieltjes measure
is positive.

Measured: E_S(6) < 0 at all 3151 integers n = 50..3200 on route A, with no sign change, and
at all eight values of n from 1e4 to 1e20 on route B; n^5 L E_S(6) runs from -0.258 at
n = 50 to -1.872 at n = 1e20 (table above), toward -2. Route B agrees with route A on
E_S(6) to relative 5.0e-12, 1.4e-14, 8.6e-17, 1.9e-18, 2.1e-20 and 1.8e-22 at n = 100,
200, 400, 800, 1600 and 3200, within its own spread between six and five Laplace
corrections, and resolves the sign at each. This is a hardened-shape reading on those six
points (two routes sharing no quadrature agree); the file grades it measured, as phase 0
did.

### 11.5 Near-identity factors: obstructed at Holland's scale, mesoscopic at leading order

Holland's construction is near-identity: one main Jacobi factor, and a second with
rho = (C - D)/C = O(1/L) (1/(12L) at leading order), which Lemma 9.1 consumes. The MISSION
asks whether a third factor of that kind absorbs R_5.

**Obstruction at first order in 1/L (derivation, self-reviewed).** Take a main factor with
w_A = alpha, w_B = 1 - beta, and K auxiliary factors with w_(D_j) = omega_j and
w_(C_j) = omega_j - gamma_j, where alpha, beta and every gamma_j are of order eps and
every omega_j stays in a compact subset of (0, infinity). In this pairing the
positive-root class is gamma_j > 0. To first order, matching R_0..R_5 is
-beta - alpha + sum gamma_j = -eps and sum_j gamma_j omega_j^k - beta = -eps/(k+1) for
k = 1, 2, 3. With g_j = gamma_j/eps and b = beta/eps, the moments m_k = sum_j g_j omega_j^k
of a positive measure would equal b - 1/(k+1): m_1 > 0 needs b > 1/2, and Cauchy-Schwarz,
m_2^2 <= m_1 m_3, needs b <= 1/6. No solution, for any K. If gamma is allowed to be
negative and K = 1, the unique solution is b = 1/6, omega = 1/2, g = -2/3: a hole at
w = 1/2, which in its own pairing has C < D and which re-pairs into the Simpson
configuration of 11.3. By compactness, a sequence of exact solutions with bounded scaled
parameters would converge to a first-order solution, so the obstruction holds for exact
solutions at all large n in this class. Grade under `ALIGNMENT.md` section 5: restricted
class obstructed, on a self-reviewed derivation (the class: one main factor plus any number
of auxiliary factors, all deviations of relative order 1/L).

**Mesoscopic configurations exist at leading order (measured, leading-order model only).**
Outside that class three factors do match R_0..R_5 with both non-main factors
near-identity in the limit. A grid scan of the two-parameter family of three-factor
solutions (all nodes real, poles in (0, 3], every factor U > V) finds admissible
configurations whose largest non-main relative gap X is 0.173 at eps = 0.342
(L = 5.85, n = 3200) and 0.182 at eps = 0.1, then falls to 0.145, 0.109, 0.077 and 0.055
at eps = 0.03, 0.01, 0.003 and 0.001 (L = 2000); between eps = 0.01 and 0.001 it falls
like eps^0.30, close to the eps^(1/3) of a first-order picture with gaps of size
eps/delta^2 at separations delta. The values are grid minima, so upper bounds on the best
X. In the best configurations two auxiliary factors overlap near w ~ 0.92 to 0.98. At
n = 1e20 (eps = 0.048) this scaling gives X ~ 0.2, against Holland's second factor at
1/(12L) ~ 0.002: near-identity only asymptotically and only at rate L^(-1/3). Whether
exact solutions of this kind exist at finite n, and whether Lemma 9.1's perturbation
argument extends to a 4F3 whose auxiliary factors have rho ~ L^(-1/3), was not examined:
unresolved.
## 12. Q1(c): six-point stability, a conditional derivation

**Status: an ordinary derivation, self-reviewed only, not externally reviewed. Two of
its inputs are not proved here (H1, H3 below). It is not a theorem and this file does not
call it one. Novelty: not searched.**

### 12.1 Proposition 2.2 for m points

Holland's proof of Proposition 2.2 uses the five vanishing conditions only to start the
sum in (8) at k = 5. Starting it at k = m gives, word for word:

> **Proposition 2.2_m.** Let m <= d, p real of degree d with d simple positive zeros and
> p(0) != 0, c holomorphic near Omega_r with c(0), ..., c(d) real, c(0) = ... = c(m-1) = 1,
> c(d) > 0 and sup over Omega_r of |c - 1| <= eps < 2^(m-1). If (6) holds at every critical
> point of p, then P = sum p_j c(j) y^j has d simple positive zeros, and (7) holds.

Proof: at a critical point, |P/p - 1| <= eps * sum_{k=m}^{d} 2^(-k) < eps 2^(1-m) < 1, then
Holland's sign-alternation argument unchanged. So the six-point version holds with the
same radius r and eps < 32; the answer to the MISSION's "does Proposition 2.2 generalise
to six-point vanishing with the same radius" is yes, and it is the trivial part. The
radius was never Proposition 2.2's: it is whatever r makes (6) true for the model.

### 12.2 Lemma A: the derivative ratios from root geometry

> **Lemma A.** Let p have d simple real zeros y_1 < ... < y_d and let y > 0 be a critical
> point. Then for every k >= 0, |y^k p^(k)(y)/p(y)| <= (y sum_j 1/|y - y_j|)^k. If
> consecutive zeros are at least g apart, y sum_j 1/|y - y_j| <= y (4 + 3 H_d)/g, with
> H_d the d-th harmonic number.

Proof: p^(k)/p = k! e_k(x) with x_j = 1/(y - y_j), and |e_k(x)| <= e_k(|x|) <= (sum |x_j|)^k/k!.
For the second claim let y lie between y_i and y_{i+1}, delta_1 = y - y_i <= delta_2 =
y_{i+1} - y (the other case is symmetric), so delta_2 >= g/2. The remaining zeros on each
side sit at distances at least g, 2g, ..., so each side sums to at most H_d/g. p'(y) = 0
gives 1/delta_1 <= 1/delta_2 + H_d/g <= (2 + H_d)/g, and the total is at most
(2 + H_d)/g + 2/g + 2 H_d/g.

So (6) holds with r = y_max (4 + 3 H_d)/g, where y_max is the largest zero and g the
smallest gap. Lemma A needs no differential equation and no closeness of the model to a
single Jacobi polynomial. The price is the factor H_d ~ log d.

### 12.3 The smallest gap of a finite-free model

> **Lemma B (Sturm).** Let p_1(y) = 2F1(-d, A; B; y/A) with A >= 8B and B >= 256 d. Its
> zeros lie in [B/2, 3B/2] and consecutive zeros are at least
> g_1 = pi sqrt(B/(2.47 d + 6.07)) apart.

Proof: the zeros lie in [B - 8 sqrt(Bd), B + 8 sqrt(Bd)] by Holland's (79) (his (77) holds),
inside [B/2, 3B/2] when B >= 256 d. p_1 solves R p'' + P p' + d p = 0 with R = y(1 - y/A),
P = B - y + (d-1)y/A (Holland's operator J). With p = u exp(-(1/2) int P/R), u'' + Q u = 0,
Q = d/R - (P/R)^2/4 - (P/R)'/2 <= d/R + (P R' - P' R)/(2 R^2). On [B/2, 3B/2]: 1 - y/A >= 13/16,
R >= 13B/32, |P| <= 0.501 B, |R'|, |P'| <= 1, R <= 3B/2, so Q <= (32d/13 + 6.07)/B. Sturm
comparison with sin(sqrt(Q_max) y) separates consecutive zeros of u, which are those of
p_1, by at least pi/sqrt(Q_max).

> **Lemma C (log-mesh transfer).** If p_F = p_1 [x]_d q with q having positive zeros, then
> min_i y_{i+1}/y_i over the zeros of p_F is at least the same quantity for p_1.

This is Martinez-Finkelshtein, Morales and Perales, arXiv:2309.10970, Proposition 2.17
(preservation of lmesh, attributed there to Katkova, Shapiro and Vishnyakova), read in
the PDF on 2026-10-18. Holland's convolution is the reciprocal form of theirs (his Lemma
7.1 proof), and the ratio of consecutive zeros is invariant under reciprocation.

Combining with Holland's Lemma 7.1 for the further factors (zeros of the normalized
factor in [1 - eta, 1 + eta], eta = 8 sqrt(d/D) by (79)): the zeros of p_F lie in
[(B/2)(1 - eta), (3B/2)(1 + eta)], their smallest gap is at least (1 - eta) g_1/3, and
Lemma A gives (6) with

    r <= (9/(2 pi)) ((1 + eta)/(1 - eta)) (4 + 3 H_d) sqrt(B (2.47 d + 6.07)),

that is r = O(sqrt(Bd) log d) with every constant explicit. Nothing here uses
(C - D)/C -> 0.

### 12.4 The sixth-order residual

Write w = n/(parameter) and mu = sum_i 1_[w_{U_i}, w_{V_i}] for the model (section 11.1).
For complex z with |z| <= eta n,

    E^(6)(z) = h^(6)(n + z) + int f_z'(t) (mu(t) - 1_[0, n/b](t)) dt + O(n^-6),
    f_z(w) = 24 w^5/(n + z w)^5,

because psi^(5)(p + z) = f_z(n/p) + O(p^-6) and f_z(0) = 0. |f_z'(t)| <= C/n^5 on
0 <= t <= 2, so the middle term is at most (C/n^5) times the L^1 distance from mu to
1_[0, 1], which is the total uncovered length of [0, 1] plus overlaps: exactly eps = 2/L
at leading order for the Pade model (measured: `gap_total_times_L` -> 2). With Holland's
(25) carried to the sixth derivative (H3), sup over n + Omega of |E^(6)| <= C/(n^5 log n),
and Hermite-Genocchi on the convex Omega gives
sup over Omega of |E| <= C (d + 2r)^6/(6! n^5 log n).

### 12.5 The chain, and its two open inputs

- **H1 (matching at every large n).** For all n >= n_0, Holland's four-parameter system
  with D free has a solution within relative O(1/L) of the leading-order Pade
  configuration. Measured at every integer n in 50..3200 (route A) and at eight values
  from 1e4 to 1e20 (route B), section 11.3. A proof would follow Holland's Lemma 6.1 contraction in scaled
  variables; the limiting system's Jacobian is nonsingular (determinant -1/24 in the
  quadrature coordinates of section 11.2, pinned in the tests). Not written.
- **H3 (sixth derivative of the saddle).** Holland's Proposition 4.1 states the
  remainder bound (19) for 0 <= r <= 5; his proof is Cauchy's inequality on an
  O(|z|^(-1+eps_0)) remainder and gives any fixed r, and (29) differentiates once more.
  Routine, not written.

Given H1 and H3: for d >= 6 and n^4 log^2(n+2) >= K d^6 log^12(d+2) with K large, every
parameter condition of 12.3 holds (all parameters are of order n and d = o(n)), r =
O(sqrt(nd) log d), sup over Omega_r of |E| <= C d^3 log^6(d+2)/(n^2 log n) <= 1/2, so
|c - 1| <= 1 < 32, and Proposition 2.2_6 applied to the Pade model gives d distinct negative
zeros of J^{d,n}. As a delta against Holland's Theorem 1.1 (n^3 log^2(n+2) >= K d^5) this
would move the exponent from 3/5 to 2/3 at the cost of a log^12 d factor, conditional on
H1, H3 and review.

The same Lemmas A to C applied to Holland's own m = 5 model replace his Lemma 9.1 and give
his wedge with a log^10 d loss; that is a cross-check of the route, not an improvement.

### 12.6 Measured: the hypotheses of the chain on actual polynomials, n = 3200

Holland's model at theta = 1/2 and the Pade model, each with its route A parameters at
n = 3200, for d = 6 to 96. Every polynomial was evaluated at dps 60 + 2d from a dps-260
route A block (coarse/fine 9.3e-275, agreeing with the main table to 1.1e-71); roots by
sign changes on a grid of step sqrt(B/d)/20, refined by bisection. "r needed" is
max_k |T_k|^(1/k) over every critical point; "Lemma A" is max y sum 1/|y - y_j|; "explicit"
is y_max (4 + 3 H_d)/g. Units of sqrt(Bd) throughout, with B the first factor's
parameter (4093.7 for Holland's model, 7540.4 for the Pade model).

| model, d | real roots (model / Jensen / first factor) | min gap x sqrt(d/B) | r needed | Lemma A | explicit | first-factor gap / Sturm bound | max over j <= d of abs(c_j - 1) | c_j = 1 through j |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Holland, 6 | 6 / 6 / 6 | 2.877 | 1.136 | 2.104 | 4.146 | 1.683 | 4.1e-14 | 4 |
| Holland, 24 | 24 / 24 / 24 | 2.956 | 1.348 | 2.982 | 5.886 | 1.529 | 2.9e-10 | 4 |
| Holland, 96 | 96 / 96 / 96 | 2.963 | 1.565 | 3.957 | 8.619 | 1.479 | 3.9e-7 | 4 |
| Pade, 6 | 6 / 6 / 6 | 3.905 | 0.837 | 1.550 | 3.055 | 1.710 | 5.7e-19 | 5 |
| Pade, 24 | 24 / 24 / 24 | 4.011 | 0.993 | 2.197 | 4.337 | 1.554 | 7.5e-14 | 5 |
| Pade, 96 | 96 / 96 / 96 | 4.021 | 1.152 | 2.916 | 6.351 | 1.506 | 4.9e-10 | 5 |

(d = 12 and 48 are in the JSON and sit between their neighbours.) What this shows, and its
limits:

- Every model and every Jensen polynomial has all its roots real and simple; the count
  discrepancy of Proposition 2.2's (7) is 1 everywhere. These J^{d,n} are hyperbolic by
  GORTTW Cor. 1.3 already, so this checks instruments, not mathematics.
- The radius actually needed in (6) is about sqrt(Bd) for both models (0.84 to 1.57), and
  grows slowly with d. Lemma A's bound grows like log d, as derived (2.1 to 4.0), and is
  above the need at every point, as it must be.
- The first factor's smallest gap is 1.48 to 1.71 times the Sturm bound of Lemma B, even
  at d = 24 to 96 where Lemma B's hypothesis B >= 256 d fails. The log-mesh of every model
  is at least that of its first factor (Lemma C) at every d.
- The sixth-order model's residual multiplier is smaller than Holland's at every d, by a
  factor of 7e4 at d = 6 and 8e2 at d = 96: one more matched coefficient, measured.
- The Pade model meets Lemma B's A >= 8B here (A/B = 10.8) but its second factor has
  rho_CD = 0.35, far outside Holland's eq. (57) window, and its roots still behave like
  Holland's. That is the claim of 12.2 and 12.3, that the window is not what stability
  needs, seen at one n; it is not evidence for the asymptotic chain.

### 12.7 What the chain would and would not give

If H1, H3 and review all hold, the result is a wedge of exponent 2/3 against Holland's 3/5,
with an explicit-in-principle route to the constant (every constant in Lemmas A to C is
explicit; the saddle constants are phase 2's job). It would leave the small-n, large-d
corridor exactly as Holland's does, and n = 0 with all d is RH itself (`MISSION.md`, "What
success would mean"). It is a statement about one family of comparison models; it is not
progress on RH, and nothing here says otherwise.

## 13. Phase 1 verdict

**Q1 is graded attempt unresolved** (`ALIGNMENT.md` section 5, item 3): the sixth-order
construction step is found and measured, and a derivation of the stability step exists,
but it rests on two unproved inputs (H1, H3) and has had no review. Inside Q1:

| piece | disposition | grade of the evidence |
| --- | --- | --- |
| (a) sign of E_F(5) over (theta, n) | mapped: negative below theta_star(n), positive up to theta_inf(n), outside the positive-root class beyond | measured, routes A and B; leading constants derived (11.2) |
| (b) matching R_5 with positive parameters | found: Holland's own family at D = theta_star B_J, the [2/2] Pade point; no third factor needed | measured at every n = 50..3200 and to 1e20; identification derived (11.1, 11.3) |
| (b) a third factor of Holland's near-identity kind | restricted class obstructed (item 2): impossible with all deviations of relative order 1/L | derivation, self-reviewed (11.5) |
| (b) three factors at mesoscopic scale | exist at leading order with non-main gaps ~ L^(-1/3); finite-n and Lemma 9.1 extension unresolved | measured in the leading-order model only |
| (c) six-point Proposition 2.2 | holds, same radius, eps < 32 | derivation, self-reviewed (12.1); a one-line change to Holland's proof |
| (c) derivative ratios (6) without Lemma 9.1 | Lemmas A to C give r = O(sqrt(Bd) log d) for any finite-free model with a Jacobi factor | derivation, self-reviewed (12.2, 12.3); measured at n = 3200, d <= 96 (12.6) |
| (c) the six-coefficient wedge n^4 log^2(n+2) >= K d^6 log^12(d+2) | conditional on H1 and H3 | derivation, self-reviewed; not a theorem, not claimed as one |

The kill conditions of `MISSION.md`, checked one by one:

| kill condition | status after phase 1 |
| --- | --- |
| Holland's sign facts at R_3 and R_4 fail to reproduce | not met (phase 0; unchanged) |
| the saddle expansion disagrees with the exact table beyond its stated error at n <= 3200 | not met under the rule phase 0 finally used (section 3); phase 1's direct route B agrees with route A on E_S(6) within its stated spread at all six points checked |
| the R_5 defect changes sign within the measured n range on both routes, blocking a single sixth-order factor of Holland's type | **not met as written**: at Holland's D = B_J/2 it is negative at every n on both routes. At a fixed D = theta B_J with theta in (0.794, 0.896) it does change sign with n on route A, because the crossing theta_star(n) moves through theta; that is a curve of crossings, not a defect without a sign. The condition's consequence is overtaken by 11.3: the sixth coefficient needs no extra factor |
| every candidate third factor needs a parameter outside the positive-root class to match R_5 | **not met**: the two-factor Pade model matches R_5 with every parameter positive and both factors positive-root (U - V of order n), and positive three-factor configurations exist at leading order. Met only inside the restricted class of 11.5, where the one-factor first-order solution needs C < D |
| a planted weakening of an explicit constant does not turn the effectivity check red | not yet applicable (phase 2) |
| the time box of 2026-11-29 passes | not reached |

What phase 1 changes for the rest of the hunt. The construction is no longer the open
step at m = 6: it is a Pade problem with a positive answer. The open steps are H1 (a
contraction proof of the matching at every large n, which Holland's Lemma 6.1 method
should give), H3 (the sixth saddle derivative, routine), and review of Lemmas A to C.
Phase 2 (effectivity, Q2) can be run on either wedge; Lemmas A to C have explicit
constants, which is what Q2 wants. The Davenport-Heilbronn rival gate of phase 3 now has
a sharper target: the leading-order reduction reads the weight only through h and L,
that is through its double-exponential decay, which DH shares, so the MISSION's
prediction that the construction also succeeds for DH is expected to carry over to the
Pade model unchanged. That is a prediction, to be tested.

## 14. Files (phase 1)

- `probe_phase1.py`: the theta map through A = infinity, the four-parameter Pade solve,
  route B by direct saddle evaluation, the leading-order model (Pade point, theta-family,
  three-factor scan), and the root geometry at n = 3200.
- `results_phase1.json`: every number in sections 10 to 12.
- `test_jensen_wedge_phase1.py`: solvers on planted sequences (including a planted third
  factor of each orientation and a planted Laguerre first factor), the leading-order
  statements of section 11 (Lobatto limit, the exact Jacobian -1/24, the first-order
  hole, Holland's limits, theta_inf), Lemma A on known roots with a planted
  near-collision, a live recomputation at n = 400 against phase 0's crossing, and the
  pins.
- `RUNS.md`: phase 1 unit timing, estimate, and one manifest per run.

# Rival gate (2026-10-19): Davenport-Heilbronn

## 15. The prediction held

**Nothing in this section bears on RH.** `MISSION.md` predicted before the run that the
construction succeeds for Davenport-Heilbronn (DH) exactly as for zeta, since it reads the
weight only through its double-exponential decay. **Graded: held, on every item, on both
routes** (`DH_GATE.md` has the tables; `dh_gate.py`, `results_dh.json`,
`test_dh_gate.py`). Grade: measured.

- Holland's sign facts: the Laguerre defect at R_3 is positive and the Jacobi defect at R_4
  negative at all 3151 n in 50..3200 on route A (DH's gamma table by quadrature), with route
  B (Laplace series with DH's constants, no quadrature) agreeing in sign, resolving it and
  sitting inside its stated error at all 21 subgrid n, and both signs holding at n = 1e4..1e20.
- The sign map of E_F(5): negative at theta = 1/2 at every n on both routes; over theta the
  map has zeta's shape at all 21 subgrid n (negative below theta_star, positive up to
  theta_inf, A < 0 beyond), with theta_star(n) from 0.8466 at n = 50 to 0.9143 at n = 3200,
  and route B's theta_star equal to route A's to 4.7e-13 at six n.
- The [2/2] Pade match of R_5: solved at all 3151 n and all 8 large n with A > B > 0 and
  C > D > 0, and theta_star is its D/B_J to all 12 printed digits. Its R_6 defect is negative
  at every n, as for zeta.
- With L read from DH's own weight (L_DH, the saddle of its leading moment), every
  normalised constant approaches the limit Holland states or section 11 derives; at
  n = 1e20 the DH values sit within 0.5 percent of zeta's.
- The contrast: DH's Jensen non-hyperbolicity was found only at n = 0 (a complex pair at
  d = 22000, landed at d = 20000, and landed at n = 1 for d = 30000, consistent with
  `hunts/jensen_clock`'s d* = 20785.13), while every DH Jensen polynomial checked at the
  wedge cells (n = 3200, d <= 96; n = 50, d <= 24) is real-rooted. No overlap; it is
  structural, since a wedge of this shape excludes n = 0 for every constant.

So the construction of phases 0 and 1 cannot tell an RH-true function from an RH-false one
in this range: a measured, in-tree form of Farmer 2022 and GORTTW Remark 3 for this
construction. One table defect was found and worked around on the way: jensen_clock's
`omega_dh` cuts at an absolute floor and returns 0 above u = 2.86 at dps 75, so its literal
table drifts from the true one past n = 100 (log gamma off by 1.6e-21 at n = 200, 1.7e-4 at
n = 400 and 832 at n = 3200). The gate uses a relative cutoff; the two jensen_clock tables
checked against it, in the ranges jensen_clock used, agree with it (`DH_GATE.md` section
1). No kill condition of `MISSION.md` changes status.
