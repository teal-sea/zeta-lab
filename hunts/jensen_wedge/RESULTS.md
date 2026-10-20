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

Phase 3 (2026-10-19) lands the hunt: section 19 credits the prior deposits and states what
is the hunt's own, and section 20 is "The doors".

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

*Correction, 2026-10-19 (phase 2, from `REVIEW_PHASE1.md` R2):* the combination above uses
two hypotheses it does not state. The step "zeros of the normalized factor in
[1 - eta, 1 + eta], eta = 8 sqrt(d/D) by (79)" needs Holland's (77) for the second factor,
(U, V) = (C, D): **D >= 32d and C >= D + d**. The gap bound (1 - eta) g_1/3 is positive only
if eta < 1: **D > 64d**. With them the statement reads: *let p_F = p_1 [x]_d p_2 with p_1 as in
Lemma B (A >= 8B, B >= 256d) and p_2(y) = 2F1(-d, C; D; Dy/C), D >= 32d, C >= D + d,
D > 64d; then the zeros of p_F lie in [(B/2)(1 - eta), (3B/2)(1 + eta)], their smallest gap is
at least (1 - eta) g_1/3, and (6) holds with the displayed r.* Both hypotheses follow from H1
for d = o(n) (`H1_H3.md` section 5); phase 2 checks all five on every subinterval of its
covers (`EFFECTIVE.md` section 6, section 18 below). The text above is kept as written.

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

*Correction, 2026-10-19 (phase 2, from `REVIEW_PHASE1.md` R3):* the parenthesis "all
parameters are of order n" is wrong for A, which is of order n log n
(A = 3nL(1 + O(1/L)), `H1_H3.md` 4.4). The conclusion stands for n >= n_0: Lemma B's
A >= 8B holds because A/B ~ (3/2)L grows (from n = 346 on in the measured Pade model,
review R4), and B, C, D are of order n. The sentence above is kept as written.

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

*Credit, 2026-10-19 (phase 3, from `NOVELTY.md`):* rows (b) and (c) of the table above were
posted first by others, before this hunt opened on 2026-10-18. The [2/2] Pade point is the
r = 2 case of Sarnowski's diagonal Pade spine (Zenodo Papers 134Z and 134AA, 20 August
2026), and the 2/3 wedge was posted by Savva (Zenodo 10.5281/zenodo.22293642, 3 September
2026) as `n^2 log(n+2) >= K d^3`, stronger than row (c)'s `log^12 d` form. Both deposits are
unreviewed, and this hunt did not check their proofs. Phase 1 is an independent
re-derivation of them, not a delta against Holland that the lab can claim. Section 19 has
the credit in full and what remains the hunt's own. The verdict above is kept as written.

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

# H1 and H3 (2026-10-19)

## 16. The open inputs of the six-coefficient chain, closed by derivation

**Nothing in this section bears on RH.** `H1_H3.md` has the derivations;
`probe_h1_h3.py`, `results_h1_h3.json` and `test_h1_h3.py` the numbers and their pins.
Both derivations are self-reviewed only, not externally reviewed, and are not theorems.
No novelty search was run.

| input | status before | status now | rests on |
| --- | --- | --- | --- |
| H1 (section 12.5): the system with D free has, for `n >= n_0`, a solution within relative `O(1/L)` of the [2/2] Pade configuration | open, measured | **proved by derivation (self-reviewed)**, `H1_H3.md` section 4 | Holland's Proposition 4.1 at r = 0 and the holomorphic branch of `L_N` on his sector, (P1) and (P2) |
| H3 (section 12.5): `\|h^(6)(x + w)\| <= C_6/(x^5 log x)` on `\|w\| <= eta_6 x` | open, "routine" | **proved by derivation (self-reviewed)**, section 3 | one Cauchy estimate on Holland's (25); or (P1), (P2) by his own route, (19) at r = 6 and (29) once more |
| R1 (`REVIEW_PHASE1.md`): the leading constant of h^(5), needed by H1 | open, measured | **proved by derivation (self-reviewed)**, Lemma S(b) at k = 5 | (P1), (P2) |

How. Lemma S gives every derivative of h from (P1) and (P2) by Cauchy estimates on the
error terms: `h^(k)(x) = (-1)^k 2 (k-2)!/(x^(k-1) L_x)(1 + (H_(k-2) - 1)/L_x + O(1/L_x^2))`,
uniformly on complex disks, which is Holland's (21) to (25) at k = 2..5, sharpened at
k = 5, and continued to every k. For H1 the matching system is rewritten exactly as gap
moments, `tau_j = int_G u_j'` with `u_j'(t) = (j+1) t^j prod_{i<=j+1} (1 + i t/n)^(-1)`;
in scaled variables its limit vanishes at Simpson's rule, `det J = -1` (phase 1's -1/24
with rows rescaled), and an explicit contraction on a weighted box closes once the data
`tau_j` are close enough to their limits. Every model-side constant is exact
(`kappa = 4533/15625`, `nu_w = 86/9`, admissibility iff `eps < 2/3`).

What is not explicit: `n_0`, and the constant of H3. Both inherit the non-explicit
constants of Holland's Proposition 4.1 (the complex form of GORTTW (3.2)). That is the
missing step for an explicit wedge and is phase 2's object (MISSION Q2), not a gap in H1
or H3 as the chain uses them: as in Holland's section 10, `n < n_0` is absorbed into K.

Measured beside the derivations (grade: measured):

- The contraction inequality, evaluated on the measured targets, holds at every measured
  n from 1e7 to 1e20 (route B) and fails at n <= 1e6 and on all of route A (n <= 3200);
  where it holds, phase 1's solution lies inside the radius it predicts (0.0072 against
  0.0128 at n = 1e20).
- The first-order predictions are approached monotonically over 1e4..1e20:
  `L t_j -> H_j` (0.954, 1.452, 1.792 at 1e20 against 1, 1.5, 1.833),
  `A/(nL) = 3 + 7/L` (3.1687 against 3.1672), `(D - n)L/n = 1/3 + 2/(3L)`, and
  `(B - 2n)L/n -> 5/3`, `(C - 2n)L/n -> -11/3` (1.719 and -3.341 at 1e20). The last two
  answer section 11.3's open item on B and C individually: the interior node moves by
  `1/(4L)`.
- Holland's (P1) itself, at two n: h computed from his (15) by quadrature on a complex
  circle `|z - n| = n/8` has Taylor coefficients agreeing with route B's real-axis
  derivatives to 1e-17 or better for k = 2..7 at n = 400 and 3200, `sup |h^(6)|` on
  `|z - n| = n/16` is 1.52 and 1.54 times `48/(n^5 L)`, and his remainder R varies on the
  circle by at most 0.04/n. This measures (P1); it does not establish it.

What this changes. The conditional wedge `n^4 log^2(n+2) >= K d^6 log^12(d+2)` of
section 12.5 no longer has an open input of its own: it rests on inputs Holland's
Theorem 1.1 also rests on (his Proposition 4.1, (79) and Lemma 7.1; MFMP Propositions
2.7 and 2.17), on sections 11 and 12 (reviewed internally once, no step broken) and on
`H1_H3.md` (self-reviewed). Its grade is that of its weakest step: a derivation,
internally reviewed in part, not a theorem, pending external review, and not promoted
here. The review's items R2 to R4 follow from H1 and are recorded in `H1_H3.md` section
5; R2's two hypotheses still have to be written into 12.3's statement. The derivations
read xi only through the targets, so nothing in them separates zeta from
Davenport-Heilbronn, consistent with section 15. No kill condition of `MISSION.md`
changes status.

# Literature search (2026-10-19)

## 17. Claims A and B already have prior instances; claim C has none located

**Nothing in this section bears on RH.** `NOVELTY.md` records a bounded literature search
of 2026-10-19: OpenAlex and Semantic Scholar citation listings, Google Scholar, the arXiv
API, zbMATH Open, Zenodo through OpenAlex, both 2026 Planat articles, and
`the-omega-institute/trureturing` PRs. It lists every query and what it returned. Each
verdict below is about the searched set only.

| claim | verdict | prior instance |
| --- | --- | --- |
| A: the six-coefficient wedge `n^4 log^2(n+2) >= K d^6 log^12(d+2)` (section 12.5) | prior instance found | Savva, Zenodo 10.5281/zenodo.22293642, 3 September 2026: `n^2 log(n+2) >= K d^3`, the same exponent without the `log^12 d` loss, by Holland's family with D free matching six coefficients at the limit point of section 11.3. Unreviewed and AI-assisted by the author's own account; its proof was not checked here |
| B: Holland's two-factor family matches the sixth coefficient at a [2/2] Pade point (section 11.3) | prior instance found | Sarnowski, Zenodo Papers 134Z and 134AA (10.5281/zenodo.22023893, 10.5281/zenodo.22025447), 20 August 2026: the rank-r diagonal Pade spine. At r = 2 its limits (`A ~ 3NL`, smallest parameter `~ N`, interior node 2, first unprotected derivative `~ -2/(N^5 L)`) are those of sections 11.3 and 11.4. Unreviewed |
| C: an explicit value of Holland's K or GORTTW's c | no prior instance found in the searched set | Savva, Sarnowski and Ning (Zenodo 10.5281/zenodo.19891455, a `n + d >= C_0 d^3` wedge predating Holland) leave their constants uncomputed. Planat's `C_0 ~ 0.020` belongs to a weaker `n >= C_0 d^4` statement in an inconsistent normalisation (`NOVELTY.md` section 4) |

Planat, Mathematics 14 (2026) 1884, is not a degree-uniform "all n >= C" result: its
threshold is `n >= C_0 d^4`, with an exponent chosen to fit observed scaling and a
constant partly fitted. It places a positive onset at `d >= 9`, which GORTTW Corollary 1.3
excludes for the standard family, and it cites neither GORTTW nor Holland.

What this changes. Phase 1's sixth-order construction and its conditional wedge
independently re-derive results deposited 6 to 9 weeks before the hunt opened. They are
not a delta against Holland that this lab can claim. Phase 2 (MISSION Q2, explicit
constants) has no located prior instance. `NOVELTY.md` section 2.3 adds a derived,
unreviewed remark: any proved bound `K <= e^(1e21)` on Holland's K makes `c = 1`
admissible in GORTTW Theorem 1.1, so the substantive explicit target is K. Whether to
redirect phase 2 is the owner's decision. No kill condition of `MISSION.md` changes
status.

# Phase 2 (2026-10-19): explicit constants, MISSION question Q2

## 18. Both wedges with explicit constants

**Nothing in this section bears on RH.** `EFFECTIVE.md` has the derivations; `effective.py`
evaluates every numeric step in Arb ball arithmetic (python-flint, checked through
`zeta.rigor.BACKEND`), `results_effective.json` records the run and `test_effective.py` (36
tests) pins it. **Grade: derivation, self-reviewed, not reviewed by an independent session,
not a theorem.** `NOVELTY.md` (claim C) found no explicit constant for any wedge of this kind
in the searched set.

| statement | explicit constant | the chain covers | small n |
| --- | --- | --- | --- |
| (5a) `n^3 log^2(n+2) >= K d^5` implies `J^{d,n}` hyperbolic | **K = 17 900** | n >= 9.91e33 | GORTTW Cor. 1.3 (d <= 9.36e20, every n) |
| (5s) `n^3 log^2(n+2) >= K d^5` implies d distinct negative zeros | **K = 9.10e19** | n >= 789 702 | wedge empty below |
| (6a) `n^4 log^2(n+2) >= K' d^6 log^12(d+2)` implies hyperbolic | **K' = 7.21e9** | n >= 5.65e35 | GORTTW Cor. 1.3 |
| (6s) the same, d distinct negative zeros | **K' = 3.61e30** | n >= 14 237 025 | wedge empty below |

(5s) is Holland's Theorem 1.1 with its constant explicit; (5a) trades his small-n absorption
for GORTTW's corollary, which rests on Platt's verification of RH to 3.06e10. In (5a), (6a) the
zeros are distinct and negative for d > 9.36e20. By `NOVELTY.md`'s remark 2.3, (5a) makes
`c = 1` admissible in GORTTW Theorem 1.1 (hyperbolic for every `n >= e^(d/2)`), with (5a)'s
grade.

**The missing step of section 16, closed.** `n_0` and the H3 constant inherited Holland's
non-explicit Proposition 4.1. Lemma R replaces it: on `|z - x| <= x/4`, `x >= x_0`,
`h(z) = const - (2z+1) log 4 + G(2z) + R(z)` with an explicit main term `G` (the complex
saddle of the leading Mellin term) and `|R| <= lambda(x_0)`, from a Laplace bound on a contour
through the complex saddle (Lemmas V and L). Its rate is `|z|^(-1/2 + eps)`, not Holland's
`|z|^(-1 + eps_0)`, and only `|R| < 1` is needed. The derivatives of `G` are exact rational
functions `F_k(e, m)` of the saddle; their first-order constants are `H_(k-2) - 1`, as in
`H1_H3.md` Lemma S(c). Every later step of Holland's proof (Lemmas 4.3 to 10) has an explicit
replacement: matching with `D = n/2` by an interval Krawczyk test, a sharper Gershgorin
localisation (`C_loc <= 2.094`), his Lemma 9.1 closed by `a + b + theta < 1` with
`K_6 = 2.53`, and his Lemma 8.1 with `Theta_5 <= 1.034` against the leading value 1. The
six-coefficient chain uses an explicit H1 (Lemma M6), Lemmas A to C with R2's hypotheses (now
written into 12.3), and the sixth-order residual with its Simpson cancellation kept
(`Theta_6 <= 0.066` against `1/24`). **No step is left non-explicit; nothing is graded attempt
unresolved.**

**The kill condition.** `effectivity_check` is green for all four variants at the claimed
constants. `planted_weakenings` moves each claimed constant (42 across the four variants)
just past its recomputation and lowers `K_6` by 0.01 (two more plants); all 44 plants turn it
red. **Not met.** Formula-level faults, which a
recomputation cannot see, are caught by independent measurements: the Laplace remainder
measured by quadrature on another contour (slack 785 to 6554), route B's derivatives and
targets inside every enclosure at n = 1e8, 1e12, 1e20, mpmath Newton solutions inside every
Krawczyk box, and the actual model polynomials at n = 1e12 (measured `C_loc` 1.52 and 1.79
against 2.16; radius needed 1.14 and 1.24 against `K_6 = 2.82`; actual defects 0.795 of the
Hermite-Genocchi bound). `test_effective.py` plants one formula fault per step and requires
each to be caught. One was caught for real on the way: a first draft stated a diagonal bound
of Lemma G without its case condition `U < 2V`, and the test on `U = 5405`, `V = 400` failed.

What this changes. MISSION Q2 is answered for both wedges, with explicit constants and a
check that fails when any of them is weakened. The constants are loose where the arguments
are: in (5a) the closing condition of Lemma 9.1 accounts for up to about 1.2e3 in K (K grows
like `K_6^10`, and `K_6 = 2.53` against a measured need near 1.24); in (6a) Lemmas A to C's
radius is 36 to 44 times what (6) needs at n = 1e12, up to about 5e18 in K'. The standalone
constants are set by where Lemma L and Lemma M6 stop closing (n_0 = 789 702 and 14 237 025).
These are inputs for phase 3's "The doors", not measured ceilings. The planted-weakening
kill condition, "not yet applicable" after phase 1 (section 13), is now checked and not met;
no other kill condition of `MISSION.md` changes status.

*Grade, 2026-10-19 (phase 3, from `REVIEW_PHASE2.md`):* an independent session reproduced
all four constants and the c = 1 remark with its own Arb code (`review_p2/`, no import of
`effective.py`) and broke no step. The grade above now reads: derivation, self-reviewed and
reviewed once by an independent session, not a theorem, pending external review. The
sentence "not reviewed by an independent session" is kept as written.

*Correction, 2026-10-19 (phase 3, from `REVIEW_PHASE2.md` item P and D3):* two sentences
above claim more than the tests delivered. "Formula-level faults ... are caught by
independent measurements" and "`test_effective.py` plants one formula fault per step and
requires each to be caught" were true of the plants phase 2 chose, not of the steps. The
review planted four formula faults into a copy of `effective.py`, each making a bound
unsoundly smaller, and **three passed all 36 tests**: Lemma L's cubic Taylor constant 8/3
written as 8/15 (`C_rho` five times too small, inside the quadrature slack of 785), Lemma
D(ii)'s Cauchy radius n/4 where only n/8 is available (no measurement sees a remainder of
order `lambda`), and Lemma B's Sturm constants 2.47, 6.07 divided by 10 (inside Lemmas A to
C's measured looseness, 39 to 44 by the note below). The review rederived those steps by hand and found them
correct, so no constant changes. Phase 3 adds seven tests (43 in all). Each of the three
steps is now checked against its own derivation: the cubic constant against its defining
Gaussian integral by quadrature; the Cauchy part against the radius the disk geometry
leaves; the Sturm factor the chain uses against the derived minimum
`(32/13) d + 2.001 (32/13)^2/2` and against the actual smallest gap of the first Jacobi
factor at the chain's own A and B (measured slack 1.75). The review's four plants are
replayed in the suite as source edits that these checks must reject, and the review's own
`review_p2/plant_formula_faults.py`, rerun on this tree, now turns the suite red on all four.
What a green suite attests, as of this correction: every claimed constant covers its
recomputation; the steps in `EFFECTIVE.md` section 8's table agree with an independent
measurement, or with their derivation, as far as the stated slack reaches. It does not
attest to the derivation as a whole. Lemma W, `c_H` and the `psi` remainders of sections
5.4 and 6 are tested only on samples or not at all, and rest on the review's hand
rederivation (R10, R12), not on a test. The sentences above are kept as written.

*Note, 2026-10-19 (phase 3, from `REVIEW_PHASE2.md` R13):* `Theta_6` is loose. The review
encloses the two averages `<omega_5'>` by exact divided differences instead of the hull of
`omega_5'` over each interval and gets `Theta_6 <= 0.0477` (6a) and `0.403` (6s), against
`0.0661` and `0.538` here, a factor of about 1.4. Since K' grows like `Theta_6^2`, the same
chain supports `K' = 3.70e9` for (6a) (review recomputation, upper end of its ball). The
claimed constants are not changed: they hold with that margin, `effective.py` keeps its
looser enclosure, and the effectivity check still compares against it. This is an input
for section 20, not a defect.

*Correction, 2026-10-19 (phase 3, found while writing section 20):* "36 to 44 times what (6)
needs at n = 1e12, up to about 5e18 in K'" above, and `EFFECTIVE.md` section 6's "12.3's r is
32 and 39 times it", misread `results_effective.json`. There 12.3's r is 32.1 and 39.1 times
`sqrt(Bd)` (d = 10, 40) and the radius (6) needs is 0.815 and 0.885 times `sqrt(Bd)`, so the
looseness is 39 and 44 times the need, and the room it leaves in K' (which moves like the
twelfth power of the radius) is up to `44^12 = 5e19`, not 5e18. No constant changes; the
looseness is larger than stated. The sentences above are kept as written.

# Phase 3 (2026-10-19): landing

## 19. Credit, the delta, and the grade

**Nothing in this section bears on RH.** Every wedge of this shape leaves out n = 0, which
is RH itself, and section 20 says why no improvement of these constants changes that.

**Prior work, credited.** Two results this hunt derived had been posted by others before it
opened on 2026-10-18 (`NOVELTY.md`, section 17):

- **The 2/3 wedge.** John Savva, *A Two-Thirds Hyperbolicity Wedge for Jensen Polynomials
  of Riemann's Xi-Function*, Zenodo 10.5281/zenodo.22293642, 3 September 2026: for an
  absolute K, `n^2 log(n+2) >= K d^3` implies that `J^{d,n}` has d distinct negative zeros,
  by Holland's two-Jacobi family with D free matching six coefficients. Squared, it is
  section 12.5's `n^4 log^2(n+2) >= K d^6 log^12(d+2)` without the `log^12 d` loss, so it is
  the stronger statement. Its K is not computed (`C_B6` and `N_analytic` are left implicit).
  Written with substantial AI assistance and with no human review claimed, by its author's
  account.
- **The Pade spine.** Michael Sarnowski, Papers 134Z and 134AA, Zenodo
  10.5281/zenodo.22023893 and 10.5281/zenodo.22025447, 20 August 2026: the rank-r diagonal
  [r/r] Pade spine of the coefficient quotients, whose r = 2 case is section 11.3's [2/2]
  point with section 11.4's constants. Unreviewed. `NOVELTY.md` does not record whether
  these deposits were AI-assisted.

This hunt did not check either proof. Sections 11.3, 11.4 and 12 are independent
re-derivations of them, and (6a), (6s) are explicit constants for the weaker `log^12 d`
form of a wedge already claimed in the literature, reached by a different stability step
(Lemmas A to C, where Savva uses a shifted 3F2 recurrence).

**What has no prior instance in the searched set.** `NOVELTY.md` (claim C) found no explicit
constant for any wedge of this kind, and none for GORTTW's c. Stated as deltas:

| source statement | as published | this hunt |
| --- | --- | --- |
| Holland, arXiv:2608.08682v1, Theorem 1.1 | an absolute `K > 0` with `n^3 log^2(n+2) >= K d^5` implying d distinct negative zeros; K not computed | **K = 9.10e19** suffices as stated, with no outside input (5s); **K = 17 900** suffices for hyperbolicity when GORTTW Corollary 1.3 is admitted for d <= 9.36e20, with distinct negative zeros for d > 9.36e20 (5a) |
| GORTTW, arXiv:1910.01227v3, Theorem 1.1 | `J^{d,n}` hyperbolic for `n >= c e^(d/2)`, some c > 0 not computed (the published version states `n >= c e^d`) | **c = 1** is admissible in both forms, from (5a) and Corollary 1.3 (`NOVELTY.md` remark 2.3, review R15) |
| section 12.5, the `log^12 d` form of the 2/3 wedge | `n^4 log^2(n+2) >= K' d^6 log^12(d+2)` with K' implicit; Savva's stronger form has K implicit too | **K' = 7.21e9** with Corollary 1.3 (6a); **K' = 3.61e30** standalone (6s) |

(5a) and (6a) rest on Corollary 1.3, which rests on Platt's verification of RH to height
3.06e10. K = 17 900 is a constant for Holland's statement reached through his family with
`D = n/2`, not the constant of his exact model with `D = B_J/2` (`EFFECTIVE.md` section 9).

**Grade.** Derivation; self-reviewed; reviewed once by an independent session
(`REVIEW_PHASE2.md`: all four constants and c = 1 reproduced with independent code, no step
broken); not a theorem; pending external review. (6a) and (6s) also take the grade of
sections 11 and 12 and of `H1_H3.md`, each reviewed once internally. Every numeric step is
an Arb enclosure, which makes each number a bound and does not review the derivation. The
hunt does not promote its own claims (`hunts/README.md`). Promotion, and any contact with
Holland, Savva or Sarnowski, are the owner's decisions.

**The kill conditions at landing.**

| kill condition (`MISSION.md`) | final status |
| --- | --- |
| Holland's sign facts at R_3 and R_4 fail to reproduce | not met (section 4) |
| the saddle expansion disagrees with the exact table beyond its stated error at n <= 3200 | not met under the rule finally used; the preset rule missed once, at n = 150 (section 3) |
| the R_5 defect changes sign within the measured n range on both routes | not met as written (section 13) |
| every candidate third factor needs a parameter outside the positive-root class | not met (sections 11.3, 13) |
| a planted weakening of an explicit constant does not turn the effectivity check red | not met: 44 of 44 constant plants red (section 18); since phase 3 the review's 4 formula plants are rejected too (`plants_phase3.json`) |
| the time box of 2026-11-29 passes | not reached; the hunt lands 41 days early, and what the remaining time is spent on is the owner's call |

**What the hunt did not do.** It makes no statement about RH. It leaves the small-n,
large-d corridor untouched. It did not check Savva's or Sarnowski's proofs, and nothing in
it has been reviewed outside this lab. No Lean formalisation was attempted (`MISSION.md`
plan step 3 puts it out of scope).

**Files (phase 3).** `test_effective.py` (seven tests added, section 18's correction);
`plants_phase3.json` (the review's `plant_formula_faults.py` rerun on this tree: control
green at 43 passed, all four plants red); dated notes in this file, `EFFECTIVE.md` and
`MISSION.md`; `docs/44-the-constant-in-the-wedge.md` (front door); three entries in
`docs/37-methods.md`.

## 20. The doors

Phase 2 measured no ceiling of the wedge. It produced the smallest self-consistent
constants of one chain of arguments, and those are **candidates, not optima of the
problem**: upper bounds on what Holland's K (and the `log^12` form's K') can be, with no
lower bound on the true constant anywhere in this hunt.

- **Candidate:** K = 17 900 (5a), 9.10e19 (5s); K' = 7.21e9 (6a), 3.61e30 (6s); c = 1.
- **Range:** the chain covers n >= 9.91e33, 789 702, 5.65e35 and 14 237 025 respectively,
  every d the wedge allows there; (5a) and (6a) hand d <= 9.36e20 to GORTTW Corollary 1.3.
- **Proof status:** section 19's grade.

### 20.1 Active constraints at the optimum

No saturation curve was measured. Each constraint is ranked by the exponent with which its
constant enters K, read off `EFFECTIVE.md`'s formulas: that exponent is its shadow price in
log K. `K_req = (C_E max(log(n+2)/v_1)/log 17)^2` with
`C_E = T_0 Theta_5 (sqrt(d/n) + 2 K_6/sqrt(w_B))^5/10` (five), and
`K'_req = (C_E max(log(n+2)/v_1)/log 33)^2` with `C_E = T_0 Theta_6 [bracket]^6/15` (six).

| variant | constraint, ranked | shadow price in log K | state at the optimum | measured room |
| --- | --- | --- | --- | --- |
| (5a) | 1. Lemma 9.1-E's closing condition `a + b + theta < 1`, which sets `K_6` | 10 (K moves like `K_6^10`; `sqrt(d/n)` is negligible past 1e33) | binding: 0.99693 at `K_6 = 2.53` and 1.0015 at 2.52, both on the subinterval at the start of the cover (n near 9.9e33), where `K_req` also peaks; on the subinterval containing n = infinity it is 0.950 | the radius actually needed at n = 1e12 is 1.14 to 1.24 `sqrt(Bd)`: up to `(2.53/1.24)^10 = 1.2e3` in K |
| (5a) | 2. Lemma G's `C_loc`, which enters `a` and so sets the `K_6` that closes | through `K_6` (not computed separately) | `C_loc <= 2.094` over the cover | measured 1.52 (d = 10) and 1.79 (d = 40) at n = 1e12 |
| (5a) | 3. Lemma 8.1-E's `Theta_5` | 2 | 1.034 against the leading value 1 | at most a factor 1.07 in K |
| (5a) | 4. Proposition 2.2's `eps < 16`, through `log 17` | -2 in `log(1 + eps)` | fixed by Holland's proposition | none inside this chain |
| (5s) | the absorption `K >= n_0^3 log^2(n_0 + 2) = 9.08e19`, with `n_0 = 789 702`, near where Lemma L's hypothesis `R_min >= 10` stops holding (`R_min = 10.21` there) | 3 in `n_0` (plus a log) | binding: the chain itself needs only `K_req = 2.49e5` | lowering `n_0` needs Lemma L below `R_min = 10`, and the chain's own `K_req` grows as `n_0` falls (`lambda = 7.0e-3`, `Theta_5 = 1.57` already at 789 702) |
| (6a) | 1. the radius of Lemmas A to C, through `bracket = 20.02` | 12 | at n = 1e12 the radius is 32.1 and 39.1 `sqrt(Bd)` where (6) needs 0.815 and 0.885 (d = 10, 40): 39 and 44 times the need | up to `44^12 = 5e19` in K' |
| (6a) | 2. `Theta_6` | 2 | 0.0661 | exact divided differences give 0.0477 (R13): a factor 1.95 in K', so K' = 3.70e9 |
| (6a) | 3. Proposition 2.2_6's `eps < 32`, through `log 33` | -2 in `log(1 + eps)` | fixed by the proposition | none inside this chain |
| (6s) | the absorption `K' >= n_0^4 log^2(n_0 + 2)/log^12 3 = 3.61e30`, with `n_0 = 14 237 025` where Lemma M6's Krawczyk test stops closing | 4 in `n_0` | binding: the chain itself needs only `K'_req = 1.48e16` | the test was not pushed below 1.4e7 |

Inside the (6a) bracket, `2 rho_r sqrt(2.47 + 6.07/d)/sqrt(w_B)` with
`rho_r = (9/(2 pi)) ((1 + eta)/(1 - eta)) c_H` carries every factor of the radius: Lemma C's
`9/(2 pi)` (zero window over gap), Lemma A's `c_H = 3.124` (the `4 + 3 H_d` over
`log(d + 2)`, the `log d` loss), Lemma B's Sturm factor and Lemma C's window
`(1 + eta)/(1 - eta)`. Each enters K' to the twelfth power. The 39 to 44 times looseness
is their product; which factor holds most of it was not measured.

### 20.2 The frozen-constant inventory

Every number below was chosen, not optimised. "Trade" marks a genuine trade shape, where
relaxing the constant helps one step and hurts another.

| constant | value | where | what relaxing it trades against | trade |
| --- | --- | --- | --- | --- |
| `RHO` | 1/4 | Lemma R's disks `\|z - x\| <= x/4` | a larger disk gives Cauchy more radius, but widens the sector `asin(RHO)`, which raises `b`, lowers `R_min` and tightens Lemma L's condition (i) | trade |
| `RHO_D` | 1/8 | the derivative disk; Cauchy spends `RHO - RHO_D` | a larger `RHO_D` admits larger `zeta = (d + 2r)/n` (checked `<= RHO_D`), at a cost of `((RHO - RHO_D) n)^(-k)` in every remainder; that cost is below 1e-40 at the assisted thresholds and 3 percent of `Theta_5` at (5s) (review R3) | trade, nearly free in one direction at the assisted thresholds |
| `T` | 1/2 | Lemma L's contour step | `C_rho`'s leading part grows like `e^T` and condition (ii) tightens; the Gaussian tails beyond T, below 1e-3700 relative at every threshold, grow as T shrinks | trade, low leverage: `lambda` enters K only through the remainder parts |
| `R_min >= 10` | 10 | Lemma L's hypothesis | sets `n_0` of (5s), K moving like `n_0^3`; relaxing it means rebuilding the majorants where the `alpha - 1` tail and the segment piece are no longer negligible | trade |
| `D` | n/2 | Lemma M5 (Holland's D is free within relative `O(1/L)` of n/2) | enters `C_loc` and `theta` through the second factor; not explored | unknown |
| `B >= 256 d`, zero window `[B/2, 3B/2]` | 256 | Lemma B | a narrower window gives smaller Sturm constants (through 13/16 and 0.501) but needs larger B/d; the constants sit 1.003 above the derived minimum | trade, low leverage |
| `eta = 8 sqrt(d/D)` | 8 | Holland's (79), used in Lemma C for the second factor | Lemma G shows the first factor's spread tends to 2, not `2(1 + sqrt 2)`; the six-coefficient chain still uses Holland's 8 | no trade found: a sharper row bound is free if it holds |
| `4 + 3 H_d`, `c_H` | 3.124 (d > 9.36e20), 5.878 (d >= 6) | Lemma A | the `log d` loss; the radius needed grows far slower (`RESULTS.md` 12.6: 0.84 to 1.57 `sqrt(Bd)` at d <= 96) | none inside Lemma A; removing it needs a different stability step |
| enclosure of `<omega_5'>` | hull | `Theta_6` | exact divided differences are tighter by 1.4 (R13), for more code | cost only |
| cover step | 1e-4, 5e-4 | every chain | finer covers cost time; the review's finer (5s) cover moved `K_req` by 2.5 percent | cost only |
| `eps < 16`, `< 32` | Holland's | Proposition 2.2, 2.2_6 | fixed by the proposition's proof (`eps sum_(k>=m) 2^-k < 1`) | not free here |
| GORTTW cut | d <= 9.36e20 | (5a), (6a) hand-off | an outside input (Platt's height 3.06e10). Platt-Trudgian's 3e12 gives d <= 9e24 (`MISSION.md`), which moves the start of the cover up; since `a + b + theta` and `K_req` both peak at that start, a later start lowers the `K_6` that closes, and K with it (like `K_6^10`); not computed | a lever from outside the family: it reads more zeros |
| `PREC` | 256 bits | every enclosure | time only | none |

`K_6` is not frozen: it is optimised on a 0.01 grid. The doors with the largest shadow
price are `K_6` with `C_loc` in (5a) and the Lemma A to C radius in (6a). Being top of this
list gives neither automatic priority, and Savva's deposit already claims the 2/3 wedge
without the `log d` loss, which bears on what an improved (6a) constant would be worth.
Allocation is the owner's decision.

### 20.3 The information class

**Every door above stays inside the data the current family already reads**: the
weight's Mellin moments through the saddle main term G and `lambda`, and the comparison
model's parameters. Tightening `K_6`, `C_loc`, `Theta_6`, the Lemma A to C radius, `T` or
`RHO` needs no new information about xi; each is slack in the proof technique.

None of them reads arithmetic. The construction reads the weight only through its
double-exponential decay (h and L, sections 11.1 and 16), which the Davenport-Heilbronn
weight shares, and section 15 measured the whole construction succeeding for
Davenport-Heilbronn on every item. So no door in 20.1 or 20.2 can separate zeta from an
RH-false function, and tightening all of them would move K, not the shape of the wedge.

**The untouched corridor: small n, large d.** Below the wedge with d > 9.36e20, and above
all at n = 0, which is RH, nothing here applies, for any K: a wedge of this shape excludes
n = 0 for every constant. Entering that corridor needs information this family does not
read, something that tells zeta from Davenport-Heilbronn, whose `J^{d,0}` stops being
hyperbolic near d = 20 785 (`hunts/jensen_clock`, section 15). That is arithmetic, a door
of a different information class, and this hunt has no mechanism for it. Raising the GORTTW
cut is also outside the family, since it reads more zeros (RH verified to a greater
height). It moves where the chain starts, and with it the constant, because (5a) binds at
the start of its cover (20.1); it does not move the corridor.
