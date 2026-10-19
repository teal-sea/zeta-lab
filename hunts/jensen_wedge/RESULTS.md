# jensen_wedge: RESULTS

**Nothing here bears on RH.** Phase 0 of hunt #135 reproduces two sign facts from
Holland's construction (arXiv:2608.08682v1) on a finite range of shifts n, and measures
one further quantity that phase 1 needs. A finite computation is not a uniform statement,
and a wedge of this shape would not touch RH even if proved (`MISSION.md`, "What success
would mean"). Grade: **measured** throughout. At the 21 subgrid points two independent
routes agree, which is the shape of a hardened reading; this file still grades it
measured.

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
