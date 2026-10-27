# Probe lane: what a comparison system other than the sextic one is worth

**Hunt #136, lane `probe`, 2026-10-21, revised after two verifier passes the same day.
Status: pricing, not proving; unreviewed by any person. Files produced, not landed:
`probe_table.py`, `test_probe_table.py`, this page.**

Grades. *cited*: a line of the pinned `paper.tex` (sha256 `42a5ee0f...c6a3`), quoted in
`probe_table.CITATIONS` and checked by `verify_citations` (all 91 on their stated line),
or a line of a pinned outside source (`OUTSIDE_CITATIONS`, all 22 checked against Liu's
cached sources and their sha256). *derived*: algebra done here, checked in exact
rational arithmetic (fractions, and sympy for symbolic k) by `test_probe_table.py`.
*inferred*: a reading no computation here checks. *measured*: a float optimisation,
labelled as such. A composite claim takes the grade of its weakest step. Nothing here
concerns real part 1/2, nothing here checks a lemma of the paper, and no improvement of
the half-plane is claimed: every number below is the price of an input nobody here has
proved.

```
.venv/bin/python hunts/below_seven_eighths/probe_table.py --paper   # tables + citations
.venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_probe_table.py
```

## Summary

1. **The target is a function of one structural integer.** Write k for the order of the
   row characters: the Poisson frequencies are u a^k, the signal's pole is that of
   zeta_F(kz) at z = 1/k, and the Gram bound's exceptional frequencies are k-th powers.
   Holding every other estimate of the paper at its stated form, the direct-bound
   target is `sigma_0 = 1 - 1/k + (M - 2 ell)/(2k)`. The algebra is derived, symbolic in
   k; that it describes a system whose row characters have order k rests on the k-reading
   of item 2, so as a statement about systems it is inferred. The offset b cancels
   exactly because the Gram coefficient 1/(2k) is half the pole: both count k-th powers.
   At k = 6 this is hunt #134's `5/6 + (M - 2 ell)/12`.
2. **Seven constants of the 7/8 assembly carry a 6 that this lane reads as k; the
   sextic large sieve is not one of them.** The pole 1/6, the slot weight q_p^(-5/6),
   the Gram term P_a^(1/6) with its two consequences b/12 and 11b/6, the amplification
   slope 5/6 and the 6 in the plain capacity 6 kappa (section 1). Their values are cited;
   that each 6 is the row-character order is inferred. The large-sieve exponent
   (KD)^(2/3) is the same for every order n >= 3 (Blomer, Goldmakher and Louvel,
   Theorem 1.3, read here from the arXiv copy; the paper follows their Section 3
   recursion, line 4728) and enters the 7/8 only through the 11/12 bootstrap, which does
   not bind.
3. **Walls per k (derived, exact LPs with dual multipliers valid for every k >= 2):**
   balanced probe `1 - 1/(2k)`, per-summand corner `1 - 3/(4k)`, and the perfect-row-count
   floor, which depends on the floor bin. The paper's floor bin is a = 51/100,
   delta_0 = 1/50 (line 15843), the left edge of the held Euler region x_r >= 51/100
   that carries the nonprincipal contours (lines 4054 and 4069; that the region fixes the
   bin is inferred); there the floor is `1 - 25/(32k)`. Hunt #134 took the limit
   delta_0 -> 0 ("as the floor approaches 1/2"), which also needs that region extended;
   there it is `1 - 4/(5k)`. At k = 6: 11/12, 7/8, and
   167/192 at the paper's bin, 13/15 in the limit. So the 13/15 ceiling needs a floor
   bin nearer 1/2 as well as perfect row counts.
4. **With the paper's row counts carried over, every endpoint optimum is measured and
   bracketed exactly on both sides** (section 4): an exact single-point lower bound, and
   an exact upper bound from a point that meets every constraint of the template, the
   endpoint by Bernstein subdivision in exact arithmetic. At k = 6 with the plain
   capacity tied to the target the template returns 0.8749570194, the optimum Liu states
   for this comparison system in an unrefereed arXiv preprint (2610.12234v2,
   0.874957019420098946, cached source line 131) to 1e-12, together with his binding
   point xi in (0.38858, 0.38859) and his ell and b. With the capacity held at 4/9 it
   returns Liu's earlier closed form (1507 - 2 sqrt 921)/1653 (2610.12234v1, cached
   source line 104) to 1e-12. The template's count R_* = 2/3 at x = 1/2 is also Liu's
   printed count equation, identically in kappa (v2 source line 298). These check the
   k = 6 transcription where it binds, the endpoint at x = 1/2 near delta = 0.3886 and the
   tie. The floor rows, the Gram cap, the losslessness and the slot supply are slack
   there, and nothing in the k != 6 structure is exercised.
5. **Levers at k = 6, compared like for like** (variant A at the paper's floor bin,
   measured). One step of the row order, 6 to 5, is worth 0.0255. Each other lever pushed
   as far as the template allows: removing the Gram exceptional term outright 0.0110,
   removing the row-count excess outright (alpha -> 0) 0.0052, the plain capacity at its
   best (c near 1.144, a local best on a grid of step 0.001, where the slot supply binds)
   0.0011. Single steps are smaller:
   alpha from 5/6 to 3/4 buys 0.0004 and to 1/2 buys 0.0027, c from 4/9 to 1 buys 0.0008.
   Part of the pole's lead is built into the template: at b = 0 the variant-A endpoint,
   floor and Gram constraints do not involve k, so `1 - sigma_0 = (1 - (M - 2 ell)/2)/k`
   at a k-free optimum geometry (derived). A step in k rescales the whole distance to 1,
   which no single row-count input can do.
6. **Every k <= 5 puts the corner, both floors and the endpoint below 13/15, 0.8748867
   and 0.8748087; k = 8 and 12 are worse than 7/8 at every wall.** The balanced probe is
   below 0.8748867 only for k <= 3 and equals 7/8 at k = 4.
7. **No system known to the literature realises k <= 5** (section 6, inferred from cited
   lines plus a literature check). The paper twists by prod_p chi_p^(j_p), with j_p
   chosen for each prime (lines 1700 and 1703); in Part II the twist is the row
   character, whose exponent at p is the valuation j_p of the row u (line 8969). This
   lane reads a system as one exponent j at every prime, which is an inference, not a
   case the paper treats. On that reading, inside the cubic-theta family the twist is
   pinned at the sextic one by the Gauss pairing that cancels the theta's angular
   factor; the cubic twist (pole 1/3) leaves that factor and lands on Groessencharacter
   L-functions; the classical theta (k = 4 over Q(i)) has no squarefree coefficients;
   the biquadratic and quintic thetas have coefficients the literature does not
   determine. Liu's extension to fields containing mu_12 keeps zeta_F^S(6z): a bigger
   field has not moved the pole.
8. **The tied variant has no fixed point at k = 2 and k = 3, and that is a property of
   the equality, not of the template** (section 4). Lemma plain needs only
   beta_* <= (1 + kappa)/2 (line 12565) and nothing at kappa = 1, so a relaxed tie has
   admissible points: 0.6093750 at k = 2 (the floor wall 39/64) and 0.7435200 at k = 3
   with kappa inside the lemma's stated range, both at the paper's floor bin (measured,
   bracketed exactly).

## 1. Where each constant comes from

Origins: *sextic* (a 6 this lane reads as k = 6), *cubic-theta* (set by the cubic theta,
its pairing with the sextic twist, or the Euler regions of its local identity),
*generic* (form independent of k), *choice*. The table is rendered from
`probe_table.PROVENANCE` (the tests compare every row), and every line it names is
checked.

| constant | value at k = 6 | enters | lines | origin | order-k template | grade |
|---|---|---|---|---|---|---|
| pole | 1/6 | h/6 in C(s) | 3758, 4045, 4071, 5588, 8641 | sextic | 1/k | cited value; k-reading inferred |
| slot weight | q_p^(-5/6) | +ell/6 in C(s) | 15563, 15576, 5589 | sextic | q_p^(1/k-1) | cited value; k-reading inferred |
| Gram exceptional | P_a^(1/6) | additive Gram bound | 8353, 8535, 8541 | sextic | P_a^(1/k) | cited value; k-reading inferred |
| Gram in the low bound | b/12 | l_x/2 + b/12 | 8570, 8619 | sextic | b/(2k) | cited value; template derived on the inferred k-reading |
| Gram cap | 11b/6 | l_y - d >= 11b/6 | 8530, 8597 | sextic | (2 - 1/k) b | cited value; template derived on the inferred k-reading |
| amplification | alpha = 5/6 | L(t), R_* | 12369, 12383, 15101 | sextic | 1 - 1/k | cited value; k-reading inferred |
| plain capacity | 6 kappa | z_P, c = 4/9 | 12561, 12594, 12596, 14378, 15175 | sextic | k kappa | inferred |
| Euler regions | 51/100, 17/50, 33/200, 19/20, 7/8 | local identity | 3866, 4054, 4056 | cubic-theta | held; region two misses z = 1/k for k >= 7, and its x_r >= 7/8 misses every target below 7/8 | cited regions; fit derived |
| floor bin | delta_0 = 1/50 (a = 51/100) | floor rows | 15843, 4054, 4069, 15742 | cubic-theta | held; the limit 0 reported beside it | cited bin; inferred that region one fixes it |
| Gauss pairing | gamma_1 gamma_2 = -alpha(p) chi_p(4)^- gamma_3 | scalar Euler identity | 3819, 3967, 4118, 4124 | cubic-theta | none known | inferred |
| reflected energy | Z^(M') | row norm | 1790, 2648, 3159, 8116 | cubic-theta | held | cited |
| row-norm loss | (1 + 3 ell' - 2M')/4 | corner M - 2 ell >= 1/2 | 8306 | cubic-theta | held | cited |
| dual length | M + ell <= 1 | reflection | 8246 | generic | held | derived subtraction; sufficiency inferred (hunt #134) |
| Poisson normalisation | X^(1/2), Z^(x+z-1) | weight | 3752, 3825 | generic | held, cancels | derived |
| rescaling | q_p^(-3/2), f(d) = -d | compensated probe | 6898, 8631 | generic | held | cited |
| additive sieve | (Q + delta^-2) | additive norm | 3509 | generic | held | cited |
| large sieve | (KD)^(2/3) | Part I count R(delta) | 4717, 4728, 5196 | generic | held | cited; every n >= 3 by BGL Theorem 1.3 |
| inverse capacity | (1 - r)/2 | Lemma marked | 15182 | generic | held | inferred |
| detector windows | t in [1, 3/2], x in [0, 1/2] | row counts | 15206, 15964 | generic | held | cited |
| numerator | U^(delta/2) | high exponent | 15801 | generic | held | cited |
| contour | Re z = 17/50 | nonprincipal rows | 15742, 15729, 15849 | choice | held for k >= 3; k = 2 needs 1/2 < Re z < 3/4 | derived |
| geometry | ell = 1/6, M = 5/6, b = 1/8 | Part II | 6860 | choice | free | cited |
| Mellin positivity | M(1/6) > 0 | scalar c_S | 3781, 3784 | generic | M(1/k) > 0, k >= 2 | cited (the proof covers 0 < sigma < 1) |

Readings behind the table:

- **The pole and the slot weight are one constant.** The principal residue sits at
  w = 1, z = 1/6 (line 4071); the weight X^(1/2-z) Z^(x+z-1) (line 3825) there gives
  X^(1/3) Z^(s-5/6), and each slot prime is summed with q_p^(-5/6) = q_p^(z-1) (line
  15563), adding Z^(ell/6) after the normaliser A_T (line 15576). Together:
  `C(s) = s + l_x/2 - 1 + h z_*` with h = 1 - l_x + ell, the paper's line 5588 at
  z_* = 1/6 (derived for every z_*, sympy).
- **The Gram exponent is half the pole for the same reason.** The exceptional
  frequencies of the Gram bound are sixth powers times a bounded part (line 8535),
  counted as K^(1/6) (line 8541); Cauchy-Schwarz halves it to P_a^(1/12) (line 8619).
  Since P_a = Z^b, the low exponent is `l_x/2 + b z_*/2`, and b cancels from the target.
  Without that equality b would have a price of its own (section 5).
- **The bootstrap ceiling equals the amplification slope for every k.** The Part I
  analogue gives beta_* <= 1 - 1/(2k), so delta <= kappa <= 1 - 1/k = alpha(k) (derived).
  Hunt #134 noted that the paper's alpha = 5/6 equals 2(11/12) - 1 "by coincidence"; in
  the template it is an identity, so the bin ceiling delta <= alpha of line 15107 holds
  automatically.
- **The dual length.** With M' = M - 2d and ell' = ell - d the subtraction of line 8246
  leaves an extra term M + ell - 1 for general parameters (derived, sympy), so
  M + ell <= 1 keeps the paper's bound; that nothing else in the dual-length argument
  depends on the geometry is hunt #134's reading, not checked here.
- **The large sieve.** Line 4717 states the sextic bound with the term (KD)^(2/3), and
  the proof follows the recursion of Blomer, Goldmakher and Louvel (line 4728). Their
  Theorem 1.3 has the same term for n-th order characters, "valid for all n >= 3", over a
  number field containing the n-th roots of unity (section 6, L5). That is why the row
  is generic rather than sextic.
- **Where the held contour and regions stop fitting** (`held_inputs_fit`, derived from
  lines 4045, 4054, 4056 and 15849). The pole 1/k sits in every row, so the nonprincipal
  contour Re z = 17/50 must lie right of it: true exactly for k >= 3. For k = 2 it must
  move into 1/2 < Re z < 3/4, where the frequency slope R + delta/2 - Re z of every row
  priced here (R >= 1 - delta) stays positive for delta <= 1/2; E(h) does not involve
  the contour, so the k = 2 prices survive the move, but the intermediate rows that pin
  the contour near 17/50 in hunt #134's reading are not re-priced. The principal residue
  z = 1/k lies in region two (z_r >= 33/200) exactly for k <= 6, so every k >= 7 (k = 8
  and 12 in the tables here) needs that region re-derived. Region two also asks
  x_r >= 7/8, so every target below 7/8 needs it extended; Liu v1 states that extension
  for the sextic system ("Their Euler correction is shown to be holomorphic below 7/8",
  cached source lines 244 and 245), and for k != 6 it is part of L3.

## 2. The template and its formulas (derived)

For an order-k system, with l_x = (M - b)/2, l_y = (M + b)/2, h = 1 - l_x + ell,
z_* = 1/k and a = (1 + delta)/2:

- signal `C(s) = s + l_x/2 - 1 + h/k`; low exponent `l_x/2 + b/(2k) + f(d)`, f(d) = -d;
- target `sigma_0 = 1 - h/k + b/(2k) = 1 - 1/k + (M - 2 ell)/(2k)`;
- high exponent (line 15729 with sigma_0 and z_* free)
  `E(d) = a - sigma_0 + h(17/50 - z_*) - a l_y - ell/2 + q ell + d(R + delta/2 - 17/50)`;
- floor rows `C_0(k) = 1/2 + ell/2 - 3M/4 + b(1/4 - 1/(2k))`, so the floor condition
  is `C_0 + (1 + ell - M/2) delta_0 <= 0`;
- endpoint `-E_* = -C_0(k) + delta(ell + b)/2 - ell x delta - (h/2) K`, with
  `K = (alpha - delta)_+ delta P_x / J`, `J = (alpha - delta) D_x + delta P_x`,
  `D_x = 3 - (1 + 2c) x`, `P_x = (2 - 2cx)(1 - x)`, and c the plain-capacity coefficient
  (4/9 in the paper). The endpoint covers delta_0 < delta <= 1 - 1/k, x in [0, 1/2]
  (line 15949 at the paper's bin).

`test_closed_forms_symbolically_for_every_k` re-derives all of these in sympy with k,
ell, M, b, delta, x, alpha, c and the contour as symbols, and checks that the balancing
t of line 15964 makes R_short = L = R_*; `test_two_routes_agree_exactly...` checks the
transcribed and closed forms against each other on random rational points for k = 2 to
12. Two structural facts fall out: the contour cancels at d = h, and the pole enters
E(h) only through the b-coefficient of C_0, because the signal and the row bound move
together under a change of pole. The constant-target slope `1 + delta(1/2 - x)` is free
of k, so M + ell = 1 is optimal for every system, as hunt #134 found for k = 6.

## 3. Walls per system order (derived)

| k | balanced probe 1 - 1/(2k) | per-summand corner 1 - 3/(4k) | floor, paper's bin 1 - 25/(32k) | floor, limit 1 - 4/(5k) |
|---|---|---|---|---|
| 2 | 3/4 | 5/8 | 39/64 | 3/5 |
| 3 | 5/6 | 3/4 | 71/96 | 11/15 |
| 4 | 7/8 | 13/16 | 103/128 | 4/5 |
| 5 | 9/10 | 17/20 | 27/32 | 21/25 |
| 6 | 11/12 | 7/8 | 167/192 | 13/15 |
| 8 | 15/16 | 29/32 | 231/256 | 9/10 |
| 12 | 23/24 | 15/16 | 359/384 | 14/15 |

The floor walls are exact LPs over (ell, M, b) with the dual-length, Gram-cap, d = 0
losslessness (inferred, as in hunt #134) and floor constraints. For every floor bin
0 <= delta_0 <= 1/2 the minimum of M - 2 ell is `m = (2 + 12 delta_0)/(5 + 6 delta_0)`,
so the wall is `1 - 1/k + m/(2k)`, attained at b = 0 and ell = (1/4 - delta_0/2)/(5/4 +
3 delta_0/2), and proved optimal by the dual identity

`M - 2 ell - m = y1 (-(C_0 + (1 + ell - M/2) delta_0)) + y2 (1 - M - ell) + y3 b`,

with `y1 = 12/(5 + 6 delta_0)`, `y2 = 4/(5 + 6 delta_0)` and `y3 = y1 (1/4 - 1/(2k))`,
nonnegative exactly when k >= 2 (checked in sympy, symbolic in k and delta_0, and exactly
for k = 2 to 39). At the paper's bin m = 7/16 at ell = 3/16, M = 13/16 (multipliers 75/32
and 25/32); in the limit m = 2/5 at ell = 1/5, M = 4/5 (multipliers 12/5 and 4/5). At
delta_0 = 1/2 the vertex is ell = 0, M = 1 and the floor wall is the balanced probe
1 - 1/(2k). Above 1/2 the floor rows cannot be met at all: they are smallest at ell = 0,
M = 1, b = 0, where they read -1/4 + delta_0/2 <= 0 (derived; the LP is infeasible at
delta_0 = 51/100). Under the stricter per-summand reading the floor wall coincides with
the corner for both bins.

Read against the mission's thresholds: the corner and both floors are below 13/15 and
0.8748867 for every k <= 5; at k = 6 both floors (167/192 and 13/15) are below 0.8748867;
the balanced probe is below 0.8748867 only for k <= 3 and equals 7/8 at k = 4. This hunt's
follow-ups lane (`FOLLOWUPS.md`) reports a newer record of 0.8748087 for Dirichlet
L-functions; every k <= 5 corner, floor and endpoint value here is below that too. That
page measures the room left for row counts at k = 6 against 13/15 (0.0081420); with the
floor bin held at 51/100 the same room is 0.0050170, the distance from 0.8748087 to
167/192 (derived here, a thread for that lane).

## 4. The endpoint wall per k, with the paper's row counts carried over

Variants of the row counts: **A** moves only the pole and the Gram terms (alpha = 5/6,
c = 4/9 held); **B** also moves the amplification slope to alpha = 1 - 1/k; **C** also
ties the plain capacity to the target, c = 2/(k kappa_0) with kappa_0 = 2 sigma_0 - 1
(the inferred reading of 6 kappa), the limit of Liu's iteration ("Iteration reaches the
limiting equality", v2 source lines 310 and 311). Constraints: M + ell = 1 (optimal),
b >= 0, the Gram cap, the d = 0 losslessness ell <= 1/5, the floor rows, the endpoint on
its whole range and the slot supply ell/h above the largest requested capacity (7/37 at
c = 4/9, line 16116). Measured values are float optimisations (affine in ell at fixed
(delta, x, b); concave in b). Every valid row is also bracketed exactly:
`best_exact_bound` gives a single-point relaxation, a lower bound, and
`exact_upper_bound` steps back from the measured point until `point_is_feasible` passes
every constraint in exact arithmetic (the endpoint by Bernstein subdivision of J (-E_*),
a polynomial of degree 2 in delta and 3 in x). Each bracket holds the measured value and
is narrower than 2e-8 (`test_endpoint_optimum_and_exact_bracket`, 38 rows: every valid
row at both floor bins, the unchanged k >= 5 limit rows included).

| k | A, paper's bin | B, paper's bin | C, paper's bin | A, B, C in the limit delta_0 -> 0 |
|---|---|---|---|---|
| 2 | 0.6093750 = 39/64 (the floor binds) | 0.6093750 = 39/64 (the floor binds) | no fixed point of the tie (c >= 2) | 0.6060442, 0.6038808, no fixed point |
| 3 | 0.7449310 | 0.7441280 | no fixed point of the tie (slot supply) | 0.7442838, 0.7434565, no fixed point |
| 4 | 0.8106425 | 0.8102393 | 0.8096920 | 0.8105686, 0.8102025, 0.8096034 |
| 5 | 0.8494278 | 0.8492734 | 0.8491144 | unchanged |
| 6 | 0.8749571 | 0.8749571 | 0.8749570 | unchanged |
| 8 | 0.9065214 | 0.9067045 | 0.9068015 | unchanged |
| 12 | 0.9378033 | 0.9381005 | 0.9382153 | unchanged |

- **k = 6 reproduces Liu's optimum of this comparison system** (an unrefereed arXiv
  preprint; it is not the current record, which this hunt has at 0.8748867 and 0.8748087
  from other inputs). Variant C at k = 6 gives 0.8749570194, matching Liu v2's
  0.874957019420098946 to 1e-12, with binding delta in Liu's interval
  (0.38858, 0.38859) and his ell and b (v2 source lines 302 to 304) to 1e-6
  (`test_k6_tied_variant_matches_liu...`). Variant A gives 0.8749571, Liu v1's closed form
  (1507 - 2 sqrt 921)/1653 to 1e-12 (his v1 fixes kappa = 3/4, source line 2485, which
  is the held c = 4/9), with exact bracket
  `4995360671043583/5709263753593183 <= sigma_0 <= 0.8749570699`, above hunt #134's
  exact bounds 5655673/6464057 and 44117/50422, which `single_point_bound` without the
  floor reproduces exactly at hunt #134's witness points delta = 223/576 (no Gram cap)
  and delta = 7/18 (Gram cap), x = 1/2. Hunt #134 reported a float optimum of 0.874958 in
  its RESULTS.md, from a b-grid of step 0.01; that figure is quoted, not re-run here.
  Liu's count equation (v2 source lines 295 to 298: "For a critical class delta = xi and
  x = 1/2, the count equation R_kappa = 2/3 becomes" a quadratic in xi) is the
  template's R_* = 2/3 at x = 1/2 with c = 1/(3 kappa), identically in kappa (sympy),
  and at the measured binding point the template's R_* is 2/3 to 1e-6. The floor bin
  moves none of the k >= 5 rows.
- **For k <= 6 the endpoint is slack at the corner** (its ell exceeds 1/6), so under the
  per-summand reading the optimum is the corner 1 - 3/(4k) exactly; for k = 8 and 12 the
  endpoint binds below ell = 1/6 and both readings agree. Both hold for both floor bins.
- **The excess over the floor is nearly k-free.** The endpoint's largest ell stays
  between 0.16 and 0.20 in every row of the table, so the target is roughly
  `1 - 1/(2k) - (3/(2k)) ell` with ell near 1/6; removing the row-count excess entirely
  (alpha = 0) returns the floor wall of section 3 to 1e-12 for k = 4, 6, 12 and both bins
  (a consistency check of the float optimiser against the exact LP).
- **The tied variant has no fixed point at k = 2 and k = 3; a relaxed tie has admissible
  points.** At k = 2 the equality asks for c = 1/(2 sigma_0 - 1), which is at least 2 for
  every target the template allows there (sigma_0 <= 3/4), so the plain count stops
  decreasing in m (line 15342 generalised; derived). At k = 3 the capacity it requests
  exceeds the slot supply (measured). Neither is a property of the template. Lemma plain
  at kappa needs only beta_* <= (1 + kappa)/2 (line 12565; Liu v2 keeps it, source line
  284) and no zero-free hypothesis at kappa = 1, and a larger kappa only shrinks its
  condition n_1 + n_2 + 6 kappa z <= M (line 12561; derived), so c = 2/(k kappa) is
  admissible for every kappa whose hypothesis is already known. Liu's iteration is of
  this kind, each step using the bound the step before established. Admissible points
  (measured, each bracketed exactly on both sides, narrower than 1e-8, the lower end with
  cutting planes; `test_relaxed_tie_points_and_their_exact_brackets`):

  | k | kappa | c | hypothesis | supplied by | stated range 3/4 <= kappa <= 1 | paper's bin | limit delta_0 -> 0 |
  |---|---|---|---|---|---|---|---|
  | 2 | 1 | 1 | none | kappa = 1 | inside | 0.6093750 = 39/64 (the floor binds) | 0.6033313 |
  | 3 | 3/4 | 8/9 | beta_* <= 7/8 | the order-3 Part I analogue 5/6 | inside | 0.7435200 | 0.7428264 |
  | 3 | 3/5 | 10/9 | beta_* <= 4/5 | the row above | below it, and below Liu's 13/18 | 0.7430799 | 0.7425970 |

  They are points, not optima: a larger c helps until the slot supply binds, which it
  already does at k = 2 with kappa = 3/4 (c = 4/3). Each needs the order-k moments (L6).
- **Which variants need Lemma plain below its stated range** (on the inferred reading
  c = 2/(k kappa)). Variants A and B hold c = 4/9, which is kappa = 9/(2k): 9/4, 3/2 and
  9/8 at k = 2, 3 and 4, above 1 and admissible through kappa = 1, which needs no
  zero-free hypothesis; 9/10 at k = 5, inside the stated range 3/4 <= kappa <= 1 (line
  12532), with hypothesis beta_* <= 19/20 (line 12565), which the order-5 Part I analogue
  9/10 supplies; 3/4 at k = 6, with hypothesis beta_* <= 7/8, which the paper's theorem
  supplies. Liu v1 makes exactly that move for the sextic system ("After the original
  argument establishes beta_* <= 7/8, the unweighted moment permits kappa = 3/4", source
  lines 245 and 246) and warns against substituting kappa = 2 beta_* - 1 "below the
  allowed moment range" (source line 2488). At k = 8 and 12 the held c = 4/9 means
  kappa = 9/16 = 0.5625 and 3/8 = 0.375, below the stated range; those orders are dead
  by price already, and the c of kappa = 3/4 (1/3 and 2/9) only raises their A and B
  values (measured). The tied variant C asks for kappa_0 = 2 sigma_0 - 1 below 3/4:
  0.7499 at k = 6, inside Liu v2's extension to 13/18 <= kappa <= 1 (v2 source line 282),
  and 0.6982 at k = 5 and 0.6194 at k = 4, below it. For k != 6 every variant still needs
  the order-k moments (L6).

## 5. Price of each structural constant at k = 6 (measured)

| change, everything else as variant A at k = 6 | paper's floor bin | limit delta_0 -> 0 |
|---|---|---|
| none | 0.8749571 | 0.8749571 |
| pole, slope in 1/k near 1/6 | -0.7618 per unit | -0.7618 per unit |
| row order k = 6 to 5 | 0.8494278 | 0.8494278 |
| Gram exponent 1/12 to 1/18 (cap moved with it) | 0.8714226 | 0.8710590 |
| Gram exponent to 1/24 | 0.8696095 | 0.8690251 |
| Gram exponent to 0 (slot supply binds at 7/37) | 0.8639502 | 0.8633974 |
| alpha 5/6 to 3/4 | 0.8745098 | 0.8745098 |
| alpha to 1/2 | 0.8722267 | 0.8722267 |
| alpha to 0 (no row-count excess) | 167/192 = 0.8697917 | 13/15 = 0.8666667 |
| plain capacity c 4/9 to 1 | 0.8741768 | 0.8741768 |
| c near 1.144 (a local best on a grid of step 0.001; the slot supply binds) | 0.8738710 | 0.8738710 |

Like-for-like gains at the paper's bin: the step in k 0.0255; the Gram term removed
0.0110; the row-count excess removed 0.0052; c at its best 0.0011 (in the limit the second
and third are 0.0116 and 0.0083). Exact shadow prices at the paper's own geometry
(derived): d sigma_0 / d z_* = -(h - b/2) = -3/4 with the Gram term tied to the pole,
-h = -13/16 with it held; d sigma_0 / d g = b, so removing the Gram term outright at
fixed geometry would be worth 1/96 there. With the Gram exponent at 0 the
perfect-row-count wall drops to 1601/1854 at the paper's bin and to 31/36 in the limit
(exact LPs). These are prices of inputs, not candidates: the Gram exponent's exceptional
term is dominated by C of bounded norm (its sum over C_0 converges like C_0^(-1/6), line
8551), where the frequencies k are sixth powers and the residual character is principal,
so the complete sums are full lattice counts with no cancellation to find (inferred). A
smaller Gram exponent needs a different additive factor, which is a different probe.

## 6. Systems, the lemmas they would need, and what kills them

The pole is the order of the row character, and in the paper that character is the twist
of the completed cubic-theta sum. The paper twists by Psi(n) = Psi_0(n) prod_p
chi_p(n)^(j_p), with an exponent j_p in {0, ..., 5} chosen for each prime (lines 1700
and 1703); in Part II the twist is the row character chi_n(u), whose exponent at p is
the valuation j_p of the row u (line 8969, where reciprocity writes chi_n(u) through
prod chi_p(n)^(j_p)). This lane reads a candidate system as one exponent j at every
prime, a twist chi^j; that reading is an inference, not a case the paper treats. On it,
two cited facts constrain j: the reflection's local column factor at p is
chi_p^(-(j_p+2)) (line 1790; principal Ramanujan factors at j_p = 4, line 1791), and the
scalar Euler identity needs the theta coefficient gamma_2(c) alpha-bar(cn^3) (line 3819)
times the Poisson Gauss sum of the twist to be an explicit phase. At j = 1 the pairing
`gamma_1 gamma_2 = -alpha(p) chi_p(4)^- gamma_3` (line 4118) supplies alpha(p), which
cancels the angular factor, and the dual chi^(-3) is quadratic, which the quadratic large
sieve (line 2648) handles without loss. That is why the paper's k is 6 (inferred from
these lines).

| system | field | theta | k | walls (Part I / corner / floor at the paper's bin) | missing lemma | known? | status, kill |
|---|---|---|---|---|---|---|---|
| S0 paper | Q(sqrt(-3)) | cubic, sextic twist j = 1 | 6 | 11/12 / 7/8 / 167/192 | none new | OpenAI's lemmas, unreviewed | the public follow-ups on record work in this system (inferred from their stated inputs) |
| S1 cubic twist | Q(sqrt(-3)) | cubic, j = 4 | 3 | 5/6 / 3/4 / 71/96 | a pairing that cancels alpha-bar(c) | no | killed on an inferred reading, for Dirichlet L-functions: gamma_2 gamma_4 = 1 (line 4124) leaves alpha-bar(c), so the denominator is L(s, eta alpha-bar), a Groessencharacter family with no transfer |
| S2 quadratic twist | Q(sqrt(-3)) | cubic, j = 3 | 2 | 3/4 / 5/8 / 39/64 | explicit gamma_2 gamma_3 | no | killed on an inferred reading: no explicit product, so no scalar Euler identity; the contour would also have to move (section 1) |
| S3 classical theta | Q(i) | degree 2, quartic twist | 4 | 7/8 / 13/16 / 103/128 | squarefree coefficients | no (classical) | killed on an inferred reading: theta(z) = sum e(n^2 z) vanishes off squares, so no Moebius c-sum and no 1/L in the principal row |
| S4 biquadratic theta | Q(i) | degree 4, quartic twist | 4 | 7/8 / 13/16 / 103/128 | L1 to L6 below | L5 yes; L1 no | open but unsupported: coefficients at squarefree indices not determined |
| S5 quintic theta | Q(zeta_5) | degree 5 | 5 | 9/10 / 17/20 / 27/32 | as S4, over a quartic field | L5 yes; L1 no | open but unsupported |
| S6 cubic theta, F with mu_12 | Q(zeta_12), K(zeta_12) | cubic exceptional theta, sextic | 6 | as S0 | none new | Liu 2610.26835 runs it | the pole stays at 1/6 (its source line 756 keeps zeta_F^S(6z)); his B-flat is stated as 0.874886647 (source line 122), not reproduced here |
| S7 higher twists of the cubic theta | F with mu_9 or mu_12 | cubic, order 9 or 12 | 9, 12 | worse | none | | dead by price: pole 1/k < 1/6 |
| S8 biquadratic, octic twist | Q(zeta_8) | degree 4 | 8 | 15/16 / 29/32 / 231/256 | as S4 | | dead by price |

The lemmas an S4- or S5-type system would need, beyond the walls it is priced at:

- **L1 coefficients and pairing.** Fourier coefficients of the degree-n theta at
  squarefree indices, in closed form, with a Gauss-sum identity making (coefficient) x
  (Gauss sum of the twist) an explicit phase that cancels the theta's angular factor.
  *Literature* (cited from the arXiv HTML of David, Dunn, Hamieh and Lin, 2306.11875v5,
  fetched on 2026-10-21 into scratch and read here, not in the campaign cache; quoted,
  with the quotes normalised to ASCII): for the cubic theta "all
  the Fourier-Whittaker coefficients were computed in closed form by Patterson [Pat77]",
  while the quartic ones "are in general not all determined!" (section 1.2); after Hecke
  theory and periodicity there remain
  "n/2-1 (respectively (n-1)/2-1) undetermined coefficients" for even (odd) n (section
  1.2); "Deligne [Del80] ... explained that the inaccessibility of the cases n>=4 on GL_2
  was owed to the fact that local representations do not have unique Whittaker models",
  and "Kazhdan and Patterson [KP84] generalised Deligne's work and showed the periodicity
  property held in greater generality" (section 4.5); Suzuki's closed form covers the
  quartic coefficients at squares m^2 of squarefree m (Remark 4.6). For n = 6 Broker and
  Hoffstein (arXiv 1312.0568, abstract read here) give "partially proven, partially
  conjectured values". Not known for any n >= 4.
- **L2 twisted reflection.** The analogue of Proposition completed-reflection with
  explicit dual local factors, whose dual character for the chosen twist is quadratic,
  so that the reflected energy is Z^(M') by the quadratic sieve. Not known; depends on L1.
- **L3 scalar Euler identity.** The analogue of Lemma local-euler with
  zeta_F(kz) L(w, chi(u))/L(x, eta chi-bar(u)) and Euler regions containing z = 1/k, the
  contours and the target (section 1). Depends on L1.
- **L4 Gram bound of order k.** The proof pattern of Proposition probe-gram with k-th
  power exceptional frequencies; routine given the correlation lemma for the new Gauss
  sums (inferred).
- **L5 large sieve of order k.** Known for every n >= 3 over a number field containing
  the n-th roots of unity: Blomer, Goldmakher and Louvel, arXiv 1112.1650, Theorem 1.3,
  read here from the arXiv PDF (fetched on 2026-10-21 into scratch, sha256 `1ab29e36...`,
  not in the campaign cache; text extracted locally from the decompressed file, the
  relation signs read through the PDF's font encoding; quoted with ASCII signs): "The
  following theorem, which is valid for all n >= 3", with the bound
  (MN)^eps (M + N + (MN)^(2/3)) over squarefree ideals coprime to S. For quartic
  characters BGL also cite Gao and Zhao (their [GZ]; arXiv 1101.3646, not read here).
- **L6 the Part II moments.** Analogues of Lemma marked and Lemma plain for order-k rows.
  Under variant C they would also have to reach kappa_0 below 3/4 (section 4): 0.6982 at
  k = 5, below the 13/18 to which Liu extends the sextic lemma (2610.12234v2 source line
  282; the cyclotomic version, 2610.26835v1 source line 148). Not known; these are the
  bulk of the paper.

**What would kill each candidate.** S1 and S2: confirming that no twist of the cubic
theta other than j = 1 cancels the angular factor (a local Gauss-sum computation in the
style of lines 4101 to 4126, not done here). S3: nothing left to kill. S4 and S5: an L1
that exists but fails the pairing, or a reflection whose dual character for the twist is
principal (as at j = 4 for the cubic theta) or of order above 2 (the energy would then
pay the (KD)^(2/3) term), or any of these systems running into the Davenport-Heilbronn
rival at the step that uses the Euler product (hunt #120). S6 and S7: none needed.

## 7. Controls

- **Reproduction at k = 6** (`test_template_reproduces_the_paper_at_k6`): 14 values
  rebuilt from the general-k formulas. Twelve are printed in the paper, and
  `test_reproduction_sources_are_honest` finds each printed fragment on its stated line:
  11/16, 3/16, 7/8, 2/3, 1/4, 11/12 (line 509), h = 13/16, C_0 = -1/48, the floor
  -7/1200, the large-delta formula -1/48 - delta/16, the supply 8/39 and the inverse
  capacity 7/37. Two are values hunt #134 derived and the paper does not print, and the
  same test finds them absent from `paper.tex`: the worst point 7/30672 at
  delta = 79/204, and 13/15. The paper's completed-square identity holds on 105 points.
- **Outside values:** Liu's two optima and closed forms, (1507 - 2 sqrt 921)/1653 with
  kappa fixed and B_new with kappa tied, reproduced by variants A and C at k = 6; Liu v2's
  printed count equation, identical to the template's; hunt #134's exact bounds
  5655673/6464057 and 44117/50422, reproduced exactly at its witness points
  (`test_hunt_134_exact_bounds_at_their_witness_points`).
- **Two routes:** transcribed and closed forms agree exactly on random rational points
  for k = 2 to 12; the polynomial J (-E_*) used by the upper bounds agrees exactly with
  the closed form; the float optimiser re-implements the endpoint in floats while both
  bracket ends go through the fraction functions, and every measured value lies in its
  bracket; the float optimiser meets the exact floor LP when the row-count excess is
  removed; the slot supply has a closed form and a grid route that agree; and
  `point_is_feasible` agrees, constraint by constraint, with an independent route (the
  floor through the transcribed E(h), the slot supply through an exact capacity grid,
  the large-delta corners through the closed form) on 400 random rational points on
  which every constraint is both met and missed.
- **Defects of the first pass, fixed in the first revision.** The float slot-supply test
  passed points whose requested capacity was at least 2/3, which no ell can supply; no
  table row reached it, and `test_slot_supply_beyond_two_thirds_is_infeasible` pins the
  fix. In the limit convention the first pass scanned the endpoint only from
  delta = 1/50, leaving 0 < delta < 1/50 unchecked; the scan now starts at the floor bin,
  and every value of the first pass's table comes back as the limit column
  (`MEASURED_LIMIT`). Starting at 0 needed a guard for J = 0 at delta = alpha = 0, which
  the alpha = 0 control exercises.
- **Defects of the first revision, fixed in this one.** The k = 2 and 3 cells of variant
  C said "outside the derivation", which holds only for the equality tie (section 4).
  Fractions and line numbers on this page were not tied to the computation: the
  verifier's four typos passed every test. The floor and slot-supply parts of the exact
  checker were never fault-tested. "Region two misses z = 1/k for k >= 8" is true from
  k = 7. The floor-wall formula was stated for every delta_0 >= 0 and holds for
  0 <= delta_0 <= 1/2. The summary called Liu's optimum a check of the whole
  transcription. Variants A and B at k = 8 and 12 were missing from the Lemma plain
  bullet. BGL's theorem had not been read, and hunt #134's exact bounds were not
  reproduced.
- **Planted faults** (`test_planted_faults_turn_the_reproductions_red` and the tests
  after it): dropping the Cauchy-Schwarz half of the Gram term, moving the pole to
  1/(k+1), shifting the signal by 1/1000, adding 1/100 to P_x, or moving the floor bin to
  1/100 each turns at least one reproduction red; dropping K from the upper-bound
  polynomial makes it accept a point that the true check rejects; source mutants of
  `probe_table.py` that make the floor, slot-supply or plain-count check vacuous, or
  loosen or alter the Gram-cap, loss or large-delta corner check, each disagree with the
  independent route (`test_point_is_feasible_mutants_are_caught`); edits of this page are
  flagged by
  `prose_problems` (`test_prose_faults_are_caught`), among them the verifier's four typos
  (a fraction of section 5, a cell of the walls table, the S1 wall and a line number of
  section 6), a line of the section 1 table, a swap of two fractions that are both
  pinned, a relaxed-tie value and the earlier decimal edits. By hand, a scratch copy
  of `probe_table.py` with the Gram coefficient set to 1/k printed four FAIL lines (low
  exponent 19/96, target 85/96, C_0 = -1/32, worst point 653/61344).
- **The page pinned to the computation** (`test_probe_md_numbers_are_the_pinned_ones`):
  every decimal must sit in a phrase that the tests compute or quote; every fraction must
  be a computed, cited or quoted value; every line reference must name a line that a
  citation check reads (paper or outside source); and the tables of sections 1, 3, 4 and
  5 and the walls of section 6 are rendered from the computation. It cannot catch a swap
  of two allowed fractions outside the rendered tables and phrases, or an integer that
  no phrase carries.
- **Lexical rules:** a test reads the bytes of this lane's three files (ASCII only, no
  reserved word, no em dash).

## 8. Limitations

- The template holds the cubic-theta estimates (reflected energy, row-norm loss, Euler
  regions, floor bin) at their k = 6 form for every k. That is a pricing assumption, not
  a claim that any other system satisfies them; section 1 says where the held contour
  and regions stop fitting, and section 6 why no system is known to satisfy them.
- The mapping of the plain capacity 6 kappa to k kappa is inferred from lines 12594 to
  12599 and 14378 (exceptional rows counted as sixth powers); variants A and B use it
  only in the Lemma plain bullet of section 4.
- The reasons the paper's twist is j = 1 (section 6) are readings of cited lines, on the
  uniform-exponent reading of the twist; the local computation that would confirm them
  for j = 2 to 5 was not done.
- The exact brackets are statements about the transcribed template, not about the
  paper's lemmas: they show where its formulas put the optimum, nothing more. The
  relaxed-tie rows are admissible points; the relaxed optimum, where the slot supply
  binds, was not computed.
- Prior art: searched only for the lemmas in section 6 (BGL, Gao and Zhao, DDHL,
  Broker and Hoffstein) and the public follow-ups cached by the campaign. The order-k
  pricing itself was not searched for; nothing here is said to be new.

## Open issues

- The local Gauss-sum computation for the twists j = 2 to 5 (lines 4101 to 4126 style),
  which would confirm or kill S1 and S2, was not done.
- The k-reading of the sextic constants, the 6 kappa to k kappa mapping and the
  uniform-exponent reading of the twist are inferred, and every statement about a system
  other than S0 inherits that grade.
- The Euler regions were not re-derived for k != 6; the template holds them.
- Liu's B-flat 0.874886647 and the record 0.8748087 that `FOLLOWUPS.md` reports are
  quoted, not reproduced.
- The sharpness of the Gram exceptional term is inferred, not proved.
- The relaxed-tie optimum at k = 2 and 3 was not computed.
- The page checks leave the blind spots named in section 7.

## The doors

Candidate status: within the order-k template, with the paper's row counts carried over,
the endpoint optimum is the table of section 4 (measured, bracketed exactly on both
sides); parameter range ell, M, b >= 0 with M + ell <= 1 and the Gram cap; proof status:
exact arithmetic on transcribed formulas, unreviewed; information class below.

### Active constraints at the k = 6 optimum (ranked)

1. **The endpoint inequality at delta = 0.3886, x = 1/2** (binding, with the offset b =
   0.1234 interior where -E_* is flat in b). Its pole price is -0.7618 per unit of 1/k;
   its row-count prices are alpha (0.0004 from 5/6 to 3/4, 0.0052 to 0) and c (0.0008 from
   4/9 to 1, 0.0011 at its best).
2. **The slot supply** ell/h = 0.2055 against 7/37: slack here, binding once the Gram
   exponent is lowered or c reaches 1.144 (section 5).
3. **The Gram cap** b <= 3(1 - 3 ell)/8 = 0.1873 against b = 0.1234: slack.
4. **The floor rows** C_0 = -0.0209, and -0.0059 with the paper's bin: slack; they bind
   only at perfect counts (167/192 at the paper's bin, 13/15 in the limit).

### Frozen-constant inventory

| constant | value | trades against | trade shape |
|---|---|---|---|
| row-character order k (pole 1/k) | 6 | the whole theta construction (L1 to L3) | the largest lever (0.0255 for the step to k = 5), partly by construction (summary, item 5); no trade available inside the cubic theta |
| Gram exceptional exponent | 1/6 | b becomes valuable; slot supply then binds | genuine, but the term reads as a true main term |
| amplification slope alpha | 5/6 = 1 - 1/k | row excess K | 0.0004 to 3/4, 0.0027 to 1/2, 0.0052 to 0 |
| plain capacity coefficient c | 4/9 = 2/(6 kappa_0) | row excess K; slot supply | 0.0008 to 1, 0.0011 at its best |
| inverse capacity (1 - r)/2, windows t <= 3/2 | held | row excess K | outside this lane |
| numerator U^(delta/2) | held | high exponent | the input Xu and Sang average; outside this lane |
| floor bin 1/50 | held | the perfect-count wall: 167/192 here, 13/15 in the limit | genuine only once the row counts are near perfect; needs region one below 51/100 |
| contour 17/50 | held | none at the optimum (cancels at d = h) | none for k >= 3 |

### Information class

- **Inside the current data:** re-choosing (ell, M, b) is exhausted (hunt #134 and the
  exact brackets here: the k = 6 template optimum is 0.8749571 with fixed capacity and
  0.8749570194 with the tied one).
- **Inside the family, better inputs:** the row-count lever is worth at most 0.0052 at the
  paper's bin (0.0083 in the limit), single steps of alpha and c 0.0004 to 0.0027; the
  Gram exponent would buy up to 0.0110 but its exceptional term looks sharp; the floor bin
  matters only after the row counts.
- **Reading more:** only a different row-character order moves the targets by a
  structural amount, and it needs a theta-type completed sum that the literature does
  not supply for any order below 6 (section 6). Larger fields (Liu) and larger orders
  move the other way or not at all. Compared with other mechanisms open to this hunt,
  this door is the most valuable per unit of success and the least supported; it should
  not get automatic priority over the row-count lane.

## Run manifest

```runmanifest
id: below_seven_eighths-2026-10-21-probe
hunt: below_seven_eighths
started: 2026-10-21T14:36Z
finished: 2026-10-21T15:28Z
ran:
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper --quick
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_probe_table.py
  - planted-fault run of a scratch copy of probe_table.py with the Gram coefficient 1/k
outcome: priced the order-k template; k = 6 reproduces the paper and Liu; every order below 6 is cheaper in principle and none is available
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```

```runmanifest
id: below_seven_eighths-2026-10-21-probe-repair-r1
hunt: below_seven_eighths
started: 2026-10-21T16:44Z
finished: 2026-10-21T17:41Z
ran:
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - .venv/bin/python -m pytest -q -n0 hunts/below_seven_eighths/test_probe_table.py
  - planted-fault runs of the test file against scratch copies of PROBE.md and probe_table.py
  - curl of the arXiv HTML of 2306.11875v5 and the abstract of 1312.0568 into scratch, read as data
  - .venv/bin/python -m pytest -q -n0 -m "not slow" tests/test_huntspec.py tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py --check
outcome: repaired the probe lane after verification; floor-bin convention made explicit with both walls, two-sided exact brackets added, two float-route defects fixed, grades and citations corrected
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```

```runmanifest
id: below_seven_eighths-2026-10-21-probe-repair-r2
hunt: below_seven_eighths
started: 2026-10-21T22:00Z
finished: 2026-10-21T22:46Z
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m pytest -q -p no:cacheprovider -n0 hunts/below_seven_eighths/test_probe_table.py
  - .venv/bin/python hunts/below_seven_eighths/probe_table.py --paper
  - scratch scripts for the relaxed ties, hunt 134's witness points, Liu's count equation and the cutting-plane brackets
  - WebFetch of the arXiv abstract and PDF of 1112.1650, decompressed with qpdf and its text extracted in scratch, read as data
  - planted-fault runs: page typos, a table line, a fraction swap and source mutants of the exact checker, all inside the test file
  - three scratch copies of the lane, each with one planted fault (a page fraction, a relaxed-tie hypothesis bound, the sign of a large-delta corner term), each run against the full test file
  - .venv/bin/python -m pytest -q -n0 -m "not slow" tests/test_huntspec.py tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py --check
outcome: repaired the probe lane after the second verification; the k = 2 and 3 tie verdicts corrected with relaxed-tie points, the page's fractions, line numbers and tables tied to the computation, the exact checker fault-tested, wording and grades corrected
artifacts:
  - hunts/below_seven_eighths/PROBE.md
  - hunts/below_seven_eighths/probe_table.py
  - hunts/below_seven_eighths/test_probe_table.py
```
