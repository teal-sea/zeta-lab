# probe_tower: probes of growing degree in the 7/8 assembly

**Hunt #150 (`rh_moonshot`), mechanism 6. 2026-10-21. Status: constructed and pushed to a
located obstruction; not challenged yet; unreviewed by any person.** Nothing here is a
result until the case log in `hunts/README.md` says how this hunt ended. Files produced on
branch `hunt/rh-moonshot`: `tower_template.py` (the arithmetic), `test_probe_tower.py`
(the pins), `results_probe_tower.json` (one run of the report), `RUNS.md`, this page.

Grades, as in the hunt's `MISSION.md`: *cited* (a line of a source, quoted and checked
against the pinned file by `verify_citations`, or a primary source read at the stated
place), *derived* (algebra done here, checked in exact rational arithmetic, with `sympy`
for statements symbolic in k; every derivation here is self-reviewed only), *inferred* (a
reading that no computation here checks), *measured* (one floating route, mpmath).
Nothing here is hardened or kernel-checked. A composite claim takes the grade of its
weakest step. The paper is OpenAI, *The Quasi-Riemann Hypothesis*, 2026-09-30,
`github.com/openai/math` at `adc7f124`, read by line number from
`<cache>/openai-math-adc7f124/paper.tex`, SHA-256
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3` (49 cited lines, all
found on their stated lines).

## 0. The answer

1. **The tower goes the wrong way.** In the paper the comparison pole sits at z = 1/6
   because the row characters are sextic: Poisson frequencies are u a^6 (line 3758), the
   sum over a is zeta_F(6z) (line 4045), and its pole at 1/6 is the principal residue
   (line 4071). Replacing the order 6 by k where sixth powers are counted, and holding
   every other estimate at the paper's form, the abscissa is
   **sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k)** (derived; the k-reading is inferred). For
   every admissible geometry it is strictly increasing in k, with
   sigma_0(k + 1) - sigma_0(k) = (2 - (M - 2 ell))/(2k(k + 1)) > 0, and it tends to 1.
   A tower of probes of growing degree drives the abscissa toward 1, not toward 1/2.
2. **No order reaches 1/2, and the best order is the smallest.** The dual-length
   condition alone gives sigma_0(k) >= 1 - 2/k (above 1/2 for k >= 5); with the floor rows
   counted in full, which is what perfect row counts give, sigma_0(k) >= 1 - 4/(5k) in the
   limit delta_0 -> 0 and 1 - 25/(32k) at the paper's floor bin (derived, exact LPs with
   dual multipliers, symbolic in k). The infimum over all orders k >= 2 is **3/5**, at
   k = 2, for which no system exists.
3. **The formal order k = 1 is RH itself.** At k = 1 (no twist: every frequency is
   principal) the balanced geometry gives sigma_0 = 1/2 exactly, and the direct bound it
   asks for is square-root cancellation in the Moebius sum, Littlewood's RH-equivalent
   condition. The template interpolates between that restatement of RH (k = 1) and the
   trivial bound (k -> infinity): the twist buys a provable direct bound and pays for it
   with the density 1/k of k-th powers among the frequencies.
4. **The large-k estimates.** None needs to fail for the tower to fail. Of the two named
   candidates: the large sieve of degree k does not degrade (Blomer, Goldmakher and
   Louvel's Theorem 1.3 has the same M + N + (MN)^(2/3) for every n >= 3, read here from
   the arXiv source); the theta coefficients at squarefree indices are undetermined over
   number fields for n >= 4 and, over F_13[T] at n = 4, exist but are not multiplicative
   (hunt #148, uncommitted). That second failure closes the small-k doors (k = 4, 5), the
   only direction that helps, not the tower.
5. **The step that reads the Euler product is the same at every k**: the principal row
   is linear in the target's coefficients and carries their Moebius-weighted squarefree
   sum (line 3967 supplies mu(c)), which the criterion needs as H/L with
   sup |H - 1| <= 1/2 (line 413). DH fails it at its zero 0.808517 + 85.699348i
   (|H - 1| = 1.0000, measured) and, for every finite deletion set, on every half-plane
   Re s > sigma_0 with sigma_0 < 1 (Saias and Weingartner, cited); Epstein (1,1,6) fails
   it at 0.953260 + 16.290216i (measured); W_a passes it at its own zero
   3/4 + 14.1347i (|H_W - 1| = 0.236 with nothing deleted, measured) and is held off by
   unitarity in the direct bound, which moves its template target up by exactly 1/4.

Disposition: **restricted class obstructed** (section 9), with the mission's tower
premise refuted inside that class.

## 1. Target and its relation to RH

**Target.** A sequence of probes P_k, k = k_1 < k_2 < ..., each verifying the hypotheses of
the paper's continuation criterion (Proposition 2.1, lines 400-432) unconditionally at a
boundary sigma_0(k), for every primitive finite-order Hecke character of its field, with
sigma_0(k) -> 1/2. The Dirichlet transfer (the quadratic transfer proposition, line 6705)
then gives zeta(s) != 0 for Re s > sigma_0(k) for every k, so zeta has no zero with
Re s > 1/2, and the functional equation places every nontrivial zero on Re s = 1/2:
**the target implies RH** (indeed GRH for Dirichlet L-functions). It is not an RH
equivalent with a new estimate attached; the all-k step is the whole content, as the
mission says. The question this mechanism had to answer is whether any natural tower
makes the all-k step plausible.

## 2. The construction: the order-k template

### 2.1 Where the 6 enters (cited) and the reading of it as k (inferred)

| constant | value at k = 6 | lines | order-k form |
|---|---|---|---|
| Poisson frequencies u a^6, u sixth-power-free | a^6 | 3758 | a^k |
| principal pole of zeta_F(6z) | z* = 1/6 | 4045, 4071 | z* = 1/k |
| slot weight q_p^(z* - 1), normaliser Z^(-ell z*) | q_p^(-5/6), Z^(-ell/6) | 15563, 15576 | q_p^(1/k - 1), Z^(-ell/k) |
| Gram exceptional frequencies a_1^6 e, counted K^(1/6) | P_a^(1/6) | 8353, 8535, 8541 | P_a^(1/k) |
| the same after Cauchy-Schwarz, P_a = Z^b | Z^(b/12) | 8570, 8619 | Z^(b/(2k)) |

That each of these sixes is the order k of the row characters is a reading (inferred), the
same one hunt #136's probe lane makes (`PROBE.md` there, uncommitted, read). Everything
else is held at the paper's form: the reflected energy, the dual length M + ell <= 1
(line 8246; that M + ell <= 1 suffices for a general geometry is hunt #134's reading,
inferred), the floor-row exponent (lines 15729-15734, 15843-15847), the contour
Re z = 17/50 (line 15742), the Euler regions (lines 4054-4056).

### 2.2 The formulas (derived)

With l_x = (M - b)/2, l_y = (M + b)/2, h = 1 - l_x + ell (line 5586), and z* = 1/k:

- **Signal.** The weight X^(1/2 - z) Z^(x + z - 1) (line 3825) at z = z*, with X = Z^l_x,
  times the slot product Z^(ell z*), is Z^(x + c) with
  c = l_x(1/2 - z*) + (z* - 1) + ell z* = l_x/2 - 1 + h z*. At k = 6 this is line 5588,
  C(s) = s + l_x/2 - 1 + h/6. Two routes (weight and line 5588) agree identically.
- **Direct bound.** l_x/2 + b z*/2 (line 8570 at k = 6: l_x/2 + b/12).
- **Target.** C(sigma_0) = low exponent gives
  **sigma_0 = 1 - h z* + b z*/2 = 1 - 1/k + (M - 2 ell)/(2k)**. The offset b cancels
  because the Gram term counts k-th powers exactly as the pole does.
- **Floor rows.** Line 15729 with 7/8 replaced by sigma_0(k) and 1/6 by z*, at d = h,
  R = 1, q = delta_0/2, a = (1 + delta_0)/2:
  E(h) = C_0(k) + (1 + ell - M/2) delta_0, C_0(k) = 1/2 + ell/2 - 3M/4 + b(1/4 - 1/(2k)).
  The contour 17/50 cancels at d = h. At k = 6 the transcription of line 15729 equals
  line 15732 identically in (delta, q, R, d).

### 2.3 Reproduction at k = 6 (cited values rebuilt exactly)

Part I (ell, M, b) = (0, 1, 0): c = -2/3, low exponent 1/4, sigma_0 = 11/12 (lines 190,
509-510, 3717). Part II (1/6, 5/6, 1/8): (l_x, l_y, h) = (17/48, 23/48, 13/16),
c = -11/16, low exponent 3/16, sigma_0 = 7/8 (lines 191, 514-515, 6860-6864,
8641-8642), C_0 = -1/48 and the floor value -7/1200 (lines 15734, 15847). For random
geometries at k = 6 the target equals hunt #134's 5/6 + (M - 2 ell)/12.

**What the reproduction does not pin.** A pole read as k/36 also equals 1/6 at k = 6 and
reproduces every constant above, yet makes sigma_0 decrease in k
(`test_planted_fault_a_wrong_k_reading_passes_k6_but_reverses_the_tower`). The direction
of the tower therefore rests on the structural reading "pole = 1/(character order)",
which comes from lines 3758 and 4045 (the sum over the k-th power part a^k of the
frequency is zeta_F(kz)), not from any reproduced number. Grade of the direction:
inferred reading, derived algebra.

## 3. The tower question

### 3.1 Direction (derived)

sigma_0(k) = 1 - (2 - m)/(2k) with m = M - 2 ell. Every admissible geometry has m <= M <= 1,
so 2 - m >= 1 > 0 and

    sigma_0(k + 1) - sigma_0(k) = (2 - m) / (2 k (k + 1)) > 0,   1 - sigma_0(k) <= 2/k.

At the paper's geometry the increment from k = 6 to 7 is 1/56, and sigma_0(k) = 1 - 3/(4k):
7/8, 25/28, 29/32, 15/16, 31/32 at k = 6, 7, 8, 12, 24. The mechanism behind it: the
principal frequencies of an order-k twist are the k-th powers, whose number up to height T
is about T^(1/k); the signal is proportional to that density, so it weakens as k grows.

### 3.2 Walls per order (derived; exact LPs over (ell, M, b), dual multipliers checked
symbolically in k and delta_0)

Constraints: ell, b >= 0, l_x >= 0, M + ell <= 1, and as stated per column. Every value
below is computed by `tower_template.wall` and equals its closed form.

| k | pole | Part I balanced 1 - 1/(2k) | paper geometry 1 - 3/(4k) | dual length only 1 - 2/k | floor, paper bin 1 - 25/(32k) | floor, limit 1 - 4/(5k) | z = 1/k in region two |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1/2 | 1/4 | (formal) | (formal) | (formal) | yes |
| 2 | 1/2 | 3/4 | 5/8 | 0 | 39/64 | 3/5 | yes |
| 3 | 1/3 | 5/6 | 3/4 | 1/3 | 71/96 | 11/15 | yes |
| 4 | 1/4 | 7/8 | 13/16 | 1/2 | 103/128 | 4/5 | yes |
| 5 | 1/5 | 9/10 | 17/20 | 3/5 | 27/32 | 21/25 | yes |
| 6 | 1/6 | 11/12 | 7/8 | 2/3 | 167/192 | 13/15 | yes |
| 7 | 1/7 | 13/14 | 25/28 | 5/7 | 199/224 | 31/35 | no |
| 8 | 1/8 | 15/16 | 29/32 | 3/4 | 231/256 | 9/10 | no |
| 12 | 1/12 | 23/24 | 15/16 | 5/6 | 359/384 | 14/15 | no |
| 100 | 1/100 | 199/200 | 397/400 | 49/50 | 127/128 | 124/125 | no |

- The dual-length wall is attained at the degenerate vertex ell = 1, M = b = 0 (no
  averaging at all); it needs no row count and no reading of the direct bound's
  bookkeeping, which is why it is the robust statement: whatever the row counts and
  the loss accounting, an order-k probe of this template cannot pass 1 - 2/k.
- The floor wall: for every delta_0 >= 0 the minimum of M - 2 ell is
  m* = (2 + 12 delta_0)/(5 + 6 delta_0) at b = 0, ell = (1 - 2 delta_0)/(5 + 6 delta_0),
  M + ell = 1, so the wall is 1 - 4/((5 + 6 delta_0) k). It is proved for every geometry by
  the identity (M - 2 ell) - m* = y1 (-floor) + y2 (1 - M - ell) + y3 b with
  y1 = 12/(5 + 6 delta_0), y2 = 4/(5 + 6 delta_0), y3 = y1 (1/4 - 1/(2k)), all >= 0 exactly
  when k >= 2. In the limit the corner is (ell, M, b) = (1/5, 4/5, 0) for every k, where
  the unrescaled-summand condition M >= (1 + 3 ell)/2 is tight as well (so that reading of
  the direct bound gives the same wall).
- These walls agree with hunt #136's probe lane (its section 3, recomputed here by
  separate code from the paper's lines) and, at k = 6, with hunt #134 (11/12, 7/8, 13/15).
  Below 7/8 at k = 6 the row counts matter (hunt #134's endpoint optimum 0.874958); for
  the tower only lower bounds matter, and the walls are lower bounds for any row counts.
- **Best order.** 1 - 4/(5k) increases with k, so the infimum over k >= 2 is 3/5 at
  k = 2. Every wall is above 1/2 for every k >= 2 (the dual-length wall is exactly 1/2 at
  k = 4, at its degenerate vertex).

### 3.3 The order k = 1 (derived arithmetic; the reading is inferred)

At k = 1, z* = 1 and the balanced geometry gives c = -1/4, low exponent 1/4,
sigma_0 = 1/2. There is no twist, so every frequency is principal and the probe is the
signal itself: Z^(-1/4) times a smoothed sum of mu(n) eta(n) of length Z. The direct
bound Z^(1/4) it asks for is square-root cancellation in that Moebius sum, which for
eta = 1 is Littlewood's condition M(x) << x^(1/2 + epsilon), equivalent to RH (Littlewood
1912; Titchmarsh, *The Theory of the Riemann Zeta-Function*, section 14.25; classical,
quoted, not rechecked here). The floor-wall multipliers fail at k = 1 (y3 < 0), so k = 1
is outside the walls' proof, as it must be. The reading is that the template is a
one-parameter family whose k = 1 member is a restatement of RH and whose k = 6 member is
the paper; moving k toward 1 is moving toward the restatement, which supplies no estimate.

### 3.4 The price of 1/2 (derived, exact LPs)

Three generic constraints meet at the floor corner (ell, M) = (1/5, 4/5): the dual length
M + ell <= 1 (D), the floor rows at delta_0 -> 0 (F, high side), and the direct bound's
loss condition (L, low side), which hunt #134 reads either as "only the unrescaled
summand lossless", M >= (1 + 3 ell)/2 (total accounting, tight at the same corner), or as
"every summand lossless", M - 2 ell >= 1/2 (per-summand, the paper's own corner, which
gives 1 - 3/(4k) and is higher still). How far they would have to be relaxed, by a common
eps in powers of Z, for some geometry to reach sigma_0 = 1/2, i.e. M - 2 ell = 2 - k:

| k | D and F | F alone (D exact) | D alone (F exact) | D, F, L (total accounting) | D, F, L (per summand) |
|---|---|---|---|---|---|
| 2 | 1/8 | 1/6 | 1/2 | 2/7 | 1/2 |
| 3 | 7/16 | 7/12 | 7/4 | 1 | 3/2 |
| 4 | 3/4 | 1 (only at ell = 1, M = 0) | 3 | 12/7 | 5/2 |
| 5 | 17/16 | infeasible | 17/4 | 17/7 | 7/2 |
| 6 | 11/8 | infeasible | 11/2 | 22/7 | 9/2 |
| 8 | 2 | infeasible | 8 | 32/7 | 13/2 |
| 12 | 4 | infeasible | 13 | 52/7 | 21/2 |

Closed forms (each checked against its LP for k = 2..12): max((5k - 8)/16, (k - 4)/2);
(5k - 8)/12 for k <= 4; 5k/4 - 2; (5k - 8)/7; k - 3/2. Every column increases with k.
The two columns without L are relaxations of the template, not readings of it: with L
imposed in either reading, a gain on the floor rows alone moves nothing (the wall stays
1 - 4/(5k) under total accounting and 1 - 3/(4k) per summand), because L is tight at the
same corner. Improving F and L together by Z^g gives 1 - (4 + 3g)/(5k) up to g = 2 and the
dual-length wall 1 - 2/k after it; a dual length longer by Z^e with F exact gives
1 - (4 + 2e)/(5k) (derived, checked against the LPs). In words: at the paper's order 6,
reaching 1/2 needs all three generic constraints relaxed by 22/7 (total accounting) or 9/2
(per summand) in powers of Z, more than the whole range of the geometry, and **no gain on
the floor rows and the direct bound together takes the template below the dual-length
wall 2/3**. At k = 2, for which no system exists, the joint price is 2/7 or 1/2.

### 3.5 The first test that could fail

`test_tower_hypothesis_fails_sigma0_increases_to_one` encodes the mission's hypothesis in
its negation: for 200 random rational admissible geometries and k = 1..64 the increment is
the closed form above and positive, 1 - sigma_0(k) <= 2/k, sigma_0 > 1/2 from k = 5 on,
and sigma_0(10^6) > 0.999997. It would have failed had the pole entered the template in
any way that made the signal stronger with k (the planted k/36 reading does exactly
that and is caught by the comparison at k = 7). It passed.

## 4. Which estimate fails at large k

None has to: the signal's density 1/k ends the tower before any estimate is reached. For
the record, the candidates the mission named and the others the template holds:

- **Theta coefficients at squarefree indices, n >= 4 (L1).** Over number fields the
  Fourier coefficients of the n-fold theta at squarefree indices are not determined for
  n >= 4 (David, Dunn, Hamieh and Lin, arXiv 2306.11875, as quoted in hunt #136's
  `PROBE.md` section 6, uncommitted, read; the obstruction traced there to Deligne's
  non-uniqueness of Whittaker models and Kazhdan and Patterson). Over F_13[T] at n = 4
  they exist and are not multiplicative up to phases: on three linear primes their
  modulus is 0 for 234 triples and nonzero for 52, so no scalar local identity of Lemma
  7.1's type exists (hunt #148 `ff_probe`, `S4.md`, uncommitted on branch `hunt/ff-probe`,
  exact computation, unreviewed, read here). Grade here: cited from uncommitted sources.
  For a tower k = 2n -> infinity, L1 is missing at every level from k = 8 on; but it is
  the small-k doors (k = 4, 5) that it closes, which matters more (section 5).
- **Large sieve of degree k.** Does not fail. Blomer, Goldmakher and Louvel, *L-functions
  with n-th order twists*, arXiv 1112.1650, Theorem 1.3 (label `thm:thm3`, read in the
  arXiv TeX source `nth-order-twist.tex`, SHA-256
  `bd846eb6f570c40cc2b571595260cdd250c633f337c88c33e261e95f7979a6cb`, fetched into scratch):
  for every n >= 3 and a number field containing the n-th roots of unity,
  sum* over N a <= M of |sum* over N b <= N lambda_b chi_a(b)|^2 << (MN)^epsilon
  (M + N + (MN)^(2/3)) sum* |lambda_b|^2, over squarefree ideals prime to S. The
  exponents do not depend on n (the constants may). Cited.
- **Amplification slope and plain capacity.** The template's alpha = 1 - 1/k and the
  capacity k kappa (hunt #136's readings, inferred) both get worse as k grows: they only
  raise the endpoint above the walls.
- **Euler region two.** The principal residue z = 1/k lies in the region z_r >= 33/200
  (line 4056) exactly for k <= 6 (derived): from k = 7 on the paper's correction product
  is not shown to converge at the residue point, so the scalar Euler identity's region
  would have to be re-derived for an order-k identity that does not exist (L1).
- **Field degree.** An order-k twist needs the k-th roots of unity in the base field, of
  degree phi(k) over Q for k outside {1, 2, 3, 4, 6}; the template does not price the
  field degree (inferred). Liu's extension to fields containing mu_12 keeps
  zeta_F^S(6z) (as hunt #136's probe lane records Liu, arXiv 2610.26835): a bigger field
  has not moved the pole.

## 5. The small orders, the only useful direction

| system (hunt #136's labels) | k | template floor (limit) | status |
|---|---|---|---|
| S2: cubic theta, quadratic twist | 2 | 3/5 | no scalar Euler identity (hunt #136 referee, committed `b6c4972a8`, `REFEREE_W1.md` section 3: gamma_2 gamma_3 has alpha-exponent 1/3) |
| S3: classical theta over Q(i), quartic twist | 4 | 4/5 | theta supported on squares: no squarefree c, no 1/L (same, exact through t = 4) |
| S1: cubic theta, cubic twist | 3 | 11/15 | the referee finds a scalar factorization L(x, eta)/L(2x, eta^2) at u = 1 (disagreeing with the probe lane's reading); **its reciprocal factor cannot fire**: its poles sit at x = rho/2, real part below 1/2, under every k = 3 wall (derived here on the referee's factorization) |
| S4: biquadratic theta, quartic twist | 4 | 4/5 | L1 undetermined over Q(i); fails over F_13[T] (hunt #148, uncommitted) |
| S5: quintic theta over Q(zeta_5) | 5 | 21/25 | L1 undetermined (hunt #136 probe lane, uncommitted) |
| S0: the paper, cubic theta, sextic twist | 6 | 13/15 | the only realized system; its assembly's optimum 0.874958 (hunt #134); public records near 0.8748 (hunt #136) |

So the direction that lowers the abscissa has no working system below k = 6, and even a
working k = 2 system with perfect row counts would stop at 3/5.

## 6. The function-field analogue

Hunt #148 (`ff_probe`, branch `hunt/ff-probe`, files uncommitted at the time of reading)
built the F_7[T] transplant of the cubic probe and checked Lemma 7.1 exactly there, and
found the biquadratic case unusable (section 4). What that settles for this mechanism:

- **The walls are the method's, not the zeros'.** In F_q[T] RH is a theorem (Weil) for
  every L-function concerned, while the template's algebra (Mellin weight, Poisson
  frequencies u a^k, pole of zeta(kz) at 1/k) is the same; so the template would price
  sigma_0(k) -> 1 there too, against the truth 1/2 at every k. The tower's failure is a
  property of the probe's signal, independent of whether RH holds (inferred from the
  shared algebra; hunt #148's ledger records the k = 6 excess, 7/8 priced against the
  truth 1/2).
- **The small-k door at n = 4 is closed in F_13[T]** (squarefree coefficients not
  multiplicative). That is evidence, not proof, about Q(i).
- **What it cannot settle:** nothing about number-field L1 for n >= 4 beyond evidence,
  and nothing new about large k, which the algebra already settles negatively.

## 7. The distinguishing step and the rival gate

### 7.1 The step

The continuation criterion (Proposition 2.1) is a shared lemma: hunt #120 showed it goes
through for any function whose reciprocal is bounded on Re s >= 2. The Euler product is
consumed where its hypotheses are manufactured. In the probe, the theta coefficient at a
squarefree index is gamma_2(c) = mu(c) alpha(c) G(c)/gamma_1(c) (line 3967), so the target
enters the principal row through mu(c) eta(c) and, by the scalar Euler identity
(lines 4043-4047), as 1/L^S(x, eta) times a correction H that the criterion needs within
1/2 of 1 (line 413). The target enters the row linearly through eta(A) at the completed
index (hunt #136 referee, section 2), at every order k. So the step, in the form that can
be tested on any coefficient sequence f, is:

> **(E_k)** The principal row's dependence on the target is
> R_f(s) = sum over squarefree n of mu(n) f(n) n^(-s), and the criterion needs
> R_f = H_f / L_f with sup over Re s > sigma_0 of |H_f - 1| <= 1/2, for some finite
> deletion set.

It does not depend on k. For a linear combination f = c1 eta1 + c2 eta2 of two Euler
products, linearity gives R_f = c1 H1/L1 + c2 H2/L2, whose poles are the constituents'
zeros, never the combination's. Below, the constituents' corrections H_i are set to 1
(over Q, for characters, exactly) or computed (degree 2). For unitary characters the
paper's full correction at the principal point converges absolutely from Re x > 2/3 by
the closed form's monomials (hunt #148 derived this for F_7[T]; the number-field monomials
are the same, inferred; `principal_correction_abscissa` pins the arithmetic), which covers
the DH points used here. For the degree-2 constituents of Epstein (1,1,6) and for W_a the
paper writes no identity; section 7.5 says how unitarity enters there.

### 7.2 Control: zeta and Dirichlet L-functions

f completely multiplicative: R_f = 1/L_f exactly, H_f = 1. Measured control: the
squarefree Moebius sum to n = 20000 at s = 2 equals 1/zeta(2) to 6.9e-8, inside its tail
bound 5e-5.

### 7.3 Davenport-Heilbronn (fails, at every k)

f = c1 chi + c2 chibar with chi mod 5, chi(2) = i, c1 = (1 - i kappa)/2, from
`zeta.epstein`.

- **Linear structure, second route (measured).** At s = 2 the squarefree Moebius sum of
  the DH coefficients to n = 20000 is 0.9755806880; c1/L(2, chi) + c2/L(2, chibar) is
  0.9755806815 (gap 6.5e-9, inside the tail bound 5e-5); 1/DH(2) is 0.9999316669 (gap
  0.0244). The probe sees the combination of reciprocals, not the reciprocal of DH.
- **At the zero rho = 0.80851718 + 85.69934849i (measured, dps 30).** |DH(rho)| = 6.5e-40
  by `dh_f` and 6.5e-40 as c1 L(chi) + c2 L(chibar); |L(rho, chi)| = |L(rho, chibar)| =
  0.70220 (equal, as they must be at a zero of the combination); the probe-visible
  reciprocal is finite, |R| = 0.77832; so H = DH R has |H| = 5.1e-40 and |H - 1| = 1.0000.
  The closed form H - 1 = c1 c2 (L1 - L2)^2/(L1 L2) gives the same. The contraction fails
  on every half-plane Re s > sigma_0 with sigma_0 < 0.8085.
- **On the 7/8 line, nothing deleted (measured).** On Re s = 7/8, t in [1, 300], step 1/4
  (1197 points): max |H - 1| = 3.68 (at t = 256) and |H - 1| > 1/2 at 572 points. The
  paper's own normalization hypothesis cannot be met for DH even at 7/8.
- **With primes deleted (measured, then cited).** With S = {2, 3} the same scan gives
  max |H^S - 1| = 0.276 (t = 178) and no point above 1/2; with S = {p <= 100},
  max |H^S - 1| = 0.018 (t = 100.5) and again no point above 1/2. Deleting primes makes
  the two constituents' ratio close to 1 at every height a computation reaches, so **no
  finite scan shows the failure once small primes are deleted**. The failure is an
  all-height fact, at the placement over Q used here: the coefficients of DH^S (DH with n
  restricted to n prime to S) are periodic, and DH^S is not a Dirichlet polynomial times
  one L-function (its coefficients at large primes take the values 1, kappa, -kappa, -1,
  of two different moduli, while a Dirichlet polynomial times L(s, psi) has coefficients
  b_1 psi(p) of one modulus at every large prime; derived), so by Saias and Weingartner
  (Acta Arith. 140 (2009) 335-344, arXiv 0807.0783, abstract read here; proof not
  checked) there is eta(S) > 0 such that every strip sigma_1 < Re s < sigma_2 with
  1/2 < sigma_1 < sigma_2 < 1 + eta(S) holds >> T zeros of DH^S up to height T. At those
  with Re s > 1 the constituents have no zeros, so R^S is finite and H^S = 0. Hence for
  every finite S and every sigma_0 < 1 + eta(S) the contraction fails (cited theorem plus
  derived steps). The placement over F = Q(sqrt(-3)) through the norm, which hunt #136's
  referee used, processes c1 L(chi) L(chi chi_-3) + c2 L(chibar) L(chibar chi_-3)
  instead; its coefficients are not periodic, and nothing is cited here for its zeros.

### 7.4 Epstein (1,1,6), discriminant -23 (fails)

Z_Q/2 = (zeta_K + 2 L_psi)/3 with K = Q(sqrt(-23)) and psi the cubic class character, so
R_f = (H_1/zeta_K + 2 H_psi/L_psi)/3 with H_1, H_psi the degree-2 corrections (absolutely
convergent on Re s > 1/2), computed over p <= 10^4 from exact representation counts.
At rho = 0.9532604748 + 16.2902157204i (measured, dps 25): |Z_116(rho)| = 3.1e-29;
|zeta_K(rho)| = 1.45600 by the lattice route (Z_116 + 2 Z_213)/2, agreeing with
zeta(rho) L(rho, chi_-23) by the Hurwitz route to 5.2e-27; |L_psi(rho)| = 0.72800;
|H_1| = 1.4163, |H_psi| = 1.0963; the probe-visible reciprocal is finite, |R| = 0.70349;
H_E = (Z_116/2) R has |H_E| = 1.1e-29 and |H_E - 1| = 1.0000. The contraction fails for
every sigma_0 < 0.9533, past 7/8: the step refuses this rival exactly where hunt #120
located the refusal for discriminant -15.

### 7.5 W_a = zeta(s + 1/4) zeta(s - 1/4) (passes the step; held off by unitarity)

The coefficients a(n) = n^(-1/4) sigma_(1/2)(n) are multiplicative, so
R_W = H_W / W_a with H_W = prod over p of (1 - p^(-2s)/((1 - p^(1/4 - s))(1 - p^(-1/4 - s)))),
absolutely convergent on Re s > 1/2. Second route: at s = 3 the squarefree Moebius sum to
n = 20000 equals H_W/W_a to 1.0e-10 (measured). At the zero s_1 = 3/4 + 14.1347251417i,
|W_a(s_1)| = 1.7e-21, and over p <= 10^5 (omitted factors within 0.0064 of 1):
|H_W - 1| = 0.236 with nothing deleted, 0.0017 with p <= 10 deleted, 0.0024 with
p <= 100 deleted (measured). The pass is uniform, not just at the zero: for
Re s >= sigma > 1/2 each omitted factor is 1 + e_p with
|e_p| <= p^(-2 sigma)/((1 - p^(1/4 - sigma))(1 - p^(-1/4 - sigma))), so deleting the primes up
to P makes sup |H_W - 1| at most exp(c(P) sum_{n > P} n^(-2 sigma)) - 1, which is below 1/2
for P large enough at every sigma > 1/2 (for instance below 0.26 on Re s >= 3/4 with
P = 100, summing crudely over all integers; derived). **W_a passes (E_k)** on every
half-plane Re s > 1/2 + delta: its probe-visible reciprocal has the pole at its off-line
zero that the criterion needs (this tests the bare Moebius
identity; the paper writes its full identity only for unitary GL(1) targets, and the
cube-completion terms of a degree-2 target are not computed here). What keeps the
template away from W_a is unitarity, which the paper uses twice: the direct bound uses
|eta| = 1 through the mean square of the theta row, and the local identity's parameters
rho, a_p, b_p have absolute value one (line 3870). For the GL(1) factor zeta(s - 1/4),
whose character n^(1/4) is not unitary, both shift by exactly 1/4, as a change of
variables (derived): the direct bound and the target rise by 1/4, and the region where the
principal correction converges absolutely moves from Re x > 2/3 to Re x > 11/12 (its term
a_p^2 Q^(4 - 6x - 6z) at z = 1/6 grows by Q^(6/4)). For the degree-2 placement the same
rise of 1/4 in the direct bound is inferred (coefficients up to d(n) n^(1/4)). W_a's zeros
sit at 1/2 + 1/4, so they are within reach only if sigma_0 < 1/2, which no wall allows
(the best is 3/5 + 1/4 = 17/20 > 3/4). W_a is a rival that lacks a hypothesis the argument
uses, not a counterexample; what it shows is that the tower needs unitarity at every k,
beside the Euler product.

### 7.6 What the gate says

Read two-sidedly (`docs/08` section 4.3): DH and Epstein (1,1,6) violate the conclusion
and fail the step that uses the Euler product, at every k, so they are not
counterexamples and the step is genuinely distinguishing. W_a satisfies the step and
violates the conclusion's analogue, but lacks unitarity, which the direct bound and the
local identity use at every k. No rival passes every hypothesis. The gate does not bear on the tower's failure,
which is internal to the template.

## 8. Known obstructions engaged, and what differs from refuted forms

- **Hunt #134** (13/15 floor of the k = 6 assembly, 0.874958 endpoint): reproduced at k = 6
  as the floor wall; the tower generalizes its floor to 1 - 4/(5k).
- **Hunt #136's probe lane** (uncommitted, read) priced the order-k template first: its
  formula, walls and system table agree with this page, which recomputes them from the
  paper's lines by separate code. Added here: the mission's tower question answered in the
  negative with the row-count-free bound 1 - 2/k; the price of 1/2; the order k = 1 as
  Littlewood's restatement; the cubic-twist factorization's non-firing; the large sieve
  read at the source; and the step tested at the rivals' zeros in its analytic form.
- **Hunt #120** placed the Euler-product step at the Moebius identity and Lemma 7.1 and
  refused the discriminant -15 Epstein zeta there; hunt #136's referee refused DH and the
  -15 form coefficient by coefficient; hunt #148 refused a DH analogue over F_7[T] at X^2.
  This page evaluates the same step analytically at each rival's actual zero, adds
  Epstein (1,1,6) and W_a, and shows that deletion hides DH's failure from any scan.
- **docs/09 section 5.1's evasions.** Direct estimation: the tower's endpoint k = 1 is
  exactly a direct estimate of the Moebius sum. Zero-importing: no zero enters any
  formula. Finite approximants: every statement in sections 3 and 4 is uniform in k by
  closed form, not a finite scan; the rival scans are labelled measured and finite.
- **Refuted forms in the mission's list.** EPP/Herglotz (composing archimedean and
  prime-side positivity) was refuted by W_a; the tower is not a positivity mechanism, and
  its direct bound uses unitarity, which W_a lacks. Jensen wedges and the heat-flow clocks
  succeed for DH; the tower's step refuses DH. Neither refuted form is the tower, and the
  tower fails for its own reason, the signal density 1/k.

## 9. Disposition

**Restricted class obstructed.** The class: probes in which the target is twisted by a
family of nontrivial power-residue characters of order k >= 2 (so the principal
frequencies are the k-th powers and the comparison pole is z* = 1/k <= 1/2), whose signal,
direct bound, dual length M + ell <= 1 and floor rows keep the paper's forms. The proof:
the LP of section 3.2 with its dual multipliers (derived, symbolic in k, self-reviewed).
That its hypotheses apply to such probes is the inferred reading of section 2.1. Within
the class the tower premise is refuted (sigma_0 increases to 1) and 1/2 is unreachable
(sigma_0 >= 3/5). Outside the class nothing is claimed: a probe whose principal frequency
set had density above 1/2, or whose dual length or floor rows were handled differently,
is not covered.

## 10. The furthest true statement reached

> In the order-k template, for every k >= 2 and every admissible geometry,
> sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k) >= max(1 - 2/k, 1 - 4/((5 + 6 delta_0) k)) >= 3/5,
> with 3/5 attained only at k = 2 in the limit delta_0 -> 0, at (ell, M, b) = (1/5, 4/5, 0);
> and no common gain on the floor rows and the direct bound's loss condition takes it
> below the dual-length wall 1 - 2/k;
> sigma_0(k) is strictly increasing in k and tends to 1; the formal order k = 1 gives 1/2
> exactly, where the direct bound is Littlewood's RH-equivalent Moebius bound.

Grade: **derived** (exact, symbolic in k, self-reviewed) on **cited** formulas, with the
k-reading and the sufficiency of M + ell <= 1 **inferred**; composite grade **inferred**.
Beside it, at the rival gate: the step (E_k) is k-independent; DH and Epstein (1,1,6) fail
it at their zeros (**measured**), DH for every finite deletion set by Saias and
Weingartner (**cited**, with **derived** steps); W_a passes it (**measured**) and is held off
by unitarity (**inferred**), a shift of exactly 1/4 (**derived**).

## 11. Next step

The tower is closed inside its class, and its best member (k = 2) stops at 3/5 even with
perfect row counts, so as a route to RH this mechanism has no next construction step that
the template contains; continuing it is the owner's call. Section 3.4 prices the generic
doors: at the realized k = 6, 1/2 needs the dual length, the floor rows and the direct
bound's loss condition all relaxed by at least 22/7 in powers of Z, and no improvement of
the floor rows and the direct bound together gets below 2/3 without a longer reflected
dual. So the next step is not an RH step. The one decidable step left is a half-plane step,
and it belongs with hunt #136, which owns the half-plane: since the floor rows and the loss
condition are tight at the same corner, any attempt below 13/15 must improve both at once,
for instance a mean value over the row family in place of the floor rows' pointwise
treatment (R = 1, each row at its full size; Blomer, Goldmakher and Louvel's Theorem 1.3
applied to the floor rows' Moebius polynomials is the obvious candidate) together with a
row-norm lemma whose second-branch loss (1 + 3 ell' - 2M')/4 (line 8306) is smaller. The
exact LP of section 3.2 then prices the pair, 1 - (4 + 3g)/(5k) for a common gain Z^g.
Recorded here as the hand-off; the mechanism as obstructed for RH.

## 12. Tests, commands, files

```
.venv/bin/python hunts/rh_moonshot/probe_tower/tower_template.py --paper --write
.venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/probe_tower/test_probe_tower.py
.venv/bin/python -m pytest -q -n0 -m "not slow" hunts/rh_moonshot/probe_tower/test_probe_tower.py
```

`test_probe_tower.py`: 23 fast tests (citations, the k = 6 reproduction, both signal
routes for k = 1..40, b-freeness, the line 15729/15732 transcription, the floor closed
form, the symbolic identities, the tower's direction, the k = 1 endpoint, the walls and
their dual multipliers, the best order, the price of 1/2 in five modes, the relaxed walls
of the doors, region two, the S1 remark, the W_a shift and the 2/3 and 11/12 correction
abscissae, four planted faults, the committed report and this page's quoted numbers
against the code, the lexical rules) and 6 slow ones (DH at its zero, the DH Moebius-sum
route, the DH 7/8-line scan near t = 85, Epstein (1,1,6) at its zero, W_a at its zero,
the W_a Moebius-sum route); 29 in all, all passing (`RUNS.md`). Planted faults: a pole read as k/36 (passes
k = 6, reverses the tower), the floor rows dropped (the k = 2 wall falls from 3/5 to 0), a
Gram term held at 1/12 for every k (sigma_0 starts depending on b), a perturbed dual
multiplier (the identity breaks). `RUNS.md` has the run manifests.

## 13. Sources, and what was searched

- The paper (pinned above). Hunt #134 `RESULTS.md` (branch
  `origin/claude/hunt-134-seven-eighths-pin`, committed). Hunt #136 `REFEREE_W1.md`
  (committed on `hunt/below-seven-eighths`, `b6c4972a8`) and `PROBE.md` (uncommitted in its
  worktree, read, quoted as uncommitted). Hunt #148 `S4.md`, `RIVAL.md`,
  `LOCAL_IDENTITY.md` (uncommitted in its worktree, read). Hunt #120 `RESULTS.md`.
- Blomer, Goldmakher, Louvel, arXiv 1112.1650, Theorem 1.3, read in its TeX source
  (SHA-256 above). Saias and Weingartner, arXiv 0807.0783, abstract read. Littlewood's
  criterion, quoted as classical.
- **Novelty: not searched.** No arXiv, zbMATH or OEIS search was made for the order-k
  pricing or the tower statement. Original to this laboratory as a reading; overlapping
  hunt #136's probe lane as stated in section 8.

## The doors

The page measures a ceiling of a construction family, so it owes this section. Candidate
status: the walls of section 3.2 are lower bounds for the template's abscissa, proved by
LP duality; parameter range k >= 2, ell, b >= 0, l_x >= 0, M + ell <= 1, delta_0 >= 0;
information class below; proof status derived on an inferred reading, unreviewed.

### Active constraints at the optimum

Ranked by what relaxing them buys toward 1/2 (section 3.4):

1. **The comparison pole z* = 1/k** (the density of k-th powers among the frequencies).
   It scales the whole distance to 1: 1 - sigma_0 = (2 - m)/(2k). Its shadow price at the
   paper's geometry is d sigma_0/d z* = -(h - b/2) = -3/4. Lowering k is the largest lever;
   raising it, the tower, is the wrong sign.
2. **The floor rows and the direct bound's loss condition, together.** The floor rows
   C_0(k) + (1 + ell - M/2) delta_0 <= 0 (multiplier y1 = 12/5 in the D-F system) and the
   unrescaled-summand condition M >= (1 + 3 ell)/2 are tight at the same corner, so
   neither moves the wall alone; a common gain of Z^g moves it to 1 - (4 + 3g)/(5k), down
   to the dual-length wall at g = 2. Price of 1/2 with the dual length: 2/7 at k = 2, 22/7
   at k = 6 (total accounting); 1/2 and 9/2 per summand.
3. **The dual length** M + ell <= 1 (multiplier y2 = 4/5 in the D-F system; a longer dual
   by Z^e moves the wall to 1 - (4 + 2e)/(5k)). Alone it bounds sigma_0 by 1 - 2/k, above
   1/2 for k >= 5.

### The frozen-constant inventory

| constant | value | what relaxing it trades | trade shape |
|---|---|---|---|
| character order k | 6 (realized), any k >= 2 here | the whole theta construction (L1-L3); larger k weakens the signal | genuine; the useful direction (smaller k) has no system |
| floor bin delta_0 | 1/50 | the floor wall from 1 - 25/(32k) to 1 - 4/(5k); needs Euler region one below 51/100 | genuine, small |
| slot length ell, total length M, offset b | free, optimum (1/5, 4/5, 0) at the floor corner | lower m = M - 2 ell against the floor rows, the loss condition and the dual length | exhausted by the LP |
| row-norm second-branch loss (1 + 3 ell' - 2M')/4 | held (line 8306) | tight at the floor corner with the floor rows; must improve together with them | genuine, outside the template |
| contour Re z = 17/50 | held | cancels at d = h | none |
| Euler region two z_r >= 33/200 | held | contains z = 1/k only for k <= 6 | binding for the tower from k = 7, needs an identity that does not exist |
| large-sieve exponent (MN)^(2/3) | n-free (BGL) | row counts only | none for the walls |

### The information class

- **Inside the data the template reads:** the geometry, the floor bin and the order are
  exhausted by the walls; no choice inside the class reaches 1/2, and the increasing tower
  moves away from it.
- **Reading more:** a mean-value treatment of the floor rows across the row family
  together with a smaller row-norm loss (the next step above, a half-plane step), a
  reflection with a longer dual length, or a twist family whose principal frequencies have
  density above 1/2. The last cannot be a power-residue family
  (density 1/k <= 1/2); at density 1 it is the Moebius sum itself, k = 1, whose direct
  bound is RH. This door gets no automatic priority over the other mechanisms of the hunt.
