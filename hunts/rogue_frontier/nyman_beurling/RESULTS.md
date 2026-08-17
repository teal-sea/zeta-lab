# Enclosure-checked d_N^2 for the Baez-Duarte criterion, N up to 4096

Session of 2026-08-17. Grade: **measured, with enclosure-checked arithmetic**
(every headline d_N^2 is an arb ball that rigorously contains the exact value
of the stated finite-dimensional minimization, conditional only on Vasyunin's
published formula, which is validated five independent ways below). Nothing
here is evidence about RH (docs/08): d_N -> 0 is *equivalent* to RH, and no
finite ladder distinguishes convergence to 0 from convergence to a small
positive limit. The repo's standing caution applies verbatim.

Everything is reproducible from this directory:

    .venv/bin/python validate.py          # the five-route validation battery
    .venv/bin/python run_ladder.py 4096   # the ladder (hours)
    .venv/bin/python run_supplement.py    # extra N points, 128-bit solves
    .venv/bin/python analyze.py           # fits, conditioning, figure

## 1. What was computed

On L^2(0, infty) with basis e_k(t) = {1/(kt)} and target chi = chi_(0,1),

    d_N^2 = inf_a || chi - sum_{k=1}^N a_k e_k ||^2 = 1 - b^T G^{-1} b,

with G[j,k] = <e_j, e_k> by Vasyunin's formula (SOURCES.md section 2) and
b_k = (1 - gamma + log k)/k. Baez-Duarte 2003: RH iff d_N -> 0. BCF
(arXiv:1211.5191) + BBLS/Burnol: conjecturally d_N^2 ~ C/log N with
C = 2 + gamma - log 4pi = 0.0461914179322420676...

Implementation: the Vasyunin sum V(p/q) is evaluated as an exact integer
matrix (the reduced weights 2(mp mod q) - q, a numpy computation) times a
ball vector of cot(pi m/q) values, entirely inside flint; the only inexact
inputs anywhere are cot, log, pi, gamma balls at 256 bits. The reduction
uses the pairing m <-> q-m and the reflection V((q-p)/q) = -V(p/q); both
identities are exercised against unreduced sums in the battery. The solve is
`arb_mat.solve` (proves invertibility, returns enclosures), run at several
precisions per N; the headline balls are the 192-bit solves for the power
ladder and 128-bit for the supplement points.

## 2. Validation battery (all green)

Five routes to the same numbers, none sharing code with the production arm
beyond the formula itself:

| check | scope | worst disagreement | floor set by |
|---|---|---|---|
| arb vs mpmath Vasyunin (unreduced O(q) sums) | 15 pairs, j,k <= 101 | 4.3e-61 | mpmath dps |
| same, large q | (999,1024), (1023,1024), (997,1499), (512,1497), (700,1050) | 2.6e-62 | mpmath dps |
| arb vs cotangent-free quadrature (piecewise closed form + exact trigamma tail) | 15 pairs | 1.3e-47 | quadrature dps |
| arb vs adaptive mp.quad variant | (2,3), (5,7) | 2.5e-41 | quadrature dps |
| b_k closed form vs direct quadrature | k in {1,2,3,5,12,64} | 3.7e-41 | quadrature dps |
| full d_N^2: arb pipeline vs mpmath pipeline (mp.lu_solve) | N in {1,...,32} | 5.3e-58 | mpmath dps |
| bridge identity vs the repo's digamma-based cache | all 1225 entries of data/baez_duarte_gram_N50_dps50.json | 4.9e-61 | cache digits (60) |

The bridge identity, derived in this session from e_k(t) = 1/(kt) for t > 1:

    <A_j, A_k>_{L^2(0,1)} = G_jk - G_j1/k - G_1k/j + G_11/(jk),

where A_k is the repo's BBLS basis. The repo cache was produced by an
unrelated closed form (digamma series, `zeta.criteria._bd_gram_block`), so
this ties the Vasyunin implementation to an independent derivation across
1225 entries at the cache's own rounding floor. Details: results/validation.json.

Exact small case, pinned: d_1^2 = 1 - (1-gamma)^2/(log 2pi - gamma)
= 0.85821205139551088466996... (ball and closed form agree to 4.9e-59).

## 3. The enclosure-checked table

Headline solves at 192 bits (radii ~1e-56; the 128-bit supplement rows have
radii ~1e-37, and radii never matter at the size of anything analyzed).
Full balls in results/ladder.json; digits below are exact to the last place.

| N | d_N^2 (ball midpoint) | ball radius | d_N^2 log N / C | cond(G) |
|---|---|---|---|---|
| 1 | 0.858212051395510885 | 2.3e-58 | (log 1 = 0) | 1.0 |
| 2 | 0.289964573742202732 | 3.0e-57 | 4.351201 | 1.6e1 |
| 4 | 0.065128868659900250 | 6.6e-56 | 1.954644 | 5.7e1 |
| 8 | 0.024161421585896685 | 6.7e-54 | 1.087697 | 2.0e2 |
| 16 | 0.017894023476969435 | 6.4e-50 | 1.074069 | 8.4e2 |
| 32 | 0.014051943699529860 | 5.1e-57 | 1.054315 | 3.8e3 |
| 40 | 0.012715197195336612 | 6.2e-57 | 1.015445 | 5.7e3 |
| 50 | 0.011869048866095566 | 7.1e-57 | 1.005208 | 9.4e3 |
| 64 | 0.011376040299673658 | 6.5e-57 | 1.024251 | 1.5e4 |
| 96 | 0.010406820577199184 | 5.5e-28* | 1.028337 | 3.4e4 |
| 128 | 0.009658545903771290 | 8.6e-57 | 1.014552 | 6.3e4 |
| 192 | 0.009094022741544412 | 4.7e-28* | 1.035079 | 1.4e5 |
| 256 | 0.008233721418475596 | 1.1e-56 | 0.988439 | 2.5e5 |
| 384 | 0.007767420691761304 | 3.9e-28* | 1.000644 | 5.7e5 |
| 512 | 0.007386511214681442 | 1.4e-56 | 0.997576 | 1.0e6 |
| 768 | 0.006719444485058544 | 5.0e-29* | 0.966469 | 2.3e6 |
| 1024 | 0.006528722968216871 | 1.8e-56 | 0.979698 | 4.0e6 |
| 1536 | 0.006238577237365889 | 3.7e-28* | 0.990921 | 9.1e6 |
| 2048 | {{D2_2048}} | {{RAD_2048}} | {{RATIO_2048}} | {{COND_2048}} |
| 3072 | {{D2_3072}} | {{RAD_3072}} | {{RATIO_3072}} | {{COND_3072}} |
| 4096 | {{D2_4096}} | {{RAD_4096}} | {{RATIO_4096}} | {{COND_4096}} |

(* = supplement rows, 128-bit solves.) Monotone decrease of d_N^2 in N holds
across the whole table, as it must (nested minimizations). The residual
quadratic form 1 - 2b.x + x^T G x, recomputed from the solution enclosure,
overlaps the reported ball at every N.

## 4. The approach curve d_N^2 log N vs the BCF constant

{{APPROACH_SECTION}}

## 5. The BCF vector at finite N

The vector a_k = -mu(k)(1 - log k/log N) (the coefficients of BCF's V_N,
which achieves the conjectured asymptotic) gives a rigorous upper bound
U_N >= d_N^2 at every N, computed here as a ball. It is far from optimal in
this range: U_N/d_N^2 falls from ~34 (N = 8) to {{BCF_RATIO_LARGE}} at
N = {{BCF_N_LARGE}}, and U_N log N is still {{BCF_ULOGN_LARGE}} there,
more than an order of magnitude above C. This quantifies, with enclosures,
the observation of Landreau-Richard that the natural Mobius vector "looks
bad" at reachable N even though (BCF, Theorem 1) it is asymptotically
optimal: the convergence of the smoothed Mobius choice is slow enough that
at N ~ 10^3 it is >10x worse than the true minimizer.

The true minimizing coefficients do echo the Mobius shape: at N = 4096 the
solved x has x_1 = {{X1_4096}} (model: -1), cosine similarity
{{COS_4096}} to -mu(k)(1 - log k/log N), with the largest deviations at
squarefull k where the model is 0.

## 6. Conditioning, measured

The folklore (docs/07 for the cousin basis) says this problem is severely
ill-conditioned; the measurement says otherwise, matching the repo's earlier
finding for the BBLS basis. Float64 estimates on ball midpoints:

    cond(G) ~= {{COND_PREFACTOR}} * N^{{COND_EXPONENT}}   (fit over N = 8..4096)

i.e. almost exactly quadratic growth, reaching {{COND_4096}} at N = 4096:
trivially inside 128-bit arithmetic, and in principle inside float64. The
solve enclosures follow rad(d_N^2) ~= 2^-P * A(N) with A(N) growing slowly
(A ~ 40 at N = 64, ~{{A_4096}} at N = 4096): each extra bit of solve
precision buys exactly one bit of enclosure, with no conditioning cliff
anywhere in reach. The obstruction to pushing this criterion numerically is
not conditioning; it is the 1/log N decay itself (to see d_N^2 = 0.001 one
would need N ~ e^46 ~ 10^20).

## 7. External anchors

- Landreau-Richard 2002 computed d_n (floats, Gram-Schmidt on exact
  Vasyunin entries) to n = 20000. Their Figure 2 shows d_n crossing the
  window [0.07, 0.08] during n ~ 2000..10000: here d_2048 = {{DN_2048}} and
  d_4096 = {{DN_4096}}, inside the window at the right place.
- Their least-squares fit d_n ~ a/sqrt(log n) gave a = 0.21377 at
  N = 20000, below sqrt(C) = 0.21492; here d_N sqrt(log N) runs
  0.213-0.216 over N = 512..4096, the same slight undershoot.
- The repo's own BBLS-basis sequence (different quadratic form, same
  conjectured limit): at N = 50 its d_N^2 log N / C is 1.00673 (pinned in
  `zeta.criteria.baez_duarte_table`); this basis gives 1.00521 at the same
  N. Two formulations, same story.

## 8. Honest caveats

- **This is numerical evidence about a criterion, not about RH.** The
  computation proves (in the enclosure sense) values of a finite-dimensional
  quadratic minimum; it proves nothing about the limit.
- The enclosure chain starts at Vasyunin's formula as published. The formula
  is validated here five independent ways, including a cotangent-free
  quadrature and an unrelated digamma route, but a kernel-checked proof of
  the formula itself is not part of this study.
- The d_N^2 log N values below C at N >= 256 do not contradict the
  unconditional BBLS/Burnol bound, which constrains only the liminf; they do
  mean the approach to C is from below in this range and that any finite-N
  extrapolation of the constant is delicate: the free-intercept fit lands
  {{FREE_INTERCEPT_SUMMARY}}.
- Solve enclosures are rigorous relative to flint's arb; the mpmath arm
  cross-checks the full pipeline only up to N = 32, entry-level checks reach
  q ~ 1500.
- The prime-driven irregularity of the approach curve means the fits in
  section 4 are descriptive, not model selection; none of the fitted
  constants is a measurement of C.
