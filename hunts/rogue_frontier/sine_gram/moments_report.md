# Exact spectral moments of the CUE band Gram matrix: m_5, m_6, m_7, and the lambda structure

Status: probe output of the `sine_gram` hunt. Everything below is a statement
about the CUE band-Gram model at band ratio `lambda = d/N` (equivalently, in
the limit, the sine process of unit density with kernel
`sin(pi lambda x)/(pi x)`), whose `N -> infinity` limit is what the 10 August
2026 paper ("more than two thirds", Remark 7.5(f)) calls `m_k(lambda)`.
Nothing here is a statement about the zeros of zeta, and nothing here bears on
RH. Grades follow the repository ladder: the integers are exact, the
polynomials and limits are measured identifications with the overdetermination
stated per claim.

## 1. The object and the engine

`T_{m,m'} = Tr U^{m-m'}` for `m, m'` in a band of `d` consecutive integers,
`U ~ CUE(N)`; `G = T/N`; `m_k(lambda) = lim_N E tr T^k / (N^k d)` with
`lambda = d/N` held fixed. `E tr T^k` is an integer, computed exactly (integer
arithmetic throughout, no floats, no truncation) by `fast_moments.py`, an
optimized reorganisation of the validated engine `exact_finite_N.py`:
sum over sorted h-multiset classes of `J(class, N) * A(class) / mult(class)`,
where `J` is the exact CUE joint trace moment (set partitions, then signed
permutation cycles, each cycle a lattice count `max(0, N - spread)`) and `A`
is the ordering-summed band count (details and the validation list in the
module docstring).

Validation passed before anything below was computed (`fast_moments.py
validate --slow`):

- term counts equal the Fubini numbers 13, 75, 541, 4683, 47293 (k = 3..7);
- vectorized `J` equals `exact_finite_N.joint_trace_moment` on
  `E |Tr U^h|^2 = min(|h|, N)` (h = 1, 3, N-1, N, N+3, 2N) and on 180 random
  sum-zero tuples, k = 3..7, N in {5, 9, 12};
- full `E tr T^k` equals the naive engine at (k=2, N=7,9), (k=3, N=7,9,11),
  (k=4, N=7..15 odd, including the recorded values 53739, 190029, 519981,
  1201031, 2459255), (k=5, N=7), (k=6, N=7);
- the negation-symmetry shortcut equals the unreduced sum at (k=5, N=7),
  (k=6, N=5);
- `E tr T^1 = dN` and `E tr T^3 = 2N^4 - N^2` on the sweep range.

All integers are checkpointed in `exact_trTk_values.json` (lambda = 1; keys
`k -> N -> E tr T^k`) and `exact_trTk_values_lambda.json` (lambda = p/q
families computed at `N = q t`, `d = p t`; keys `p/q -> k -> N`).

## 2. Results at lambda = 1: the exact polynomials and the limits

Computed at every odd `N` in [5, 35] for k <= 6 (16 values each), and at odd
`N` in [5, PLACEHOLDER_K7_NMAX] for k = 7. Protocol: fit a degree-(k+1)
polynomial through the k+2 smallest grid points, demand exact integer
agreement at every remaining computed value, then check even `N` values not
on the fitting grid at all.

| k | E tr T^k (exact, all checked N) | m_k(1) | decimal |
|---|---------------------------------|--------|---------|
| 1 | N^2 | 1 | 1.0000000000 |
| 2 | (4/3)N^3 - (1/3)N | 4/3 | 1.3333333333 |
| 3 | 2N^4 - N^2 | 2 | 2.0000000000 |
| 4 | (13/4)N^5 - (31/12)N^3 + (1/3)N | 13/4 | 3.2500000000 |
| 5 | (101/18)N^6 - (115/18)N^4 + (16/9)N^2 | **101/18** | 5.6111111111 |
| 6 | (640/63)N^7 - (140/9)N^5 + (64/9)N^3 - (5/7)N | **640/63** | 10.1587301587 |
| 7 | PLACEHOLDER_K7_POLY | **PLACEHOLDER_K7_M** | PLACEHOLDER_K7_DEC |

Evidence, per k:

- **Regime start.** For every k the degree-(k+1) fit through N = 5..(2k+7)
  (odd) reproduces every other computed value exactly. No pre-regime point
  was observed: on this grid the polynomial form holds from N = 5 on.
- **Overdetermination.** k=5: fitted on 7 points, reproduced exactly at the
  9 remaining odd values N = 19..35. k=6: fitted on 8 points, reproduced at
  the 8 remaining odd values N = 21..35. k=7: PLACEHOLDER_K7_OVER.
- **Parity.** The same polynomials reproduce the directly computed even-N
  values N = 6, 8, 10, 12 for k = 2..6 (16 further exact checks;
  PLACEHOLDER_K7_EVEN). No odd/even quasi-polynomial split is present at
  lambda = 1 in this range.
- **Monte Carlo consistency** (control, not proof; CUE sampling at N = 41,
  d = 41). Evaluating the polynomials at N = 41:
  `E tr G^4/d = 3.248463` vs MC `3.2449 +- 0.0056` (-0.6 sigma);
  `E tr G^5/d = 5.607311` vs MC `5.597 +- 0.014` (-0.7 sigma);
  `E tr G^6/d = 10.149479` vs MC `10.12 +- 0.033` (-0.9 sigma);
  PLACEHOLDER_K7_MC

The moment sequence of the limiting spectral law of the lambda = 1 band Gram
matrix therefore begins

    1, 4/3, 2, 13/4, 101/18, 640/63, PLACEHOLDER_K7_M, ...

(m_1..m_4 as published in the source paper; m_5 onward computed here.)

**Not established / not attempted.** m_8(1) was not computed: with this
engine the k = 8 sweep needs roughly 10x the k = 7 per-class work on ~5x the
classes per N, an estimated 50+ CPU-hours for a validated fit, beyond this
session's budget. Nothing above proves the polynomial form for N outside the
computed range; the limit identification rests on the (heavily overdetermined,
exact) agreement on the computed grid.

## 3. The lambda structure of m_k(lambda)

`E tr T^k` was computed exactly for the families `N = q t`, `d = p t`
(so `lambda = d/N = p/q` exactly), `t = 1..12` (t = 1..10 or 11 for the more
expensive families), for the lambda values listed below; each family was
identified as a degree-(k+1) polynomial in `t` by the same fit-and-check
protocol (every family reproduced its 2-4 spare points exactly), and
`m_k(lambda)` is the leading coefficient divided by `q^k p`.

Exact values (`lambda_structure.py` re-derives this table from the JSON and
re-runs every check):

| lambda | m_2 | m_3 | m_4 | m_5 | m_6 |
|--------|-----|-----|-----|-----|-----|
| 1/6 | | | | | 87413/76545 |
| 1/5 | | | 10129/9375 | 2129/1875 | 1979282/1640625 |
| 1/4 | 49/48 | 17/16 | 1081/960 | 233/192 | 17851/13440 |
| 2/7 | | | | | 17726573/12353145 |
| 3/10 | | | | | 810809/546875 |
| 1/3 | 28/27 | 10/9 | 1489/1215 | 337/243 | 122882/76545 |
| 3/8 | | | | | 100963189/56623104 |
| 2/5 | 79/75 | 29/25 | 12439/9375 | 2939/1875 | 149912303/78750000 |
| 3/7 | | | | | 228493586/111178305 |
| 4/9 | | | | | 766424795/357128352 |
| 1/2 | 13/12 | 5/4 | 91/60 | 23/12 | 403967/161280 |
| 6/11 | | | 1706299/1054152 | 73392247/34787016 | |
| 3/5 | 28/25 | 34/25 | 197387/112500 | 200203/84375 | 49205704/14765625 |
| 5/8 | | | 46641/25600 | 461807/184320 | 1689869423/471859200 |
| 2/3 | 31/27 | 13/9 | 18871/9720 | 48019/17496 | 4945567/1224720 |
| 3/4 | 19/16 | 25/16 | 6361/2880 | 11387/3456 | 31751927/6193152 |
| 4/5 | 91/75 | 41/25 | 358141/150000 | 551191/150000 | 132881447/22500000 |
| 1 | 4/3 | 2 | 13/4 | 101/18 | 640/63 |

(Blank cells were not needed for any fit or check and were not computed.)

The data identify the following piecewise structure, with `J = floor(k/2)`
and one breakpoint at `lambda = 1/j` for each `j = 2..J`:

    m_k(lambda) = 1 + sum_{j=1..J} a_{k,j} lambda^{2j}
                  - sum_{j=2..J, lambda > 1/j}
                        (j lambda - 1)^{2j+1} * g_{k,j}(lambda) / lambda

with `g_{k,j}` a polynomial of degree `k - 2j`. Identified exactly:

| k | Wick piece (valid on lambda <= 1/J) | defect pieces (each active above its 1/j) |
|---|--------------------------------------|-------------------------------------------|
| 2 | 1 + lambda^2/3 | none |
| 3 | 1 + lambda^2 | none |
| 4 | 1 + 2 lambda^2 + (4/15) lambda^4 | j=2: (2 lam - 1)^5 * (1/60) / lam |
| 5 | 1 + (10/3) lambda^2 + (4/3) lambda^4 | j=2: (2 lam - 1)^5 * (1 + lam)/(36 lam) |
| 6 | 1 + 5 lambda^2 + 4 lambda^4 + (32/105) lambda^6 | j=3: (3 lam - 1)^7 * (1/2520) / lam; j=2: (2 lam - 1)^5 * (1/35 + (2/105) lam + (1/21) lam^2) / lam |

Fit-and-check bookkeeping (all matches are exact rational equalities, run by
`lambda_structure.py`):

- k=2, k=3: one-coefficient fits reproduce all 8 remaining lambda values,
  including everything above 1/2 (the defect is identically zero, consistent
  with the Wick/Gaussian computation being exact for k <= 3).
- k=4: Wick fitted on {1/5, 1/4}, reproduced at {1/3, 2/5, 1/2}; g fitted on
  {6/11} alone, reproduced at {3/5, 5/8, 2/3, 3/4, 4/5, 1} (6 spare).
- k=5: Wick fitted on {1/5, 1/4}, reproduced at {1/3, 2/5, 1/2}; g fitted on
  {6/11, 3/5}, reproduced at {5/8, 2/3, 3/4, 4/5, 1} (5 spare).
- k=6: Wick fitted on {1/6, 1/5, 1/4}, reproduced at {2/7, 3/10, 1/3};
  the j=3 defect fitted on {3/8}, reproduced at {2/5, 3/7, 4/9, 1/2}
  (4 spare); the j=2 defect fitted on {3/5, 5/8, 2/3}, reproduced at
  {3/4, 4/5, 1} (3 spare).
- Consistency across routes: the piecewise model evaluated at lambda = 1
  returns 13/4, 101/18, 640/63, equal to the independent lambda = 1 sweeps.
- Independent check of the Wick pieces: the superseded continuum Wick engine
  (`exact_moments.py`, a quadrature over Gaussian pairing patterns, no
  finite-N input) reproduces `1 + 2 lam^2 + 0.26667 lam^4` (k=4),
  `1 + 3.3333 lam^2 + 1.3333 lam^4` (k=5) PLACEHOLDER_WICK6 to its working
  precision, i.e. exactly the W_k identified here from finite-N integers.

Observed patterns worth recording (observations, not theorems):

- The Wick piece breaks exactly where `j = floor(k/2)` frequencies can
  saturate the band simultaneously (`lambda = 1/j`), which is where the
  Gaussian (Diaconis-Shahshahani) regime for joint trace moments ends; this
  is the same mechanism that made the Wick value 49/15 wrong at
  `m_4(1)` (RESULTS.md, entries 1-4).
- The first defect beyond `lambda = 1/j` is `-(j lambda - 1)^{2j+1} * 2 /
  ((2j+1)! lambda)` for even k = 2j: coefficient 1/60 = 2/5! at j=2,
  1/2520 = 2/7! at j=3.
- Everything is continuous at the breakpoints to high order (the defects
  vanish to order 2j+1), so finite-precision numerics near a breakpoint
  would never see this structure; exact arithmetic was load-bearing.

**Honest scope of the lambda claims.** The window forms are exact rational
identifications on the sampled lambda grids with the stated spare-point
counts; between sampled lambda values an additional breakpoint would go
unseen. The sampled grids are: 6 values in (0, 1/3], 5 in (1/3, 1/2],
7 in (1/2, 1]. The forms are conjectured, with this evidence, to hold on the
full windows; they are not proved anywhere, and for k = 7 the lambda
structure was not measured at all (only lambda = 1).

## 4. Files

- `fast_moments.py`: the optimized exact engine, validation suite, sweep and
  analysis CLI (this file computed every integer cited here).
- `exact_trTk_values.json`: all exact `E tr T^k` at lambda = 1.
- `exact_trTk_values_lambda.json`: all exact `E tr T^k` for the p/q families.
- `lambda_structure.py`: re-derives the m_k(lambda) table from the JSON and
  re-runs every lambda fit-and-check above.
- `exact_finite_N.py`: the naive reference engine (unchanged; the instrument
  the fast engine was validated against).

Produced 2026-08-17 in the `sine_gram` hunt; not committed by this session.
