# sine_gram — exact spectral moments of the band Gram matrix of the sine process

Status: ACTIVE. Opened 2026-08-17. Nothing here is a result until it survives
the campaign's destruction stages; grades follow the repository ladder.

## The object

For the sine process of unit density and band-width `0 < lambda <= 1`, let
`G_ij = K_lambda(x_i - x_j)`, `K_lambda(x) = sin(pi lambda x)/(pi x)`, and
`d = lambda N`. The normalised spectral moments

    m_k(lambda) = lim_N E tr G^k / d

are the quantities the 10 August 2026 paper ("more than two thirds", §7.5(f))
uses through its Christoffel-function bound: `m_k(1) = 1, 4/3, 2, 13/4` for
`k = 1..4` are stated there, and each additional pair of moments sharpens the
conditional ladder built on the hypotheses HL*(k0, lambda).

## What happened so far (chronological, kept as the record of method)

1. A quick Wick-pairing engine (`exact_moments.py`) produced
   `m_4(1) = 49/15`, disagreeing with the paper's `13/4`. Per the certainty
   ladder the first inference was a defect on our side.
2. A CUE Monte Carlo at `lambda = 1` exactly (`N = d = 41`, 6000 samples)
   gave `m_4 = 3.2449 +- 0.0056`: consistent with `13/4` (0.9 sigma),
   inconsistent with `49/15` (+3.9 sigma).
3. The decisive route (`exact_finite_N.py`): at finite `N` the circular model
   is exactly computable in integer arithmetic. `E prod_j Tr U^{h_j}` over
   CUE(N) reduces, through the determinantal correlation functions and the
   Dirichlet kernel, to lattice-point counts `max(0, N - spread)` per
   permutation cycle. No floats, no truncation, no Wick approximation.
   Validated: `E |Tr U^h|^2 = min(|h|, N)` for all tested `h` including
   `h > N`; `k = 3` gives exactly `E tr G^3/d = 2 - 1/N^2` and extrapolates
   to the paper's `2`.
4. Exact values for `k = 4`, `N = 7..15` odd, Lagrange-extrapolated in `1/N`
   from both ends: `3.2499827` and `3.2499630`. **The paper's 13/4 stands;
   the Wick engine was wrong.** Diagnosis: the Gaussian (Diaconis-
   Shahshahani) regime for joint trace moments requires total positive
   frequency at most `N`; at `lambda = 1` the two-pair patterns leave that
   regime, exactly where `k = 4` first differs from `k <= 3`.
   `exact_moments.py` is retained as a cautionary artifact and is superseded
   by `exact_finite_N.py`.

## Files

- `exact_finite_N.py` — the exact engine (integer arithmetic; the instrument
  of record for this study).
- `mc_moments.py` — CUE Monte Carlo control.
- `position_space.py` — independent graph-integral machinery (B-splines /
  cycle space); check on individual terms.
- `exact_moments.py` — the superseded Wick engine, kept with its defect
  documented above.

## Measured so far, and the immediate programme

Monte Carlo at `lambda ~ 1` (naive, finite-size uncorrected):
`m_5 ~ 5.6`, `m_6 ~ 10.2`. The literature (as surveyed today) stops at
`m_4`. Programme:

1. Exact `m_k(1)` for `k = 5, 6, 7, 8` via the exact engine plus
   quasi-polynomial identification in `N`, cross-checked by Monte Carlo and
   by the graph route where feasible.
2. The same as polynomials in `lambda` (the band constraint enters only
   through the spread counts, so the `N`-quasi-polynomials carry `lambda`
   as the band ratio `d/N`).
3. The Christoffel function `Lambda_m(0)` of the limiting spectral measure
   from moments `m_0..m_{2m}`: each new pair of moments prices the next
   HL*-type hypothesis in the source paper's conditional ladder. New
   conditional constants, stated as arithmetic consequences of hypotheses
   the paper already names.
4. Identification attempt on the limiting spectral law of the
   `lambda = 1` sine-Gram matrix (moment sequence 1, 4/3, 2, 13/4, ...),
   plus a novelty search for it in the random-matrix and time-frequency
   (prolate/Landau) literature.
