# cutoff/ interface

Gap (c): product-ball cutoff against the module cutoff, S = {∞, 2}. This
folder builds no trace term. It holds the checks behind `RESULTS.md`.

## Functions (`cutoff.py`)

| function | returns | convention |
|---|---|---|
| `two_adic_facts(K)` | dict of exact booleans and ranks | radial functions on Q_2 in the ball basis b_k = 1{\|x\|_2 ≤ 2^k}, \|k\| ≤ K; self-dual measure, F(b_k) = 2^k b_{−k} |
| `BallModel(K)` | exact sympy model | `ball_mult(r)` is multiplication by 1{\|x\|_2 ≤ 2^r}; r = 0 is the closed ball Z_2, r = −1 the open ball {\|x\|_2 < 1} |
| `in_product_ball`, `in_module_ball`, `act`, `orbit_count_product_ball`, `orbit_count_formula` | exact | a point with x_2 ≠ 0 is (x_inf, v), v = ord_2(x_2); the S-unit 2^n acts by (x_inf, v) → (2^n x_inf, v + n) |
| `eta_theta_check(s_list, dps)` | list of dicts | CCM arXiv:2310.18423 (47) and (57) at S = {∞, 2}, f = exp(−πx²), two routes |
| `m_of_s(s)` | mpf | \|1 − 2^{−1/2−is}\|² = 3/2 − √2 cos(s log 2) |
| `kappa_exact()` | sympy | 17 + 12√2 = max m / min m |
| `comparison_lemma_trials(...)` | dict | finite-dimensional sanity check of the RESULTS s4 lemma (numpy, float) |
| `shift_form_matrix(c, N, dps)` | Hermitian (2N+1)×(2N+1) mpmath matrix | shared basis U_n(y) = L^{−1/2} e^{2πiny/L} on [0, L], L = log c, index 0 ↔ n = −N; v*Hv = Re ∫ f(y) conj f(y − log 2) dy |
| `atom_matrix(c, N, dps)` | same shape | √2 log 2 · H, the n = 2 atom W_2; the Weil form is Q = Q_∞ − W_2 on c ∈ (2, 3) |
| `galerkin_prime_block(c, N, dps)` | same shape | −W_2 read from `hunts/rogue_frontier/weil_trunc/galerkin.py` (read-only import) |
| `shift_form_spectrum(c, N, dps)` | dict | eigenvalue counts of H above 1/4 and below −1/4 |

## JSON (`cutoff_cells.json`, written by `python cutoff.py`)

- `two_adic_facts`: output of `two_adic_facts(5)`.
- `eta_theta_check`: rows with keys `s`, `eta_rel_dev`, `theta_rel_dev`,
  `ratio_theta_over_eta` (string of a complex), `m_of_s`; dps 30.
- `kappa_exact`: string.
- `comparison_lemma_trials`: `kappa`, `ratio_min`, `ratio_max`, `trials`.
- `shift_form_cells`: rows with `c`, `N`, `dps` (40), `dim`,
  `n_above_quarter`, `n_below_minus_quarter`, `max_eig`, `min_eig`,
  `collar_fraction_times_dim` = (2N+1)(L − log 2)/L.
- `atom_two_route_dev`: `"<c>_<N>"` → max entrywise |atom_matrix + galerkin_prime_block| at dps 40.
- `theta_gram_atom_dev`: rows `c`, `N` (2), `dps` (30), `gram_vs_H` = max |Gram(theta_S) − (3/2 I − √2 H)|,
  `prime_block_vs_gram` = max |galerkin prime block − log 2 (Gram(theta_S) − 3/2 I)|; Gram by direct quadrature
  (`theta_gram_quadrature(c, N, dps)`).

Runtime: `python cutoff.py` about 100 s on the laptop; the tests about the same with `-n 2`.
