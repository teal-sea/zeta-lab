# INTERFACE: bound_quad/

What this folder delivers to assembler/ and referee/ (BRIEF.md, "The bound
interface"). Derivation: `DERIVATION.md` s2. Outcome: `RESULTS.md`.

## `eps_quad.py`

- `eps_quad(c, N, nvec, S, Kmax) -> flint.arb`: an upper bound on
  ‖ΔT_nvec,exact − ΔT_stored‖₂ on the (2N + 1)-dimensional window space from
  every source except the mode truncation. **It is +∞ (`arb.pos_inf()`) on
  every stored build**, because source E2 (the projection taken in the inner
  product truncated to [−S, S]) has no bound (DERIVATION s2.3, Prop 3). A
  caller that forms ε = eps_trunc + eps_quad gets +∞, and a Weyl count below
  −ε is then 0 by construction, which is the honest reading: nothing is
  counted on the strength of this folder.
- `eps_quad_parts(c, N, nvec, S, Kmax) -> dict`: per source `E1` .. `E7`, an
  arb upper bound or `None` where the source does not close on that build.
  E1: window integral beyond the grid (Prop 2). E2: s discretization of the
  projection (always `None`). E3, E4, E5: w panels, tail series, mode data
  (always `None`, not bounded in the box). E6: QR and triangular solve
  (Prop 5; `None` on every N = 32 build). E7: remaining float64 rounding
  (Prop 6).
- `eps_quad_reasons(c, N, nvec, S) -> dict`: the reason for each `None`.
- `e2_obstruction(nvec, S, N) -> arb`: a lower bound on ‖X‖, the quantity a
  perturbation bound through the Gram needs below 1 (Prop 3).
- `kappa(c, N, S0)`, `e1`, `e6`, `e7`, `rho_rel_error(m, n, cond)`,
  `cond_enclosure(cond_rec, m, n)`: the pieces, arb at 128 bits.
- `upper_str(x, digits=4, lower=False)`: a decimal string at or above the
  upper end of the ball (at or below the lower end with `lower=True`).
- Constants: `BUILDS` (the eleven stored builds, S as passed to
  `delta_T_cells`), `CELLS`, `C_QR = 32` (A6), `C_CX = 4` (A7),
  `ASSUMPTIONS` (which of A1 .. A9 each piece uses).

Reads (read-only): `checker/checker_ts_snapshot.json` (`units[..].diag`:
cond_Fz, cond_Fb, gram_z_offI; `T_S` rows for the max entry used by E7) and
`bound_quad_gram.json` (this folder). Imports nothing from two_adic/ at
run time (`kmax_for` is restated; a test checks it against two_adic/'s).

## `eps_quad.json`

A list of 33 entries, one per (c, stored build), c ∈ {2.2, 2.5, 2.9}, with
the interface keys `c, N, nvec, S, Kmax, eps_upper, grade, assumptions` and:

- `eps_upper`: **null on every entry**; `why`: the E2 reason with this
  build's lower bound on ‖X‖;
- `blocking_step`: the step that does not close (E2), read by
  assembler/'s loader;
- `parts_upper`: per source, a decimal string at or above the arb upper end,
  or null; `parts_reasons`: why each null source does not close;
  `parts_assumptions`: which numbered assumptions each piece uses;
- `e2_obstruction_lower`: a decimal string at or below the lower end of the
  lower bound on ‖X‖;
- `s_nodes`: the stored s-grid size.

Regenerate: `PYTHONPATH=<worktree> <venv python> hunts/weil_propagation/c4_s2/bound_quad/eps_quad.py`
(seconds). `test_json_is_what_the_module_computes` fails if the file and the
module disagree.

## `run_bound_quad.py`, `bound_quad_gram.json`

Float64 measurements (measured grade) at (80, 1200) and (80, 1600) with the
stored route's own ingredients: extreme eigenvalues of G_S^z and G_S^b,
‖G_S^z − I‖, leverage sums (A5), and the probe ‖M_∞(G_S) − M_∞(I)‖₂ per
(c, N). About 2 minutes on an idle laptop (536 s wall for (80, 1200) at a
load average near 70).
