# checker/ INTERFACE

Phase 1 (independent of kernel/ and two_adic/, which were not read).

## Functions

| module | function | returns |
|---|---|---|
| `checker_q.py` | `Q_matrix(c, N, dps)` | the Weil form Q of theory s0 on the shared basis: real symmetric (2N+1) x (2N+1) mpmath matrix, index 0 is n = -N, F(f) = v^* Q v |
| `checker_q.py` | `q_parts(c, N, dps, method="gl", with_error=False)` | dict with the blocks `"pole"`, `"arch"`, `"prime"`, `"Q"` (and `"quad_err"`) |
| `checker_q.py` | `q_of_w(w, D, c, dps, ...)` | Q of a single function given its symmetrised correlation w = g(x) + g(-x) and D = w(0) - w(x) |
| `checker_q.py` | `transform_rows(c, N, dps)` | rows r with r . v = int f, int f e^{-y/2}, int f e^{+y/2} (keys `zero`, `minus`, `plus`) |
| `checker_q.py` | `constraint_basis(rows, dim, dps)`, `compress(M, B, dps)` | orthonormal basis of {r . v = 0} and B^* M B |
| `checker_props.py` | `class_bases(c, N, dps)` | bases of the reported spaces `full`, `minus`, `minus_zero`, `plus_zero` |
| `checker_props.py` | `cc611_margins(Q, T_inf, c, N, dps)` | Connes-Consani Thm 6.11 margins in the mission basis |
| `checker_gate.py` | `run_gate(n_max=200)` | exact (U-S) events per object; `accepts_window(events, c)`, `accepts_places(events, c)` |
| `checker_glue.py` | `T_inf`, `T_S`, `T_S_places`, `T_S_with_data` | the seam to kernel/ and two_adic/; raise `NotRouted` in phase 1 |

c may be given as a decimal string ("2.9"); it is parsed at the working
precision. A float c is rounded to 53 bits first, which moves Q by about
1e-15 (observed while testing, so pass strings).

## Conventions

- Q is theory s0 (Zhu arXiv:2608.24827 eq. (2)-(3)) with f the window
  function and g = f * f~ its autocorrelation. Only n = 2 is an atom on
  c in [2, 3); the prime block is -(log 2 / sqrt 2) K(log 2), which is
  -sqrt(2) log 2 g(log 2) for real f.
- The reported function classes. `minus`: g-hat(-i/2) = 0 in Connes-Consani's
  convention (their (22), F(g)(s) = int g(v) v^{-is} d*v), which in the
  mission basis is int_0^L f(y) e^{-y/2} dy = 0. `minus_zero`: that and
  g-hat(0) = 0, i.e. v_0 = 0. `plus_zero`: the reflected class
  (int f e^{+y/2} = 0 and v_0 = 0).
- **A discrepancy in the source.** Connes-Consani arXiv:2006.13771 Thm 6.11
  (p. 48) imposes g-hat(-i/2) = 0 and carries the remainder c |g-hat(0)|^2,
  c = 4 gamma / log 2, gamma ~ 2.94355 (Lemma 6.10). Their Theorem 1 in the
  introduction (p. 2) states vanishing at +i/2 and 0. The reflection
  y -> L - y exchanges the two classes and leaves Q invariant. It leaves T_inf
  invariant if the Fourier transform preserves Sonin's space and turns theta(g)
  into theta(g(1/.)); that was not verified from the source here, so both
  `minus_zero` and `plus_zero` are reported.

## JSON: `checker_q_cells.json`

`cells[c]` for c in {1.5, 1.9, 2.2, 2.5, 2.9}:
`full_N{N}_dps{dps}` (three lowest eigenvalues of Q), `minus_N{N}_dps40`,
`minus_zero_N{N}_dps40`, `quad_err_dps40`, `galerkin_maxdev_N32_dps40`,
`drift_40_60_N32`, `atoms`. `gate`: the output of `run_gate()`.
Numbers are decimal strings (25 significant digits).
