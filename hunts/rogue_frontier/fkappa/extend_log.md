# Extension log: corrected C_{kappa,i} beyond i = 20

Session date: 2026-08-17. Owner: extension session (extend_*.py,
coefficients_ext.json). Mode: corrected, assembly: coefficient (eq 10.1)
throughout. All arithmetic exact (Fraction). Nothing here is committed to
git by this session.

Targets:
(a) kappa = 2 row to i = 32 or as far as compute allows; per-term bound
    1 - 2 sum_{i<=I} C_{2,i}/((i+1)(i+2)) and |C_{2,i}|^{1/i}.
(b) kappa = 3 row to i = 28+; does the partial bound turn around, and does
    |C_{3,i}|^{1/i} show a limit above or below 1.
(c) diagonal C_{i-2,i} past 20.
(d) structure guessing on the extended corrected kappa = 2 row and diagonal.

Checkpoint discipline: every computed coefficient is written to
coefficients_ext.json immediately (atomic replace) as computed.

## Timeline

- [start] Read RESULTS.md, bian_engine.py, closed_form.py, analyze.py,
  coefficients.json (both modes complete to i = 20). Existing timing:
  corrected level 20 (all six kappa rows + both diagonals, both
  assemblies) took 760 s; growth ~2.5-3.5x per level. Extending the full
  table to 32 with the stock engine is infeasible; a per-row engine plus
  optimizations is required. Profiling next.
