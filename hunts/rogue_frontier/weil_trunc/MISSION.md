# weil_trunc: replication and rigorization of the CvS/CCM truncated Weil form

A sub-study of `hunts/rogue_frontier/` (its `MISSION.md` and HuntSpec govern
here). Opened 2026-08-17.

## Question

Two 2026 postings by A. Groskin (arXiv:2605.20224, arXiv:2607.02828) report
high-precision numerics and two finite theorems about the Connes-van Suijlekom
/ Connes-Consani-Moscovici Galerkin truncation of the Weil quadratic form,
whose ground state approximates the Riemann zeros and whose convergence as the
prime cutoff grows is an open question posed by Connes (arXiv:2602.04022, s6).
This study asks:

1. Do the printed numbers replicate under a fully independent implementation
   built only from the sources' definitions?
2. Can the smallest eigenvalue be *enclosed* (ball arithmetic, Arb backend,
   `zeta.rigor` conventions) over a (c, N) grid, so that its sign and
   magnitude carry rigorous error bars rather than float trust?
3. What convergence law err(c, N) do the ground-state zeros follow against
   gamma_1..gamma_k, measured on our grid?
4. Battery discipline: does the same pipeline, run with Davenport-Heilbronn
   data in place of zeta's, look any different? If the truncation is equally
   well-behaved for an RH-violating rival, the truncation's zeta behaviour
   distinguishes nothing, and measuring that is the finding.

## Scope

May write: `hunts/rogue_frontier/weil_trunc/**` only. Reads anything.
Modifies no core module. Commits nothing.

## Rules inherited

- Nothing here is a result; grades are *measured* or *hardened* only.
- The word owned by `zeta/rigor.py` is not used in this directory at all
  (`tests/test_hunt_probe_discipline.py`); we say "enclosure-checked".
- Every claim against the sources cites the source equation or table.
- Oracles: mpmath (`zetazero` via `zeta.zeros.first_n_zeros`), python-flint
  (Arb) ball arithmetic, `zeta.epstein` for the DH rival, direct quadrature
  cross-checks of every closed form used.

## Files

- `SOURCE.md`     what the sources actually say (step 0/1 record)
- `galerkin.py`   the independent implementation (mpmath float route)
- `enclosures.py` the ball-arithmetic route (python-flint / Arb)
- `run_*.py`      experiment drivers; JSON outputs land beside them
- `RESULTS.md`    findings, tables, grading, caveats
