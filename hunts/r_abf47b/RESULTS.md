# Hunt R-ABF47B Results

## 1. Calibration
- Installed from `hunts/r_044dd2/requirements-solver.txt` successfully.
- Re-ran `hunts/r_044dd2/audit.py` on `artifacts/orbit18-support-07.json`: Passed (`verified_support_survivor: true`).
- Re-ran `hunts/r_044dd2/audit_laurent.py` on `orbit18-laurent-01.json` (and `orbit18-support-01.json`): Passed (`verified: true`).
- Re-ran the 6x3 gate in `hunts/r_31b6c1/probe.py`: Passed (produced `[1]` in ~0.2 seconds).
- Reproduced the cap-3 residual 4,500 and cap-4 residual 4,216 via `polynomial_sieve.py`.

## 2. Redundancy of the 57 Pair Orbits
The inherited first step from R-31B6C1 proposed scaling the sparse algebraic sieve using the 57 exact $H \times S_2$ pair-orbit skeletons. However, since $S_8$ acts transitively on perfect matchings, every triple of monochromatic matchings $(M_a, M_b, M_c)$ can be mapped by $S_8$ to one starting with $M_0$. The subgroup of $S_8 \times S_3$ preserving $M_0$ (allowing color swaps of the remaining two) is exactly $H \times S_2$. Thus, the 57 pair orbits merely refine the 31 triple orbits. They add no new branches that the 31 do not already cover. Scaling the sieve to 57 skeletons is therefore redundant.

## 3. Bounded Unrestricted Computation
I chose option (2a): exact Groebner computation on the Support-7 restricted system (138 variables, 6561 equations with common support-torus factors removed). 

I ran `sympy.groebner` with a `grevlex` ordering on this system.

### Pricing details:
- **Solver**: `sympy.groebner`
- **Ordering**: `grevlex`
- **Variables**: 138
- **Equations**: 6561
- **Wall clock**: 300.03 seconds
- **Peak memory**: 32.59 MB
- **Stopped at**: Timeout (5 minutes)

The exact computation in `sympy` did not complete within the 5-minute allocation. A compiled characteristic-zero backend or sharper structural constraints are required.

