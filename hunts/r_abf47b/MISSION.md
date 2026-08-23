# Mission: Unrestricted Groebner Basis on Support-7 Restricted System

## Huntspec
- Target: `teal-sea/zeta-lab`
- Branch: `hunt/r-abf47b`
- Budget: 60 minutes
- Goal: Run exact ideal membership / Groebner basis on the Support-7 restricted system (138 variables).

## Bounded unrestricted computation (Option 2a)
I will compute the Groebner basis of the 6561 polynomial equations restricted to the Support 7 torus (with common support-torus factors removed). First, I will verify the system by reproducing the cap-3 residual 4,500 and cap-4 residual 4,216. Then, I will construct the system using `sympy` with 138 variables and a `grevlex` ordering. If it does not complete within 20 minutes, I will interrupt it and price where it stopped (wall clock, peak memory, solver: `sympy.groebner`, ordering: `grevlex`).
