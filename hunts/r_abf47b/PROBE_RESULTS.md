# Hunt R-ABF47B: calibration rerun of R-31B6C1's probe

> **Retitled on landing, 2026-10-21.** `probe_6x3.py` wrote this file. It is a copy of
> `hunts/r_31b6c1/probe.py` with only its output paths changed, run by this hunt
> (Hunt #140, `r_abf47b/`) as a calibration gate. The copy carried the header "Hunt
> R-31B6C1 Results", so the file read as Hunt #74's record, which is
> `hunts/r_31b6c1/RESULTS.md`; the script's header string now writes the title above.
> The body below is the run's output, unchanged. Its `[1]` results hold on the
> 8-variable H x S2 symmetric quotient only. See `RESULTS.md`, "Audit correction",
> part C.

## Calibration Gate (6x3)
The 6x3 system was evaluated on the 8-variable H x S2 quotient. Groebner basis completed in 0.16s and returned `[1]`, confirming the no-complex-witness verdict.

## 8x3 System
The variables were confirmed to be 252 (28 edges x 9 colorings). The 57 H x S2 pair orbits were evaluated in the working quotient.
- Generator count: 57
- Distinct monomial count (in quotient): 8
- Degree profile: all 12

## Pricing
- Solver: sympy.groebner
- Configuration: reduced ideal (8 edge-color-orbit variables)
- Wall clock: 0.81s
- Peak memory: 63.50 MB
- Stopped at: Completed
- Result: [1]
