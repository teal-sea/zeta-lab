# RESULTS: `gabcke_remainder`

**Status: opened. The remainder is not proved.**

## What is checked

Satz 2.1.1's recursion for `λ_n` matches the seven values printed on pages
19–20 of Gabcke's 2015 PDF. Lean's kernel accepts `lambda_printed` and
`lambda_divides` in `lean/Coefficients.lean` with no axioms, on toolchain
`leanprover/lean4:v4.35.0-rc2`. The Python mirror in `coefficients.py` checks
the same seven values.

## What is not checked

Satz 3.2.2, the explicit remainder bounds, is not proved. No height past the
existing kernel-checked strip is claimed. The coefficient match is not that
bound.

## Kill conditions

None fired. The recursion agreed with the printed values, and the kernel did
not take an external computation as an axiom.
