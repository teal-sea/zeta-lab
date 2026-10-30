# DESIGN: kernel-checking the Davenport–Heilbronn negative cell

Status: design only, nothing implemented, no compute run. Owner: Scholar, 2026-10-29.
Scope: turn the hardened negative cell of `weil_propagation/numerics/RESULTS.md` §3.2
(N = 256, c ≥ 30.617188) into a statement whose algebraic core is kernel-checked, without
pretending the analytic enclosures are.

*Corrected 2026-10-30 (review).* This file was pushed to `main` directly rather than
through a pull request. As first written it misread its source in three places, fixed
below: the cell at c ≥ 30.617188 rests on N = 256 (the N = 64 and N = 128 cells start at
30.818359 and 30.647461); the eigenvalues are already hardened (ball Rayleigh quotients
and Temple brackets), not float-grade, so a rational certificate re-grades the algebra,
not a float step; and the grid is a dyadic bisection, not a half-integer grid.

## What exists

The DH form is negative on every window c ≥ 30.617188, established by the hardened
N = 256 cell (bisection bracket 30.616211 to 30.617188, ball Rayleigh quotients, ball
LDLᵀ and Temple brackets) plus a nesting argument (Fact B, ordinary and unreviewed).
Grade: hardened (enclosure-carrying), not kernel-checked. The smaller cells start
higher: c ≥ 30.818359 at N = 64 and c ≥ 30.647461 at N = 128.

## What a kernel-check can and cannot cover

Three pieces, graded separately:

1. **Analytic enclosure (stays Arb, not Lean).** Every entry of the DH Gram matrix on a
   fixed span is a transcendental expression (Bessel/trigonometric values times exp/log of
   the window parameter). Arb produces, for each entry, an exact rational midpoint and a
   radius. No part of this is formalized; it stays a hardened enclosure with its own
   receipts, exactly as the existing cell does.
2. **Rational certificate (kernel-checked, pure algebra).** Let A be the rational
   midpoint matrix and e an exact rational bound on the spectral norm of the entry
   perturbation. Produce a rational vector w with
   `wᵀ A w / (wᵀ w) + e < 0`. In Lean this is a finite rational computation plus
   Cauchy–Schwarz: for any symmetric G with `‖G - A‖ ≤ e` one has
   `λ_min(G) ≤ wᵀ G w / wᵀ w ≤ wᵀ A w / wᵀ w + e < 0`.
   The kernel checks the arithmetic and the Rayleigh bound; it does not check that the
   true DH form is within e of A.
3. **Composite statement.** "The DH form has a negative direction on this window, modulo
   the Arb enclosure of its entries." That is the honest claim. Its algebraic step is
   kernel-checked where today it is hardened; its analytic step is unchanged.

## Why the composite is worth having

The current record already carries the negative direction in ball arithmetic (an
enclosed Rayleigh quotient below zero, and Temple brackets). A kernel-checked rational
certificate moves that algebraic step from hardened to kernel-checked: anyone can re-run
`decide`/`norm_num` on the rational data and see the sign.
What it does not remove is trust in Arb, which is the same trust the rest of the lab's
hardened results already carry.

## Step 0, before any Lean

Choose the cell by the size it forces. The recorded crossings c*(N) fall as N grows
(30.818, 30.696, 30.647, 30.629, 30.617 for N = 64 to 256), so a sweep of N ≤ 32 at
c = 30.62 is expected to be empty. The cell at c ≥ 30.617188 needs the N = 256 matrix, a
symmetric rational certificate of 32,896 entries; the N = 64 matrix (2,080 entries)
certifies only the weaker cell c ≥ 30.818359. Price `norm_num` on both before choosing,
and record which cell the certificate covers.

## Step 1, the rational certificate

Take the negative eigenvector from the Arb run, round it to rationals with a denominator
that keeps the Rayleigh quotient below `-e/2`, then verify the rounded vector in exact
rational arithmetic. If the eigenvector is too ill-conditioned to round, fall back to an
LDL pivot certificate: one negative pivot d_k with the preceding pivots positive, checked
by rational arithmetic on the Schur complements.

## Step 2, the Lean file

`Matrix` over ℚ, `w : Fin n → ℚ`, the quadratic form as a `Finset.sum`, `norm_num` for the
sign, and the Rayleigh/Weyl inequality as a small general lemma. No `sorry`, no floats,
`#print axioms` standard.

## Stop gates

- If the N = 256 certificate is too expensive for the kernel, report its price and
  either stop or certify the N = 64 cell, stated as c ≥ 30.818359.
- If the rounded vector cannot keep a strict margin in rational arithmetic, report the
  required denominator growth and stop rather than loosening e.

## Out of scope

Formalizing Arb, the Bessel functions, or the nesting argument. Those stay hardened and
are cited, not re-proved.
