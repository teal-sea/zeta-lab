# DESIGN: kernel-checking the Davenport–Heilbronn negative cell

Status: design only, nothing implemented, no compute run. Owner: Scholar, 2026-10-29.
Scope: turn the hardened ball LDL^T inertia result (`weil_propagation` §3.2, N = 64/128,
c in [30.617, 30.818]) into a statement whose algebraic core is kernel-checked, without
pretending the analytic enclosures are.

## What exists

The DH form is negative on every window c ≥ 30.617188, established by ball-arithmetic
LDL^T inertia at N = 64 and N = 128 on a half-integer grid, plus a nesting argument.
Grade: hardened (enclosure-carrying), not kernel-checked. Eigenvalues are float-grade;
the inertia is the hardened part.

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
   the Arb enclosure of its entries." That is the honest claim, and it is strictly stronger
   than today's float-grade eigenvector.

## Why the composite is worth having

The current record says "negative eigenvalue, eigenvalues float-grade, inertia hardened".
A kernel-checked rational certificate removes the float step between the inertia and the
direction: anyone can re-run `decide`/`norm_num` on the rational data and see the sign.
What it does not remove is trust in Arb, which is the same trust the rest of the lab's
hardened results already carry.

## Step 0, before any Lean

Find the smallest configuration where the cell is negative: sweep N in {8, 16, 24, 32} at
fixed c = 30.62 and 30.82, reuse the existing assembly code, and record the first N where
λ_min < 0 with margin. A 16×16 certificate is a 136-entry rational matrix; a 64×64 one is
2080 entries and may cost minutes per `norm_num` call. Price the Lean step at the smallest
N that works, not at N = 64.

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

- If no N ≤ 32 is negative at the cell's c, report that and stop: the composite claim then
  needs the 64-mode matrix and its price.
- If the rounded vector cannot keep a strict margin in rational arithmetic, report the
  required denominator growth and stop rather than loosening e.

## Out of scope

Formalizing Arb, the Bessel functions, or the nesting argument. Those stay hardened and
are cited, not re-proved.
