# MISSION: C4 first instance, S = {∞, 2}, semilocal trace remainder on c ∈ [2, 3)

Opened 2026-09-23 on branch `teal-sea/weil-c4-s2`, based on
`teal-sea/weil-propagation-theory` at f723209. Approved by the operator on
2026-09-23.

**This mission inherits `hunts/weil_propagation/MISSION.md` in full** (rules,
kill conditions, compute limits, the reserved word, no claim about RH) and
does not restate it. What follows adds scope, gaps, folders, controls and the
definition of done.

## Scope

Build the first instance of candidate C4 (theory `RESULTS.md` §7.2) for
S = {∞, 2} on windows ℓ = log c with c ∈ [2, 3), and measure its remainder.

- **Q** is the Weil form of theory §0 on these windows. Only the atom n = 2
  is active (log 2 < ℓ < log 3), so Q = Q_∞ − √2 log 2 · g(log 2), with
  Q_∞ = P + A.
- **T_S(f) = Tr(ϑ_S(f) Π_S ϑ_S(f)*)**, with the product-ball projection
  Π_S = S_∞ ⊗ P_2 + 1 ⊗ (1 − P_2) of theory §7.3 item 2.
  *Amended 2026-09-24 by the coordinator:* this product-ball Π_S defines no
  operator on X_S and has infinite trace there (cutoff/, two_adic/), so T_S
  was built on the module form (CCM arXiv:2310.18423 Thm 4.6); see
  `c4_s2/RESULTS.md` line 1. The text above is kept as approved.
- **R_S := Q − T_S.** C4 says Q ≥ T_S − (a remainder of bounded rank). The
  operational content measured here is the inertia of R_S (how many negative
  eigenvalues, and whether that count is stable in N) and its lowest
  eigenvalues, cell by cell.

The conclusion (positivity on c ∈ [2, 3)) is already known: Zhu,
arXiv:2608.24827 (support ≤ 1.6). This instance tests the **mechanism**, not
the conclusion. Connes-Consani arXiv:2006.13771 Thm 6.11 is the S = {∞} case
(c < 2) and is the calibration target for anything archimedean.

**Notation clash, fixed here:** in this mission f is the window function and
g = f ⋆ f̃ its autocorrelation, as in theory §0. Connes-Consani's g is our f.

**Function class.** C4 as stated in theory §7.2 carries vanishing conditions
on the transform. kernel/ states from the source (arXiv:2006.13771 Thm 6.11)
exactly which conditions are imposed; checker/ reads the same source
independently. All matrices are delivered on the full (2N+1)-dimensional
space; the class restriction is applied afterwards as a projection onto the
constraint subspace, and results are reported on both.

## The shared basis and cells (interface contract)

Every matrix in this mission is a Hermitian (2N+1) × (2N+1) mpmath matrix on
the CCM basis U_n(y) = L^{−1/2} exp(2πiny/L) of L²([0, L]), n = −N … N,
L = log c, exactly as in `hunts/rogue_frontier/weil_trunc/SOURCE.md` and
`galerkin.py` (equivalently V_n on [λ^{−1}, λ] with du/u, λ = √c). Index 0 of
a delivered matrix is n = −N. A quadratic form F is delivered as the matrix
M with F(f) = v* M v for f = Σ v_n U_n.

- Cells: c ∈ {2.2, 2.5, 2.9}; N ∈ {8, 16, 32}. Calibration cells for the
  archimedean part only: c ∈ {1.5, 1.9} (S = {∞}).
- Working precision: dps 40 unless a stated entry needs more; the dps used is
  recorded with every number.
- Each module exposes a function `(c, N, dps) -> matrix` and writes its cell
  values to a JSON file in its own folder with named keys. Each folder has an
  `INTERFACE.md` naming the functions, their conventions and their JSON keys.

## The three gaps and who owns them

The prior attempt (cabinet run `req-c4-s2-remainder/a1`, rejected by review)
built only the split of Q and stopped at these three gaps. Its code is input,
not evidence.

| folder | gap | delivers |
|---|---|---|
| `kernel/` | (a) S_∞, the archimedean Sonin projection, has no closed kernel on these windows (Connes-Consani s6 uses numerically identified prolate data) | S_∞ on window functions in a Galerkin-computable form; `T_inf_matrix(c, N, dps)`, the S = {∞} trace term, calibrated against CC Thm 6.11 at c ∈ {1.5, 1.9}; the representation of S_∞ that two_adic/ composes with |
| `two_adic/` | (b) the action of P_2 on window functions through E_S is not in a form that yields matrix entries | P_2 through E_S on the shared basis; `T_S_matrix(c, N, dps)` for S = {∞, 2}, product-ball cutoff, taking the local data at 2 and the archimedean type as inputs |
| `cutoff/` | (c) the passage from the product-ball cutoff to the global module cutoff \|x\|_S (Connes arXiv:2602.04022 eq. (22)) is unproved | a proof, a bound, or the gap stated exactly; if feasible, the module-cutoff variant or the difference on the same cells |
| `checker/` | independent verification and the kill-controls | its own Q matrix, the assembly R_S = Q − T_S, inertias and lowest eigenvalues per cell, the (U-S) gate, the controls below |

**Ownership of the pieces nobody else owns:** checker/ owns Q (an independent
implementation, calibrated against `zeta.weil.weil_functional` on at least
two unrelated test-function families) and the R_S assembly and its numbers.
two_adic/ owns the assembly of T_S from S_∞ and P_2. The coordinator writes
only this file and the header of `c4_s2/RESULTS.md`.

**Independence of the checker.** checker/ writes and commits its own tests of
R_S = Q − T_S from theory §0 and §7 before it reads any code in kernel/ or
two_adic/. The coordinator routes their output to it only after that commit
is in `git log`.

## Kill-controls (owned by checker/)

On c ∈ [2, 3) only n = 2 is in the window, and Epstein (1,1,6) has
Λ_Q(2) = 0, so a window-only test cannot see the failures that theory §7.1
names. The controls are therefore defined on the construction's inputs:

1. **(U-S) gate, exact arithmetic, n ≤ 200** (rational coefficients in the
   log-prime basis, as theory check K and numerics `us_check.py`). As a
   function of c it must reject Epstein (1,1,6) from n = 6 (composite atom)
   and from n = 8 (s₃(2) = 6 > 2), reject W_a (a = 1/4) from n = 2
   (s₁(2) = 2^{1/4} + 2^{−1/4} > 2), and accept ζ and Dedekind ζ_{Q(√−23)}
   throughout.
2. **The construction refuses non-unitary data.** The 2-adic local factor
   uses the whole tower s_k(2), not only atoms inside the window. The
   T_S builder, given W_a's data at 2 or Epstein's 2-adic tower, must refuse.
   Any code path that returns a trace term for W_a or Epstein data is a
   defect.
3. **Positive control: Dedekind ζ_{Q(√−23)}** (degree 2, 2 split so
   s_k(2) = 2, archimedean factor Γ_ℂ). It exercises the construction only if
   kernel/ and two_adic/ accept degree-2 unitary data and the Γ_ℂ archimedean
   type. If they build ζ only, the checker records "positive control not
   exercised" and says why. It does not fabricate a Dedekind run.
4. **Lesion (optional, labelled as such):** bypass the gate, build T_S with
   W_a's non-unitary data, and report whether T_S stays positive
   semidefinite and how the inertia of R_S moves.

## Limits

- Python: `PYTHONPATH=<worktree root> /Users/thomas/zeta-lab/.venv/bin/python`.
  This worktree has no `.venv`.
- Local runs under 10 minutes and a few GB each; four workers share a 16 GB
  laptop, so pytest runs with `-n 2` at most. Anything larger becomes a CI
  proposal with an estimate in the worker's `RESULTS.md`.
- Provers: AXLE only (`axle` on PATH, runs remotely). No `lake build`.
- Each worker writes only in its own folder. Nobody edits `zeta/`,
  `ontology/`, `harness/`, another worker's folder, this file, or
  `c4_s2/RESULTS.md`. Nothing is pushed.

## Done

Each worker folder has a committed `RESULTS.md` whose statements carry
their rung on the `AGENTS.md` ladder (weakest step governs), with every
stated number pinned by a test in that folder, and an ALIGNMENT s5 status
(refuted, obstructed in a restricted class, unresolved, or paused by
allocation). The mission is done when `c4_s2/RESULTS.md` is committed and its
first five lines say, each graded:

1. whether T_S was built;
2. what R_S measures on these cells;
3. how the kill-controls came out;
4. what is still open.

## Follow-up, 2026-09-24: the compute proposals on Modal

*Added by the coordinator.* The operator approved running the two compute
proposals of `c4_s2/RESULTS.md` line 4 (a) and (b) on Modal, with a hard cap
of 25 USD: no GitHub Actions, no push, no workflow file. A fifth folder,
`modal/`, runs them and records outputs and cost only (its `BRIEF.md`). The
grading stays with the owners: checker/ re-grades the R_S counts from the new
N = 32 rows, and two_adic/ grades its accuracy run (s7b), each in its own
folder. The Limits above still hold for everything run on the laptop; Modal
is the only place the new runs may execute.
