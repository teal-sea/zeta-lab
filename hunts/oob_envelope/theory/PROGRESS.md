# PROGRESS: theory worker, hunt oob_envelope

STATUS: holding, no compute. RESULTS.md now cites the referee's final REVIEW.md (b65ef69) per result, with no change of ladder grade (every proof stays an ordinary derivation, none kernel-checked). Earlier referee repairs: b447f0d.

Branch `teal-sea/oob-cert-theory`. Writes only in `hunts/oob_envelope/theory/`.
Brief: `theory/BRIEF.md`. Output: `theory/RESULTS.md`.

## Caveats for the referee (reading only, 2026-09-27)

Own text (theory RESULTS.md at 9f5bbc3):

1. **Sector mismatch in §1.7.** Theorem 1′ and the numerics work on real even
   f; Propositions 1.2 to 1.4 are written on complex W_L. The chain
   T_op ≥ T′_op ≥ T_res holds sector by sector with the same proofs, but the
   last step T_res ≥ 2π e^{λ_max(P)} on the even sector needs
   sup σ_ess(P restricted to even functions) = λ_max(P), which is not
   written. Sketch: P commutes with x ↦ −x and preserves positivity, so a
   nonnegative near-top vector on a finite piece of a component and its
   reflection combine into an even vector with the same Rayleigh quotient;
   then modulate by cos(τ_k x), whose cross terms vanish by Riemann–Lebesgue.
2. **Definitions in Proposition 1.3.** R′ and B_T are written as Q minus a
   tail integral, which is ∞ − ∞ when ∫|F|² log(2 + |t|) = ∞. Read them as
   defined by their bounded-symbol forms: R′ by its second expression, B_T by
   the symbol Ψ_L − log(|t|/T)_+, which is bounded. The inequalities then hold
   for every f, and ≤ Q is trivial when Q(f) = +∞.
3. **The bracket in §1.7.** "R_{0,150} ⪰ 0 on the whole window" cites only
   Zhu §5.5 (a), which is the even sector; his odd sector at T# = 150 is §6.2.
   On the even sector alone, T_res(0.8) ≤ 150 follows from §5.5 (a). Both are
   his unrefereed computer-assisted results.
4. **Overstatement in the §1.7 consequences.** "A better joint H helps only
   where the envelope is the binding height" is too strong. Proposition 1.3
   only says no H goes below T_res. A better H can still lower T_op(H) toward
   T′_op, and it raises λ_min at fixed T#: at L = 0.8, T# = 200 the numerics
   lane has λ_min ∈ [1.02e-17, 1.028e-17] with H = 0 (enclosure-carrying,
   their line 5) against 1.42e-17 with per-prime H (measured, N = 200).

Numerics RESULTS.md (read with git show at c53d379, nothing re-run):

5. **Scope is right.** The claim Q ≥ 1.158e-17 ‖f‖² is for real even f only,
   graded candidate because its step d is my self-reviewed Theorem 1′. It is
   consistent with K1 and with the monotonicity of Proposition 1.2 (measured:
   2.0e-18 at T# = 65, 1.16e-17 at 100, 1.42e-17 at 200). No contradiction
   with Propositions 1.2 to 1.4.
6. **For the referee to confirm in the step-e budget** (not errors found):
   (a) the pole vector p of the rank-one term 2pp^T is not in the listed
   quadrature budget; (b) whether the entry bound behind ε_D and ε_B carries
   the factor (1/π)·T# from integrating over [0, T#], which Zhu's printed §4
   row bound lacks (RESULTS §1.5 (d)); immaterial at 3e-44 against 1e-17, but
   a correctness item; (c) the envelope bound and the assembled matrix must
   use the same H (their sign gate addresses this).
7. **A conditional tightening.** If steps a, b, e and f survive the referee,
   Proposition 1.3 (R_H ≤ B_T, self-reviewed) turns their T# = 100 result
   into B_100 ⪰ 0 on the even sector, so T_res(0.8) on that sector lies in
   [≈ 21.3, 100]. (Referee REVIEW §5: their full-space endpoint must read
   1.158e-17 − ε_B, e.g. 1.1579e-17; the sign conclusion is unchanged.)
8. **Stage A at L = 1.19** (measured, midpoint LDL): negative at T# = 320,
   positive from 350, with T_env ≈ 2π e^{3.8635} ≈ 299 for sine:16. The
   candidate operating point sits just above the envelope threshold and far
   above 2T* ≈ 136, which is the envelope-bound regime that §1.7 expected for
   the per-prime H at this L. Consistency only.

## Log

- 2026-09-27: started. Read MISSION.md, AGENTS.md, BRIEF.md, method skill,
  seed probes. Fetched arXiv:2608.24827v2 LaTeX source (scratchpad, not in repo).
- Task 1 written (RESULTS.md §1): Lemma 1 for complex f and H = μ̂ with μ
  carried by |λ| ≥ 2L (boundary via a null overlap), Theorem 1′, line-by-line
  table. Four changed places: sup|Ψ+H−β*| constant, H inside [0,T#] in the
  assembly, Bernstein-ellipse constant (cosh(0.4·70) ≈ 8e11 at D=64), and an
  incidental missing length factor in Zhu's §4 row bound. Main caveat: T# now
  sits near the resolution height T* ≈ 31 at L = 0.8 (Zhu used 200).
- Measured side checks for task 2 (float64, one route): at L = 0.6 the window
  graph splits into paths of 1, 2, 4 vertices, λ_max = 0.9009276 (4-path,
  exact formula) vs Galerkin 0.90077 at M = 800. At L = 0.8 three component
  types (4, 7, 12 vertices), λ_max = 1.2191380 (12-type) vs Galerkin 1.21863.
  A 13-vertex "type" seen once was a float-merge artifact (two copies of one
  point 3e-17 apart). Components percolate once 5 enters the comb (L > 0.805):
  at L = 0.85 90% of samples exceed 3000 vertices, at L ≥ 0.9 all do.
- Task 2 written (RESULTS.md §2): weak duality (Prop 2.1), strong duality
  (Theorem 2, proof via strip positivity + chordal completion along the
  order s(k) = k·ℓ + weighted box averaging), exact finite-component values
  (Prop 2.2), duality_check.py (measured: L=0.6 N=20 0.90719 vs floor
  0.90093 vs per-prime 1.12441; L=0.8 N=20 1.23295 vs 1.21914 vs 1.52205).
- Supervisor note (2026-09-27): numerics per-prime D=128 values 1.52268,
  2.97835, 3.76891 sit above the D=∞ limits 1.522051, 2.977298, 3.767084:
  consistent with weak duality (§2.7). Answered the two asks: finite-measure
  H with continuous part cannot lower the constant envelope even on tails
  (Prop 2.3, Wiener + almost periods); pointwise envelopes are a different,
  unresolved problem, with an exponential total-variation cost for long
  lifts (Prop 2.4). Complex pole term derived and checked: 2|∫f cosh|² −
  2|∫f sinh|² (§1.3, pole_check.py, agreement 1e-15; Lemma 1 check at
  λ = 2L, 2L+0.3 gives 1e-15, in-band 2L−0.05 matches π(g(λ)+g(−λ))).
- Task 3 written (RESULTS.md §3): S*_L = e^L(1+O(e^{-c√L})) via a two-sided
  pointwise estimate of P on cosh(κ_L x) (model kernel e^{|x-x'|/2}, exact
  eigenfunction), Collatz–Wielandt above and Rayleigh below; S_sep ~ 2e^L;
  A_L ~ 4e^L. Explicit lower bound ℓ(L) for every L. asymptotics_check.py
  (measured) shows S*/e^L = 0.548, 0.811, 1.079, 1.082 at L = 0.8, 1.19, 2, 4.
- Supervisor note 2 (numerics, finite N=200 block, quadrature/tail/coupling
  unbounded: per-prime H at L=0.8 negative eigenvalues at sampled T# ≤ 60,
  none at sampled 65; T#=200 leading λ ≈ 1.42e-17). Added RESULTS §1.7: envelope
  threshold vs operating point; Prop 1.2 (monotone, β*I + compact);
  Prop 1.3 domination chain R_H ≤ R′ ≤ B_T ≤ Q (R′ = operator split with the
  comb kept exact, B_T = archimedean-capped form); Prop 1.4 floor
  T_op(H) ≥ T_res ≥ 2πe^{S*_L} for every H (essential spectrum + Dirichlet
  modulation). Heuristic: T_res tracks T* (fake zeros below Nyquist).
  Requested from numerics: λ_min(B_T) at L=0.8, T ∈ [30,70].
- Tasks 4–5 written (RESULTS §4–5). Prior art: Burnol 2000 (math/0101068,
  Théorème 3.7) already adds a support-edge cosine to the symbol: the device
  is not novel. Liu Theorem B = operator split with κ = 7/2 (implies
  λ_max(P) ≤ 2.5753 at L=17/16; our Galerkin 2.1665). Record: refereed
  (log 2)/2; unrefereed 0.8 (Zhu), 1 and 17/16 (Liu). Desogus 2609.20367
  claims RH: recorded as a claim only. Liu's obstruction: does not apply.
  Search summary errors caught: Bombieri "log 2" and Burnol "√2" are
  normalisation misreadings.

## Task status

| # | task | status |
|---|---|---|
| 1 | out-of-band lemma + modified Theorem 1.1 | done (RESULTS §1) |
| 2 | weak / strong duality for the optimal constant | done (RESULTS §2) |
| 3 | asymptotics of S*_L | done (RESULTS §3) |
| 4 | prior art and the current record | done (RESULTS §4) |
| 5 | Liu's obstruction vs the out-of-band route | done (RESULTS §5) |
- Supervisor review (2026-09-27): §1.7 reworded to sampled finite-block
  candidate language (no full-form positivity at 65, no T_res upper bound);
  Prop 1.2 now states validity for β* of either sign and the β* = 0 endpoint
  (compact form, no positive constant; coercivity needs β* > 0).
- Gates: tests/test_hunt_probe_discipline.py and test_docs_numbering.py pass;
  test_doors.py::test_the_evaluate_door_command_runs failed once on a 90 s
  verifier timeout at load average ~50 and passed on rerun (63 s); this diff
  touches only hunts/oob_envelope/theory/. make_context.py --check: up to date.
- Referee REVIEW (read in the referee worktree, 2026-09-27; nothing run).
  Repairs in RESULTS.md: Theorem 2's cosine form restricted to 2N+1 ≥ max m,
  with the referee's all-m quadratic bound in Step 3 (N=1, m=8 counterexample
  acknowledged); analytic-strip hypothesis for the quadrature transfer
  (finite cosine sums or an exponential moment); Zhu's threshold gap is O(1)
  additive, not O(T_1^{-1}); ε_D/ε_B rescaling is a conservative bound, not an
  identity; R′ and B_T defined by bounded symbols, Proposition 1.3 proved
  without subtracting infinities; even-sector essential spectrum proved
  (closes caveat 1); T_res bracket cites both of Zhu's sectors; overstated
  consequence withdrawn; component census marked sampled; Lemma 1 scope
  versus general Bohr almost periodic H stated.
- Referee final verdict read (REVIEW.md at b65ef69 on teal-sea/oob-cert-referee,
  git show only): PASS on Lemma 1, Theorem 1′ with scope, Theorem 2 after the
  b447f0d repair; Theorem 3 and Proposition 2.3 inspected with no gap; §1.7
  repairs pass ordinary analytic review; prior art, record and the Liu reading
  not independently cleared; L = 0.8 even-sector R_H ≥ 1.1579e-17 reproduced
  (hardened); L = 1.19 unresolved. RESULTS.md updated: header, status table,
  grade labels, the Proposition 1.3 wording point, and the even-sector
  bracket T_res(0.8) ∈ [≈21.3, 100]. No ladder upgrade.
