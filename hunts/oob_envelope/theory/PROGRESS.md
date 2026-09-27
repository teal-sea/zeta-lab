# PROGRESS: theory worker, hunt oob_envelope

STATUS: all five tasks done (RESULTS.md; last commit before this line: e62cac5). Open requests to numerics: λ_min(B_T) scan at L = 0.8, T ∈ [30, 70]; the H = 0 λ_min at T# = 200 from the same pipeline.

Branch `teal-sea/oob-cert-theory`. Writes only in `hunts/oob_envelope/theory/`.
Brief: `theory/BRIEF.md`. Output: `theory/RESULTS.md`.

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
