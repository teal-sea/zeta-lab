# CHALLENGE (circularity): positivity_geometry

Hunt #150, mechanism 4. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` and `frobenius_span.py` as committed at
`6c3b90e4b` and scored them against the rubric pre-registered in `MISSION.md` (section
"Challenge-phase scoring rubric", 2026-10-26).

Files here: `circ_positivity.py` (independent recomputation, shares no code with
`frobenius_span.py`), `test_positivity_geometry_challenge_circularity.py` (8 tests, every
number below), this page. The builder's own 58 tests pass in this checkout.

Grades as in `MISSION.md`. Nothing written here is kernel-checked.

## Verdict

**Unresolved, as the builder says; the restricted-class obstruction is downgraded to a
scoped refutation of a loosely defined class.** No hidden use of RH, GRH or the zeros was
found in any definition or computation. The target H_Q is an RH-equivalent restatement,
which the builder states openly and which is already in print (Connes 1999; Connes,
Consani and Marcolli 2008), so it is recorded as a reformulation. Three defects, none
fatal to the disposition:

- **D1 (GRH in the scope boundary).** NOTES section 5.4, lines 389-391, and section 9,
  lines 574-576, say a degree-1 Q-analogue of the golden fake "cannot exist", so the
  obstruction does not reach Q. Unconditionally, Kaczorowski-Perelli says only that a
  degree-1 element of the Selberg class is zeta or a shifted Dirichlet L-function; such
  an element violating RH exists **if and only if GRH fails** for some Dirichlet
  L-function. The scope boundary is therefore conditional on GRH and should be stated as
  such. The obstruction itself does not use it.
- **D2 (the class is not explicitly defined).** Section 9 calls the obstruction a
  restricted-class obstruction for arguments that "transfer verbatim to global function
  fields". `ALIGNMENT.md` section 5, item 2, asks for an explicitly defined class and a
  theorem whose hypotheses are shown to apply. "Transfers verbatim" is not a definition;
  what the golden fake actually establishes is a counterexample to one implication in the
  function-field world: {rationality, curve functional equation, curve pole structure,
  nonnegative integer closed-point counts in every degree, a ±1 local factor per place
  of F_5(t) with conductor 4} does not imply RH. That is disposition 1 (refuted) for that
  implication, which is sharper and fully supported; "restricted class obstructed" for
  number-field arguments overreaches by the vagueness of the transfer clause.
- **D3 (prior art on the phenomenon).** Ihara zeta functions of (q+1)-regular graphs carry
  an Euler product over primitive closed paths with nonnegative counts, a functional
  equation and rationality, and satisfy their RH analogue exactly when the graph is
  Ramanujan (Ihara 1966; Sunada; Hashimoto; Stark-Terras). For a non-Ramanujan graph the
  factor 1 - lambda u + q u^2 with |lambda| > 2 sqrt q has precisely the golden fake's
  shape (q = 5, lambda = 5 gives 1 - 5u + 5u^2). The Ihara zeta carries extra
  (1 - u^2)^(r-1) factors, so it does not have the curve pole structure, and its Euler
  product is over graph primes, not places of F_q(t). The exact form is therefore not
  covered, but "Euler product with nonnegative prime counts plus functional equation does
  not give RH" is published, and the NOTES' novelty search (section 12) missed it.

## Scorecard

1. **Disposition.** Unresolved (agreeing with NOTES section 9), with the golden fake
   recorded as a **refutation** of the function-field implication listed under D2, and
   the "restricted class obstructed" label withdrawn to that scope (D2). Evidence:
   `circ_positivity.quadratic_split`, `closed_points`; NOTES lines 562-576.
2. **Grade per step.**
   - Shadow H_F on 8 curves, exact inertia: hardened (exact integer arithmetic, two inertia
     routes; builder's `test_positivity_geometry.py`, 58 passed here). Agreed.
   - H_Q equivalent to RH (NOTES 1.2): derived, self-reviewed; I rechecked the projection
     (P(gamma_f) orthogonal to F1 and F2, block diagonal) and the reduction to real f
     (the form W(f * g*) is symmetric because the zero set is closed under rho -> 1 - rho,
     so complex f splits into its real and imaginary parts). Agreed, and published: the
     grade of the *reformulation* is "cited" (Connes 1999; Connes-Consani-Marcolli 2008,
     arXiv math/0703392, section 6.2 "Weil positivity and the Riemann hypothesis").
   - Window-2g lemma (2.4): derived, self-reviewed. I rechecked the proof (t_k symmetric
     in k because the multiset is inversion-closed; the interpolation uses at most 2g
     nodes). Independent measured check on 120 random conjugation- and inversion-closed
     multisets of genus 2, 3, 4, on and off the circle, not Weil-type polynomials:
     0 disagreements (`test_window_2g_lemma_on_arbitrary_closed_multisets`). Sharpness
     at genus 2 rebuilt by float eigenvalues: min eigenvalue >= 0 at window 3 and < -1e-3
     at window 4. Grade stays derived, now with a second-session measured check.
   - Sharpness in random families (2.4): the on/off-circle classification is by mpmath
     roots at 40 digits, so the "on-circle cases positive on every window" half is
     *measured*, not hardened; the refusals are exact. Minor overgrade.
   - Golden fake in every degree (4.2, 5.3): derived for all degrees, self-reviewed, exact
     below thresholds. Recomputed to d = 300 here by separate code: b_d nonnegative
     integers, min b_d = 1; split and inert counts nonnegative integers to d = 300,
     first eight values equal to NOTES line 338-339. Ramification configurations
     {1: 4}, {1: 2, 2: 1}, {2: 2}, {4: 1} fail by d = 10 (planted control). Agreed.
   - Number-field G1/G2 table (6.2): measured. Lambda_DH(6) = (1 + kappa^2) log 6
     recomputed by a separate log-derivative recursion to 25 digits. Agreed.
   - Composite: the obstruction is derived, self-reviewed, as NOTES says; the mechanism's
     RH step (G3, an ambient Hodge index) does not exist, so no grade attaches to it.
3. **The Euler-product step.** Named: G1, the Lefschetz identification of off-diagonal
   intersection numbers as point counts (NOTES 6.1). Tested on rivals that lack it: DH
   fails G1 (Lambda(3) < 0, Lambda(6) != 0), Epstein (1,1,6) fails at n = 48 and n = 6.
   The builder correctly says G1 is a precondition and not the engine; G3 uses no Euler
   product and is missing for zeta.
4. **Finite stand-ins.** None found standing in for a uniform step in a claim. The
   all-degree golden-fake statements carry derived tail thresholds (D0 = 2, D1 = 4) with
   exact checks below them; the 8-curve shadow is presented as a finite exact check of a
   theorem (Weil), not as evidence for zeta. The window-2g statement is derived, not
   scanned. The G1 table runs to n = 60 and is labelled measured, and its role is only to
   exhibit failures (a finite range suffices for a failure).
5. **Novelty search.** Recorded by the builder (two web searches, NOTES 12). This session's
   queries, 2026-10-26, web search: (a) "Ihara zeta function regular graph Riemann
   hypothesis Ramanujan non-Ramanujan functional equation Euler product counterexample":
   found Sunada's equivalence (RH for Ihara zeta iff Ramanujan), see D3; (b) "Connes
   Consani Marcolli Weil proof adeles class space Hodge index ... equivalent Riemann
   hypothesis": found arXiv math/0703392, where RH is equivalent to positivity of a trace
   pairing, which is H_Q's content; (c) "function field analogue Selberg class zeta
   functions ... not satisfying Riemann hypothesis F_q(t)": nothing on golden-type fakes
   over F_q(t); (d) "Weil explicit formula function field positivity finitely many test
   functions ... Toeplitz 2g": nothing explicit on the window-2g statement (Carathéodory-
   Toeplitz-Pisarenko is the likely home, not confirmed). arXiv, zbMATH and MathSciNet
   full text, and Lean Zulip, were not searched by this session.
6. **Rivals on complete hypotheses.** The mechanism's complete hypotheses for zeta do not
   exist (G3 is missing), so no rival can refute an RH implication here; the entries
   concern the stated preconditions and the restricted-class claim.
   - DH: lacks G1 and G2 (no pole; signed, off-support Lambda). Not that counterexample.
     Measured, n <= 6 suffices.
   - Epstein (1,1,6): lacks G1 (first negative Lambda at 48, off-support at 6; builder's
     measurement, n <= 60). Not that counterexample.
   - W_{1/4}: lacks G2 (two poles, signature (2, 2)). Not that counterexample.
   - zeta(s - delta), delta = 1/10 and 1/4 (computed here, not in the NOTES): **passes G1
     and G2** (Lambda(n) n^delta nonnegative and on prime powers for n <= 60; one pole at
     1 + delta, residue 1) and violates RH (zeros at 1/2 + delta + i gamma). It lacks the
     functional equation about Re s = 1/2, which the restricted class includes, so it is
     not a counterexample to the golden-fake class. It does show over Q, without the
     function-field detour, that G1 and G2 alone separate nothing, which strengthens the
     builder's "preconditions, not engine". Measured, n <= 60.
   - Golden fake (function field): meets every listed function-field hypothesis and
     violates RH: refutes that implication (D2). Derived, self-reviewed, with this
     session's exact recomputation to d = 300.
7. **Circularity.** No definition reads the zeros. Requirement A provenance, by hand:
   `frobenius_span.py` imports numpy, mpmath, flint, sympy and, inside the two rival
   routines `nf_log_derivative_profile` and `nf_pole_residues` only, `zeta.epstein`'s
   coefficient interfaces and function values near s = 1; nothing imports `zetazero`,
   `siegelz`, a zero table or a xi-phase. Point counts are literal enumeration
   (`count_points`), and the Weil-polynomial roots appear only as a cross-check
   (`eigenvalue_moduli_ratio`). W is defined in NOTES 1.2 as a sum over zeros, but the
   pairing is evaluated through the explicit formula (the pole terms cancel exactly and
   leave the prime and archimedean sides), an unconditional identity, so that is not
   zero-importing. The only conditional input is D1: the claim that the obstruction does
   not reach Q rests on GRH for Dirichlet L-functions.

## What this challenge does not settle

The rival-gate challenger's computation is separate. Whether some square of Spec Z
carries a pairing that passes G1 and G2 (NOTES section 11, step 1) is untouched here.

## Run manifest

```runmanifest
id: rh_moonshot-positivity_geometry-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T12:20+00:00
finished: 2026-10-26T13:20+00:00
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry hunts/rh_moonshot/probe_tower
  - .venv/bin/python hunts/rh_moonshot/positivity_geometry/challenge/circ_positivity.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry/challenge
outcome: no hidden RH or zero import; golden fake recomputed exactly to degree 300; the scope boundary over Q is conditional on GRH; the restricted-class label narrowed to a refutation of the function-field implication; Ihara zeta prior art on the phenomenon
artifacts:
  - hunts/rh_moonshot/positivity_geometry/challenge/circ_positivity.py
  - hunts/rh_moonshot/positivity_geometry/challenge/test_positivity_geometry_challenge_circularity.py
  - hunts/rh_moonshot/positivity_geometry/challenge/CHALLENGE_circularity.md
```

Compute: about 2 s of one core for the script, a few seconds for the tests; no estimate
block needed (well under one core-hour).
