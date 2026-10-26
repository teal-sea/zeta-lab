# CHALLENGE (circularity): probe_tower

Hunt #150, mechanism 6. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` and `tower_template.py` as committed at
`6c3b90e4b` and scored them against the rubric pre-registered in `MISSION.md` (section
"Challenge-phase scoring rubric", 2026-10-26).

Files here: `circ_probe.py` (independent recomputation, shares no code with
`tower_template.py`), `test_probe_tower_challenge_circularity.py` (7 tests, every number
below), this page. The builder's 29 tests pass in this checkout, with the pinned paper at
`~/.cache/zeta-lab/openai-math-adc7f124/paper.tex` matching the recorded SHA-256
`42a5ee0f...6a3`.

Grades as in `MISSION.md`, plus the builder's *cited* and *inferred* (NOTES lines 9-14).
Nothing written here is kernel-checked.

## Verdict

**Restricted class obstructed, as the builder says, for the class as section 9 defines it
(the order-k template), with composite grade inferred.** No hidden use of RH, GRH or the
zeros was found in the template; the formal order k = 1 is Littlewood's RH-equivalent
Moebius bound, and the NOTES flag it as a restatement and use it as nothing more (lines
183-194). The LP walls are recomputed here by a separate route (exact vertex enumeration
in rationals) and the dual-multiplier identity is rechecked symbolically: they hold. What
limits the result is not circularity but one inferred reading, and one place where
agreement is counted as more independent than it is:

- **P1 (shared inferred reading).** Every wall rests on reading each 6 of the paper as the
  character order k (NOTES 2.1, line 89). The builder's own planted fault (a pole k/36,
  NOTES lines 122-128) shows that the k = 6 reproduction cannot pin this. The NOTES then
  count agreement with hunt #136's probe lane as a cross-check (lines 175-176, 436-441).
  Both start from the same reading, so their agreement checks algebra, not the reading.
  This session's recomputation starts from the NOTES' section 2.2 formulas and shares the
  reading too. The reading is structurally well motivated (lines 3758 and 4045: the
  principal frequencies are a^k, and the sum over them is zeta_F(kz), with its pole at
  1/k), but it remains *inferred*, and the class's relevance to any actual order-k theta
  system takes that grade.
- **P2 (sources that were uncommitted when cited).** Sections 4 to 6 grade as *cited*
  some statements read from worktrees that were uncommitted at the time (hunt #136
  `PROBE.md`, hunt #148 `S4.md`, `RIVAL.md`, `LOCAL_IDENTITY.md`). They have since been
  checkpointed: `3f6ab82fd` on `hunt/ff-probe` (pushed; `S4.md` line 79 has the quoted
  234 / 52 split) and `57c7024c1` on `hunt/below-seven-eighths` (local only, not on
  origin when checked). Until the latter is pushed, an outside reader cannot check those
  citations; they feed only the small-k doors (sections 4 and 5), not the walls.
- **P3 (no novelty search).** The NOTES record none (line 536). This session's searches
  found no published treatment of the order-k tower (queries below), so nothing published
  covers the exact form as far as these searches reach.

## Scorecard

1. **Disposition.** Restricted class obstructed. The theorem is the LP of NOTES 3.2 with
   its dual multipliers (derived, self-reviewed; rechecked here). Its hypotheses apply to
   the class *by definition* (section 9 defines the class as the template), so the
   transfer from the class to real probes is exactly the inferred reading of P1. Within
   the class the mission's tower premise is refuted: sigma_0(k) increases to 1.
2. **Grade per step.**
   - The paper's constants at k = 6: cited (49 lines checked by `verify_citations`
     against the pinned file; builder's tests pass here). Agreed.
   - sigma_0(k) = 1 - 1/k + (M - 2 ell)/(2k): derived. Rebuilt here symbolically from the
     signal offset c = l_x/2 - 1 + h/k and the direct bound l_x/2 + b/(2k) (NOTES 2.2):
     difference from the closed form 0, value 7/8 at (ell, M, b) = (1/6, 5/6, 1/8), k = 6
     (`test_sigma0_closed_form_and_paper_value`). Agreed.
   - The k-reading: inferred (P1). Agreed with the NOTES' own grade.
   - Sufficiency of M + ell <= 1 for a general geometry: inferred, from hunt #134 (NOTES
     line 92). Agreed.
   - Walls (NOTES table, section 3.2): derived. Rebuilt here by exact vertex enumeration,
     no LP solver: for k in {2, ..., 8, 12, 100}, dual-length wall 1 - 2/k, floor wall
     1 - 4/(5k) at delta_0 -> 0 with minimiser (ell, M, b) = (1/5, 4/5, 0) for every k,
     and 1 - 25/(32k) at delta_0 = 1/50; all equal to the NOTES table. Floor wall strictly
     increasing for k = 2..40, minimum 3/5 at k = 2. Dual-multiplier identity
     (M - 2 ell) - m* = y1 (-floor) + y2 (1 - M - ell) + y3 b: residual 0 symbolically in
     k and delta_0; a 1 percent perturbation of y1 breaks it (planted fault). With the
     second route the walls at the listed k are two-route exact; the all-k statement
     stays derived (symbolic identity, self-reviewed by the builder, rechecked here).
   - Rival measurements at zeros (7.3-7.5): measured. DH recomputed here by a Hurwitz
     route that does not use `zeta.epstein`: the zero refined by `findroot` to
     0.80851718245663738555 + 85.699348485377592172i, |DH| = 5.5e-41, |L(chi)| =
     |L(chibar)| = 0.70219735, |R| = 0.77831832, |H - 1| = 1.0000 (to 1e-20), and the
     closed form c1 c2 (L1 - L2)^2/(L1 L2) agrees to 2.4e-41. Agreed.
   - Saias-Weingartner (7.3): cited from the abstract, proof not checked. I re-read the
     abstract (arXiv 0807.0783): for periodic a not of the form P(s) L(s, psi) there is
     eta(a) > 0 with c1 T <= N_a(sigma_1, sigma_2, T) <= c2 T for all
     1/2 < sigma_1 < sigma_2 < 1 + eta. The NOTES quote it correctly.
   - Composite: inferred (P1), as the NOTES say (line 481).
3. **The Euler-product step.** Named: (E_k), the principal row's Moebius-weighted
   squarefree sum must equal H/L with sup |H - 1| <= 1/2 (NOTES 7.1, from lines 3967,
   4043-4047, 413). It is k-independent. Tested on rivals lacking the Euler product: DH
   fails it at its zero (recomputed above) and, for every finite deletion set, by
   Saias-Weingartner; Epstein (1,1,6) fails it at 0.953260 + 16.290216i (builder's
   measurement, not recomputed here). The step distinguishes.
4. **Finite stand-ins.** None in the claims. The tower's direction, the walls and the best
   order are closed forms symbolic in k (rechecked); the random-geometry scan for
   k = 1..64 (NOTES 3.5) is a supplementary test, not the argument. The NOTES' point that
   deleting small primes hides DH's failure from every finite scan (lines 361-366) is
   itself a correct warning against a finite stand-in, and the all-height failure is
   carried by the cited theorem, not by the scan.
5. **Novelty search.** Absent in the NOTES (line 536). This session's queries,
   2026-10-26, web search: (a) "Quasi-Riemann hypothesis 7/8 Patterson cubic theta higher
   order metaplectic theta zero-free region generalization order k": returned David,
   Dunn, Hamieh and Lin (arXiv 2306.11875) and Patterson-bias papers, nothing on an
   order-k zero-free tower; (b) a grep of the pinned paper for "higher order", "order $k$",
   "n-th order", "barrier", "limitation": only lines 134 and 4728, both on Blomer,
   Goldmakher and Louvel's higher-order large-sieve recursion. arXiv listing search,
   zbMATH and Lean Zulip were not searched.
6. **Rivals on complete hypotheses.**
   - DH: lacks (E_k) (|H - 1| = 1.0000 at its zero; measured here by a second route).
     Not that counterexample.
   - Epstein (1,1,6): lacks (E_k) at its zero (builder's measurement; not recomputed
     here, so from this session: not run, excludes nothing beyond the builder's record).
   - W_{1/4}: passes (E_k), violates RH's analogue, lacks unitarity, which the direct
     bound and the local identity use (NOTES 7.5). Not that counterexample (builder's
     measurement and derivation).
   - zeta(s - delta), delta = 1/4 and 1/10 (computed here, not in the NOTES): f(n) = n^delta
     is completely multiplicative, so the squarefree Moebius sum is 1/zeta(s - delta)
     exactly and H = 1: it **passes (E_k)** (measured at s = 3 to n = 20000: 0.79352844955
     against 0.79352844951 for delta = 1/4, and 0.817571979528 against 0.817571979518 for
     delta = 1/10, inside the tail bound) and violates RH (zeros at 1/2 + delta + i gamma).
     It lacks unitarity, |f(n)| = n^delta, and the NOTES' change-of-variables argument for
     the factor zeta(s - 1/4) of W_a (lines 412-418) applies to it verbatim with 1/4
     replaced by delta: every wall rises by delta, to at least 3/5 + delta > 1/2 + delta.
     Not that counterexample; it is the cleanest rival for the unitarity hypothesis,
     cleaner than W_a because it has degree 1 and no second factor.
7. **Circularity.** None found. Requirement A provenance, by hand: `tower_template.py`
   imports only the standard library at module level; the template routines (`wall`,
   the sigma_0 formulas, the LPs) use Fractions and sympy and read no zero. Zeros enter
   only the rival diagnostics: `dh_at_offline_zero` (from `zeta.epstein`'s
   `OFFLINE_ZERO_RE/IM`), `epstein_at_offline_zero` (a hard-coded zero) and
   `wa_at_offline_zero` (`mp.zetazero(1)` to place W_a's zero). That is evaluation of a
   rival at its known zero, which is what the gate asks for, and nothing feeds back into
   a wall. The target implies RH and GRH for Dirichlet L-functions (NOTES section 1); no
   input assumes either.

## What this challenge does not settle

The rival-gate challenger's computation on Epstein (1,1,6) and W_a is separate. Whether
an order-k theta system exists for k in {2, 4, 5} with a scalar Euler identity, and
whether the k-reading survives a reading of the paper's proof at k != 6, are open.

## Run manifest

```runmanifest
id: rh_moonshot-probe_tower-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T12:20+00:00
finished: 2026-10-26T13:30+00:00
ran:
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry hunts/rh_moonshot/probe_tower
  - .venv/bin/python hunts/rh_moonshot/probe_tower/challenge/circ_probe.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/probe_tower/challenge
outcome: no hidden RH or zero import; walls rebuilt by exact vertex enumeration and the dual identity rechecked; DH correction at its zero rebuilt by a Hurwitz route; zeta(s - delta) passes the Euler step and lacks unitarity; composite grade stays inferred on the k-reading
artifacts:
  - hunts/rh_moonshot/probe_tower/challenge/circ_probe.py
  - hunts/rh_moonshot/probe_tower/challenge/test_probe_tower_challenge_circularity.py
  - hunts/rh_moonshot/probe_tower/challenge/CHALLENGE_circularity.md
```

Compute: about 3 s of one core for the script, under 10 s for the tests; no estimate block
needed.
