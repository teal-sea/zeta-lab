# PROGRESS (theory worker)

## 2026-09-23, milestone 1: sources read

Read in full or in the relevant sections (local copies in the session
scratchpad, not committed):

- Zhu arXiv:2608.24827v2 (support 1.6, Landau-Widom law, barrier).
- Connes-Consani-Moscovici arXiv:2511.22755 (s3.1-3.2, s5, s7, s8).
- Connes-van Suijlekom arXiv:2511.23257 (abstract, s1, s4).
- Connes arXiv:2602.04022 (s6, s7.2-7.4).
- Connes-Consani arXiv:2006.13771 (intro, s3, Thm 6.11).
- Connes arXiv:math/9811068 (Thm 4, the semilocal trace formula).
- Bombieri, Rend. Lincei 11 (2000) 183-233 (Thms 5, 8, 10, 12; s13).
- Suzuki arXiv:2606.09096 (s1, s4 scaling, s5 Dirichlet form).
- Yoshida 1992: full text not reachable (Project Euclid bot wall);
  cited through Bombieri s1 and Zhu s1.2 only.

First scoped finding: at the DH crossing c = 30 -> 31 the only entering
atom is n = 31, prime, 31 = 1 mod 5, so Lambda_f(31) = log 31 = Lambda(31).
The new arithmetic at that step is identical for zeta and DH.

Next: derivations (dilation identity, prime-entry kink, Schur collar),
numerical checks, candidates, RESULTS.md.

## 2026-09-23, milestone 2: derivations and checks (checks.py, checks.json)

- Kink at a prime-power entry: slope of lambda_min(L) jumps by
  -Lambda(q) q^{-1/2} (2/L) (sum_n u_n)^2 (exact at finite N); measured
  agreement 4e-9 to 6e-8 relative at q = 3, 4, 5, 7.
- DH lattice step 30 -> 31 adds no arithmetic: Lambda_f(30) = 0 (all
  multiples of 5 vanish), and the n = 31 atom sits at the window edge with
  weight 0 at c = 31.
- Dilation identity (fixed window) matches zeta/weil.py Fejer values to
  5e-16 .. 2e-21 at dps 30.
- Pole-free zeta form: one negative even eigenvalue, positive ground state
  (min/max 0.80 at c=13, 0.71 at c=31); its 2nd eigenvalue sits at
  0.64 lambda_2(Q), about 1e6 above lambda_1(Q).
- DH ground state moves 7.7e-3 in norm across 30 -> 31 while lambda flips
  sign; zeta moves 4.4e-3.
- Structural finding (derivation): with the pole removed, the zeta Weil
  form on any window is a jump Dirichlet form (Levy measure: archimedean
  kernel + atoms 2 Lambda(n) n^{-1/2} at +-log n) minus a constant; uses
  Lambda >= 0. DH's jump measure is signed.

Next: RESULTS.md.

## 2026-09-23, milestone 3: supervisor review applied, Poincare attempt

- Correction to milestone 1: the effective entering set at DH's 30 -> 31
  step is empty (Lambda_f(30) = 0; the n = 31 atom has zero weight at the
  edge), not "n = 31 with zeta's weight".
- Summary lines now carry grades in words; Proposition M hypotheses
  (H1)-(H3) stated; the nongeneric coincidence named; DH stated to be
  outside C2's hypotheses (does not test it); W_a added as the Euler-product
  rival (two poles, also outside); Epstein (1,1,6) pending with numerics.
- Numerics worker's crossing brackets and N = 128 edge data cited from
  their JSONs (read-only, not recomputed).
- Section 6: Poincare attempt. Ground-state representation exact;
  comparison bound short by 10x-20x; (a) saturated to 6e-38 / 7e-64
  relative; extremal e2 orthogonal to the pole to 2<c,e2>^2 ~ 1e-63.
  Status: attempt unresolved, non-sharp bounds obstructed (measured),
  paused by allocation; (a) identified with CCM step 2 at eigenvalue scale
  (hypothesis supported by measurement).
- Expected test failure on this branch: tests/test_hunt_probe_discipline.py
  ::test_every_hunt_directory_is_covered_by_the_case_log fails because the
  weil_propagation case-log entry in hunts/README.md lives on the numerics
  branch (commit e46cf90), by supervisor ruling. Not a defect; it clears
  on merge. The reserved-word test passes.

## 2026-09-23, milestone 4: Epstein control result

- Numerics commit 3a799d8 read via git show (read-only). Confirmed in
  epstein_N64/N128.json: odd first negative c = 28, even c = 29.5, every
  later window to 48 negative, all LDL conclusive; dedekind_N64.json
  positive on all 93 windows; epstein_offline.json root
  0.953260474794661 + 16.2902157203904i, residual 1.43e-32 at dps 20.
- Check J (exact, log-prime basis + mpmath.iv): Lambda_Q(n) >= 0 for all
  n <= 47, first negative n = 48; nonzero n <= 29 all strictly positive.
- C2 refuted as a positivity mechanism (rival satisfies H1-H3 and one
  pole). Proposition M kept separate (derivation). Odd-first crossing
  recorded as evidence against even-below-odd for Markov + one pole.
  Which of (a)/(b) fails: placeholder, pending numerics epstein_polefree.py.

## 2026-09-23, milestone 5: bounded multiplicativity attempt (C4)

- Separating step named before development: (U-S) = prime-power support +
  unitary local roots (|s_k(p)| <= degree). Check K (exact, n <= 60):
  Dedekind Q(sqrt -23) passes; Epstein fails (composite atom 6; s_3 = 6 at
  n = 8, 27); W_a fails (s_1(2) = 2.0303); DH fails.
- C4 = Connes-Consani semilocal Sonin program restricted to windows (not
  original). Produced: collar flattening is vacuous (Schur complement
  intrinsic to the quotient); Sonin projection factorizes at finite places
  for product cutoffs (caveat: Connes uses module cutoffs); first open
  instance S = {inf, 2}, c in [2, 3). Status: unresolved, paused.
- Epstein (a)/(b) placeholder NOT filled: numerics has not committed
  epstein_polefree yet (branch head still 3a799d8).

## 2026-09-23, milestone 6: reproducibility and case log

- checks.py takes check letters (`checks.py J K`); J and K regenerate
  checks.json content identically in about 1 s. RESULTS s10 updated.
- hunts/README.md: applied numerics' case-log change (402c1cd + e46cf90)
  byte for byte, so both branches carry the identical hunk and merge
  cleanly. The case-log test now passes on this branch.
- test_hunt_probe_discipline, test_docs_numbering, test_doors: 18 passed;
  make_context --check clean.

## 2026-09-23, milestone 7: placeholders filled from numerics 3b76739

- epstein_polefree.json read via git show: even sector breaks (a)
  (pole-free inertia (64,1) at c = 29 -> (63,2) at 29.5); odd sector breaks
  the odd pole capacity (pole-free odd (64,0) through c = 30, full odd
  negative from 27.74). Refined crossings from epstein_crossing.json
  (N = 128): odd (27.7412, 27.7417], even (29.3037, 29.3042].
- Both PENDING placeholders replaced; grading and line 5 updated.
