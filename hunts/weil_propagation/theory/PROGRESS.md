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
