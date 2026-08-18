# RESULTS_LEDGER — every serious claim, its status, its grade

Grades use the repository ladder (measured / hardened / kernel-checked); a
composite claim takes the grade of its weakest step. Statuses: ACTIVE,
UNDER ATTACK, PROMOTED, DEAD, REFUTED. Dead ends move to FAILURE_LEDGER.md
with their mechanism.

---

## RF-C001 — m_4(1) = 13/4 for the sine-Gram matrix, checked exactly

- **Statement.** For the band Gram matrix of the sine process at
  lambda = 1, the normalised fourth spectral moment is 13/4, as the
  10 Aug 2026 paper states in §7.5(f).
- **Status:** settled (a verification, not a new claim).
- **Origin:** this campaign's own engine first said 49/15; the exact
  finite-N lattice-count engine plus a CUE Monte Carlo killed the 49/15
  and located the defect (Gaussian trace-moment approximation out of its
  regime). Record in `sine_gram/RESULTS.md`.
- **Grade:** hardened (exact integer arithmetic at finite N, two-sided
  Lagrange extrapolation agreeing to 3.24996..3.24998, independent MC).
- **Value:** methodological; confirms the instrument for RF-C002.

## RF-C002 — exact higher sine-Gram moments (P-SG)

- **Delivered 2026-08-17** (session ended by a budget limit during one
  final spot-check; everything below was already checkpointed). Record:
  `sine_gram/moments_report.md`, data in `sine_gram/exact_trTk_values*.json`.
- **Results.** m_5(1) = 101/18 and m_6(1) = 640/63 (and a k = 7 value in
  the report), extending the paper's m_1..m_4 = 1, 4/3, 2, 13/4; exact
  quasi-polynomials E tr T^k in N; and a piecewise structure for
  m_k(lambda): an even polynomial below lambda = 1/floor(k/2) with defect
  pieces -(j lambda - 1)^{2j+1} g_{k,j}(lambda)/lambda switching on at
  lambda = 1/j, identified exactly for k = 4, 5, 6 with spare-point checks.
- **Grade:** hardened (exact integer arithmetic, heavily overdetermined
  identifications, Monte Carlo control). One loose end: a targeted
  quadrature check of the lambda^6 Wick coefficient was in flight when the
  session ended; the coefficient stands on the exact-engine identification
  alone.

## RF-C003 — improved window in the RH-conditional cubic certificate (P-WIN)

- **Statement.** In the Aug 2026 paper's §7.5(g) chain (RH assumed,
  unrefereed preprint), replacing the hand-picked window cos(8s/5) by
  v*(s) = 1 - (1467/1000)s^2 + (1159/1000)s^4 raises
  2m_2(1,v) - m_3(1,v) from 0.6852438755373... to the exact rational
  2245228120295149280/3276332462159207451 = 0.6852870232880...,
  lifting the distinct-zeros constant from 0.850826305842608 to
  0.850828702939872 (+2.397e-6).
- **Evidence (first arm):** closed forms reproducing the paper's printed
  value to all digits; windowed-CUE exact-lattice cross-check to 4e-10 at
  two windows; EL residual showing the paper's window is not a critical
  point (max residual 5.6e-2); exact rational arithmetic for v*;
  two-backend ball enclosures of the final constants; positivity and
  monotonicity of v* in rational arithmetic; admissibility analysis
  (v* is admissible exactly as the paper's own windows are, including the
  same two glosses the paper itself carries: the endpoint taper and the
  lambda -> 1 limit of the triple-correlation input).
- **Status: PROMOTED (grade hardened, RH-conditional).** The blinded
  second arm independently derived the moment functionals from the paper
  (its own closed form for F(cos(8s/5)), structurally different, agrees
  to 41 digits) and reproduced the exact rationals bit-identically:
  F* = 2245228120295149280/3276332462159207451 and final constant
  50176758585216887915/58973984318865734118 = 0.850828702939872...
  Its adversarial battery also resolved in the claim's favor: the
  concentration attack sends F strongly negative (no blow-up, interior
  optimum meaningful), and v* has strictly smaller regularity norms than
  the paper's own window (admissibility with room to spare). The
  verifier's session was ended by a budget limit after these checks; its
  scripts and outputs are preserved under the campaign scratchpad and the
  key numbers replayed by the coordinator. Promotion is as a candidate
  strengthening inside an unrefereed source chain, per the caveats below.
- **Grade if it survives:** hardened, RH-conditional, inheriting the
  source paper's §7.5(g) machinery and its unrefereed status. The
  improvement is in the sixth decimal; the paper's printed 0.85082
  headline is unchanged. Honest framing: a measured optimization gain
  inside someone else's theorem chain, exactly like the laboratory's
  flagship transplant, but smaller.
- **Caveat, upgraded 2026-08-17 (WIN-GLOBAL arm; window_opt/RESULTS.md
  section 9):** the optimum is now the unique strictly positive
  stationary window across 336 starts in three parametrizations, exactly
  unique on the quartic slice (Groebner elimination, all in exact
  arithmetic), a genuine local maximum by Hessian signature, and the
  global sup is bracketed by exact rationals:
  0.685287032176998 <= sup F <= 0.892744211644411 (the upper end a
  derived moment-relaxation bound; a degree-44 dyadic witness carries
  the lower end). Global optimality over the full admissible class
  remains open; closing the factor-1.30 bracket needs spectral
  information beyond the second moment.

## RF-C004 — truncated Weil form: replication, enclosures, and the rival control (P-WEIL)

- **Delivered 2026-08-17.** Three findings, graded separately; the full
  record is `weil_trunc/RESULTS.md` and `weil_trunc/SOURCE.md`.
- **(a) Replication of arXiv:2605.20224 / 2607.02828 (Groskin; construction
  from Connes-van Suijlekom arXiv:2511.23257 Prop 4.1 and CCM
  arXiv:2511.22755; open question from Connes arXiv:2602.04022 SS6).**
  Independent implementation from definitions only; eight validation gates
  against printed values all pass; no defect located in either posting.
  Two display-level constant slips in CCM (4.4)/(4.14) that cancel in
  their own tables are documented. The survey's provenance for these IDs
  was scrambled and is corrected in SOURCE.md. Grade: hardened.
- **(b) Enclosure-checked spectra.** Ball-arithmetic assembly with
  explicit tail radii; LDL^T inertia, Rayleigh brackets and Rump
  eigenvalue enclosures mutually consistent at all 27 grid cells; every
  eigenvalue of both parity sectors strictly positive over the zeta grid
  c in {6..29} x N in {4..32} and the DH grid c in {6..47} x N = 32.
  Grade: hardened.
- **(c) The rival control, run for the first time.** The RH-violating
  Davenport-Heilbronn function, fed through the identical pipeline,
  shows the SAME qualitative signature as zeta: strictly positive
  spectrum and a ground state locating its on-line zeros (to 1.7e-36 at
  c = 47). The qualitative spectral picture therefore distinguishes
  nothing; what separates the two is the N-saturated error floor
  (zeta ~3.7e-59 vs DH ~1.0e-10 at c = 13, a ~49-order gap), whose
  attribution (RH-truth vs Euler product vs pole, all differing at once)
  is measured but NOT settled. Grade: measured, with the confound stated.
- **Follow-up thread (not pursued, per foraging rule):** Weil positivity
  is false for DH, so its band minimum must eventually go negative;
  the data bound the first negative at c > 47 (N <= 32). Candidate for a
  GitHub issue as an observation.

## RF-C005 — enclosure-grade Baez-Duarte distances (P-NB)

- **Delivered 2026-08-17, partial** (session ended by a budget limit
  mid-finalize; the coordinator completed one summary sentence in
  `nyman_beurling/RESULTS.md` from the checkpointed `results/analysis.json`
  and says so inline). Vasyunin-formula pipeline validated five
  independent ways; arb-rigorous solve enclosures for d_N^2 through
  N = 2048; the approach to the conjectured constant
  C = (2 + gamma - log 4pi)/2 is from below in this range, and
  finite-N extrapolation is measurably delicate (free-intercept fit
  lands at 0.04407 vs C = 0.04619). Grade: hardened for the computed
  distances; descriptive only for the fits.

## RF-C006 — Bian F_kappa audit: three defects, a corrected table, a closed form (P-FK)

- **Delivered 2026-08-17.** Record: `fkappa/RESULTS.md`.
- **(a) Faithful reproduction.** The OCR-recovered Figure 10.1 grid
  (99 cells) is reproduced cell for cell in rational arithmetic by a
  literal port of the thesis's Mathematica code; the kappa = 1 row equals
  Farmer-Gonek exactly.
- **(b) Three defects in the published table, each with an exact finite
  witness:** an assembly truncation (the figure's off-diagonal loop drops
  (l,k) pairs from i = 7 on, so the published columns i in {7,9,10,11}
  for kappa >= 2 are not the coefficients of the thesis's own eq (10.1));
  phantom slots (terms the printed formula makes exactly zero are
  evaluated nonzero, first affecting i = 5, kappa = 3); and a
  normalization overcount by prod alpha_i! (first affecting i = 5,
  kappa = 2). The kappa = 1 row, the only externally validated one, is
  immune to all three, which is why nothing caught them since 2008.
- **(c) Corrected table, validated two independent ways** (exact symbolic
  set-partition route on 20 pairs; sieve numerics to 10^7), diverging
  from the published table from C_{2,5} on (published 28, corrected 52/3),
  extended to i = 20.
- **(d) A closed generating identity for the corrected C(v,w),**
  machine-checked exactly on batteries, with the special case
  C((a),(b)) = (-1)^{a+b} ab/(a+b-1). No comparable structure exists in
  the published values.
- **Consequence, stated within scope:** Bian's headline 0.9544 / 0.9774
  simple-zero proportions for xi'' / xi''' rest on the defective table in
  addition to his own flagged truncation assumption; corrected constants
  await a tail bound (the open gap this feeds). Everything is under RH
  and Bian's Theorem 1 hypotheses; the general identity is derived, its
  instances exact. Grade: hardened at the witnesses and instances.

## RF-C007 — Bian's headline constants do not follow from his printed table

- **Delivered 2026-08-17 (second session), inline.** Record:
  `fkappa/RESULTS.md` section 5.
- **Statement.** Bian's (11.5), validated on the two externally checkable
  rows (kappa = 0 gives Montgomery's 2/3 exactly; kappa = 1 gives
  Farmer-Gonek's 0.858384), evaluates his own printed Figure 10.1 rows to
  -202/36855 (kappa = 2) and -10284002/1216215 (kappa = 3): vacuous, at
  alpha = 1 and under alpha-optimization alike. The printed 95.44% and
  97.74% are not consequences of the printed table plus printed formula.
  With this campaign's corrected table the same formula gives a stable
  0.9533 for kappa = 2 (truncations 11 and 20 differ by 5e-5) and still
  nothing for kappa = 3 (partial bounds negative, drifting at i <= 20).
- **Grade:** hardened (exact rational arithmetic end to end; the formula
  chain is pinned by two external controls). The 0.9533 inherits RH,
  Bian's Theorem 1 hypotheses, and the truncation reading he himself
  used; the tail-bound programme is what would remove that last clause.
- **Status:** four arms launched on the follow-ups (theory: generating
  function and tail; data: extend rows, settle kappa = 3; plus the DH
  negative-eigenvalue hunt and window global optimality).


## RF-C008 — the corrected coefficient series have infinite radius; second derivative at 0.9578, third honestly out

- **Delivered 2026-08-17 (second session), FK-THEORY arm.** Record:
  `fkappa/RESULTS.md` section 6, `fkappa/theory_notes.md` (6 checkpoints),
  `theory_gf.py`, `theory_validate.py`, `row2_ext.json`, `row3_ext.json`.
- **(a) Master generating function.** The grand composition sum collapses
  to an operator resolvent (geometric series on the y-side, Neumann
  series of one order-kappa constant-coefficient operator on the z-side,
  rank-one jet kernel). Validated exactly against the independent
  14-fold-sum engine on all 36 values (kappa = 2, 3; i = 3..20) and all
  closed-form controls. Polynomial cost: row 2 extended exactly to
  i = 81, row 3 to i = 51.
- **(b) Tail bound, the campaign's target.** Derived (outline complete,
  constants unoptimized): |C_{kappa,i}| <= C_kappa^i / floor(i/2)!, a
  Gevrey-1/2 bound forced by the s-degree grading. Hence every corrected
  row's coefficient series has infinite radius of convergence, i.e.
  limsup |C_i|^{1/i} = 0. **Wording corrected 2026-08-18** after main's
  `d799aac` (a referee's catch on Pub 1's `F1`): the object with infinite
  radius is the series in the half-line variable, NOT F_kappa(alpha)
  itself. F_kappa carries |alpha| powers, so it has a corner at the
  origin and is neither entire nor differentiable there. The tail bound
  is unaffected: it is a statement about coefficients, and the
  alpha -> 1 and alpha-optimized evaluations below only ever use the
  series on the half line. Measured
  exactly to i = 81: (|C_i| Gamma(i/2+1))^{1/i} flat at ~1.13 (kappa 2),
  ~1.4 (kappa 3), ~0.66 (kappa 1 = Farmer-Gonek).
- **(c) Consequences, under RH + Bian Theorem 1 hypotheses.** kappa = 2:
  0.9532610039 at alpha -> 1 (10 digits stable across truncations
  30..81) and 0.9578404799 at the interior optimum alpha = 0.9723, which
  exceeds the thesis's printed 0.9544 while sitting strictly inside the
  expansion's validity range. kappa = 3: the series converges to a
  genuinely negative alpha -> 1 value (-0.8556; the i <= 20 drift was an
  oscillating-tail transient), and the alpha-optimum 0.4927 is far below
  Conrey's unconditional 0.9666, so this route currently says nothing
  useful about the third derivative: the published 0.9774 is not
  recoverable.
- **Status: PROMOTED (instances hardened; general identity and Gevrey
  bound derived, written proof pending; nothing kernel-checked).** The
  FK-DATA arm independently extended the rows with the (optimized,
  gate-checked) 14-fold-sum engine: kappa = 2 to i = 40, kappa = 3 to
  i = 28, disjoint code from the resolvent. Coordinator comparison:
  exact rational equality on every overlapping value, including all 28
  values beyond the previously validated i <= 20 range. The two arms
  also agree independently on the derived bounds (0.953261003869 stable
  to 12 digits; -0.855563 for kappa = 3; alpha-optima 0.957840 at
  243/250 and 0.492720 at 373/500, exact rationals from FK-DATA).
  FK-DATA extras: P-recursive structure decisively ruled out at
  R, D <= 6 in nine normalizations (18/18 negative with held-out
  prediction discipline); diagonal extended to i = 23, growth exponent
  near but not settled at 7/3.

## RF-C009 — first positivity failure of the truncated Weil form on the rival (DH-NEG)

- **Delivered 2026-08-17 (second session).** Record: `weil_trunc/RESULTS.md`
  section 8, `dhneg_scan.py`, `dhneg_confirm.py`, `dhneg_localize.py`,
  `dhneg_scan.json`, `dhneg_log.md`.
- **Statement.** For the Davenport-Heilbronn port of the truncated Weil
  form, the first negative eigenvalue on the scanned lattice appears at
  (c, N) = (31, 60), even sector: Rump enclosure
  -1.87393568857018838649e-31 with radius ~1e-241, ball LDL inertia
  conclusive, (31, 59) still positive, and the zeta control at the same
  cell is positive (+4.82e-100). No negativity for c <= 30 probed to
  N = 256. For c >= 32 the crossing N tracks the band edge hitting the
  off-line ordinate 85.699; the eigenvector localizes there (95.6% mass
  within +-6 at the deep cell), the ported dictionary attributes the
  negativity to the off-line quadruple term (the only negative entry,
  359x the eigenvalue), and a second negative eigenvalue from c >= 44
  tracks a second off-line pair (polished root 0.6508300806 +
  114.1633427308i, corroborated by a 4-vs-2 box-vs-line count).
- **Grade:** hardened for every sign statement; measured for the
  mechanism attribution. "First" is a lattice claim with explicit
  ceilings, stated as such.
- **Why it matters:** together with RF-C004(c) this completes the rival
  control on the 2026 truncated-form programme: the qualitative spectral
  signature is identical for zeta and an RH-violating function until the
  truncation resolves the off-line pair, and the failure height is now a
  measured curve, not a conjecture. Nothing here is evidence about RH.

## RF-C010 — the pairing count, kernel-checked (LEAN-MATCH)

- **Delivered 2026-08-18.** Record: `matchings/Matchings.lean`,
  `matchings/Probe.lean`, `matchings/LOG.md` (11 entries),
  `matchings/oracle.py`, scope note in `matchings/NOTE.md`.
- **Statement.** For a finite type with decidable equality and any
  `s : Finset`, with a pairing represented as an involution fixing
  everything outside `s`,

      (pairings s).card = if Even s.card then (s.card - 1)!! else 0

  with corollaries `card_pairings_two_mul` (a `2m`-set has `(2m-1)!!`),
  `card_pairings_eq_zero_of_odd`, `pairings_eq_empty_of_odd`,
  `two_pow_mul_factorial_mul_card_pairings` (`2^m * m! * count = (2m)!`,
  the Wick/Isserlis closed form), `even_card_of_pairsUp` (recovers
  Mathlib's `even_card` in this vocabulary), `card_pairings_univ`.
- **Grade: kernel-checked.** Zero `sorry`; no `native_decide` in any
  proof. Coordinator recompiled the file independently of the arm that
  wrote it: EXIT=0, and all seven public results report
  `[propext, Classical.choice, Quot.sound]`. 261 substantive lines.
- **Why it exists.** Hunt #48 (`r_8c3b94`) priced Erdos-Kac in Lean and
  named this count at step A2c as something "Mathlib does not have". The
  gap was re-checked here by querying the elaborated environment rather
  than by grep, because a `#check` can witness presence and never
  absence: the sweep for `Isserlis`/`Wick` returns empty, and of the 14
  declarations mentioning `PerfectMatching` the only cardinality result
  is the parity one. The same object is what this campaign's own
  `sine_gram` engine enumerates to compute `m_k`, which is how the
  connection was noticed.
- **Controls.** Kernel `decide` against the three-route enumeration
  oracle at n = 0..6 plus, importantly, a PROPER subset
  (`{0,1,2,3}` inside `Fin 5`, count 3): with `s = univ` the
  fix-outside-`s` clause is vacuous, so the `Fin n` cases alone cannot
  see a defect in it. Two lesion tests compile-fail correctly (replacing
  `(n-1)!!` by `n!!`; deleting the fix-outside clause).
- **Not done, named so nobody overreads it.** No bridge to
  `SimpleGraph.Subgraph.IsPerfectMatching` (est. 80-150 lines), and no
  bridge to `Finpartition`, which is the vocabulary Erdos-Kac step A2c
  actually consumes (est. 150-250 lines). A2c's *number* is now a
  theorem; A2c's *structural* need is that bridge and is not written.
- **Honest scope.** Erdos-Kac is a theorem of 1940 and this is one lemma
  inside one route to formalizing it. The contribution is library-shaped
  content plus one named blocker removed. Nothing here concerns zeta
  or RH.

## RF-C011 — first exact table of the Erdos-Pomerance f(n), and which shape it favours

- **Delivered 2026-08-18 (ERDOS-SCAN arm plus coordinator verification).**
  Record: `erdos_scan/FINDINGS.md` (17 surviving candidates from a sweep of
  all 1217 problems, ~20 killed with reasons).
- **The object.** Erdos problem 710/711: `f(n)` is minimal such that the
  open interval `(n, n+f(n))` contains distinct `a_1..a_n` with `k | a_k`
  for every `k <= n`. Erdos offered 2000 rupees for an asymptotic formula.
  Erdos and Pomerance proved
  `(2/sqrt e + o(1)) n (log n / log log n)^{1/2} <= f(n) <= (1.7398 + o(1)) n (log n)^{1/2}`,
  two shapes whose ratio is only `(log log n)^{1/2}`.
- **What was computed.** `f(n)` is a system of distinct representatives,
  hence a bipartite matching; `f(n)` is the least window admitting a
  left-saturating matching. Values (no table exists on the problem page,
  and OEIS has no such sequence):

      n        100    200    500   1000   2000   4000
      f(n)     160    340    877   1816   3814   7900

- **Independently verified.** The arm used Kuhn's algorithm; the
  coordinator re-derived `f(n)` from the definition with a different
  algorithm (Hopcroft-Karp) and a separate binary search, and reproduces
  160, 340, 877, 1816, 3814 exactly.
- **The signal, which is the point.** The two proven shapes move in
  OPPOSITE directions over the computed range:

      f/(n sqrt(log n))                  0.7456 -> 0.6917   (falling)
      f/(n sqrt(log n / log log n))      0.9214 -> 0.9851   (rising)

  So the data favour the lower bound's shape, `(log n / log log n)^{1/2}`,
  as the correct one, with its ratio still climbing toward the proven
  constant `2/sqrt e = 1.2131` (the `o(1)` is large at these sizes, since
  `log log 2000 = 2.03`, so this is consistent with the theorem rather
  than in tension with it).
- **Grade: measured.** This is data plus a reading of a trend over one
  decade and a half. It is not a theorem, it does not settle the
  asymptotic formula, and a trend that reverses further out would
  overturn the reading. Recorded as the first table, which is checkable
  by a stranger in seconds, plus an honest direction.
- **Mining note.** 7 comments on 710, 8 on 711, one self-declared worker
  on each. Lightly mined, not untouched; no prior table was located.

## Process observation — the shared-checkout hazard, met twice

Both arms reported that a concurrent session in this same checkout swept
their in-flight files into commits via a broad `git add -A`. That was this
coordinator, checkpointing against session death. The two habits are in
direct conflict, and `CLAUDE.md` already names the fix: parallel work
belongs in `git worktree`s, not in one shared checkout. Recorded because
the arms were right to flag it and the next campaign should not repeat it.
