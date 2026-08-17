# REPORT — the rogue_frontier campaign, 2026-08-17

One autonomous session: environment built from a fresh clone, an 11-way
primary-source survey of the RH-adjacent frontier, a scored portfolio, five
studies executed through a discovery / destruction / rigor pipeline, three
worker sessions ended early by a session token limit with all state
checkpointed. Everything below sits inside `hunts/`, so by this
repository's rules nothing here is a result until it leaves by the battery
or the funnel; grades are the repository ladder. Nothing here is evidence
for or against RH.

## BEST RESULT

**The Bian audit (RF-C006).** The only computation of the pair-correlation
form factor for zeros of xi'' and xi''' in the literature (Ji Bian, PhD
thesis, Rochester 2008, unpublished, cited by Bui) is defective beyond its
own flagged truncation assumption: three separate defects, each pinned by
an exact finite rational witness, with the kappa = 1 row (the only row
independently checkable against Farmer-Gonek) immune to all three, which
is why 18 years passed unnoticed. A corrected table was computed and
validated by two independent routes, and the corrected constants turn out
to have structure the published ones lack, including the closed form
C((a),(b)) = (-1)^{a+b} ab/(a+b-1) and a rational generating identity.

## EXACT CLAIM

For the coefficient table of Bian's Theorem 1 expansion of
F_kappa(alpha,T): (i) the thesis code's assembly drops nonzero (l,k)
pairs from i = 7 (witness: consikapa(6,2,3,2) = 1/30 while the figure
code omits it, so published C_{2,7} = 544/45 differs from the thesis's
own eq (10.1) value 352/45); (ii) terms with a phantom slot are exactly
zero by the printed formulas yet evaluated nonzero by the code (witness:
|C((j),(1))| = 1 exactly vs 6/5, 7/6, 9/7 for j = 3, 4, 5); (iii)
eq (6.18) overcounts each side by prod_i alpha_i! (witness at n = 6:
Lambda_2(6) log 6 = 2 log2 log3 log6 against the printed RHS
4 log2 log3 log6). The corrected table diverges from the published one
from C_{2,5} on (28 published, 52/3 corrected).

## STATUS

Level C in the campaign directive's ladder (rigorous computational
result: exact rational arithmetic end to end); repository grade hardened.
The three witnesses are finite computations a stranger can replay in
minutes from `fkappa/REPRODUCE` steps. The generating identity is
hardened at its checked instances, derived in general (a written proof
is routine but not written).

## NOVELTY

Bian's thesis is the unique source for these tables (one citation, Bui
2010, which reproduces no formula). No erratum or recomputation exists in
anything surveyed; the audit, the corrected table, and the closed form
are original to this session in the provenance sense. Caveat recorded in
the ledger: a targeted search for any later recomputation of Bian's
tables has not been run beyond the sources named; per this laboratory's
knownness rule the novelty claim awaits that search.

## PROOF / EVIDENCE

`fkappa/RESULTS.md` (witnesses, validation batteries, corrected tables to
i = 20), `fkappa/bian_engine.py` (literal port + fast engine, exact
agreement), `fkappa/validate_pairs.py` (20-pair symbolic battery),
`fkappa/validate_numeric.py` (sieve to 10^7), `fkappa/closed_form.py`.

## INDEPENDENT VERIFICATION

Within-campaign: the literal Mathematica port and an independently
reorganised fast engine agree exactly; the corrected constants are
confirmed by a symbolic set-partition route that shares nothing with
chapters 6-7 of the thesis, and separately by sieve numerics. External
verification is pending, as it is for everything this laboratory
publishes.

## REMAINING GAP

The tail bound Bian himself flagged: the corrected table still feeds an
expansion whose i-tail is unbounded for kappa >= 2, so corrected
simple-zero proportions for xi'', xi''' remain conditional on truncation.
The generating identity is the plausible route to that tail bound and is
the named next step.

## WHY IT MATTERS

Every future use of the xi-derivative pair-correlation constants must
route around the published table; the corrected one, with exact
witnesses, is now the state of the art for kappa >= 2, and its rational
structure suggests the tail problem is tractable, which would turn
Bian's program into theorems.

## OTHER RESULTS

- **RF-C003 (PROMOTED, hardened, RH-conditional).** In the Aug 2026
  two-thirds paper's SS7.5(g) chain, the hand-picked window cos(8s/5) is
  not a critical point; the rational window 1 - (1467/1000)s^2 +
  (1159/1000)s^4 gives 2m_2 - m_3 = 2245228120295149280/3276332462159207451
  and lifts the distinct-zeros constant to
  50176758585216887915/58973984318865734118 = 0.8508287029... (+2.4e-6).
  Independently re-derived blind (bit-identical rationals), enclosure-
  checked in both ball backends, admissibility strictly cleaner than the
  paper's own window. Inherits RH and the unrefereed source chain.
- **RF-C004 (hardened + measured).** Full replication of the 2026
  truncated-Weil-form postings (no defect found; two cancelling display
  slips in CCM documented); ball-arithmetic positivity of all 27 spectral
  grid cells; and the first structure-matched control on that programme:
  the RH-violating Davenport-Heilbronn function shows the identical
  qualitative signature (positive spectrum, ground state locating its
  zeros), so only the quantitative error floor (~49 orders at c = 13)
  separates zeta from the rival, and its attribution is confounded
  (RH-truth / Euler product / pole all differ at once). Follow-up
  observation for an issue: DH's first negative eigenvalue must exist and
  sits beyond c = 47 at N <= 32.
- **RF-C002 (hardened).** m_5(1) = 101/18, m_6(1) = 640/63 for the
  sine-kernel Gram moments (literature stops at 13/4), exact
  E tr T^k quasi-polynomials in N, and a piecewise-in-lambda structure
  with defect pieces switching on at lambda = 1/j.
- **RF-C001 (hardened).** The paper's m_4 = 13/4 verified exactly after
  this campaign's own first engine said 49/15; the defect was ours
  (Gaussian trace-moment approximation out of regime), caught by the
  assume-your-own-bug reflex, and the exact engine that settled it became
  the instrument for RF-C002.
- **RF-C005 (hardened, partial).** Enclosure-grade Baez-Duarte distances
  d_N^2 to N = 2048 via a five-way-validated Vasyunin pipeline; the
  approach to C = (2 + gamma - log 4pi)/2 is from below in range, and
  finite-N extrapolation is measurably delicate.

## DEAD ENDS

`FAILURE_LEDGER.md`: the xi' variational window (already solved inside
this repository by `hunts/wide_search/`, killed pre-work as lab prior
art); the scalar-moment LP over window certificates (collapses, killed by
two prior hunts); the F_1 closed form (a CAS one-liner over a classical
generating function, killed by novelty audit with the honest verdict
"routine"). The killed-before-spend rate is the campaign working as
specified.

## NEXT THREE EXPERIMENTS

1. Prove the generating identity for the corrected C(v,w) in general and
   extract a tail bound for the i-sum at fixed kappa; recompute the
   xi''/xi''' simple-zero proportions with a controlled truncation error.
   (Highest expected value; the object is now rational and structured.)
2. The configuration-level LP over marked periodic configurations against
   the 0.68185 ceiling, starting from the paper's N = 256 extremal-law
   artifact (available on request per wide_search).
3. Locate the first negative eigenvalue of the truncated Weil form for
   Davenport-Heilbronn (c > 47), giving the first quantitative
   positivity-failure height for the 2026 spectral programme and a clean
   discriminating statistic to report as an issue.

---

# ADDENDUM — second wave, 2026-08-17 (later sessions)

The token cutoff ended the first wave; a second session salvaged all
checkpointed state, then ran four more arms. Everything below is in the
ledger with full records; grades as stated there.

## The best result upgraded

The Bian audit grew from "the published table is defective" into a
complete replacement of the thesis's quantitative content:

1. **RF-C007.** The thesis's own bound formula (11.5), validated on two
   external controls (Montgomery's 2/3, Farmer-Gonek's 0.858384),
   evaluates the thesis's own printed table to vacuous bounds
   (-202/36855 and -10284002/1216215). The printed headlines 95.44% and
   97.74% do not follow from the printed data by the printed formula.
2. **RF-C008 (PROMOTED).** The corrected coefficients collapse to an
   operator resolvent; every corrected row is entire (derived
   Gevrey-1/2 tail bound, the exact property whose absence capped the
   thesis); two disjoint exact engines agree on every coefficient
   (kappa = 2 to i = 40, kappa = 3 to i = 28, resolvent values to
   i = 81/51). Consequences under RH + the thesis's Theorem 1
   hypotheses: at least 0.953261 of zeros of the second xi derivative
   are simple (0.957840 at the interior alpha optimum, exact rational
   243/250), exceeding the unreproducible printed 0.9544; for the third
   derivative the route is honestly vacuous at alpha -> 1 (series
   converges to -0.8556) and the alpha optimum 0.4927 stays far below
   Conrey's unconditional 0.9666. P-recursive structure is ruled out at
   orders R, D <= 6 in nine normalizations.

## Also landed in the second wave

- **RF-C009.** First positivity failure of the truncated Weil form on
  the RH-violating rival: (c, N) = (31, 60), enclosure-checked, zeta
  control positive at the same cell, mechanism pinned to the off-line
  pair (localization + dictionary attribution), second negative
  eigenvalue tracking a second off-line pair (polished root
  0.6508300806 + 114.1633427308i). Published as issue #57.
- **RF-C003 caveat upgraded.** The window optimum is the unique strictly
  positive stationary point across 336 starts and exactly unique on the
  quartic slice; sup F is bracketed by exact rationals
  [0.685287032176998, 0.892744211644411]. Global optimality remains
  open and is stated so.

## Revised next three experiments

1. Write the general proof of the resolvent identity and the Gevrey-1/2
   bound with explicit constants (currently derived with outline), then
   attack the remaining B-growth tail so the 0.9578 claim carries only
   RH, not the truncation reading. A Lean formalization of the
   finite-witness layer (the three table defects and the (11.5)
   evaluations) is formalization-shaped and would put kernel grade on
   the audit.
2. Close the [0.6853, 0.8927] window bracket: rule out near-two-point
   limiting spectral measures for windowed sine-Gram operators (needs
   third-moment information; the machinery for it now exists in
   sine_gram/).
3. The configuration-level LP against the 0.68185 ceiling (unchanged
   from the first wave; needs the source paper's N = 256 artifact).
