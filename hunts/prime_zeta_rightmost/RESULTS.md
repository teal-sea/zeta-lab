# RESULTS: the rightmost zeros of the prime zeta function

Run of 2026-08-16. Instruments: `decide.py` and `theorem_inputs.py` (decided
constants), `controls.py` (WP5), `witness.py` (WP6); raw numbers in
`decided.json`, `theorem_inputs.json`, `controls_results.json`,
`witness_results.json`; the mathematics in `THEOREM.md`; the pinned sources
in `SOURCE.md`. Vocabulary contract throughout (MISSION.md): *measured* is
one float route, *decided* is an interval or ball enclosure whose exact
endpoints settle a sign, stated with backend and precision, *heuristic* is
an order-of-magnitude model with measured inputs. Nothing in this directory
is a repo-level result until the case log in `hunts/README.md` says how the
hunt ended.

**The headline.** Both conjectures in OEIS A107311's Dec 21 2024 comment
are false. The supremum of the real parts of the zeros of the prime zeta
function P(s) = sum_p p^(-s) is not x* = 1.7286... (the root of
zeta(x) = 2) but sigma_c = 1.779544653546994116445898786965...
(decided, both backends), the root of the balance P(sigma) = 2^(1-sigma),
which exceeds x* by more than 1/20 (decided). The supremum is approached
by infinitely many zeros and attained by none (Theorems A and B,
THEOREM.md). The subset conjecture fails without bound: {p >= 3} already
has zeros beyond sigma_c, and the tail subsets {p >= p_k} have thresholds
tending to infinity (Theorems C1, C2). The refuting zeros live in
Re s > 1, where every reading of "the prime zeta function" agrees with the
series, so the refutation is reading-independent. No explicit zero is
exhibited; existence is by a Bohr-Kronecker-Rouche argument with every
numeric inequality decided on both backends.

## 0. The source

OEIS A107311, "Decimal expansion of the solution to zeta(x) = 2." Fetched
2026-08-15 as JSON and refetched live 2026-08-16; the two fetches are
byte-identical (empty diff). Entry revision 55, last modified
2024-12-29T23:50:41-05:00; the conjecture comment is dated Dec 21 2024
inside the entry. The full JSON body is pinned byte-for-byte in SOURCE.md
section 1. The comment field, word for word as served (spelling as served:
"partials sums", "Riemman", "the anyone subset" are in the source):

> From _Artur Jasinski_, Dec 21 2024: (Start)
> Borwein et al. (2007) proved (Theorem 3.1) that the real parts of the zeros of the partials sums of the Riemman zeta functions are not greater than this constant.
> Conjecture 1: the real parts of the zeros of the prime zeta function are not greater than this constant.
> Conjecture 2: the real parts of the zeros of the anyone subset of the prime zeta function are not greater than this constant. (End)

"This constant" is x*, the real root of zeta(x) = 2, whose correct role is
the partial-sums-of-zeta threshold (Borwein, Fee, Ferguson, van der Waall
2007, Theorem 3.1, pinned through two independent secondary quotes in
SOURCE.md section 3: Platt-Trudgian 2016 and Gonek-Ledoan 2010). The only
prior literature found on zeros of P itself is Froberg 1968 (four
numerically observed roots, "very little is known"); the search log is
SOURCE.md section 4.

## 1. The decided constants

Backends, deliberately independent code paths: **flint** = python-flint
0.9.0 (arb balls) at 350 bits, arb zeta direct for x*, Moebius series
K = 120 with a proved tail bound for P; **iv** = mpmath.iv 1.3.0 at
dps 40, zeta by finite Dirichlet sum plus Euler-Maclaurin tail with a
decided remainder (iv.zeta raises on call in mpmath 1.3.0), Moebius
K = 40. Bracket bookkeeping is exact Fractions on both legs. Derivations
of every tail bound are in `instrument.py`.

| constant | flint (arb, 350 bits) | width | mpmath.iv (dps 40) | width |
|---|---|---|---|---|
| x* (root of zeta(x) = 2) | [1.7286472389981836181351030102976660, 1.7286472389981836181351030102977450] | 7.889e-32 | [1.7286472389981835995, 1.7286472389981836884] | 8.882e-17 |
| sigma_c (root of P(s) = 2^(1-s)) | [1.7795446535469941164458987869654405, 1.7795446535469941164458987869655195] | 7.889e-32 | [1.7795446535469636, 1.7795446535470547] | 9.095e-14 |
| sigma_3 (root of u(s) = P(s) - 2^(-s) - 2*3^(-s)) | [1.8252259560738457623878727108889264, 1.8252259560738457623878727108890054] | 7.889e-32 | [1.8252259559929, 1.8252259560861] | 9.313e-11 |

Cross-checks, all decided: each flint interval lies inside its iv
interval; the OEIS entry's 102-digit value interval lies inside both x*
enclosures. Each constant is the unique root of a strictly decreasing
function on its bracket (zeta termwise-exactly on (1, 2); h and u by
decided derivative guards on [1.7, 1.9] and [1.80, 1.85], both backends),
and each bisection first decided its bracket endpoint signs.

The decided comparisons feeding THEOREM.md, every one decided on both
backends:

- **separation**: sigma_c - x* > 1/20, exact rational compare of
  enclosure endpoints; lower bound of the difference 0.050897414548810498
  (flint), 0.05089741454877 (iv).
- **margin**: h(x*) = P(x*) - 2^(1-x*) > 1/60, with h evaluated over the
  whole x* enclosure; flint enclosure [0.016907377213856298105802854273997,
  0.016907377213856298105802854274113].
- **D1**: h(7/4) in [0.009465637293734518587514821979513,
  0.009465637293734518587514821979514] (flint, width 1.275e-65; iv
  confirms); > 1/128.
- **D2**: u(9/5) in [0.004312491729413063275865581947004,
  0.004312491729413063275865581947005] (flint, width 1.897e-67; iv
  confirms); > 1/256.
- **D3**: log2(69/(5 log 23)) in [2.137903503656002856060611381367,
  2.137903503656002856060611381368] (flint width 1.423e-104; iv width
  1.837e-40, agreeing to all displayed digits); > 17/8.
- **W1-W5** (window compares, exact Fractions against outward-rounded
  endpoints): hi(x*) < 173/100; lo(sigma_c) > 7/4; lo(sigma_c) > 177/100;
  hi(sigma_c) < 89/50; lo(sigma_3) > 91/50.

Preregistration P1 and P3 check boxes recorded in `decided.json`: all
true.

## 2. The replacement theorem

Full statements and proofs in THEOREM.md; the shape:

- **Theorem A (the wall, proved there).** For prime q and sigma_c(q) the
  unique root of the balance q^(-sigma) = sum_{p>q} p^(-sigma): P_q has no
  zero with Re s >= sigma_c(q). Triangle inequality for Re s > sigma_c(q);
  the equality case on the line Re s = sigma_c(q) is excluded by
  multiplicative independence of the primes (Lemma 3, from unique
  factorization). Exact mathematics, no numeric input; the numerics only
  locate sigma_c and sigma_3 and compare them with x*.
- **Theorem B (existence up to the wall, proved there).** For every
  window (sigma_1 - eps, sigma_1 + eps) inside (1, sigma_c(q)), P_q has
  infinitely many zeros with Re s within eps/2 of sigma_1, imaginary parts
  unbounded. Proof: phase the whole series to vanish at sigma_1 (polygon
  Lemma 2 with the tail aggregated as one side), then steer actual
  vertical translates onto the phased model by Kronecker-Weyl (Lemma 4,
  proved via Weyl's method with positive lower density) and transfer the
  zero by Rouche. Corollary B1: sup of the real parts equals sigma_c(q),
  not attained.
- **Theorem C1 (subsets, proved there).** The same pair of theorems for
  q = 3: zeros of sum_{p>=3} p^(-s) fill windows below sigma_3, in
  particular (1.78, 1.82), which is beyond sigma_c: the decided enclosures
  give sigma_3 - sigma_c > 0.0456813 (exact rational compare on the flint
  legs).
- **Theorem C2 (unbounded walls, proved there).** For p_k >= 23,
  sigma_c(p_k) >= log2(3 p_k / (5 log p_k)) -> infinity, from
  Rosser-Schoenfeld Corollary 3, inequality (3.8). Decided instance: the
  {p >= 23} wall exceeds 17/8 (D3). Corollary C3: no constant bounds the
  zeros over all subsets.

Proof status of each step (THEOREM.md section 6): **decided** on both
backends: every numeric input (section 1 above; no claim rests on a
measured-only number). **Proved in THEOREM.md** with complete proofs:
Lemmas 1, 1a (Euler), 2 (polygon), 3 (independence), 4 (Kronecker via
Weyl), 5 (triangle equality); Theorems A, B, C1, C2; Corollaries B1, B2,
C3. **Cited without reproof**: the fundamental theorem of arithmetic,
Rouche, Stone-Weierstrass on the torus, Rosser-Schoenfeld (3.8), and
standard analysis facts; hypotheses checked explicitly where used.

Gaps and honesty notes, as declared in THEOREM.md section 8, restated
here at full prominence:

- **Citation numbering from memory.** The theorem/section numbers for
  Hardy-Wright, Rouche's textbook placements and Rudin (items 2, 4, 5 of
  THEOREM.md section 7) were not re-checked against copies this session.
  The load is bibliographic, not mathematical: every argument using them
  is proved in full in THEOREM.md or has its hypotheses checked against a
  stated standard form. The one externally load-bearing count,
  Rosser-Schoenfeld (3.8), was re-checked against the paper's scanned text
  this session.
- **Not kernel-checked.** No Lean formalization of any step exists; the
  ladder's top rung is untouched. A natural later rung: Lemma 2 plus
  Theorem A.
- **No explicit witness zero** (section 5 below; per MISSION.md its
  absence changes nothing).
- **Instrument defect, found and fixed.** The first D3 run produced
  disjoint enclosures on the two backends: MISSION.md kill condition 3
  fired and correctly marked the instrument. `iv_endpoints` in
  instrument.py had converted interval endpoints through the global mp
  context (dps 15), collapsing iv results to one 53-bit float. Sign
  decisions were never at risk (nearest rounding at relative precision
  cannot move a value across zero); value enclosures beyond 15 digits
  were misreported. Fixed to read the raw `_mpi_` endpoints; `decide.py`
  re-run reproduced `decided.json` identically except timings.
- **The Rouche step closes** (kill condition 1 did not fire): the model
  series carries its own tail (aggregated as one polygon side), so the
  remaining errors are the steering term and the beyond-Y remainder, both
  cut after the isolating minimum m is fixed. No assumption left
  undischarged.

## 3. The refutation ledger

| claim | verdict | falls by |
|---|---|---|
| Conjecture 1 (zeros of P bounded by x*) | **false** | Theorems A + B. Corollary B2: infinitely many zeros of P with Re s in (1.73, 1.77), each > x* (decided W1, W3); Corollary B1: the true supremum is sigma_c > x* + 1/20 (decided separation), approached, not attained. |
| Conjecture 2 (zeros of every prime-subset series bounded by x*) | **false, twice over** | (i) the {p >= 3} threshold: Theorem C1 gives infinitely many zeros of P_3 with Re s in (1.78, 1.82), beyond x* and beyond sigma_c itself (decided W4, W5; sigma_3 - sigma_c > 0.0456813 decided). (ii) unboundedness: Theorem C2 + Corollary C3, the tails {p >= p_k} have walls >= log2(3 p_k/(5 log p_k)) -> infinity (decided instance: {p >= 23} wall > 17/8, D3), so no replacement constant exists either. |

What is *not* refuted or claimed: nothing about zeros with Re s <= 1 or
about the continuation beyond the series' half-plane; nothing about
finite subsets (the conjecture quantifies over all subsets, so the
infinite witnesses settle it); nothing about RH (the zeros produced are
zeros of P and of subset series, not of zeta); and x* keeps its correct
role as the partial-sums threshold of Borwein-Fee-Ferguson-van der Waall.

## 4. Calibration control and lesions (WP5)

All in `controls_results.json`; the solver under test is
`decide.bisect_decreasing`, the same function object `decide.main()` calls
(asserted identical to `instrument.bisect_decreasing` at import), and the
baseline sigma_c re-solve reproduced the recorded interval strings
exactly.

- **Calibration (known answer, same code path): PASS.** The
  zeta-partial-sums balance (leading term 1 against sum_{n>=2} n^(-sigma),
  root of zeta(sigma) = 2) run through the same solver with sigma_c's
  bracket recovers x*: flint enclosure
  [1.7286472389981836181351030102976660,
  1.7286472389981836181351030102977450] (350 bits, width 7.889e-32),
  OEIS value interval inside both backend enclosures; 31 of the entry's
  digits reproduced on the flint leg, 13 on the iv leg. P2 held.
- **Lesion 1 (input sensitivity): PASS.** Dropping the p = 3 term from
  the tail moves the root to
  [1.4293161356678019330620811031492544,
  1.4293161356678019330620811031493235] (flint, 350 bits): a decided
  shift from sigma_c of
  [0.3502285178791921833838176838161, 0.3502285178791921833838176838163],
  decidedly below x* as well. The solver reads its input, not a cache.
- **Lesion 2 (the mis-port made mechanical): PASS.** Keeping the zeta
  series but balancing P's leading term 2^(-sigma) against the tail after
  it lands at [2.4241112509134051299681251496785051,
  2.4241112509134051299681251496785939] (flint, 350 bits), decidedly
  equal to neither x* nor sigma_c: the balance template and the series
  fed to it both matter.
- **Precision response: PASS.** The sigma_c code path at 60 / 120 / 200
  bits achieves widths 1.421e-15 / 6.163e-34 / 1.020e-57, strictly
  shrinking, all intervals nested consistently with the 350-bit run.
- **Rerun reproducibility: PASS.** `decide.py` re-run in a subprocess
  reproduced `decided.json` line for line with only `time_s` lines
  differing.

## 5. The witness hunt (WP6) and prediction P4

Budget-capped bonus hunt for an explicit zero near sigma_1 = 7/4; absence
was the pre-registered expectation and changes nothing above.

- **Margin analysis (decided, flint 350 bits, iv confirming).** The
  coherence budget at sigma_1 = 7/4 is eps_0 = h(7/4) in
  [0.009465637293734518587514821979513,
  0.009465637293734518587514821979514]: the p >= 3 resultant must shed
  less than one percent of its fully aligned modulus
  (R in [0.306767416044414785266889814619632, ...633]) to land on the
  p = 2 term (r_2 in [0.297301778750680266679374992640118, ...119]).
  eps_0 > 0 decided on both backends: cancellation is feasible in
  principle.
- **Expected height (heuristic, labeled as such).** A von Mises tilted
  importance-sampling model of the phase-coherence probability (checked
  against plain Monte Carlo at loose eps: agreement within 0.05 combined
  standard errors) puts Prob(loss <= eps_0) at about 4.1e-16 on the line
  budget, giving an expected first-witness height of order 1.6e16
  (line-exact) to 1.7e10 (window-wide budget h(x*)); expected zero count
  below t = 1e8: 6.1e-9 (line) to 0.0059 (window). The margins are parts
  in a thousand, as MISSION.md anticipated.
- **Screen (measured, numpy float64).** sigma = 7/4 exactly, t in
  [0, 1e8], 146,961,923 points at step 0.6804; head primes p <= 47 with
  the pointwise bound ||P| - |F47|| <= 0.013200; two refinement passes
  (p <= 1e4, then p <= 1e6 with all-integer tail bound 4.216e-5). Global
  refined minimum |P| = 0.010021 at t = 56316681.51 (float interval
  [0.009979, 0.010063], above the eps_0 budget). No point reached the
  candidate gate |P| < 1e-4: zero candidates.
- **Box counter (validated, never fired in earnest).** The
  argument-principle counter (python-flint acb, 192 bits, Moebius K = 25)
  passed both controls: a null box at a coarse-grid |F| maximum decided
  winding 0, and a planted-zero box (P minus the exact dyadic midpoint of
  its ball value) decided winding 1.
- **Verdict**: no witness; `witness_decided_exists: false`. **P4
  confirmed**: no explicit witness zero below t = 1e8.

## 6. Predictions P1-P4, settled

- **P1 (decided enclosures land in the pre-registered windows): held.**
  sigma_c in [1.77954465, 1.77954466] and x* in [1.72864723, 1.72864724]
  on both backends; separation > 1/20 decided on both.
- **P2 (calibration recovers the partial-sum threshold): held.** The
  OEIS value interval lies inside both same-code-path enclosures; 31
  digits reproduced on the flint leg (against "within its published
  digits": the enclosure width, 7.889e-32, is what bounds the digit
  count, and every reproduced digit matches the entry).
- **P3 ({p >= 3} threshold in [1.82522, 1.82523]): held.** Both
  backends.
- **P4 (no explicit witness below t = 1e8): held.** The screen found no
  candidate; the pleasant surprise did not occur.

## 7. Honest scope

- **Which reading of "zeros of the prime zeta function" is covered.**
  All of them. The refuting zeros have Re s > 1, inside the half-plane of
  absolute convergence, where the defining series, Glaisher's
  continuation and every branch of it agree; a zero there is a zero under
  every reading (SOURCE.md section 2). Nothing is claimed about
  0 < Re s <= 1, where the continuation has logarithmic branch points and
  the line Re s = 0 is a natural boundary, and nothing about finite
  subsets.
- **Novelty caveat.** The wall-plus-Bohr-steering mechanism is classical
  for general Dirichlet series, and a specialist may regard the
  sigma_c threshold as folklore-derivable; the searches logged in
  SOURCE.md section 4 (2026-08-16: exact-phrase, zbMATH API, MathWorld,
  citation hunts) found no source stating any rightmost-zero threshold
  for P, and only Froberg 1968 touching its zeros at all, but that is a
  record of queries run, not a completed search of record (no MathSciNet,
  no zbMATH full text). The deliverable therefore stands as: the OEIS
  correction, plus the first explicit treatment found for P specifically,
  with decided constants. **Original is claimed; novel is claimed only as
  "no prior source found by the logged searches".**
- **Composite grade.** Decided numeric inputs (both backends, exact
  endpoint sign logic) glued by classical mathematics proved in
  THEOREM.md or cited with checked hypotheses. By the certainty ladder a
  composite takes its weakest step: this is a decided-plus-proved
  composite, not kernel-checked, and the heuristic height model in
  section 5 is a labeled aside that carries no claim. Nothing here uses
  the reserved enclosure vocabulary of `zeta/rigor.py`, and nothing here
  bears on RH.

## Disposition

Instruments (`instrument.py`, `decide.py`, `theorem_inputs.py`,
`controls.py`, `witness.py`) retained. `OEIS-CORRECTION.md` drafted
alongside this file; posting anything to OEIS is an operator action, not
this hunt's (MISSION.md, agents_may_not). No claim is promoted by this
file; the case-log entry in `hunts/README.md` and any docs/ page are the
close-out steps that remain.
