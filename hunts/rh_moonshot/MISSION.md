# MISSION: `rh_moonshot`, six RH-direct mechanisms pushed to a construction or a located obstruction

**Opened 2026-10-21. Hunt #150.** The owner directed this hunt on 2026-10-21 as a genuine
attempt at the Riemann hypothesis itself, beside the campaign's other tracks: build real
constructions and push each one as far as it goes. `ALIGNMENT.md` section 0 permits the
attempt and keeps the proof requirement: claiming RH needs the complete proof. Nothing in
this directory is a result until the case log in `hunts/README.md` says how it ended.

Grades used here: *measured* (one route, float grade), *hardened* (independent routes
agree, or Arb ball enclosures carry every step), *derived* (an ordinary argument, always
stated with its review status: self-reviewed, reviewed by a separate session, or pending
external review) and *kernel-checked* (Lean 4 with Mathlib, zero `sorry`, only `propext`,
`Classical.choice` and `Quot.sound`). A composite claim takes the grade of its weakest
step. The reserved enclosure word belongs to `zeta/rigor.py` and the Lean arm and appears
nowhere in this directory, in any form, including the names of `rigor.py`'s own routines,
which are cited here by role.

## The question

> Can any of six materially different mechanisms, `ccm_arithmetic`, `de_branges`,
> `li_arithmetic`, `positivity_geometry`, `spectral_operator` and `probe_tower`, be pushed
> to a construction that proves RH, or else to a precisely located obstruction: the step
> that fails, the rival or theorem that makes it fail, and the information that step
> reads?

Both outcomes count. A located obstruction is a statement about that construction at its
stated hypotheses. It is never a verdict that no route to RH exists (`ALIGNMENT.md`
section 5.1).

## Why six at once

`ALIGNMENT.md` section 4 asks for genuinely different mechanisms to be compared cheaply
before a campaign commits to one family, and for each candidate to get a bounded chance to
produce an identity, kernel, estimate, counterexample or lemma. The six below read
different information and, where they stall, stall at different steps: the spectrum of
truncated Weil forms as the window grows, the Hermite-Biehler structure of an entire
function, the Li coefficients of xi through prime sums, an intersection-type positivity,
the self-adjointness of an operator, and zero-free half-planes from probes of growing
degree. A step one of them cannot cross may be crossed by another, and a challenge to one
does not close the others.

`docs/09` section 5.1 states what a positive construction owes (arithmetic provenance, an
exact trace realization, structural positivity) and names five evasions that have
absorbed real programmes: direct estimation, tautological completion, zero-importing,
formal C*-positivity and finite approximants. Each mechanism's notes say which of them
apply to it.

## The frontier this hunt starts from

Every RH-direct route in the laboratory's record so far stalls at an all-order,
all-window or all-height step, or is passed by the Davenport-Heilbronn function (DH),
whose zeros include 0.808517 + 85.699348i (`hunts/rh_resolve`, `docs/08`).

- **All orders.** Li's criterion needs lambda_n >= 0 for every n. `rh_resolve` holds
  positive rows for n = 1..58 (measured; its own audit withdrew their enclosure grade) and
  a float scan to n = 100, with no uniform tail. Every fixed cutoff of the Laguerre
  inequalities (`rh_theta_laguerre`) and every fixed number of central-moment matrix tests
  (`central_moments`) is passed by a function with non-real zeros.
- **All windows.** Weil positivity on every window is equivalent to RH, and it is
  established only on fixed windows: classically for small support (Yoshida; Connes and
  Consani), by a computer-checked argument for support 1.6 (Zhu, arXiv:2608.24827) and,
  in the even sector, for support 2.38 (`oob_envelope`, hardened, pending external
  verification), with a margin that decays doubly exponentially in the window length.
  `weil_propagation` found no mechanism in its searched set that carries positivity from
  one window to a larger one, and its C4 instance at S = {inf, 2} is unresolved, with
  measured evidence against its bounded-rank prediction (`weil_propagation/c4_s2`).
- **All heights.** RH is verified to height 3e12 (Platt and Trudgian, 2021), which says
  nothing above that height; hunt #137 (`rh_height_lean`, on its branch) aims at a
  kernel-checked statement to T = 50.
- **Passed by DH.** The de Bruijn-Newman constant lies in [0, 0.2] (Rodgers and Tao;
  Platt and Trudgian), while DH's own constant is at least 0.0577 (measured,
  `flow_repair`), so smallness of Lambda distinguishes nothing. The heat-flow repair clock
  and the Jensen-degree clock read only the zero configuration (`flow_repair`,
  `jensen_clock`); zero-side Weil comparisons with a positive test function are powerless
  by construction (`rh_resolve`); and the Jensen wedge construction succeeds for DH
  exactly as for zeta (`jensen_wedge`, section 15).
- **Strips.** Re s > 7/8 for every Dirichlet L-function (OpenAI, 2026) is kernel-checked
  here on two kernels, pending human review of its argument (`docs/08` section 1.1,
  `docs/38` section 7). A fixed strip is not RH; hunt #136 (`below_seven_eighths`, on its
  branch) works below 7/8, not at 1/2.

## The six mechanisms

Each mechanism gets a directory `hunts/rh_moonshot/<mechanism>/` holding a `NOTES.md` and
at least one test that could fail. The construction states the exact target and its
relation to RH, builds the specific object rather than naming a technique, names the step
where zeta's Euler product or multiplicativity enters, tests that step on the rivals
below, engages the known obstructions, and pushes to the furthest true statement it can
reach, with its grade.

1. **`ccm_arithmetic`: step 2 of Connes, Consani and Moscovici, with an arithmetic
   input.** On windows of length log c, the truncated Weil form of CCM (arXiv:2511.22755,
   prime sum over n <= c) has a lowest eigenvector v_c. Connes and van Suijlekom
   (arXiv:2511.23257, Prop. 4.1) prove, for any real distribution, that when the lowest
   eigenvalue is simple and isolated with an even eigenfunction, its Fourier transform F_v
   has only real zeros. CCM section 8 names two missing steps: (1) simplicity and evenness
   for every c, and (2) a prolate approximation of the ground state good enough for the
   zeros to converge. In the form used here, (2) is convergence of F_v, suitably
   normalized, to Xi on compact sets, and Hurwitz's theorem then gives RH (Connes,
   arXiv:2602.04022, section 6, states the same two steps). Step 2 is the distinguishing
   one: wherever DH's ground state is simple and even its transform also has only real
   zeros, so the DH analogue of step 2 must fail near the off-line pair at height 85.699
   (`weil_propagation/theory/RESULTS.md`, section C3). The record's named arithmetic
   candidate is the semilocal unitary decomposition (U-S), which Epstein (1,1,6) fails at
   n = 6 and n = 8 and W_a at n = 2 (same file, section 7.1). First test: measure how F_v
   approaches Xi for zeta as c grows (c up to 60, band N up to 128) against DH, then
   propose the input that would make zeta's convergence provable.
2. **`de_branges`: a Hermite-Biehler structure with an arithmetic input.** If E is
   Hermite-Biehler (|E(conj z)| < |E(z)| for Im z > 0), then A = (E + E#)/2 has only real
   zeros, so exhibiting such an E with A = Xi proves RH. de Branges proposed proving RH
   through positivity conditions in his Hilbert spaces of entire functions, and Conrey and
   Li (2000) showed that the condition he stated fails for zeta. Suzuki
   (arXiv:2301.00421) identifies the Weil-form completion with a de Branges space under
   RH, so that result can guide a construction but cannot be an input; his screw-function
   form of the Weil form (arXiv:2606.09096) is unconditional as a formula (both as
   `rogue_frontier/FRONTIER_MAP.md` records them, at search level). Target: an explicit E
   built from xi and the Euler product (a regularized product of local Hermite-Biehler
   factors, or a space adapted to the Weil form) whose Hermite-Biehler property or
   positivity would give RH, with an exact statement of how it differs from the condition
   Conrey and Li refuted and a numerical test of that difference. Rival gate: Xi_DH is the
   A-function of no Hermite-Biehler E, so the DH analogue of the construction must fail,
   and the step where it fails is the distinguishing step.
3. **`li_arithmetic`: a uniform bound on the arithmetic part of lambda_n.** RH holds if
   and only if lambda_n >= 0 for every n >= 1 (Xian-Jin Li, 1997; Bombieri and Lagarias,
   1999). Bombieri and Lagarias split lambda_n into an archimedean part, which grows like
   (n/2) log n, and an arithmetic part, a limit of prime sums from the explicit formula.
   Target: the inequality on the arithmetic part whose uniformity in n would finish,
   proved from the Euler product, or else the exact n-range and term at which it fails.
   Computation: the split for zeta and for DH up to n of a few thousand, with
   `zeta/li.py`, `rh_resolve` and `li_dh_onset`. Rival gate: DH's lambda_n are positive
   for n <= 5000 (measured; hardened for n <= 12) and first negative at n = 328997
   (measured inputs, extrapolated conclusion; `li_dh_onset`, hunt #128), so a bound that
   gives lambda_n >= 0 for all n must fail for DH, at the latest at DH's first negative
   index. W_a, whose log-derivative coefficients Lambda(n)(n^a + n^-a) are nonnegative and
   whose zeros rho +- a lie off its line, tests any step that uses only that positivity.
4. **`positivity_geometry`: Weil's proof for curves, carried over.** Over F_q, the
   Castelnuovo-Severi inequality, or the Hodge index theorem on C x C, makes the
   intersection pairing negative definite on the classes orthogonal to an ample class,
   and that gives |#C(F_{q^n}) - q^n - 1| <= 2g q^{n/2} (`docs/11`, section 1). Target: a
   concrete arithmetic positivity statement (an F1, Arakelov or Connes-Consani
   scaling-site analogue) whose truth implies RH, with each ingredient of Weil's proof
   given its counterpart or marked missing. Test: its finite-field shadow, exactly, on
   curves over F_p with `zeta/finitefield.py`, where RH is a theorem, including a planted
   violation that must be refused. Rival gate: DH has no curve and no Frobenius, and its
   explicit formula has signed coefficients; the construction must say which ingredient
   DH lacks, and which Epstein (1,1,6) and W_a lack. The record's nearest attempt is
   `local_positivity` (hunt #5): place-by-place norms of the prime side exist and do not
   assemble.
5. **`spectral_operator`: a Hilbert-Polya candidate, built and regularized.** Target: a
   self-adjoint operator whose spectrum is the set of ordinates of the nontrivial zeros.
   Pick one concrete construction (Berry-Keating xp with boundary conditions built from
   the Euler product, Connes' adelic scaling action and its trace formula, the CCM zeta
   spectral triples of arXiv:2511.22755, or the proposals of Sierra or of Bender, Brody
   and Muller together with the published objections to each;
   `rogue_frontier/FRONTIER_MAP.md`, territory F), regularize it to finite rank, compare
   its eigenvalues with the first 100 zeros from mpmath's `zetazero`, and say what makes
   it self-adjoint and where the Euler product enters. Rival gate: a self-adjoint operator
   has real spectrum, so the DH analogue cannot carry the off-line pair at height 85.699
   and must lose self-adjointness, the identification or convergence at a step that can
   be located. An operator that imports the zeros into its definition, or that matches
   only the counting function, proves nothing (`docs/09`, section 5.1).
6. **`probe_tower`: probes of growing degree in the 7/8 assembly.** OpenAI's 7/8 proof
   feeds the Fourier coefficients of Patterson's cubic theta function into a continuation
   criterion (Proposition 2.1) that is a shared lemma; the Euler product is consumed
   where the criterion's two estimates are made, at a Moebius identity and at the scalar
   Euler identity, Lemma 7.1 (`docs/38` section 2; hunt #120, `qrh_rival_step`). The
   assembly's abscissa is sigma_0 = 1 - h/6 + b/12 = 5/6 + (M - 2l)/12, which is 7/8 at
   the paper's (l, M, b) = (1/6, 5/6, 1/8), and perfect row counts stop it at 13/15
   (`seven_eighths_pin`, opened as hunt #134 on its branch and landing as hunt #139 in
   open pull request #325). Target: a tower of probes of degree k (an n-fold metaplectic
   theta whose comparison pole sits at 1/k) whose abscissas sigma_0(k) tend to 1/2. A
   zero-free half-plane Re s > sigma_0(k) for every k, with sigma_0(k) tending to 1/2,
   would be RH, so the all-k step is the whole content. Work: write sigma_0 as a function
   of k under the paper's generic estimates, find which estimate fails at large k
   (candidates: the theta coefficients at squarefree indices for n >= 4, and large sieves
   of degree k), and ask whether the function-field analogue settles any of it
   (`ff_probe`, on its branch, if committed). The paper is read by line number from the
   pinned copy whose commit and SHA-256 hunt #136's `MISSION.md` records. Rival gate:
   DH's zero at real part 0.808517 refutes any tower step that reaches below that
   abscissa without the Euler product, and the Epstein forms of hunt #120, with zeros past
   7/8 at discriminants -15 and -23, test whether the tower keeps an Euler-product step at
   every k.

## The rival gate

A construction that also works for a function with off-line zeros cannot prove RH. So
every mechanism names the step that uses zeta's Euler product or multiplicativity and
tests that step, by computation, on the rivals where they apply:

- **DH** (`zeta.epstein`'s `dh_f`, `completed_dh` and `Z_dh`): the functional equation of
  a conductor-5 L-function and no Euler product, being a linear combination of the two
  Dirichlet L-functions of the quartic characters mod 5; off-line zeros including
  0.80851718245663738 + 85.69934848537759i.
- **Epstein (1,1,6)** (`epstein_zeta` with the form (1, 1, 6), discriminant -23, class
  number 3): one pole, Lambda_Q(n) >= 0 for n <= 47 with the first negative at n = 48, and
  an off-line zero at 0.953260 + 16.290216i (`weil_propagation/theory/RESULTS.md`).
- **W_a = zeta(s+a) zeta(s-a)** at a = 1/4 (`shifted_completed`): a scalar Euler product,
  nonnegative coefficients and log-derivative coefficients, an exact s -> 1-s functional
  equation for its completion, two poles, and zeros rho +- a off its line
  (`epp_herglotz`; `docs/09`, section 5.1).

The test is the two-sided one of `docs/08` section 4.3: a rival that satisfies every
hypothesis and violates the conclusion refutes the implication; a rival that lacks a
hypothesis the proof uses is not that counterexample; a rival that passes only a shared
lemma gives no verdict on the whole argument; and a rival computation that fails to run
excludes nothing.

## How the hunt runs

1. **Construct.** One session per mechanism builds it in its own directory and commits
   `NOTES.md` (target, construction, distinguishing step, tests run, rival results, known
   obstructions, disposition, furthest true statement with its grade, next step) together
   with its tests.
2. **Challenge.** Two sessions that did not build it attack each construction: one at the
   rival gate, by its own computation, and one for circularity, hidden use of RH or of an
   equivalent statement, a finite computation standing in for a uniform step, published
   refutations of the exact form, and grades above their evidence.
3. **Synthesis.** A last session writes `RESULTS.md`: one section per mechanism with its
   challengers' verdicts and its disposition, a ranking of the survivors by distance to a
   proof of RH with the reason, the exact next construction step for the top one or two
   and what would decide it, and a closing section named "The doors" (`CLAUDE.md`, door
   analysis).

Dispositions are the four of `ALIGNMENT.md` section 5, plus *alive* for a construction
with a stated next step and no located failure: refuted (a counterexample or an invalid
step, at the stated parameters and hypotheses), restricted class obstructed (a proof or a
primary-source theorem whose hypotheses are shown to apply), unresolved, or paused by
allocation. Continuing any mechanism past the first wave is the owner's call.

Practicalities. Name test files after their mechanism (`test_<mechanism>*.py`) and keep
module names distinct, so the whole hunt also runs in one pytest process. Tests must not
write into the tree: `scripts/run_hunt_tests.py` fails a run that changes it. Record each
run in `RUNS.md` with a `runmanifest` block (`hunts/HUNTSPEC.md`). Methods that travel go
to `docs/37-methods.md` when the hunt lands.

## Scope

- **In scope.** The six constructions, their derivations and computations, their rival
  tests, Lean formalization of any lemma that is finished, and the primary sources they
  cite. Other hunts' directories are read-only inputs.
- **Out of scope.** Any change to `zeta/`, `ontology/`, `harness/` or another hunt; any
  claim of RH short of a complete proof; any novelty claim without a stated search; any
  edit to `hunts/README.md` beyond this hunt's own case-log entry.
- **Compute.** The campaign box (32 vCPU, 115 GiB, no swap), shared with the campaign's
  other hunts: at most 4 processes per session, pytest only with `-n0`, and a wait while
  the first field of `/proc/loadavg` is above 64. `CLAUDE.md` compute rules 3, 4, 6 and 7
  apply as ruled for the swarm box: estimate before spending, checkpoint anything over
  about twenty minutes, keep `MemAvailable` above 20 GiB when Lean and numerics run side
  by side, and never run Lake in a copied `.lake`.

```huntspec
id: rh_moonshot
question: Can any of six materially different mechanisms (ccm_arithmetic, de_branges, li_arithmetic, positivity_geometry, spectral_operator, probe_tower) be pushed to a construction that proves RH, or else to a precisely located obstruction, naming the step that fails, the rival or theorem that makes it fail, and the information that step reads?
frontier: every RH-direct route in the laboratory's record so far stalls at an all-order, all-window or all-height step, or is passed by Davenport-Heilbronn (hunts/rh_resolve, docs/08); Li positivity is measured for n = 1..58 with no uniform tail; Weil positivity holds only on fixed windows (support 1.6, Zhu; support 2.38 in the even sector, oob_envelope) and weil_propagation found no window-to-window mechanism in its searched set; RH is verified to height 3e12 (Platt and Trudgian 2021); 0 <= Lambda <= 0.2; Re s > 7/8 is kernel-checked here from OpenAI's proof, whose argument no person has reviewed; heat-flow and Jensen-degree clocks read the zero configuration only
proposed_attack: build the six mechanisms in parallel, one directory each, as specific constructions with an exact target and its relation to RH, namely ccm_arithmetic (convergence of the truncated Weil ground state's transform to Xi, CCM step 2), de_branges (a Hermite-Biehler E built from xi and the Euler product), li_arithmetic (a uniform bound on the arithmetic part of the Bombieri-Lagarias split of lambda_n), positivity_geometry (an arithmetic Hodge index analogue with an exact finite-field shadow), spectral_operator (a finite-rank regularized Hilbert-Polya operator against the first 100 zeros) and probe_tower (theta probes of degree k whose zero-free abscissa tends to 1/2); name in each the step that uses the Euler product or multiplicativity and test it on DH, Epstein (1,1,6) and W_a; have separate sessions challenge each construction at the rival gate and for circularity and known obstructions; rank the survivors and name the next construction step
dead_routes:
  - EPP/Herglotz, composing archimedean and prime-side positivity for Re(xi'/xi) >= 0 on Re s > 1/2, refuted by W_a = zeta(s+1/4) zeta(s-1/4), whose log-derivative coefficients are nonnegative and whose zeros rho +- 1/4 lie off its line (epp_herglotz, hunt 67)
  - weil_propagation C1, propagation of window positivity through entering prime atoms, refuted by DH, whose truncated Weil form changes sign at hardened brackets c in [30.617, 30.818] where no atom with nonzero weight enters
  - weil_propagation C3, norm-level transport of the Weil ground state from one window to the next, refuted by DH (measured)
  - weil_propagation C2, Levy-Markov jump structure plus one pole as a positivity or propagation mechanism, refuted by Epstein (1,1,6), which meets its hypotheses and whose Weil form is negative from c = 28 (odd sector) and c = 29.5 (even sector) by hardened ball LDLT inertia
  - product-side C4 at S = {inf, 2}, refuted on every c in (2, 3) (weil_propagation/c4_s2, ordinary argument, unreviewed)
  - Jensen-polynomial wedges of the form n^a log^b(n+2) >= K d^c, which exclude n = 0 for every constant, where hyperbolicity for every d is RH, and which succeed for DH exactly as for zeta (jensen_wedge, hunt 135, section 15)
  - heat-flow and Jensen-degree mechanisms that read only the zero configuration, since arithmetic-free N-body zero dynamics reproduce DH's repair times to 0.04 percent (flow_repair, jensen_clock)
  - zero-side Weil comparisons with a positive test function, powerless by construction because a positive h sums positive over any zero set (rh_resolve)
  - the zeros-route Li sum as positivity evidence, structurally nonnegative over any list of on-line zeros (zeta/li.py, rh_resolve)
  - positivity of a weight alone as a Polya-type criterion, since 1 + cos t + cos 3t transforms a positive measure and has a non-real zero (gauss_positivity, hunt 134)
  - any fixed finite number of Laguerre inequalities or central-moment matrix tests, each passed by a function with non-real zeros (rh_theta_laguerre, central_moments)
  - place-by-place norm decompositions of the prime side, whose local terms have indefinite sign and do not assemble (local_positivity, hunt 5)
  - a finite computation, however enclosed, offered as an all-order, all-window or all-height statement (Littlewood; docs/08 section 3)
required_oracles:
  - exact integer and rational arithmetic (Python integers and fractions, sympy) for identities, coefficients and finite-field point counts
  - Arb ball enclosures from python-flint, cross-checked against mpmath.iv where zeta/rigor.py offers both backends
  - mpmath (zetazero, siegelz, nzeros, the Li and Jensen routines of zeta/li.py) as an independent numerical cross-check, never as the proof
  - PARI/GP through cypari2, which shares no code with mpmath (the tests/test_pari_oracle.py pattern)
  - the rival functions of zeta.epstein (DH, Epstein (1,1,6), W_a), evaluated by the laboratory's own routines, as the falsifier of every distinguishing step
  - the Lean 4 kernel with Mathlib, zero sorry and axioms printed, for anything graded kernel-checked
  - primary-source theorems read at the cited section, for any restricted-class obstruction
kill_conditions:
  - a mechanism's construction or key inequality also holds for DH, Epstein (1,1,6) or W_a under its complete hypotheses, so its RH claim is withdrawn and recorded as refuted at the stated parameters
  - the step named as using the Euler product or multiplicativity is passed by a rival that lacks it
  - the target turns out to be an RH-equivalent restatement with no new estimate, recorded as a reformulation and not as progress
  - a finite computation is found standing in for an all-order, all-window, all-height or all-degree step, so the claim is withdrawn to its finite range
  - an input assumes RH, GRH or an RH-equivalent statement, so the conclusion is withdrawn to a conditional one
  - a published theorem or refutation covers the exact form, as Conrey and Li cover the positivity condition de Branges stated, so the form is recorded as refuted with the citation
  - a claimed number fails an independent precision, basis-size or second-route check, or a planted fault goes undetected
  - a claimed formal step has a sorry, an axiom beyond the standard three, or a statement that does not use Mathlib's own riemannZeta
agents_may:
  - read and search the literature
  - derive
  - code and compute within the box limits above
  - formalize in Lean under the swarm-box rules
  - attack any construction in the hunt, including their own
  - record refutations, obstructions and unresolved attempts with their scope
agents_may_not:
  - call an attempt a proof of RH, or call a step proved that is not
  - declare theorem status for anything not kernel-checked
  - declare novelty without a stated search
  - present a finite computation as a uniform result
  - turn a failed search or a set of scoped obstructions into a verdict that no route exists
  - promote their own claim
  - use the reserved enclosure word in any form
  - write outside hunts/rh_moonshot/ except this hunt's case-log entry
  - push, publish or contact outside parties
```

## Challenge-phase scoring rubric (pre-registered 2026-10-26)

Appended on 2026-10-26, when the owner resumed this hunt in place, before the `NOTES.md` of
`ccm_arithmetic` or `li_arithmetic` was written, so that the challengers of every mechanism
score against a rubric fixed before they read the constructions. The builder of a
mechanism does not fill in its scorecard. Each challenger records, per mechanism, one
scorecard with these seven fields, each answered with a citation to a file and line, a
test name, or a computation the challenger ran:

1. **Disposition.** Exactly one of: refuted, restricted class obstructed, unresolved,
   paused by allocation (`ALIGNMENT.md` section 5), or alive (a stated next step and no
   located failure). For refuted, the counterexample or invalid step and its parameters;
   for restricted class obstructed, the theorem or primary source and why its hypotheses
   apply.
2. **Grade per step.** Each step of the chain from the construction to its stated target,
   with its grade as defined at the top of this file (measured, hardened, derived with its
   review status, kernel-checked), and the composite grade, which is the weakest step's.
   A step graded above its evidence is recorded with the grade it should carry.
3. **The Euler-product step.** Whether the step that uses the Euler product or
   multiplicativity is named, whether it is tested against a rival that lacks it, and
   with what result. A construction with no such step, or with one untested, is scored so.
4. **Finite stand-ins.** Whether any finite computation (a range of n, of windows c, of
   band sizes N, of heights T, of degrees k) stands in for an all-order, all-window,
   all-height or all-degree step, and if so which step and at what range.
5. **Novelty search.** Whether a search for the construction's key statement is recorded
   (what was searched, where, and what was found). Absence downgrades nothing; it is
   recorded as absent.
6. **Rival results on complete hypotheses.** For each of DH, Epstein (1,1,6), W_{1/4} and
   zeta(s - delta) (zeta shifted off its line by a stated delta > 0), one of: meets every
   hypothesis and violates the conclusion (refutes the implication); lacks a named
   hypothesis (not that counterexample); passes only a shared lemma (no verdict on the
   whole); computation not run or failed (excludes nothing). Each entry states its range
   and grade.
7. **Circularity.** Whether any input assumes RH, GRH, an RH-equivalent statement or the
   zeros themselves, and where.

## Correction (2026-10-26)

The frontier paragraph "All heights" above says that hunt #137 (`rh_height_lean`) "aims at
a kernel-checked statement to T = 50". That was its target when this hunt opened. Hunt
#137 has since landed on `main` (pull request #351) with a kernel-checked theorem to
height 100: every zero of Mathlib's `riemannZeta` with 0 < Re rho < 1 and
0 < Im rho <= 100 lies on the critical line and is simple, and there are exactly 29 of
them (`hunts/README.md`, hunt #137's case-log entry; `rh_height_lean/RESULTS.md`). The
original sentence is left as written. A finite-height theorem says nothing above its
height, so the frontier this hunt starts from is otherwise unchanged.
