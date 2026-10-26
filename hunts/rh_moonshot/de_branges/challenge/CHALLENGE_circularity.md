# CHALLENGE (circularity): de_branges

Hunt #150, mechanism 2. Circularity challenger, 2026-10-26, branch
`hunt/rh-moonshot-challenge-circularity`. This session did not build the construction and
edited none of its files. It read `NOTES.md` and `dbr_common.py` as committed at
`c2449a4b9` (merged here at `d89c63d6d`) and scored them against the rubric pre-registered
in `MISSION.md` (section "Challenge-phase scoring rubric", 2026-10-26).

Files here: `circ_dbr.py` (an own Chowla-Selberg route for the Epstein zeta, argument-
principle counts, a census, Conrey and Li's numbers by an own xi, a zero trap around the
builder's defect), `test_de_branges_challenge_circularity.py` (9 tests), this page.

Grades as in `MISSION.md`. Nothing written here is kernel-checked.

## Verdict

**The builder's disposition stands: a reformulation under kill condition 3, with the
located obstruction that the Hermite-Biehler property of E_h is exactly a zero-free
half-plane; unresolved as a route; Conrey and Li do not cover this form.** No hidden use of
RH or of the zeros was found in the definitions; RH enters only as Lagarias's conditional
statements, which the NOTES label. Findings:

- **B1 (prior art for statement (a)).** Statement (a), "E_h is Hermite-Biehler if and only
  if Lambda has no zero with Re rho > 1/2 + h", is proved in the NOTES by Lagarias's
  factor-by-factor argument plus a one-line converse. The same mechanism, the paired
  Hadamard product with the functional equation, gives Sondow and Dumitrescu's theorem
  that |xi| is strictly increasing along every horizontal half-line in a zero-free right
  half-plane, and their reformulation of RH as monotonicity of |xi(sigma + it)| on
  sigma > 1/2 (*A monotonicity property of Riemann's xi function and a reformulation of
  the Riemann Hypothesis*, Period. Math. Hungar. 60 (2010) 37-40, arXiv 1005.1104;
  restated with sigma_0 at least every zero's real part by Matiyasevich, Saidak and
  Zvengrowski, as arXiv 2201.08599 reports). Lagarias's chapter *Hilbert spaces of entire
  functions and Dirichlet L-functions* (Frontiers in Number Theory, Physics, and Geometry
  I, Springer 2006, 365-377) gives the h -> 0 end: a de Branges space attached to L
  exists if and only if RH holds for L. The exact form (a) at a given h was not found in
  print, but it is a short step from these; novelty is not established, and nothing in
  the disposition depends on it.
- **B2 (the rival grid's high side is settled by theorems, not by the grid).** The NOTES
  say the grid passes DH at h = 3/8 and 1/2 only on |x| <= 100 and that DH has zeros in
  Re s > 1 by a quoted 1936 result (NOTES section 5). That is citable now: DH's
  coefficients are periodic and DH is not a Dirichlet polynomial times one L-function, so
  by Saias and Weingartner (Acta Arith. 140 (2009) 335-344, arXiv 0807.0783; abstract
  re-read by this session on 2026-10-26: c_1 T <= N(sigma_1, sigma_2, T) for every
  1/2 < sigma_1 < sigma_2 < 1 + eta) DH has zeros with real part in (1, 1 + eta), and by
  (a) **E_h^DH fails for every h <= 1/2**. The grid's "passes at 3/8 and 1/2" is a
  finite stand-in that the theorem overrides. For Epstein (1,1,6) the analogous
  statement (zeros in Re s > 1, Davenport and Heilbronn 1936 for class number > 1) is
  quoted, not checked here.
- **B3 (the "second Epstein off-line zero" is new against the record and is not
  enclosed).** See the section below; it is the second of at least five (B5).
- **B5 (the Epstein rival has more off-line zeros than the NOTES list, and the grid
  missed one inside its range).** This session's census finds **five** zeros of zeta_Q in
  [0.55, 1.6] x [0.5, 60.5], not two: besides 0.953260 + 16.290216i and the builder's
  0.797997 + 29.551761i, three more, at 0.663652 + 33.650101i, 0.809992 + 43.858664i and
  0.782379 + 46.960994i (offsets 0.1637, 0.3100, 0.2824; details below), none of them in
  the record. The one at height 33.65 lies inside the builder's Epstein grid (x <= 40),
  yet the grid lists no positive defect there: at h = 1/20, y = 1/20 the defect is
  +0.457 at x = 33.6501 but negative at the grid's own points x = 33.5 (-0.013) and
  x = 34.0 (-0.056) (this session's route). So a step of 1/2 in x is too coarse to see a
  failure region of this size, the NOTES' Epstein row ("h <= 3/8 at x = 16.290, and
  h <= 1/4 also at x = 29.5") is a statement about the sample, not about the function, and
  section 5's "fails for h below its offsets 0.4533 and 0.2980" omits three offsets. None
  of this contradicts (a), which predicts the failure at every one of these zeros; it is
  a finite stand-in read as complete. The same caution applies to zeta's "0 positive in
  2828 points": that is a sampled statement, as the NOTES grade it.
- **B4 (zero configuration only).** By (a) the defect reads the real parts of the zeros
  and nothing about primes; the NOTES say so (section 6) and place the family in the
  `MISSION.md` dead-route class "mechanisms that read only the zero configuration". The
  Euler product enters only through the zero-free half-plane it is known to give
  (Re s >= 1, and Re s > 7/8 from the OpenAI strip, kernel-checked here, pending human
  review). Agreed.

## The second Epstein off-line zero

**New against the record.** Searched on 2026-10-26: `git grep` for 29.551, 29.552 and
0.79799 under `hunts/`, `zeta/` and `docs/` on every local and remote branch (the only hits
are unrelated numbers in `hunts/prime_pair_error/results_residue.json`); `zeta.epstein`
pins only DH's zero (`OFFLINE_ZERO_RE`, `OFFLINE_ZERO_IM`); `hunts/weil_propagation`
(theory `RESULTS.md`, numerics `epstein_offline.py`) pins only 0.953260 + 16.290216i;
`hunts/plocal_rivals` (hunt #149, branch `hunt/plocal-rivals`, `ZEROS.md` and
`zeros.json`) is a census of the F_q rivals, not of Epstein (1,1,6); and hunt #120
(`hunts/qrh_rival_step/RESULTS.md` section 3.2) counted the D = -23 function only in
[0.8751, 1.5] x [0.5, 60.5], finding the zero at 16.29, so a zero with real part 0.798 was
outside every searched box. The zero is therefore new to this tree. Whether it is in the
literature was not settled: the search "Epstein zeta function x^2+xy+6y^2 discriminant -23
zeros off critical line computed Hejhal" returned Hejhal's ICM 1986 survey (*Zeros of
Epstein zeta functions and supercomputers*, cited, not retrieved) and papers on other
forms (arXiv 1907.06387, 1909.07112, 2110.09368, 1811.01613, 1102.0367), none listing
this zero.

**Recomputed by a third route.** `circ_dbr.epstein_cs` is this session's Chowla-Selberg
series (Poisson summation in m, re-derived here; the Bessel-sum prefactor is
2^(s + 5/2) pi^s / (sqrt(a) Gamma(s)) Delta^((1/2 - s)/2), and the 2^(s + 3/2) of a common
statement is off by a factor 2, kept as a planted fault). It agrees with `zeta.epstein` to
1e-20 at s = 3 and 0.7 + 5i, and with a direct lattice sum at s = 4. Results:

- Newton from the builder's printed value: 0.7979971571786801862221945 +
  29.55176109862911477071554i, 2.5e-14 from the builder's printed value; |zeta_Q| =
  2.2e-50 there against 0.037 at distance 0.01 (dps 50).
- Argument principle (own implementation, every argument increment below pi/4): winding
  1 on the square of half-side 0.02 around rho (largest increment 0.126, 68
  evaluations), 1 around the mirror 1 - conj(rho) (0.138), 0 on the square displaced by
  0.1 (0.029).
- Census of zeros of zeta_Q in [0.55, 1.6] x [0.5, 60.5] by windows of height 10 (the
  left edge as hunt #120's strip floor; argument principle on this route, measured):
  0, 1, 1, 1, 2, 0 for the windows starting at 0.5, 10.5, 20.5, 30.5, 40.5, 50.5. Recursive
  bisection plus Newton (`circ_dbr.locate`, each root accepted only inside its box) puts
  the three unrecorded ones at

  | zero | real part | offset | abs zeta_Q, this route | abs zeta_Q, `zeta.epstein` (at +0.01) |
  |---|---|---|---|---|
  | 0.66365167885959860983 + 33.650100582527335123i | 0.6637 | 0.1637 | 1.2e-29 | 1.2e-18 (0.033) |
  | 0.8099915314971334217 + 43.858664365004478179i | 0.8100 | 0.3100 | 2.7e-30 | 1.1e-18 (0.037) |
  | 0.78237857667772956412 + 46.960993669907468078i | 0.7824 | 0.2824 | 7.8e-30 | 3.6e-19 (0.017) |

  Each is measured by two routes (this session's Chowla-Selberg series and
  `zeta.epstein`, whose 1e-18 is its precision floor at dps 30 at these heights) and a
  winding count; none is enclosed, for the reason below. A `git grep` of every branch
  for their leading digits finds no record of them (one unrelated coincidence,
  0.782375 in `hunts/frontier_math/repulsion_trade.py`). Hunt #120's D = -23 statement
  "one zero beyond 7/8 below 60.5" is consistent with this: all three have real part
  below 7/8.

**Not enclosed.** The location is measured by three routes (the builder's Arb route through
hunt #120's Bessel series, the builder's `zeta.epstein` lattice route, and this
Chowla-Selberg route) and by a winding count, but no step carries a ball enclosure of the
zero: the builder's evidence is a Newton root plus |s(s-1) Lambda_Q| = 9e-47 against 1.3e-18
at distance 0.01, which is a small value, not an enclosure; and the in-tree ball route
cannot evaluate this function on segment balls (hunt #120 measured an input radius of 1e-4
inflating route B's output radius to 1e67 at height 15, `probe.route_c_ball` docstring), so
the segment-enclosed winding that hunt #120 ran for D = -15 is not available for D = -23.
The NOTES grade it "measured, by two routes", which is correct; it should not be quoted as
enclosed.

## Scorecard

1. **Disposition.** Agreed with NOTES section 7: the target is recorded as a reformulation
   (kill condition 3); for the Lagarias family E_h the Hermite-Biehler property is exactly
   a zero-free half-plane, so the route is as hard as quasi-RH at every abscissa above 1/2
   (unresolved); Conrey and Li's refutation concerns the positivity conditions on
   H(xi(1 - iz)) and does not cover this form.
2. **Grade per step.**
   - (a) the equivalence: derived, self-reviewed; this session rechecked the converse (a
     zero 1/2 + delta + i gamma with delta > h gives E_h(-gamma + i(delta - h)) = 0 in the
     upper half-plane). Prior art B1.
   - (b) h > 3/8: derived, conditional on the 7/8 strip (kernel-checked, pending human
     review). Agreed; not RH-conditional.
   - (c) the local factor is not Hermite-Biehler: derived and pinned by the builder.
     Agreed.
   - Zeta grid, 2828 points, defect negative: hardened at the points (two routes); a
     sampled statement, not a region statement. Agreed.
   - Rival grid: hardened at the points; the high-h passes for DH are overridden by B2.
   - Conrey and Li's numbers: reproduced by this session's own xi to 12 digits
     (-5.389100507182945e-69 at the 34th zero; -0.000131957 at 1 + 282i).
   - Second Epstein zero: measured, three routes, not enclosed (B3); the three further
     zeros of B5: measured, two routes, not enclosed.
   - Composite: derived, conditional on the 7/8 strip, as the NOTES say (section 8).
3. **The Euler-product step.** Named: the zero-free half-plane the Euler product supplies
   (NOTES section 2). Tested on DH, Epstein (1,1,6), W_{1/4} and zeta(s - 1/5); each fails
   where (a) predicts from its zeros. The step is not new arithmetic: the Euler product
   enters only through Re s >= 1 (and 7/8), and the local factors are not Hermite-Biehler
   (c).
4. **Finite stand-ins.** The grid (|x| <= 100, seven values of h, two of y) is finite and
   the NOTES say it says nothing above x = 100. One place it was read too far is B2 (DH
   "passes" at h = 3/8 and 1/2), now overridden by a theorem.
5. **Novelty search.** The builder recorded three searches and read Conrey-Li and Lagarias
   2005 at section (NOTES section 1). This session's queries, web search, 2026-10-26:
   (a) "Lagarias Zero spacing distributions for differenced L-functions structure
   function xi(1/2 + h - iz) de Branges Hermite-Biehler equivalent zero-free half-plane":
   the paper (Acta Arith. 120 (2005) 159-184; arXiv math/0601653), with Lemma 2.1 as the
   NOTES read it; a ResearchGate item *A family of deformations of the Riemann
   xi-function* (not read). (b) "Hermite-Biehler property E(z) = xi(1/2 + h - iz) if and
   only if no zeros Re s > 1/2 + h; de Branges space exists iff RH; Lagarias Hilbert
   spaces of entire functions and Dirichlet L-functions": Lagarias's 2006 chapter
   (365-377), the title the NOTES give, so the NOTES' correction of
   `rogue_frontier/FRONTIER_MAP.md` is confirmed; a Canadian J. Math. paper *On the
   Hilbert space derived from the Weil distribution*; Lagarias's slides
   (https://websites.umich.edu/~lagarias//TALK-SLIDES/benasque-riemann2012jun.pdf).
   (c) "Sondow Dumitrescu monotonicity property of Riemann's xi function ...;
   Matiyasevich Saidak Zvengrowski horizontal monotonicity": B1. (d) "Conrey Li note on
   some positivity conditions ... de Branges conjecture refuted follow-up": Conrey and
   Li, arXiv math/9812166; *A positivity conjecture related to the Riemann zeta
   function*, arXiv 2011.02847 (not read); no refutation of the form (a) found.
   (e) The Epstein query of B3. zbMATH and the Lean Zulip archive were not browsed.
6. **Rivals on complete hypotheses.**
   - DH: meets every hypothesis of (a) and agrees with its conclusion (it fails exactly
     where its zeros say), so it does not refute (a); it lacks the Hermite-Biehler
     property for every h <= 1/2 by B2 (theorem) and for h <= 3/10 on the grid (hardened).
   - Epstein (1,1,6): same reading; fails at offsets 0.4533 and 0.2980 on the grid, and by
     (a) also at the unrecorded offsets 0.3100, 0.2824 and 0.1637 (B5).
   - W_{1/4}: has an Euler product with non-unitary local roots and fails for h < 1/4: an
     Euler product alone does not supply the half-plane. Not a counterexample to (a).
   - zeta(s - 1/5): lacks the s -> 1 - s functional equation, so (a) does not apply;
     builder's measurement.
7. **Circularity.** None in the definitions. `dbr_common.py` evaluates completed functions
   by two routes (mpmath through `zeta.core.xi` and `zeta.epstein`; Arb through
   python-flint, `li_arith_split` and hunt #120's `probe`), the defect from their values,
   and reads `mp.zetazero(34)` only in `conrey_li_numbers` to reproduce Conrey and Li's
   printed number. A run-time trap (mpmath's zero routines on `mp` and on the module,
   every public function of `zeta.zeros`) around the builder's `defect_mp` for zeta, DH
   and Epstein records no call (`test_builder_defect_reads_no_zero`; the trap catches a
   planted `zetazero` call). RH appears only in Lagarias's conditional statements, which
   the NOTES never use as inputs.

## Run manifest

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-challenge-circularity
hunt: rh_moonshot
started: 2026-10-26T14:30+00:00
finished: 2026-10-26T16:09+00:00
ran:
  - .venv/bin/python hunts/rh_moonshot/de_branges/challenge/circ_dbr.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/de_branges
outcome: no hidden RH or zero import; (a) is close to Sondow-Dumitrescu and Lagarias; DH fails for every h <= 1/2 by Saias-Weingartner; the second Epstein zero is new to the tree and only measured, and a census finds three more unrecorded off-line zeros at heights 33.65, 43.86 and 46.96, one of them missed inside the builder's grid
artifacts:
  - hunts/rh_moonshot/de_branges/challenge/circ_dbr.py
  - hunts/rh_moonshot/de_branges/challenge/test_de_branges_challenge_circularity.py
  - hunts/rh_moonshot/de_branges/challenge/CHALLENGE_circularity.md
```

Compute: the script took 11 minutes of one core (15:22 to 15:33, mostly the census), and
`locate` on [30.5, 50.5] under 25 minutes of a second core; under one core-hour together, so
no estimate was sent. A first census attempt with its left edge at Re s = 0.52 ran for 41
minutes with buffered output and was stopped, unfinished; its results were never read. Times are read from the clock, except `started`, which is
approximate (to about 5 minutes).
