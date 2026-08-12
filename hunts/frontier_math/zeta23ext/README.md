# Zeta23Ext — extension package scaffold (STATUS: SCAFFOLD, NOTHING CLAIMED)

A Lean 4 package depending on the source paper's formalization
(`anthropics/zeta-23-lean`, pinned by commit; toolchain and Mathlib pin
inherited from it) into which the frontier_math formal chain lands as
its pieces are kernel-checked.

**Status discipline** (the lean/ arm's rule applies here too): nothing
in this package counts until it compiles with zero sorrys under the
pinned toolchain. As of the scaffold commit:

- `Zeta23Ext/Composition.lean` — the composition skeleton, kernel-checked
  earlier today against current Mathlib on the theorem-proving service
  (axioms: propext, Classical.choice, Quot.sound). Included verbatim; it
  imports only Mathlib. Not yet rebuilt under THIS package's pin —
  rebuild is the package's first CI obligation.
- `Zeta23Ext/GridIncidence.lean` — the grid-incidence law, same status.

**Planned modules** (from the reconnaissance report in
`../PROOF-LEDGER.md` and the zeta-23-lean mapping; not yet written):

1. `Bridge.lean` — restate Composition on the upstream repo's types
   (`Matrix (Fin (P.d T)) _ ℂ`, `RHLinalg.rtrace/frobSq/posIndex`,
   `ZeroBlockData`), forking at `rank_trace_mult` where the upstream
   pipeline discards `tr(PQ)`.
2. `Census.lean` — the gap-census counting function on `ZeroConfig`,
   plus its seam to `N0simple` (the nu input; one-sided by the LP
   floor's measured monotonicity in nu).
3. `FloorCert.lean` — **LANDED** (theorem-proving service, project
   029bed09; sorry-free, no `native_decide`, axioms propext /
   Classical.choice / Quot.sound). `MTKernel.theoremA` is the LP bound by
   explicit rational weak duality for any cost dominating the four
   rational kernel bounds; `B1`-`B4` prove those bounds about the genuine
   Montgomery-Taylor kernel (`Real.sin`, `Real.sqrt 2`, `π` — not a
   rational surrogate), via from-scratch Taylor machinery with explicit
   truncation error and interval covers; `MTKernel.corollary` combines
   them: every admissible configuration pays at least
   F = 15836524170563975879104102066119/3153949737350000000000000000000000000
   = 5.021172019e-6. Constants cross-checked identical to
   `../lp_certificate.py`. One comment reworded for the hunts/ lexical
   rules; no proof content altered.
4. `BandCert/` — **LANDED, PARTLY** (theorem-proving service, project
   7fb5612e; 8 modules, 2280 lines, sorry-free chain
   Iv -> Leaves -> Phi -> Check -> Cap -> Data -> Verify -> Main).
   Read the split carefully, it is the honest part:

   * **Unconditional**: `cap_le_slack` — the recorded certificate's
     arithmetic closes at the four depths 1/50, 1/10, 3/10, 49/100, by
     kernel `decide`; `cap` is defined with the TRUE band quantities
     (`bandSupR` the genuine supremum of the field over a band,
     `omgMinR` the genuine infimum of omega^2), the recorded numbers
     entering only as one-sided bounds, so the statement cannot be
     vacuous. Also `f_nonpos_off_bands` ("no band missed") as a property
     of the recorded cover rather than an assumption, and leaves L1-L6
     (Taylor enclosures, argument reduction, the s(u) series branch).
   * **Conditional**: `band_dual_verdict` carries H1 (Im-majorant), H2
     (spacing/repulsion beyond G) and H3 (the dual layer) as named
     hypotheses. H3 is the substantive one — it says the dual's cap
     really does bound `D - (1-theta) R` for every configuration. That
     reduction is OURS, on paper, not yet formalised; the Lean file is
     honest about it rather than hiding it inside the arithmetic.

   So the retention's ARITHMETIC is kernel-checked and its MODELLING
   STEP (H3) is not. Two notes: the service regenerated the certificate
   itself (the JSON was not shipped with the submission), an
   independent-regeneration cross-check that closed with different but
   still positive margins (+2.95e-2 vs our +4.49e-2 at y = 49/100); and
   this package pins Mathlib v4.28.0 while upstream Zeta23 pins
   v4.33.0-rc2, so a port is required before integration.

5. `RetentionHypothesis.lean` — theta = 995/1000 as a NAMED hypothesis
   (`of_literature` style) until H3 above is discharged.
5. `Main.lean` — the conditional endgame: clone of upstream
   `thmD_mult2_abstract` carrying the census term through the full
   explicit error ledger, concluding
   `(H + 2*theta*c_u - eps) * N <= N0simple` given the retention
   hypothesis.

Build note: a full local `lake build` compiles Mathlib for this pin
(hours, gigabytes); the working path is service-side proving per module
plus a single assembly build at the end. Do not add a partial build's
`.lake/` to the tree.

## Research-grade results (statements we did not know how to prove)

The four modules above are machine-checked verification of constructions
we had already built.  These two are different: the statements were open
to us, we had numerics and no proof, and we asked the service to prove
or refute.

6. `PairEnergy.lean` — **PROVED, SHARP** (project 481e49bf; 785 lines,
   36 theorems, sorry-free, standard axioms).  For the bandlimited
   kernel c2 = g*g of the paper window, every k, and ALL real depths and
   positions:

       (1/A^2) * integral c2(w) |sum_i 2 cosh(y_i w) e^{i t_i w}|^2 dw  >=  4k.

   Sharp (attained at k=1, y=t=0), and the two hypotheses we asked for
   (k >= 1, y in [0,1/2]) turned out to be unnecessary and were dropped.
   The proof is an inertia argument: the Gram matrix of u -> e^{zeta_a u}
   against the nonnegative weight g is PSD with a fixed-point-free
   involution structure, and trace Cauchy-Schwarz with a regularisation
   gives sum Q^2 >= 4k without spectral theory.  This is the pair-energy
   half of the E-form obligation, and it is now closed.

7. `EForm/` — **PARTIAL, WITH THE OBSTRUCTION NAMED** (project 00643d5e;
   5 modules, ~1200 lines, sorry-free, standard axioms).  The single-pair
   retention inequality at the exact constants theta = 199/200:
   * `retention_gap` — an EXACT reduction of the problem for every n,
     configuration, shift and depth;
   * `retention_le_three` — the target inequality proved at the exact
     constants for n <= 3 on-line points, uniformly in shift and depth;
   * `Icross_localized` — damage localisation: a single on-line point
     does no damage at all outside an explicit region;
   * `retention_of_few_near` — the inequality for ARBITRARY n provided
     at most three offsets are damaging.
   Not obtained: the unrestricted statement, and no counterexample - it
   "looks robustly true".  The obstruction is recorded exactly: any
   bound of the form -Icross <= kappa * Shq(y) with kappa uniform in the
   offset can only reach n <= 2A/kappa (here kappa = (A + 1/4)/2 gives
   n <= 3; even the numerically optimal uniform kappa would give n <= 7).
   Closing it needs the 1/s^2 far-field decay plus a band/cluster
   repulsion argument with near-sharp constants - which is precisely the
   structure of our own band dual.  So this partial is also a finding:
   it shows the band structure is NECESSARY, not merely convenient.
