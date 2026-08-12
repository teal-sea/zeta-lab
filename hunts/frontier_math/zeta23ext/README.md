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
  imports only Mathlib. **Rebuilt locally 2026-08-12 under Mathlib
  `v4.33.0-rc2`: builds clean, zero `sorry`, same three axioms.** Since it
  imports only Mathlib, that test is decisive for this module.
- `Zeta23Ext/GridIncidence.lean` — the grid-incidence law, same provenance.
  It did **not** build under `v4.33.0-rc2` at two `rw` sites (lines 109, 290);
  ported in batch 2 and now builds, 18 declarations on the three standard
  axioms (`lean/ARISTOTLE-RUNS.md`).

**The port is DONE. Every module in this package builds under Mathlib
`v4.33.0-rc2`** (measured 2026-08-12 by dropping each into `lean/` as a
scratch target against its already-compiled Mathlib, building, deleting —
minutes, and it never requires compiling Mathlib for this package):

| module | first verdict | now |
| --- | --- | --- |
| `Composition.lean` | builds clean | unchanged |
| `GridIncidence.lean` | failed at 109, 290 | **builds** (batch 2 port-A) |
| `FloorCert.lean` | failed at 82 | **builds** (port-B + one local repair) |
| `BandCert/Leaves.lean` | failed at 144 | **builds** (batch 2 port-C) |
| `BandCert/Phi.lean` | not reached | **builds** (13 sites, repaired locally) |
| `BandCert/` ×8 chain | not reached | **builds**, 8704 jobs, `Verify` 1513 s |

Zero `sorryAx` in any build log. `cap_le_slack` and `f_nonpos_off_bands`
(BandCert) and `theoremA`, `B1`–`B4`, `corollary` (FloorCert) all report only
`[propext, Classical.choice, Quot.sound]`.

**One root cause explains most of it.** `convert … using 1` on a `HasSum`
goal now leaves an `AddCommMonoid` instance-equality goal first, so the
tactic after it has nothing to act on. That is both `GridIncidence` sites and
the `FloorCert` one. `Phi`'s 13 sites are a second, separate drift:
projection-through-definition (`(a.add b).1` vs `a.1.add b.1`) that the newer
`simp` no longer unfolds.

Collection detail, including the one artifact that was refused and why, is in
`lean/ARISTOTLE-RUNS.md` under "Batch 2 collection".

The `BandCert/` imports form a single chain (Iv → Leaves → Phi → Check →
Cap → Data → Verify → Main), and it now builds end to end. On the pin note
further down: this package's `lean-toolchain` already reads `v4.33.0-rc2`
and it declares no Mathlib requirement of its own (Mathlib arrives through
the `Zeta23` dependency), so the older "this package pins v4.28.0" line
described what the service proved against, not what the tree says.

**A defect the survey found, independent of the port — now FIXED.** All
eight `BandCert/` modules carried `import RequestProject.X`, the proving
service's own project-local namespace, while `Zeta23Ext.lean` imports
`Zeta23Ext.BandCert.Main`. The package could not have assembled at any pin:
the first `lake build` died on an unknown module before reaching any
mathematics. The proofs were never implicated; the artifacts had been landed
without their import paths rewritten, and no local assembly had been
attempted to notice. All eight now import `Zeta23Ext.BandCert.X`.

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
   still positive margins (+2.95e-2 vs our +4.49e-2 at y = 49/100). The
   port to `v4.33.0-rc2` that this entry once listed as outstanding is
   done (see the port table above); the chain builds, `Verify` alone
   taking 1513 s.

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

## Two further results, one of which is prior art (correction)

The four modules above are machine-checked verification of constructions
we had already built.  These two were statements WE could not prove, so
we asked the service to prove or refute.  A novelty check afterwards
established that the first is **not new** - see the correction inside
item 6.  Both files remain useful to the chain; the framing of item 6 as
research-grade was the coordinator's error and is retracted.

6. `PairEnergy.lean` — **PROVED, SHARP, AND NOT NEW** (project 481e49bf; 785 lines,
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

   **CORRECTION (novelty check, same day).**  This is a corollary of two
   lemmas the source paper already states, proves and formalises:
   Sylvester inertia in pull-back form (their Lemma 3.1,
   `RHLinalg.posIndex_conj_le`) and Cauchy-Schwarz on positive
   eigenvalues (their Lemma 3.3 at theta = 0,
   `RHLinalg.cauchySchwarz_count`).  Worse for any novelty claim, the
   exact numerical specialisation is printed in that paper's section
   7.5(a): with all zeros off-line, "Lemma 3.2 would then force
   \|\|Ahat\|\|_F^2 >= 2N" - which at N = 2n is our 4n.  The involution
   structure is their Prop 4.1(ii) off-line block, and the cosh weight
   is literally the sum of exponentials for rho and 1 - conj rho.  The
   spectral-theorem-free route here is formalisation engineering, not
   new mathematics.  Keep the file, cite the paper, claim nothing.

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
