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
4. `RetentionHypothesis.lean` — theta = 995/1000 as a NAMED hypothesis
   (`of_literature` style) until the band certificate
   (`../band_certificate.py`, in progress) discharges it.
5. `Main.lean` — the conditional endgame: clone of upstream
   `thmD_mult2_abstract` carrying the census term through the full
   explicit error ledger, concluding
   `(H + 2*theta*c_u - eps) * N <= N0simple` given the retention
   hypothesis.

Build note: a full local `lake build` compiles Mathlib for this pin
(hours, gigabytes); the working path is service-side proving per module
plus a single assembly build at the end. Do not add a partial build's
`.lake/` to the tree.
