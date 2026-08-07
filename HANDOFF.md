# Session handoff — Scope Reconciliation, the Strengthened Gates, and the Certified Arm

**Snapshot:** 2026-08-06
**Branch:** `main` (pushed through `713c0be` + this docs pass)
**Detailed sources of truth:** `ROADMAP.md` (decisions), `docs/09-new-ontologies.md` §5.1
(the strengthened gates), `lean/` (the formalization ladder), `git log`

**Status in one line:** The lab's scope language is reconciled (falsification
laboratory, not a proof), the falsification gates are upgraded from "prove
positivity" to "exhibit factorization through a positive structure," the
battery runs a second linear-combination rival by default, and the lab has
grown a second certainty regime: a Lean 4 + Mathlib project whose theorems are
kernel-checked rather than measured.

## Where the work landed

### 1. Scope reconciliation (`4c7e480`)
A prior commit had changed the honest-scope rule to claim the repo "is a proof
by construction via the spectral operator," contradicting the rest of the rule
on the next lines. All five statements of scope (AGENTS.md→CLAUDE.md, README,
ROADMAP, docs/00) now agree: **a computational falsification laboratory and
research program exploring prime-side spectral constructions for RH; not
presently a proof.** A proof would require a natural prime-defined object, a
non-circular trace or spectral identification, and an intrinsic positivity or
self-adjointness theorem. Numerics reject candidates and validate
implementations; they cannot establish RH.

### 2. The strengthened gates — docs/09 §5.1 (`c0fa48d`)
Since Weil positivity over the full admissible class is already *equivalent*
to RH, "prove the quadratic form is positive" is RH restated, not a strategy.
The positive target is **factorization**: `−W(f ∗ f̃) = ‖Φ(f)‖²` inside a
genuinely positive structure, so the sign becomes formal. Three requirements
in causal order:

- **A — arithmetic provenance:** everything generated from
  `{(p, m, log p, p^{−m/2})}` + the archimedean factor; no zeros, ξ-phases, or
  zero counts in the definition (mechanically checkable, seam-test style).
- **B — exact trace realization:** `Str π(f) = W(f)` on the entire admissible
  algebra, primes arising intrinsically. This is where the analytic difficulty
  *relocates* (the function-field precedent: building the surface was the hard
  part, not the Hodge-index step). Testable here as a measured defect.
- **C — structural positivity:** a canonical positive pairing with the norm
  identity, signature forced independently of the zeros. The identity is
  numerically checkable; *naturality* is the boundary where the lab's writ
  ends.

§5.1 also records the five-entry **pseudo-solution taxonomy** (direct
estimation, tautological completion, zero-importing, formal C*-positivity,
finite approximants — each with its historical casualty) and the
**linear-combination sharpening** of gates 3/4: what the counterexamples kill
is primitive multiplicative structure destroyed by linear combination; no
known example satisfies the full Selberg-class package and violates RH, so the
gate is eliminative, never probative.

### 3. Battery extension (`c0fa48d`)
`zeta.epstein.battery` default rivals are now Davenport–Heilbronn **plus both
discriminant −23 forms** — non-principal `(2,1,3)` and principal `(1,1,6)`,
each a linear combination of the three Hecke L-functions of the class group.
Verified before landing: `(1,1,6)` passes the functional-equation claim and
fails multiplicativity, exactly like `(2,1,3)`. Tests pin the new default
(`tests/test_epstein.py`, 39 passing).

### 4. The certified arm — `lean/` (`713c0be`)
Lean 4 (v4.33.0-rc2) + Mathlib project under `lean/`, full binary cache (no
local Mathlib compile; rebuilds ~6 s). `ZetaLean/GroundTruth.lean` holds rung
1 of the ladder: ζ(2) = π²/6, ζ(0) = −1/2, ζ(4) = π⁴/90, and the zero-free
half-plane Re s ≥ 1 — kernel-checked, zero `sorry`s. Toolchain: `elan` via
Homebrew; build with `cd lean && lake build` (PATH needs `~/.elan/bin`).

House rule for this arm: the kernel plays the role of `rigor.py`. Nothing
counts until it compiles with zero `sorry`s; a `sorry` is an uncertified step,
tracked, never hidden. "Certified" remains a reserved word; Lean theorems and
`rigor.py` enclosures are the only two things entitled to it, and they are
different regimes (kernel-checked symbolic truth vs. enclosure-carrying
numerics).

## What not to infer

- **None of this is evidence for or against RH** (standing rule; Littlewood).
- Rung 1 is plumbing, deliberately: the four theorems are one-line wirings to
  proofs Mathlib already has. The point was the toolchain and the zero-sorry
  pipeline, which now work end to end.
- Passing gates A/B/C numerically would still not be a discovery — B and C's
  identities can be checked to 1e-30 and the construction can still be a
  re-encoding of the explicit formula. The gates are a killing floor, and the
  survivor pile is where humans look.

## What is open now

**The formalization ladder, rungs 2 and 3.**

- **Rung 2 — the κ derivation** (`zeta/epstein.py` lines ~264–324): prove in
  Lean the linear-solve derivation of Davenport–Heilbronn's κ (the
  coefficient making the combination self-dual with real coefficients) —
  finite linear algebra over explicit constants, the repo's
  "derive conventions, never remember them" habit made kernel-checked. First
  theorem Mathlib doesn't have.
- **Rung 3 — the Davenport–Heilbronn theorem**: a Dirichlet series with
  functional equation, real coefficients, and an off-critical-line zero
  exists. Mathlib has Dirichlet characters and L-functions, so the objects are
  statable; the off-line zero needs certified interval evaluation in Lean
  (thin territory — this is the mountain), with `rigor.py` as the working
  blueprint. Landing it puts gate 3 into the certified library.

**Inherited open item (previous sprint, unchanged):** the cokernel/absorption
reading of the adelic route. The matrix route was closed by experiment (see
`9360b00`, `docs/17-the-falsification-harness.md`); any revival must clear the
4-gate spectral harness (`zeta/spectral_gate.py`) *and* the new §5.1
requirements.

---

## Addendum — the upstream track (2026-08-06, `f47a490` + `f5a1cbd`)

Written by a second session working the same checkout. Two things landed, plus
one correction to the section above.

**Correction to §1 (scope reconciliation).** The wording recorded above — "a
computational falsification laboratory and research program … not presently a
proof; a proof would require …" — was replaced in `f47a490` at the owner's
direction, on the grounds that it hedged where a plain statement would do. The
scope language in `README.md` and `CLAUDE.md` is now:

> Zeta Lab is a computational and formal workbench that reconstructs, tests,
> connects, and falsifies ideas around RH, without claiming to advance RH.

Nothing about the substance changed — no numerical claim, no gate, and not the
standing rule that nothing here is evidence for RH. Only the register.

**The upstream track (`f5a1cbd`).** `lean/` produces more value if some of it
ends up in Mathlib rather than only compiling here. `scripts/mathlib_gaps.py`
generates `references/mathlib-open-targets.md` from Mathlib's own
`docs/1000.yaml`: **970 of 1179** famous theorems carry no `decl:`, which is the
library recording what it wants and lacks. `ROADMAP.md` §"The upstream track"
carries the judgment, verified 2026-08-06 by code search and open-PR search
against Mathlib master and PrimeNumberTheoremAnd:

| target | in Mathlib | claimed |
| --- | --- | --- |
| Hardy Z, Riemann–Siegel ϑ | no | no — not in PNT+ either |
| Sturm's theorem | no (`1000.yaml` Q1632301) | no |
| Critical line theorem | no (`1000.yaml` Q205966) | no |
| `N(T)` | no | **yes — PNT+ owns it, do not duplicate** |
| `riemannZeta_conj`, Λ(1−s)=Λ(s) | **yes** | — |

Two decisions worth not re-deriving. **Build Hardy Z from
`completedRiemannZeta`, not from e^{iϑ}ζ** — the textbook route needs a
continuous branch of log Γ along the critical line, which Mathlib lacks, while
the Λ route gets realness from `riemannZeta_conj` + `completedRiemannZeta_one_sub`,
both already merged. **Hardy Z precedes Sturm**, even though Sturm is the
higher-impact target: Sturm is a multi-thousand-line development and a first PR
that size from a contributor with no merged history does not get reviewed.
Impact alone argues the opposite order; that is the trap.

Porting work itself lives in a **separate repo, `../contrib-lab`** — checking
tools, target files, and the record of what review asked for. It holds no
mathematics. Nothing in this repo depends on it.

**Not done here:** neither target is scoped in Lean, and Zulip has not been
checked for an unannounced claim on either.

---

## Addendum — the department architecture (2026-08-06, `0bb04c3`..`499d632`)

**What landed.** `harness/` — the falsification protocol with the subject
factored out, and the mechanism that makes the lab extensible by *department*.
Full rationale and non-goals: `ROADMAP.md`, "The department architecture".
Design and the how-to: `harness/README.md`. Reader-facing: `docs/doors/`.

Six commits, all on `main` and pushed. Also merged in the same pass: the
`five-longshots` branch and the `worktree-factorization-gate` worktree branch
(`zeta/factorization.py`, Gate 4 as a decision statistic), both of which were
sitting unmerged.

**Two repairs worth knowing about:**

- `scripts/make_context.py` still pointed `DISCOVERY` at `ROOT/"discovery"`,
  a directory that had not existed since the `discovery/` → `ontology/`
  rename. That whole section of `CONTEXT.md` had been silently empty. Fixed,
  and a `harness/` section added. The stale name was also live in `CLAUDE.md`,
  `README.md`, `llms.txt`, `ontology/README.md` and `docs/00-orientation.md`.
- `-n auto` hung twice in `pytest_sessionfinish` teardown *after* every test
  had passed. `-n 4` completes cleanly (1548 passed, 5 skipped, 31m41s). Not
  diagnosed; if it bites you, that is the workaround, and note that
  `-p no:xdist` does **not** work because `-n auto` is already in `addopts`.

**What is open here.**

- **Department #2 is the only real test of this design.** One department means
  the four roles are a generalisation of exactly one case (`ROADMAP.md`, known
  gap 2). The cheapest honest candidate is `finitefield` — curves over `F_p`,
  where RH *is* a theorem, so its battery has an unusually clean rival
  structure. It would also answer whether "rival" survives contact with a
  subject where the property is decidable.
- **Three instruments in `zeta/` are not yet wired into the battery**:
  `zeta.spectral_gate` (used by the department's decoys only in principle —
  the decoys are declared but no measurement currently calls `run_ablation`),
  `zeta.detectors`' Li and Weil lesion functions, and `zeta.quasicrystal`.
  Wiring each is small and each would replace an argument with a measurement.
- **`factorization_defect` cannot referee one of the three rivals** — Epstein
  (2,1,3) has a₁ = 0. Recorded in `docs/doors/zeta.md` and pinned by
  `tests/test_harness_zeta_department.py`. If someone finds a normalisation
  that makes D well-defined there, it becomes a second distinguishing
  reference claim.

**Housekeeping left deliberately undone:** the merged branches
`five-longshots` and `worktree-factorization-gate` still exist locally, and the
`factorization-gate` worktree is still on disk and locked.

---

## Continuation checklist

1. `git pull`; confirm fast tier green
   (`.venv/bin/python -m pytest -q -m "not slow"`).
2. `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` — must complete with
   zero `sorry`s before adding theorems.
3. Start rung 2: state κ's defining linear system in Lean; keep the Python
   derivation open beside it as the reference implementation.
4. Regenerate `CONTEXT.md` after any public API/doc/script change.
5. If you add a department: build its battery first, list it in
   `harness/departments/__init__.py`, then run
   `.venv/bin/python -m pytest -q -o addopts='' tests/test_department_conformance.py`.
   The audit is parametrized over that listing — adding the name is what turns
   it on. `harness/README.md` has the four steps.
