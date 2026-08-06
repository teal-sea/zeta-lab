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

## Continuation checklist

1. `git pull`; confirm fast tier green
   (`.venv/bin/python -m pytest -q -m "not slow"`).
2. `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` — must complete with
   zero `sorry`s before adding theorems.
3. Start rung 2: state κ's defining linear system in Lean; keep the Python
   derivation open beside it as the reference implementation.
4. Regenerate `CONTEXT.md` after any public API/doc/script change.
