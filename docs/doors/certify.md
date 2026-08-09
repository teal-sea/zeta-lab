# Door: the two certainty regimes

**For you if** you care about the difference between a number that is *accurate*
and a statement that is *proved*, and want to work where nothing is measured.

**First command:**

```bash
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build      # must report 0 sorrys
```

## Two regimes, and they are not the same

Most of this repository is **accurate**: high-precision numerics, cross-checked
against independent oracles, with every claimed number pinned by a test. That
is a real property and a weaker one than proof.

Two things here are entitled to the word *certified*, and they mean different
things:

| Regime | What it is | Where |
|---|---|---|
| **Kernel-checked** | symbolic truth, verified by Lean 4's proof kernel against Mathlib | `lean/` |
| **Enclosure-carrying** | a numeric quantity every step of whose computation carried a rigorous interval | `zeta/rigor.py` |

Say which one you mean. Everything else in the tree is accurate, not certified.

## The safe failure mode is mandatory

`zeta/rigor.py` never silently upgrades a float to a certificate:

- `proven_sign` returns `0` for **not decided** — never a guess;
- any step that could not carry an enclosure is named in `uncertified_steps`;
- `certified` is `False` whenever that list is non-empty.

A dict reporting `certified: True` is asserting a theorem. If any step fell
back to floats, that is a critical defect, not a rounding detail.

```bash
.venv/bin/python scripts/09_certified_verification.py
```

## Certified Weil positivity

`rigor.enclose_weil_functional` encloses the Weil functional W(h) — the
arithmetic side of the explicit formula, whose nonnegativity over all
admissible h is *equivalent* to RH. The near-tight Gaussian member
(W ≈ 8.86e-18 out of pieces of size ~2, eighteen digits of cancellation)
comes back certified positive. Two limits, stated where they bind: it is
flint-only (mpmath's `iv` has no certified quadrature, so the two-backend
cross-check cannot run there — the returned dict says so), and finitely many
certified instances are not evidence for RH (`docs/08`); they are positivity
statements that no longer rest on floating-point luck.

## The Lean ladder

`lean/` climbs deliberately, and **nothing counts until it compiles with zero
`sorry`s**. A `sorry` is an uncertified step: tracked in the file, never
hidden.

| Rung | Statement |
|---|---|
| 1 (done) | the lab's ground-truth facts wired to their Mathlib proofs |
| 2 (done) | the κ derivation behind the Davenport–Heilbronn counterexample |
| 3 (analytic half done) | Davenport–Heilbronn itself — that zeta-shaped symmetry alone cannot give RH |

Rung 3's analytic half is kernel-checked in `ZetaLean/DHAnalytic.lean`: the
DH function built from the quartic character mod 5, entire, summing the
`dh_coeff` series on `Re > 1`, with its completed functional equation proved
through the root-number identity — κ is exactly the rotation aligning the two
conjugate root numbers, grown from Mathlib's `cos(π/5) = (1+√5)/4`. Proving
it exposed that the original Phase A *statement* was false in Lean's
semantics (Mathlib's junk value `Γ(0) = 0` broke the unguarded functional
equation at `z = -1`) and too weak (no differentiability, so a patchwork `f`
could fake the off-line zero); both defects are fixed in
`ZetaLean/DavenportHeilbronn.lean`.

The topological step is also closed: `ZetaLean/DHZeroCriterion.lean` proves
a minimum-modulus criterion (maximum modulus applied to `1/f` — no argument
principle needed) and instantiates it on the radius-`1/10` disk around the
oracle zero `0.808517 + 85.699348i`, so that
`davenport_heilbronn_of_certified_disk` derives the **full**
`davenport_heilbronn_statement` from exactly two interval inequalities:
`‖DH‖ < 1/100` at the centre, `‖DH‖ ≥ 1/100` on the boundary sphere. The
oracle says both hold with tenfold margin (`‖DH‖ ≈ 6.5e-7` at the centre,
boundary minimum `≈ 0.121`). What remains of rung 3 is the numeric half —
discharging those two hypotheses by certified interval evaluation of `DH`
inside the kernel, which needs certified complex `exp`/`log` and
Hurwitz-zeta continuation that `ZetaLean/Rigor.lean` does not yet have
(`ZetaLean/OracleDH.lean` holds the oracle data, still uncertified).

The ladder and the next rung live in `HANDOFF.md`;
`references/mathlib-open-targets.md` tracks what Mathlib itself records as
wanted and unbuilt.
