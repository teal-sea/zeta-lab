# Guide: the two certainty regimes

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

Two things here may use the word *certified*, and they mean different
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
| 3 (mathematics done; compute outstanding) | Davenport–Heilbronn itself — that zeta-shaped symmetry alone cannot give RH |

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
principle needed), generalises it from a disk to the frontier of any bounded
open set, and specialises that to an axis-aligned square kept right of the
critical line, so that `davenport_heilbronn_of_certified_square` derives the
**full** `davenport_heilbronn_statement` from two interval inequalities:
`‖DH‖` small at the centre, `‖DH‖` bounded below on the four boundary
segments. A square rather than a circle because rectangle arithmetic covers
segments without slack.

**The numeric half is now mathematics-complete.** What the earlier version of
this page listed as missing has been built, all kernel-checked with zero
`sorry`s:

| piece | file |
|---|---|
| certified `exp`/`log` on rational intervals, any positive rational | `IntervalExp.lean` |
| certified complex `exp` (so certified `sin`/`cos` come free), outward dyadic rounding | `IntervalCExp.lean` |
| `n^{-s}` tied to a computed box — the oracle gap, closed | `IntervalCExp.lean` |
| the tail bound: DH's analytic continuation as a finite sum plus explicit error | `DHTailBound.lean` |
| assembly: partial box + tail radius ⟹ encloses `DH s`; the κ interval | `DHAssembly.lean` |
| a worked instance: `DH(3/2 + 3i) ≠ 0` | `DHDemo.lean` |

That last one is the first kernel-certified fact about a *value* of the
Davenport–Heilbronn function, produced with no oracle input anywhere.
`ZetaLean/OracleDH.lean`'s per-term data is now redundant in principle.

What remains is **compute, not mathematics**, and it is priced rather than
guessed. The certification target is forced: `t ≈ 85.699` is the lowest
off-line zero, pinned by a standing test
(`tests/test_epstein.py::test_no_offline_zero_below_the_pinned_one`), and
the cost scales like `‖s‖^2.2`, so no cheaper zero exists to aim at.
Instantiating the square directly would cost months of single-core kernel
time at measured rates. The fix — a steeper tail exponent — is now
kernel-checked in `DHTailBound2.lean`: the sum-vs-integral comparison
(`DH_tail_bound_order1`, `K^{-(σ+1)}`) and its trapezoid refinement
(`DH_tail_bound_order2`, `K^{-(σ+2)}`), built from an elementary rectangle
and trapezoid rule for Banach-valued `C¹`/`C²` functions summed along a
half-line — no Bernoulli numbers, no general Euler–Maclaurin, and Mathlib
needs neither. The closed-form block antiderivative exists precisely
because the DH coefficients sum to zero. A 1e-3 tail at the oracle zero
drops from `K = 195301` blocks to `243`
(`tests/test_epstein.py::test_dh_tail_bound_required_K_pins_the_cost_model`),
re-pricing the offline run at ~9,550 certified terms — about half a day
single-core.

The ladder and the next rung live in `HANDOFF.md`;
`references/mathlib-open-targets.md` tracks what Mathlib itself records as
wanted and unbuilt.
