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
| 2 | the κ derivation behind the Davenport–Heilbronn counterexample |
| 3 | Davenport–Heilbronn itself — that zeta-shaped symmetry alone cannot give RH |

The ladder and the next rung live in `HANDOFF.md`;
`references/mathlib-open-targets.md` tracks what Mathlib itself records as
wanted and unbuilt.
