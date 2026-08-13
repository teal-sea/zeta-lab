# Novelty check: the `k = 1` retention inequality

**Date:** 2026-08-13. **Purpose:** price the asset before anything is built on
it publicly. Companion to `NOVELTY-CHECK.md`, which killed a different claim
from this hunt on 2026-08-12.

**Verdict up front: novel, but in the weakest available sense, and its
significance is contingent on an open problem.** It is not a strengthening of
anything in the paper. It is a statement about objects this laboratory
defined, inside a route this laboratory built, whose payoff requires `k >= 2`,
which is open.

---

## 1. What the claim was taken to be

`PROOF-LEDGER.md` records the `k = 1` retention inequality as closed at
hardened grade and adds:

> That is strictly stronger than what the tree carries (`d >= 4`, or
> `n <= 3`), and it retires the separation route rather than improving it.

Read quickly, "the tree" sounds like the surrounding literature, which would
make this a strengthening of a published lemma.

## 2. What "the tree" actually is

Both comparison lemmas are in **this laboratory's own extension package**:

```
Zeta23Ext/EForm3/Main.lean:84   theorem retention_separated_of_le  (hypothesis hsep)
Zeta23Ext/EForm3/Main.lean:105  theorem retention_le_three         (hypothesis n <= 3)
```

The upstream pin — `anthropics/zeta-23-lean` @ `3635e74`, the paper's own
complete `sorry`-free formalisation of Theorems A-E, 316 Lean files — contains
**no occurrence of `retention`, `Eng`, `Kpair` or `Dam`**. The energy
functional `Eng`, the pair kernel `Kpair`, the damage `Dam` and every
`retention_*` lemma are defined in `Zeta23Ext/EForm3/Defs.lean` and
`O9Sound.lean`, i.e. here.

Checked by:

```bash
grep -rn "retention" hunts/frontier_math/zeta23ext/.lake/packages/Zeta23/   # no matches
grep -rn "def Eng\|def Kpair\|def Dam" hunts/frontier_math/zeta23ext/Zeta23Ext/
```

So the comparison is against **an earlier version of our own lemma**, not
against the literature. The paper does not carry this inequality in any form,
strong or weak, because the paper's argument does not pass through it.

## 3. What follows

**On novelty.** The inequality is new, but trivially so: it is a statement
about a bespoke functional (`g u = cos(sqrt 2 u)` on `|u| <= 1/2`, `c2 = g * g`,
`Eng` its weighted energy). Nobody has proved it because nobody has asked it.
That is the weakest form of novelty there is, and it is not what a reader means
by the word.

**On significance.** The route exists to improve the constant, and improving
the constant needs the multi-pair quantifier `k >= 2`, which is open — three
separate approaches to it were eliminated on 2026-08-13 (`K2-ROUTE.md`).
Without `k >= 2` the inequality has no downstream consequence: the constant is
unchanged and nothing else in the tree depends on it.

**So a public claim of the form "we proved the `k = 1` retention theorem" would
invite, and fail, the question "what does it give you?"** The honest answer
today is "nothing yet". That is a lemma in an unfinished argument, and the
correct thing to do with it is finish the argument or say plainly that it is
unfinished.

## 4. What this does not diminish

Two things, and they are not the theorem:

1. **The formalisation is real and checkable.** O9 — a two-variable
   interval-arithmetic bound over `[28/5, 60] x [0, 1/2]` — went from never
   having been compiled to `decide +kernel` on 699 cells with no `sorry`, no
   `native_decide` and no added axiom, in a day.
2. **The first table was false and this laboratory is what found out.** The
   kernel refuted it on 7 of 9 chunks; the cause was traced to a leaf model
   that did not match `Leaves.lean`; the model was rebuilt operation for
   operation and pinned against Lean's own evaluation integer for integer, then
   the round trip was extended one level up because the leaf control could not
   have caught a defect in the compositions above it.

Those are claims about **method**, they are checkable by a stranger running
`lake build`, and they do not depend on `k >= 2` being resolved. A negative
result about one's own artifact, found and published by the same party, is
worth more than a lemma nobody asked for.

## 5. Scope

This file assesses novelty and consequence. It does not assess correctness:
the `k = 1` inequality is at hardened grade by four instruments plus an exact
rational certificate, and O9 beneath it is kernel-checked. Nothing here
disputes either. Nothing here moves the constant.
