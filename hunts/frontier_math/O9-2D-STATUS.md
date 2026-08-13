# O9, two-dimensional: what it costs and what still blocks it

**Date:** 2026-08-13. **Code:** `o9_leaf2d.py`, `test_o9_leaf2d.py` (21 pins).
**Reads:** `O9-SCOPING.md` (the route), `RETENTION-PROBLEM.md` §4 (the statement).
**Supersedes** `O9-SCOPING.md` §3's leaf count and §4's shopping list, on both of
which it was wrong in the safe direction and the unsafe one respectively.

## 1. The table exists and closes

Built through the removable branch `R = Qim/y`, over the full box
`[28/5, 60] x [0, 1/2]`, in the **fixed-point integer arithmetic the kernel
runs** (`o9_leaf.py`'s mirror of `Iv.lean`/`Phi.lean`, reused unchanged):

| operating point | cells | undecided | max depth |
|---|---|---|---|
| inflation `1.20x`, widening `1/200` | **339** | **0** | 17 |
| inflation `1.15x`, widening `1/200` | 373 | 0 | 17 |
| inflation `1.10x`, widening `1/200` | 435 | 0 | 17 |
| inflation `1.05x`, widening `1/200` | 601 | 0 | 17 |

Minimum margin at the recommended point is `9.9e11` ulp at scale `2^-64`,
i.e. about `5.4e-08` absolute. 95 of the 339 boxes reach `y = 0` and all of
them decide.

**This needs no depth-reduction lemma.** That is the whole point: the 1-D
table reaches other depths through `D(y,s)/y^2 <= 4 D(1/2,s)`, which is
measured and unproved.

## 2. The cost comparison in `O9-SCOPING.md` §3 is not like-for-like

That file reports 389 leaves for the 2-D route against the 1-D route's 344 and
calls the difference "45 extra leaves to drop an unproved lemma". The 389 is an
**Arb-grade** count at 160 bits; the 344 is a **kernel-grade** count. The two
arithmetics have different dependency growth, which is the entire reason
`o9_leaf.py` exists (its own docstring: the Arb-grade estimate of the 1-D table
was 196, and the kernel needs 344, understating by 43%).

Measured in one arithmetic, at one inflation:

| route | inflation | cells | needs the depth lemma? |
|---|---|---|---|
| 1-D, `y = 1/2` | `1.05x` | 344 | **yes** |
| 2-D, full box | `1.05x` | **601** | no |
| 2-D, full box | `1.20x` | **339** | no |

So dropping the unproved lemma costs **+257 cells (+75%)** at fixed inflation,
or **nothing in cells at all** if the extra `1.05x -> 1.20x` inflation is spent
instead. It is a trade between table size and budget surplus, not a free lunch.
The budget absorbs it: §7 surplus at `1.20x` is `2.599e-02` against the
`1.3945x` wall, still `1.16x` of margin in hand.

The recommendation stands, and for a better reason than the one given: at
`1.20x` the 2-D table is *no larger* than the 1-D table already generated.

## 3. One thing `O9-SCOPING.md` §4 asked for is already in the package

§4.2 asks for "one new leaf, the removable branch `Qim(y,s)/y`", needing
`sinh(a/2)/a`, and prices it as "a copy of an existing pattern". It is cheaper
than that: `Leaves.lean` already carries `sinhL`, and `sinhCoshSmall` already
evaluates `hornerI sinhL (EIv.sqr a)` internally on its way to `sinh`. That
expression **is** the `sinh(v)/v` enclosure. The new leaf is

```lean
def shcSmall (a : EIv) : EIv := EIv.widen (hornerI sinhL (EIv.sqr a)) 1
```

with `hornerI_mem sinhL sinhL_pos` supplying the series side already. What is
genuinely new is only its truncation lemma — the analogue of `sinh_taylor` for
`sinh v / v` rather than `sinh v`, which cannot be borrowed because
`sinh_taylor`'s bound divided by `|v|` blows up exactly where this branch is
used.

## 4. What §4 did not mention, and should have

**`phiC_mem` carries the hypothesis `y ≠ 0`.** The 2-D route's boxes reach
`y = 0` by construction, so the seam lemma cannot be applied to them as stated.

This is a case split, not an obstruction, and it is cheap: at `y = 0`,
`Qim(0,s) = 0`, so `Dam 0 s = -Qre(0,s)^2 <= 0 = c * 0^2` and O9 holds
immediately with no arithmetic at all. The enclosure work is then only ever
needed for `y ∈ (0, 1/2]`, where `phiC_mem` applies unchanged and the boxes
touching `y = 0` still cover it. Whoever writes the Lean should write that
split first, so the `y ≠ 0` side condition never has to be weakened.

## 5. A defect this file exists partly to record

The first draft of `r_iv` had the **wrong sign**. `Phi2(s + iy)` has real part
`Qre` and imaginary part `-Qim`, and the table uses `R` only through `R^2`, so
the sign is invisible to every cell verdict, to the leaf count, and to the
emitted Lean. It was caught only by checking the enclosure against
`o9_scoping.py`'s independent evaluation, which is now
`test_r_iv_encloses_qim_over_y_with_the_right_sign`.

The general shape is the one `PROOF-LEDGER.md` logs five times: a quantity
carried across contexts without being re-derived in the context it is used.
The specific lesson is narrower and worth keeping: **a quantity that enters
only squared has no self-check, so it needs an external one.**

## 6. Scope

This lands a generator and a pre-validated table. It does **not** land a Lean
file: the checker needs `shcSmall`, its truncation lemma, the `y = 0` split of
§4, and the `rIv`/`qreIv` compositions with their `_mem` seams, none of which
is written. Nothing here is kernel-checked. O9 remains open, the `k = 1` chain
remains at hardened grade, and `k >= 2` — the actual open mathematics — is
untouched. Nothing here is evidence about RH.
