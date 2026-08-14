# The retention inequality with no separation hypothesis

**Target**: remove the hypothesis `hsep` from `Retention.retention_separated_of_le`
and the hypothesis `n ≤ 3` from `Retention.retention_le_three`, in the package
`hunts/frontier_math/zeta23ext` (namespace `Retention`, files
`Zeta23Ext/EForm3/*.lean`).

```lean
theorem retention_unconditional {n : ℕ} {x : ℕ → ℝ} {y t : ℝ}
    (hy0 : 0 ≤ y) (hy : y ≤ 1/2) :
    (199/200) * Eng (Fsum n x) + (n : ℝ)/200 + 4
      ≤ Eng (fun w => Fsum n x w + Pfun y t w)
```

Everything below is stated in the existing definitions (`Zeta23Ext/EForm3/Defs.lean`):
`g u = cos (√2 u)` on `|u| ≤ 1/2` and `0` elsewhere, `A = √2 sin (1/√2) = ∫ g`,
`c2 = g ⋆ g`, `Eng G = (1/A²) ∫_{-1}^{1} c2 w ‖G w‖² dw`,
`Qre a b = ∫ g u cosh(a u) cos(b u) du`, `Qim a b = ∫ g u sinh(a u) sin(b u) du`,
`Shq y = Qre (2y) 0 ^ 2 - A²`.

Two abbreviations are used throughout:

```lean
noncomputable def Kpair (u : ℝ) : ℝ := Qre 0 u ^ 2                      -- the pair kernel
noncomputable def Dam (y s : ℝ) : ℝ := max 0 (Qim y s ^ 2 - Qre y s ^ 2)  -- the damage
```

---

## 1. Why the existing route stops

`retention_of_damage` (kernel-checked) reduces the theorem to

    ∑_j (Qim y s_j ² − Qre y s_j ²) ≤ Shq y / 2,    s_j = x_j − t.

**That hypothesis is false in general.** At `y = 1/2` the damage has a maximum
`0.00439642` at `s = 6.51700`, while `Shq(1/2)/2 = 0.03375420`. Eight offsets at
the maximum give `8 × 0.00439642 = 0.03517 > 0.03375`. So for `n ≥ 8` the damage
alone can exhaust the budget, and any proof for all `n` **must keep the repulsion
term**, which `retention_of_damage` discards.

The separation hypothesis works only because it forbids the offsets from
repeating; it is the *clustered* configurations that break the damage-only route,
and those are exactly the configurations on which the discarded term is large.

---

## 2. The reduction that keeps the repulsion term

**Lemma 2.1 (algebra only; `retention_gap`, `energy_F`, `Qre_zero_zero`).**
`retention_unconditional` is equivalent to

> **(★)**  `(1/200) * ∑_{j ≠ k} Kpair (x_j − x_k) + 4 * ∑_j (Qre y s_j ² − Qim y s_j ²) + 2 * Shq y ≥ 0`

*Proof.* `retention_gap` gives
`Eng(F+P) = Eng F + 4 + (1/A²)(4 ∑_j (Qre y s_j ² − Qim y s_j ²) + 2 Shq y)`,
so the goal is `0 ≤ (1/200)(Eng F − n) + (1/A²)(4 ∑_j (…) + 2 Shq y)`.
By `energy_F`, `Eng F = (1/A²) ∑_{j,k} Kpair (x_j − x_k)`; multiplying by `A² > 0`
and using `Kpair 0 = A²` (`Qre_zero_zero`) to split off the diagonal
`∑_{j,k} = n A² + ∑_{j ≠ k}` gives (★). ∎

Since `Qre y s ² − Qim y s ² ≥ −Dam y s`, (★) follows from

> **(★★)**  `4 * ∑_j Dam y s_j ≤ (1/200) * ∑_{j ≠ k} Kpair (x_j − x_k) + 2 * Shq y`

and **(★★) is the whole content of the new proof**. It is stated for every `n`,
every `x`, every `t`, every `y ∈ [0,1/2]`, with no separation hypothesis.

---

## 3. The three facts that make (★★) true

1. **`Kpair ≥ 0` pointwise** — it is a square. So *any* off-diagonal pair may be
   discarded without sign bookkeeping; there is no need to control the sign of the
   interaction between distant points, which is what forced the near/far split.
2. **`Kpair` is bounded below at short range**: `Kpair u ≥ 39/50` for `|u| ≤ 1`
   and `Kpair u ≥ 1/125` for `|u| ≤ 6` (true values `0.78066657` and `0.00834800`).
   Two points close together therefore pay a definite price.
3. **The damage is confined to narrow, widely separated windows**: `Dam y s = 0`
   for `|s| ≤ 28/5` (`no_damage`, kernel-checked), and beyond that its support sits
   in disjoint intervals of length `< 1` whose left endpoints recur at spacing
   `> 6.16` (measured: `≈ 2π` from below, width `≈ 0.96`, duty cycle 15.3%).

Points inside one window are within `1` of one another, so `m` of them pay at
least `(39/50)/200 · m(m−1)` while collecting at most `4 c_k y² m` of damage — and
**`m` is an integer**. Maximising over integers, window by window, and summing is
the proof.

---

## 4. The obligations

`⟨have⟩` = already in the package with zero `sorry`s.

| # | statement | status |
|---|---|---|
| O1 | `0 ≤ Kpair u` | ⟨have⟩ `sq_nonneg` |
| O2 | `Kpair 0 = A²` | ⟨have⟩ `Qre_zero_zero` |
| O3 | `|u| ≤ 1 → 39/50 ≤ Kpair u` | **new**, numeric; true value `Kpair 1 = 0.78066657` |
| O4 | `|u| ≤ 6 → 1/125 ≤ Kpair u` | **new**, numeric; true value `Kpair 6 = 0.00834800` |
| O5 | `|s| ≤ 28/5 → Dam y s = 0` | ⟨have⟩ `no_damage` |
| O6 | `28/5 ≤ |s| → Dam y s ≤ y² * Wt (s²−2)` | ⟨have⟩ `Qim_far_sq_abs` (`Dam ≤ Qim²`) |
| O7 | `Wt` antitone, `Wt w ≤ (637/1000)/w` for `w ≥ 1368` | ⟨have⟩ `Wt_anti`, `Wt_tail_le` |
| O8 | `(51944/100000) * y² ≤ 2 * Shq y` for `0 ≤ y ≤ 1/2` | ⟨have⟩ `Shq_half_lower` |
| O9 | window cover on `28/5 ≤ |s| ≤ 60` (table below) | **new**, numeric, the only real work |
| O10 | integer trade (Lemma 5.1) | **new**, elementary |
| O11 | final rational arithmetic (§7) | **new**, `norm_num` |

O3 and O4 are one-variable numeric bounds on `Qre 0 ·`, for which
`Estimates.lean` already carries the pattern (`fk`, the near-field lower bound on
`|s| ≤ 28/5`). A closed form that makes them elementary:

    Qre 0 s = 2 (s · cos(√2/2) · sin(s/2) − √2 · sin(√2/2) · cos(s/2)) / (s² − 2)

(equal to `Qre_closed` at `a = 0` after combining the two terms; `Qre 0 ·` is
decreasing on `[0, 2π]`, so `min_{|u| ≤ w} Kpair u = Kpair w` for `w ≤ 2π`).

### O9, stated precisely

> For every `y ∈ [0, 1/2]` and every `s` with `28/5 ≤ s ≤ 60`: either
> `Dam y s = 0`, or `s ∈ I_k` for exactly one `k < 9`, and then `Dam y s ≤ c_k y²`.

| k | `I_k` (rational endpoints) | length | `c_k` (= 21/20 × sup) |
|---|---|---|---|
| 0 | `[60653/10000, 35257/5000]` | 0.9861 | `9232503/500000000 = 1.8465006e-02` |
| 1 | `[61171/5000, 131999/10000]` | 0.9657 | `8190483/2000000000 = 4.0952415e-03` |
| 2 | `[11544/625, 48583/2500]` | 0.9628 | `3555573/2000000000 = 1.7777865e-03` |
| 3 | `[247289/10000, 256909/10000]` | 0.9620 | `396669/400000000 = 9.9167250e-04` |
| 4 | `[309971/10000, 159793/5000]` | 0.9615 | `126441/200000000 = 6.3220500e-04` |
| 5 | `[372701/10000, 76463/2000]` | 0.9614 | `219051/500000000 = 4.3810200e-04` |
| 6 | `[21773/500, 27817/625]` | 0.9612 | `128583/400000000 = 3.2145750e-04` |
| 7 | `[498237/10000, 507849/10000]` | 0.9612 | `24591/100000000 = 2.4591000e-04` |
| 8 | `[280513/5000, 570637/10000]` | 0.9611 | `194187/1000000000 = 1.9418700e-04` |

Each `I_k` has length `< 1`; the `I_k` are pairwise disjoint (left endpoints
spaced by more than `6.16`); `I_0` starts at `6.0653 > 28/5`; `I_8` ends at
`57.0637 < 60`. Negative `s` is the mirror image (`Dam` is even in `s`: `Qre` is
even and `Qim` is odd in the second argument).

**The caps carry deliberate slack, and this is load-bearing.** An earlier
draft of this file set `c_k` equal to the `sup` of `Dam y s / y²` over
`I_k × [0,1/2]`, rounded up at the seventh decimal. That version of O9 is
**not provable by interval arithmetic at any table size**: the supremum is
attained at an *interior* point of every window (always at `y = 1/2`;
`o9_scoping.py` recomputes all nine and finds ratio `1.0000` to four
figures), and any enclosure of a box containing the argmax has an upper
bound strictly greater than the supremum. An inequality that is an equality
somewhere has no margin for a ball to fit in.

The caps above are therefore `21/20` times that supremum — a documented
`1.05×` inflation. Two independent measurements bound the room available:
`o9_scoping.py` §7 finds the budget absorbs inflation up to **`1.3945×`**
before the surplus reaches zero, and `window_table.py` builds the `y = 1/2`
leaf table at `1.02×` with **0 undecided cells** in 196. `1.05×` sits inside
both, and §7 below is recomputed at it.

Measured worst case of `(Dam y s / y²) / sup_k` over `y ∈ {0.45, …, 0.02}` is
`0.995985`, so the `y = 1/2` profile dominates; the windows also **nest**
(`I_k(y) ⊆ I_k(1/2)` for `y ≤ 1/2`), which is why one table serves every `y`.

### O9 as a two-variable table (2026-08-14) — no depth-reduction lemma

The `y = 1/2` table (`o9_leaf.py`, 344 cells) reaches the other depths only
through `D(y,s)/y² ≤ 4 D(1/2,s)`, which is **measured and unproved**. The
two-variable table below removes that step. It is not a matter of resolution:

* A naive 2-D check on a box touching `y = 0` bounds `c·y²` below by `c·0 = 0`
  and so demands `Qim² ≤ Qre²`, **false at the zeros of `Qre(0,·)`** — and
  those zeros are *inside* the windows, one per window, at
  `s* = 6.6431, 12.7553, 18.9767, 25.2285, 31.4926, 37.7631, 44.0372, 50.3135,
  56.5914`.
* Layering in `y` does not help either. Measured, the `y → 0` limit of
  `sup_s Dam/y²` is `0.936 c_0` and `0.970–0.979 c_k` for `k ≥ 1`, so the
  supremum is nearly attained at *every* depth; a layer `[y_lo, y_hi]` checked
  against `lo(y²)` needs `y_hi/y_lo ≤ √1.20 = 1.0954`, and covering `(0,1/2]`
  in such layers takes infinitely many.

The cure is to factor the removable zero out. `Qim` is odd in `y`, so
`Qim = y·R` with `R` analytic across `y = 0`, and the check becomes

> **(O9′)**  `y² (R² − c) ≤ Qre²`

whose two sides are `O(1)` where the original pair was `O(y²)`. At `y = 0` the
left side is `0` and the right side is `Qre(0,s)² ≥ 0`. With `c = 0`, (O9′) is
*also* the complement claim, so one shape covers windows and gaps alike.

Built by `o9_leaf2d.py` at the `O9-SCOPING.md` operating point (widening
`1/200`, inflation `6/5`), in the kernel's own fixed-point arithmetic:

| | |
|---|---|
| leaves | **1939** |
| max depth | 20 |
| undecided | 0 |
| smallest carrying margin | `1.05e-08` (`1.9e11` ulp) |
| emitted size | 205 KB, 49 `decide +kernel` chunks |

Leaves that hold a zero of `Qre(0,·)` report zero margin under the obvious
metric and are **not** close calls: there both sides of the general test
vanish, and the leaf is carried instead by `R² ≤ c`. `cell_verdict` reports
whichever of the two slacks carries the cell.

### The leaf caveat was false, and the kernel caught it

`o9_leaf.py`'s LEAF CAVEAT says its Arb leaves and `Leaves.lean`'s Taylor
leaves "agree to well under `2^-60`", so a cell passing with margin is safe.
**That is true for narrow intervals and false for wide ones**, because the two
compute different things: Arb encloses `sin` over an interval by its *range*,
while `sinCosIv` reduces mod `2π`, quarters, evaluates a 22-term Taylor
interval and then applies `dbl` twice — and `dbl` squares an interval, so
width grows. On the first cell of this table (`s ∈ [5.6, 6.0603]`) Arb gives
`sin` width `0.224` against the kernel's `0.366`, a factor `1.63`.

A first version of this table, built on Arb leaves, reported **598 leaves**
with smallest margin `1.85e-08` — and `decide +kernel` **rejected 14 of its
15 chunks**. The leaves in `o9_leaf2d.py` are now Lean's own algorithms in
Lean's own integer arithmetic, checked bit-for-bit against `#eval` output
(`test_leaves_reproduce_the_kernel_bit_for_bit`, with
`test_arb_would_have_been_optimistic` as its control). There is no caveat left
to state: the module computes what the kernel computes.

The honest cost of that correction is `598 → 1939` leaves, and the honest cost
of dropping the unproved depth-reduction lemma is `344 → 1939`.
`O9-SCOPING.md` §3 predicted 389 for a 2-D route; that estimate used Arb
leaves and is **5× low**. Its 1-D counterpart (`o9_leaf.py`, 344 cells) rests
on the same false caveat and has never been put to the kernel; its count
should be assumed low by a similar factor until it is.

**Two new obligations replace O9, and neither is proved:**

| # | statement | status |
|---|---|---|
| O9a | `shfnIv_mem`: `shfnIv` encloses `sinh(u/2)/u` | **new**, mirrors `sfnIv_mem` (`Leaves.lean` L6) |
| O9b | `o9Field_mem`: `o9Field` encloses `(Re Φ₂, Im Φ₂ / y)` on the cell | **new**, the real/imaginary decomposition |

`O9Field.lean` defines the field and the `shfnL` series; `O9Data2.lean` and
`O9Check2.lean` are generated. **No `sorry` stands in for O9a or O9b** — until
they exist the checker checks the table and says nothing about `Dam`.

---

## 5. The proof of (★★)

**Lemma 5.1 (the integer trade).** For `q > 0`, `c ≥ 0` and `m : ℕ`,

    4 c m − q m (m−1) ≤ P(c,q) := max over m₀ ∈ {⌊½ + 2c/q⌋, ⌈½ + 2c/q⌉} of (4 c m₀ − q m₀(m₀−1)).

*Proof.* The real function `m ↦ 4cm − q m(m−1)` is concave with maximum at
`½ + 2c/q`; on the integers the maximum is at one of the two neighbours. ∎

This is the step the convex relaxation cannot take, and it is the step that makes
the bound uniform in `n` (see §8).

**Proof of (★★).** Write `s_j = x_j − t`, `q = (39/50)/200 = 39/10000`,
`q_far = (1/125)/200 = 1/25000`.

1. Partition the indices by location:
   `N = {j : |s_j| ≤ 28/5}`, `W_{k,±} = {j : ±s_j ∈ I_k}` for `k < 9`,
   `F_{j,±} = {j : ±s_j ∈ [60 + 6j, 60 + 6(j+1))}` for `j ≥ 0`, and the rest `R`.
2. `∑_{j ∈ N} Dam = 0` by O5; `∑_{j ∈ R} Dam = 0` by O9 (the rest of
   `[28/5, 60]` carries no damage).
3. In each `W_{k,±}` the offsets lie in an interval of length `< 1`, so every pair
   of them contributes `≥ 39/50` to `∑_{j≠k} Kpair` (O3); in each `F_{j,±}` they
   lie in an interval of length `6`, contributing `≥ 1/125` (O4). All remaining
   pairs contribute `≥ 0` (O1). Hence, with `m_{k,±} = |W_{k,±}|`,
   `m'_{j,±} = |F_{j,±}|`,

       (1/200) ∑_{j≠k} Kpair ≥ ∑ q · m(m−1) + ∑ q_far · m'(m'−1).

4. Damage is capped by O9 on the windows and by O6 + O7 on the far intervals
   (evaluate `Wt` at the left endpoint, `Wt` antitone).
5. Subtract, apply Lemma 5.1 to each group separately, and sum. Every group is
   independent because step 3 discarded all cross-group pairs, so

       4 ∑_j Dam y s_j − (1/200) ∑_{j≠k} Kpair ≤ 2 (∑_{k<9} P_k + ∑_{j≥0} P'_j),

   with `P_k = P(c_k y², q)` and `P'_j = P(y² Wt((60+6j)²−2), q_far)`.
6. §7 bounds the right-hand side by `2 Shq y`. ∎

Note that **`n` never appears**: the multiplicities `m` are unconstrained
nonnegative integers, so the bound holds for every `n` at once.

---

## 6. Uniformity in `y`, for free

Set `v = y² ∈ [0, 1/4]`. Each `P(c v, q)` is a maximum of finitely many affine
functions of `v`, each with value `−q m(m−1) ≤ 0` at `v = 0`; so it is convex in
`v` and vanishes at `v = 0`. Convexity plus `P(0) = 0` gives `P(λ v) ≤ λ P(v)`
for `λ ∈ [0,1]`. The budget `(51944/100000) v` is linear in `v`. Therefore

> **the check of §7 at `y = 1/2` gives the inequality for every `y ∈ [0, 1/2]`.**

(The price `q` is `y`-free while the damage scales like `y²`: small `y` is the
easy case. Measured margin runs from `1.72×` at `y = 1/2` to `2.51×` as `y → 0`.)

---

## 7. The final arithmetic, at `y = 1/2` (all exact rationals)

Budget: `2 Shq y ≥ (51944/100000) · (1/4) = 0.12986`.

| contribution | value at `y = 1/2` |
|---|---|
| window `k=0`, best integer `m = 3` | `3.1995018e−2` |
| windows `k=1..8`, each best at `m = 1` | `8.6965620e−3` (sum) |
| the nine windows, both sides | `8.1383160e−2` |
| far intervals `[60+6j, 60+6(j+1))`, `j < 57`, both sides (best `m ≤ 3`) | `3.6305145e−3` |
| far tail beyond `s = 400`, both sides, closed form | `5.414634e−4` |
| **total deficit** | **`8.5555138e−2`** |
| **budget** | **`1.2986000e−1`** |
| **surplus** | **`4.4304862e−2` > 0**, margin `1.5179×` |

Recomputed at the `21/20` cap inflation of §4. The optimal multiplicities are
unchanged (`m = 3` on `k = 0`, `m = 1` on `k = 1..8`), and the far-field rows
are untouched because they rest on `Wt` (O6/O7), a proved majorant that already
carries its own slack. At the old zero-slack caps the surplus read
`5.0408822e−2` and the margin `1.6345×`; buying enclosure margin costs
`6.104e−3` of surplus.

The closed-form tail uses `Wt w ≤ (637/1000)/w` for `w ≥ 1368` (O7) and
`∑_{j≥0} ((400+6j)² − 2)^{-1} ≤ (400²−2)^{-1} + (1/6)(400−2)^{-1}`; beyond
`s = 400` single points are optimal (`4 c ≤ q_far`), so no integer trade is needed
there.

Consequence, in the original variables:

    Eng(F+P) − (199/200) Eng F − n/200 − 4  ≥  4.4304862e−2 / A²  =  5.249e−2 > 0

at `y = 1/2`, for every `n`, every `x`, every `t`.

---

## 8. What the convex relaxation does, and why it is not this

For the record, because it is the obvious thing to try and it fails for a
structural reason (measured in `hunts/frontier_math/exact_gap_attack.py`):

Relax the `n` unit atoms to a nonnegative measure `μ` of mass `n`. The functional
is convex (the quadratic form has spectral density `c2 ≥ 0` and coefficient
`+1/200`), so the relaxed minimum lower-bounds the truth and is computable. It is

    inf gap = [C*(n) + 2 Shq y] / A² − n/200,   C*(n) = inf { (1/200)⟨ν,Kν⟩ + 4⟨ν,W⟩ : ν ≥ 0, |ν| ≤ n }

because mass may be sent to infinity as dust — spread thin it pays no energy and,
`W → 0`, collects no damage. `C*(n)` saturates at `C* = −0.038776` once `n ≥ 5.99`,
so the relaxed infimum is **exactly linear from `n = 6` on**:

    inf gap = 0.114022 − n/200,   negative for every n ≥ 23,   unbounded below.

The minimiser is not a configuration: its peak mass is `2.07819` (fractional) at
the first damage window, and the excess is dust. Since the convex hull of the
`n`-unit-atom measures contains the diffuse ones, **no convex relaxation of the
atom constraint can close this problem**; the `− n A²` in (★) is the self-energy
of `n` unit atoms, and only integrality pays it back. Lemma 5.1 is where the
integrality is spent.

---

## 9. Honest scope

* O1, O2, O5, O6, O7, O8 are kernel-checked today; O3, O4, O9, O10, O11 are not.
* O9 is a numeric statement over `[28/5, 60] × [0, 1/2]` and is the only piece
  requiring interval arithmetic in two variables. It is the analogue of the
  package's existing `BandCert` leaf tables.
* The endpoints and caps in the table were measured in double precision by
  `exact_gap_attack.damage_windows` (scan step `1e−4`, edges refined by bisection
  to `1e−13`, peaks by bounded search, caps rounded up at the 8th decimal). They
  are stable from scan step `2e−3` down to `5e−5` and to the 9th digit in the
  scan reach from `60` to `800`. They are not enclosures.
* The measured infimum of the gap over all configurations and all `n` at
  `y = 1/2` is `≈ 0.0748`; the bound proved here is `0.0597`, so the argument
  keeps about 80% of the truth. There is no claim that `0.0597` is sharp.
* Nothing here is evidence for or against RH; the retention inequality is one
  step inside the `zeta23ext` extension package.
