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

| k | `I_k` (rational endpoints) | length | `c_k` |
|---|---|---|---|
| 0 | `[60653/10000, 35257/5000]` | 0.9861 | `439643/25000000 = 1.7585720e−2` |
| 1 | `[61171/5000, 131999/10000]` | 0.9657 | `390023/100000000 = 3.9002300e−3` |
| 2 | `[11544/625, 48583/2500]` | 0.9628 | `169313/100000000 = 1.6931300e−3` |
| 3 | `[247289/10000, 256909/10000]` | 0.9620 | `18889/20000000 = 9.4445000e−4` |
| 4 | `[309971/10000, 159793/5000]` | 0.9615 | `6021/10000000 = 6.0210000e−4` |
| 5 | `[372701/10000, 76463/2000]` | 0.9614 | `10431/25000000 = 4.1724000e−4` |
| 6 | `[21773/500, 27817/625]` | 0.9612 | `6123/20000000 = 3.0615000e−4` |
| 7 | `[498237/10000, 507849/10000]` | 0.9612 | `1171/5000000 = 2.3420000e−4` |
| 8 | `[280513/5000, 570637/10000]` | 0.9611 | `9247/50000000 = 1.8494000e−4` |

Each `I_k` has length `< 1`; the `I_k` are pairwise disjoint (left endpoints
spaced by more than `6.16`); `I_0` starts at `6.0653 > 28/5`; `I_8` ends at
`57.0637 < 60`. Negative `s` is the mirror image (`Dam` is even in `s`: `Qre` is
even and `Qim` is odd in the second argument).

The caps are `sup` over `I_k × [0,1/2]` of `Dam y s / y²`, rounded up. Measured
worst case of `(Dam y s / y²) / c_k` over `y ∈ {0.45, …, 0.02}` is `0.995985`, so
the `y = 1/2` profile dominates; the windows also **nest** (`I_k(y) ⊆ I_k(1/2)`
for `y ≤ 1/2`), which is why one table serves every `y`.

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
| window `k=0`, best integer `m = 3` | `2.9357160e−2` |
| windows `k=1..8`, each best at `m = 1` | `8.2824400e−3` (sum) |
| the nine windows, both sides | `7.5279200e−2` |
| far intervals `[60+6j, 60+6(j+1))`, `j < 57`, both sides (best `m ≤ 3`) | `3.6305145e−3` |
| far tail beyond `s = 400`, both sides, closed form | `5.414634e−4` |
| **total deficit** | **`7.9451178e−2`** |
| **budget** | **`1.2986000e−1`** |
| **surplus** | **`5.0408822e−2` > 0**, margin `1.6345×` |

The closed-form tail uses `Wt w ≤ (637/1000)/w` for `w ≥ 1368` (O7) and
`∑_{j≥0} ((400+6j)² − 2)^{-1} ≤ (400²−2)^{-1} + (1/6)(400−2)^{-1}`; beyond
`s = 400` single points are optimal (`4 c ≤ q_far`), so no integer trade is needed
there.

Consequence, in the original variables:

    Eng(F+P) − (199/200) Eng F − n/200 − 4  ≥  5.0408822e−2 / A²  =  5.972e−2 > 0

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
