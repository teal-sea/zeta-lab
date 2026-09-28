# Erdős 359: what Mathlib already has, by name

**Surveyed** 2026-08-31 against the Mathlib checked out at
`lean/.lake/packages/mathlib`, pin `v4.33.0-rc2` (`lean/lake-manifest.json`,
toolchain `leanprover/lean4:v4.33.0-rc2`).

**Method.** Declaration-name grep over the Mathlib source tree in that package,
plus reading the signature at each hit. **Nothing here was elaborated**: no
`lake build`, no `exact?`, no `#check`. Every name below was read off a
`theorem`/`lemma` line in the source at the file and line given, so the name and
the shape are quotable, but implicit-argument order and typeclass resolution are
not verified. Names marked *(to_additive)* were confirmed by finding a call site
elsewhere in Mathlib rather than a declaration line.

## The statement being surveyed

The target is the DeepMind `formal-conjectures` phrasing of Erdős 359
(`FormalConjectures/ErdosProblems/359.lean`, upstream `main` as of the survey
date). Reproduced here because the rest of this document is only readable
against it:

```lean
namespace Erdos359

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest
natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop

theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0)

theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15}

theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log)

end Erdos359
```

`(k : ℝ) ^ (1 + c)` with `c : ℝ` is `Real.rpow`, not `Monoid.npow`.

---

## 1. `Filter.Tendsto` / `atTop` division for cast-nat sequences

Everything needed to move between `ℕ`-indexed and `ℝ`-valued statements is
present.

| name | shape | file:line |
|---|---|---|
| `tendsto_natCast_atTop_atTop` | `Tendsto ((↑) : ℕ → R) atTop atTop` | `Mathlib/Order/Filter/AtTopBot/Archimedean.lean:44` |
| `tendsto_natCast_atTop_iff` | `Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop` | `.../Archimedean.lean:35` |
| `Nat.comap_cast_atTop` | `comap ((↑) : ℕ → R) atTop = atTop` | `.../Archimedean.lean:31` |
| `Filter.Eventually.natCast_atTop` | transfers `∀ᶠ` along the cast | `.../Archimedean.lean:52` |
| `Filter.Tendsto.atTop_div_const` | `0 < r → Tendsto f l atTop → Tendsto (f · / r) l atTop` | `Mathlib/Order/Filter/AtTopBot/Field.lean:85` |
| `Filter.tendsto_div_const_atTop_of_pos` | `0 < r ↔`-free version | `.../Field.lean` |
| `Filter.tendsto_div_const_atTop_iff` | iff form | `.../Field.lean` |
| `Filter.Tendsto.div_atTop` | `Tendsto f l (𝓝 a) → Tendsto g l atTop → Tendsto (f/g) l (𝓝 0)` | `Mathlib/Topology/Algebra/Order/Field.lean:212` |
| `Filter.Tendsto.const_div_atTop` | `Tendsto g l atTop → Tendsto (r / g ·) l (𝓝 0)` | `.../Field.lean:222` |
| `tendsto_bdd_div_atTop_nhds_zero` | numerator sandwiched between two constants, denominator `→ atTop` ⟹ `→ 𝓝 0` | `.../Field.lean:264` |
| `Filter.Tendsto.atTop_mul_atTop₀` | `atTop * atTop = atTop` | `Mathlib/Order/Filter/AtTopBot/Ring.lean:25` |
| `Filter.Tendsto.atTop_of_le_const_mul`, `.atTop_of_mul_le_const` | reverse-direction comparisons | `Mathlib/Order/Filter/AtTopBot/Monoid.lean` |
| `tendsto_atTop_mono` | `(∀ n, f n ≤ g n) → Tendsto f l atTop → Tendsto g l atTop` | `Mathlib/Order/Filter/AtTopBot/Tendsto.lean:72` |
| `tendsto_atTop_mono'` | eventual version | `.../Tendsto.lean:67` |
| `tendsto_atTop_atTop_of_monotone` | monotone + unbounded ⟹ `atTop` | `.../Tendsto.lean:120` |
| `squeeze_zero`, `squeeze_zero'` | `0 ≤ f ≤ g`, `g → 0` ⟹ `f → 0` | `Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean:38`, `:32` |
| `Real.tendsto_rpow_atTop` | `0 < y → Tendsto (· ^ y) atTop atTop` | `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:36` |
| `Real.rpow_natCast` | `x ^ (n : ℝ) = x ^ n` | `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:62` |

Part (i) is `Tendsto (fun k ↦ (A k : ℝ)/k) atTop atTop`; part (ii) is
`Tendsto (fun k ↦ A k / (k:ℝ)^(1+c)) atTop (𝓝 0)`. The bridge between them and
`o`/`~` statements is in §2.

## 2. `Asymptotics.IsEquivalent` and its arithmetic

All of `Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean`. The arithmetic
the conjectured asymptotic needs is complete.

| name | shape | line |
|---|---|---|
| `Asymptotics.IsEquivalent.mul` | `t ~ u → v ~ w → t*v ~ u*w` (`NormedField`) | 265 |
| `Asymptotics.IsEquivalent.div` | `t ~ u → v ~ w → t/v ~ u/w` | 293 |
| `Asymptotics.IsEquivalent.inv` | `u ~ v → u⁻¹ ~ v⁻¹` | 285 |
| `Asymptotics.IsEquivalent.pow` / `.zpow` | | 297 / 302 |
| `Asymptotics.IsEquivalent.smul` | | 225 |
| `Asymptotics.IsEquivalent.finsetProd` | | 281 |
| `Asymptotics.IsEquivalent.congr_left` / `.congr_right` | rewrite either side along `=ᶠ` | 102 / 106 |
| `Asymptotics.IsEquivalent.trans_eventuallyEq`, `Filter.EventuallyEq.trans_isEquivalent` | | 406 / 391 |
| `Asymptotics.IsEquivalent.tendsto_atTop` | `u ~ v → Tendsto u l atTop → Tendsto v l atTop` | 314 |
| `Asymptotics.IsEquivalent.tendsto_atTop_iff` | | 319 |
| `Asymptotics.IsEquivalent.tendsto_nhds` / `.tendsto_nhds_iff` | | 134 / 143 |
| `Asymptotics.isEquivalent_iff_tendsto_one` | needs `∀ᶠ x, v x ≠ 0` | 208 |
| `Asymptotics.isEquivalent_of_tendsto_one` | `Tendsto (u/v) l (𝓝 1) → u ~ v` | 196 |
| `Asymptotics.isEquivalent_iff_exists_eq_mul`, `.exists_eq_mul`, `.exists_pos_eq_mul` | | 181 / 192 / 337 |
| `Asymptotics.IsEquivalent.comp_tendsto` | **the ℕ-cast bridge**: real-variable `~` pulled back along `Tendsto (↑) atTop atTop` | 468 |
| `Asymptotics.isEquivalent_map` | | 473 |
| `Asymptotics.IsEquivalent.trans_isLittleO`, `.trans_isBigO`, `.trans_isTheta` (+ duals) | | 433 / 415 / 451 |
| `Asymptotics.IsEquivalent.eventually_pos` / `.eventually_nonneg` | | 347 / 342 |
| `Asymptotics.IsEquivalent.isLittleO` / `.isBigO` / `.isTheta` | | 73 / 75 / 82 |

Little-o ↔ quotient, which is how parts (i) and (ii) connect to the asymptotic:

| name | shape | file:line |
|---|---|---|
| `Asymptotics.isLittleO_iff_tendsto` | `(∀ x, g x = 0 → f x = 0) → (f =o[l] g ↔ Tendsto (f/g) l (𝓝 0))` | `Mathlib/Analysis/Asymptotics/Lemmas.lean:392` |
| `Asymptotics.isLittleO_iff_tendsto'` | eventual side condition | `.../Lemmas.lean:386` |
| `Asymptotics.IsLittleO.tendsto_div_nhds_zero` | | `.../Lemmas.lean:372` |
| `Asymptotics.IsLittleO.of_tendsto_div_atTop` | `Tendsto (g/f) l atTop → f =o[l] g` | `.../Lemmas.lean:444` |
| `Asymptotics.IsLittleO.comp_tendsto` | `f =o[l] g → Tendsto k l' l → (f∘k) =o[l'] (g∘k)` | `Mathlib/Analysis/Asymptotics/Defs.lean:444` |

## 3. `Real.log`, and `log ∘ log`

| name | shape | file:line |
|---|---|---|
| `Real.tendsto_log_atTop` | `Tendsto log atTop atTop` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:351` |
| `Real.isLittleO_log_id_atTop` | `log =o[atTop] id` | `.../Log/Basic.lean:450` |
| `Real.isLittleO_pow_log_id_atTop` | `(log ·^n) =o[atTop] id` | `.../Log/Basic.lean:445` |
| `Real.isLittleO_const_log_atTop` | `(fun _ => c) =o[atTop] log` | `.../Log/Basic.lean:453` |
| `Real.tendsto_pow_log_div_mul_add_atTop` | | `.../Log/Basic.lean` |
| `Real.isLittleO_log_rpow_atTop` | `0 < r → log =o[atTop] (· ^ r)` | `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:364` |
| `Real.isLittleO_log_rpow_rpow_atTop` | | `.../Pow/Asymptotics.lean` |
| `Real.log_le_self`, `Real.log_lt_sub_one_of_pos`, `Real.log_le_sub_one_of_pos` | elementary bounds | `.../Log/Basic.lean` |
| `Real.log_pos`, `Real.log_pos_iff`, `Real.strictMonoOn_log`, `Real.log_lt_log`, `Real.log_le_log` | order facts | `.../Log/Basic.lean` |
| `Real.log_natCast_nonneg` | `0 ≤ log n` for `n : ℕ` | `.../Log/Basic.lean:225` |
| `Real.log_div_self_antitoneOn`, `Real.log_div_self_rpow_antitoneOn`, `Real.mul_log_strictMonoOn` | monotonicity of `log x / x`, `x log x` | `.../Log/Monotone.lean` |
| `Filter.Tendsto.log` | `Tendsto f l (𝓝 x) → x ≠ 0 → Tendsto (log ∘ f) l (𝓝 (log x))` | `.../Log/Basic.lean` |

**Iterated log.** `Mathlib/Analysis/SpecialFunctions/Log/InvLog.lean` is the
only file in Mathlib about `x ↦ log (log x)`. It has:

- `Real.one_isLittleO_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] fun x ↦ log (log x)` (line 130)
- `Real.deriv_log_log : deriv (fun x ↦ log (log x)) = fun x ↦ x⁻¹ / log x` (line 113)
- `Real.differentiableOn_log_log : DifferentiableOn ℝ (fun x ↦ log (log x)) (Set.Ioi 1)` (line 127)
- `Real.inv_log_isLittleO_one`, plus the non-continuity facts at `0, 1, -1`.

The idiom for `log (log x) → atTop` is the one used inside that file's own
proof: `tendsto_log_atTop.comp tendsto_log_atTop`. It is **not** exposed as a
named lemma (see §7).

## 4. `liminf` / `limsup`

The general API is in `Mathlib/Order/LiminfLimsup.lean`; the order-topology
side in `Mathlib/Topology/Order/LiminfLimsup.lean`; arithmetic in
`Mathlib/Topology/Algebra/Order/LiminfLimsup.lean`.

Manipulation lemmas that exist: `Filter.liminf_le_limsup`,
`Filter.limsup_le_limsup`, `Filter.liminf_le_liminf`,
`Filter.limsup_le_limsup_of_le`, `Filter.liminf_le_liminf_of_le`,
`Filter.limsup_congr` / `liminf_congr`, `Filter.limsup_const` /
`liminf_const`, `Filter.limsup_nat_add` / `liminf_nat_add`,
`Filter.le_limsup_of_frequently_le`, `Filter.liminf_le_of_frequently_le`,
`Filter.frequently_lt_of_lt_limsup`, `Filter.frequently_lt_of_liminf_lt`,
`Filter.eventually_lt_of_lt_liminf`, `Filter.eventually_lt_of_limsup_lt`,
`Filter.le_limsup_iff` / `le_liminf_iff` / `limsup_le_iff` / `liminf_le_iff`
(and primed variants), `Filter.limsup_eq_iInf_iSup_of_nat`,
`Filter.liminf_eq_iSup_iInf_of_nat`, `Filter.Tendsto.limsup_eq` /
`.liminf_eq`, `tendsto_of_liminf_eq_limsup`,
`tendsto_of_le_liminf_of_limsup_le`, `Filter.eventually_le_limsup`,
`Filter.eventually_liminf_le`, `Filter.exists_seq_tendsto_limsup` /
`_liminf`, `Monotone.map_limsup_of_continuousAt` /
`Antitone.map_liminf_of_continuousAt`.

Arithmetic over `ℝ`: `Filter.le_limsup_add`, `limsup_add_le`,
`le_liminf_add`, `liminf_add_le`, `le_limsup_mul`, `limsup_mul_le`,
`le_liminf_mul`, `liminf_mul_le`, `limsup_const_add`, `limsup_add_const`,
`liminf_const_add`, `liminf_add_const`, `limsup_const_sub`,
`limsup_sub_const`, `liminf_const_sub`, `liminf_sub_const`.

**Carrier warning.** For a real-valued sequence, `Filter.limsup` on `ℝ` is
junk-valued when the sequence is unbounded, and every ordered-field lemma above
carries `IsBoundedUnder` / `IsCoboundedUnder` side conditions. Since Erdős 359
is exactly about an unbounded quotient, the usable carriers are `EReal` and
`ℝ≥0∞`:

- `EReal`: `EReal.limsup_const_mul_of_nonneg_of_ne_top`,
  `EReal.liminf_const_mul_of_nonneg_of_ne_top`,
  `EReal.limsup_const_mul_of_nonpos_of_ne_bot`, `EReal.inv_limsup`,
  `EReal.inv_liminf`, `EReal.limsup_neg`, `EReal.liminf_neg`,
  `EReal.limsup_add_le`, `EReal.liminf_add_le`, `EReal.limsup_mul_le`,
  `EReal.limsup_toReal_eq`, `EReal.liminf_toReal_eq`
  (`Mathlib/Topology/Instances/EReal/Lemmas.lean`).
- `ℝ≥0∞`: `ENNReal.limsup_const_mul_of_ne_top`,
  `ENNReal.limsup_mul_const_of_ne_top`,
  `ENNReal.liminf_const_mul_of_ne_zero_of_ne_top`
  (`Mathlib/Order/Filter/ENNReal.lean:164`+). These are filter-generic.

`ENNReal.limsup_const_mul`, `ENNReal.limsup_mul_const`,
`ENNReal.limsup_mul_le`, `ENNReal.eventually_le_limsup` and
`ENNReal.limsup_eq_zero_iff` all require `[CountableInterFilter f]`, which
`atTop` on `ℕ` does **not** satisfy. Do not reach for them here.

## 5. `StrictMono`: recursion and induction

| name | shape | file:line |
|---|---|---|
| `strictMono_nat_of_lt_succ` | `(∀ n, f n < f (n+1)) → StrictMono f` | `Mathlib/Order/Monotone/Basic.lean:569` |
| `StrictMono.add_le_nat` | `f : ℕ → ℕ`, `StrictMono f → m + f n ≤ f (m + n)` | `Mathlib/Order/Monotone/Basic.lean:267` |
| `StrictMono.le_apply` | `[WellFoundedLT β]`, `f : β → β`, `StrictMono f → x ≤ f x` | `Mathlib/Order/WellFounded.lean:248` |
| `StrictMono.id_le` | same, unbundled | `.../WellFounded.lean` |
| `StrictMono.tendsto_atTop` | `φ : ℕ → ℕ`, `StrictMono φ → Tendsto φ atTop atTop` | `Mathlib/Order/Filter/AtTopBot/Tendsto.lean:84` |
| `Nat.le_induction` | induction from a base point (`induction n, hn using Nat.le_induction`) | core/`Mathlib` |
| `Nat.decreasing_induction_of_not_bddAbove`, `Nat.strong_decreasing_induction`, `Nat.cauchy_induction` | | `Mathlib/Order/Interval/Finset/Nat.lean:249`+ |

`StrictMono.add_le_nat` with `m := k`, `n := 0` and `A 0 = 1` gives
`k + 1 ≤ A k` immediately: the trivial half of part (i)'s lower bound.

For the recursion itself, `A (j+1)` is *the least* element of a set, the
relevant machinery is the `IsLeast`/`Nat.find`/`Nat.sInf` layer:

| name | shape | file:line |
|---|---|---|
| `Nat.isLeast_find` | `(hp : ∃ n, p n) → IsLeast {n | p n} (Nat.find hp)` | `Mathlib/Order/Nat.lean:40` |
| `Set.Nonempty.isLeast_natFind` | same, set-valued | `Mathlib/Order/Nat.lean:47` |
| `Nat.sInf_mem` | `s.Nonempty → sInf s ∈ s` | `Mathlib/Order/Lattice/Nat.lean:80` |
| `Nat.notMem_of_lt_sInf` | | `.../Lattice/Nat.lean:85` |
| `Nat.sInf_le` | | `.../Lattice/Nat.lean:91` |
| `IsLeast.unique` | `IsLeast s a → IsLeast s b → a = b` | `Mathlib/Order/Bounds/Basic.lean:830` |
| `IsLeast.isGLB`, `IsLeast.mono`, `IsLeast.nonempty` | | `Mathlib/Order/Bounds/Basic.lean` |

`IsLeast.unique` is what makes the sequence *unique* given `IsGoodFor`, hence
what makes the low-values variant provable by eight `IsLeast.unique` steps
rather than by `decide`.

## 6. `Finset.Icc` / `Finset.Iic` sums

The `IsGoodFor` predicate ranges over `Finset.Icc a b ⊆ Finset.Iic j` and
`∑ i ∈ Finset.Icc a b, A i`.

Membership / subset side:

| name | file |
|---|---|
| `Finset.Icc_subset_Iic_self` | `Mathlib/Order/Interval/Finset/Basic.lean:439` |
| `Finset.Icc_subset_Icc`, `.Icc_subset_Icc_left`, `.Icc_subset_Icc_right`, `.Icc_subset_Icc_iff` | `.../Finset/Basic.lean` |
| `Finset.mem_Icc`, `Finset.mem_Iic`, `Finset.nonempty_Icc` | `.../Finset/Defs.lean`, `.../Finset/Basic.lean` |
| `Finset.Icc_eq_empty_iff` (86), `Finset.Icc_eq_empty` (103, alias), `Finset.Icc_eq_empty_of_lt` (114) | `Mathlib/Order/Interval/Finset/Basic.lean` |
| `Nat.card_Icc : #(Icc a b) = b + 1 - a` | `Mathlib/Order/Interval/Finset/Nat.lean:83` |
| `Nat.card_Iic` (93), `Nat.Icc_eq_range'` (48), `Nat.range_succ_eq_Icc_zero` (76), `Nat.range_succ_eq_Iic` (79) | `.../Finset/Nat.lean` |

Sum side (all `to_additive` images of the `prod_*` declarations in
`Mathlib/Algebra/BigOperators/Intervals.lean`):

| name | shape | source `prod_` line |
|---|---|---|
| `Finset.sum_Icc_succ_top` *(to_additive)* | `a ≤ b + 1 → ∑ i ∈ Icc a (b+1), f i = (∑ i ∈ Icc a b, f i) + f (b+1)` | 74 |
| `Finset.sum_Ico_consecutive` *(to_additive)* | `m ≤ n → n ≤ k → (∑ Ico m n) + (∑ Ico n k) = ∑ Ico m k` | 56 |
| `Finset.sum_range_add_sum_Ico` *(to_additive)* | `m ≤ n → (∑ range m) + (∑ Ico m n) = ∑ range n` | 79 |
| `Finset.sum_Ico_eq_sub` *(to_additive)* | `AddCommGroup` only: `∑ Ico m n = ∑ range n - ∑ range m` | 94 |
| `Finset.sum_Ico_eq_sum_range` *(to_additive)* | reindex to `range (n - m)` | 128 |
| `Finset.sum_eq_sum_Ico_succ_bot` *(to_additive)* | peel the bottom term | `Mathlib/Algebra/Order/BigOperators/Group/LocallyFinite.lean:68` |
| `Finset.sum_Ico_by_parts`, `Finset.sum_Ioc_by_parts` | Abel summation | `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Finset.sum_Ico_reflect`, `Finset.sum_Ico_Ico_comm` | | same file |
| `Finset.sum_le_sum_of_subset`, `Finset.sum_le_sum`, `Finset.card_image_le`, `Finset.card_le_card` | counting the representable values | `Mathlib/Algebra/Order/BigOperators/...`, `Mathlib/Data/Finset/Card.lean` |
| `Finset.exists_mem_notMem_of_card_lt_card` | `#s < #t → ∃ e ∈ t, e ∉ s`, the pigeonhole that produces a non-representable `m` | `Mathlib/Data/Finset/Card.lean:614` |

`Finset.sum_Ico_eq_sub` is the natural partial-sum reformulation
(`∑_{i∈Icc a b} A i = S(b+1) - S(a)`) but it needs an `AddCommGroup`, so on
`ℕ` you must either cast to `ℤ`/`ℝ` first or use `Finset.sum_range_add_sum_Ico`
in additive form. Truncated `ℕ` subtraction is the trap here.

---

## 7. What Mathlib appears to lack

Ordered by how much work they are, not by importance. None of these is deep;
they are all one-to-ten-line derivations. They are listed because each one is
currently a hand-rolled `have` at every call site.

1. **`log ∘ log → atTop` as a named lemma.** There is no
   `Real.tendsto_log_log_atTop`. The composition `tendsto_log_atTop.comp
   tendsto_log_atTop` appears literally inside the proof of
   `Real.one_isLittleO_log_log` (`.../Log/InvLog.lean:132`) and nowhere else.
   Every one of the four Erdős-359 statements needs it, because
   `log (log k)` is a denominator and must be eventually positive.

2. **`log (log x) = o(log x)`.** No named lemma. Derivable as
   `(Real.isLittleO_log_rpow_atTop one_pos).comp_tendsto Real.tendsto_log_atTop`
   plus `Real.rpow_one`. Needed to show `k log k / log log k` grows faster than
   `k` (part i) and slower than `k^{1+c}` (part ii), i.e. it is exactly the
   step that makes the conjectured asymptotic imply both proved parts.

3. **Eventual positivity of `log (log x)` on `atTop`.** No
   `Real.log_log_pos` / `Real.eventually_log_log_pos`. Needed before any
   division by `log log k` is legal. Note `log (log k)` is *negative* for
   `k ≤ 15`, so this cannot be a global bound; the low-values variant and the
   asymptotic variant live on different ranges.

4. **The converse of `IsLittleO.of_tendsto_div_atTop`.** Mathlib has
   `f =o[l] g` from `g/f → atTop`, but not `g/f → atTop` from `f =o[l] g`
   under `∀ᶠ x, f x ≠ 0`. Part (i) is stated as a quotient tending to `atTop`,
   so this direction is precisely what is needed to derive it from the
   asymptotic. (`Asymptotics.IsLittleO` has no `tendsto_div_atTop` at all.)

5. **`limsup`/`liminf` const-mul and div over `ℝ`.** `limsup_const_mul` and
   `limsup_div` do not exist for real-valued sequences; only `ENNReal` and
   `EReal` versions do, and the `ENNReal` ones that are unconditional in the
   filter are only the `_of_ne_top` family. If the intended route to Erdős 359
   is through `liminf a_k log log k / (k log k)` and the matching `limsup`, the
   carrier has to be `EReal` from the start and some of the quotient
   manipulation has to be built.

6. **Any combinatorial-number-theory scaffolding for "sums of consecutive
   terms".** There is nothing: a grep for `Sidon`, `sumFree`, `IsSumFree`,
   `mianChowla`, `greedy` over all of `Mathlib/` returns only unrelated hits in
   `Linarith` and `Besicovitch`. The counting bound that drives the whole
   problem, "the set of sums of consecutive terms of `A 0, …, A j` has at most
   `(j+1)(j+2)/2` elements, so some `m ≤ A j + (j+1)(j+2)/2 + 1` is
   non-representable, so `A (j+1) - A j = O(j²)`", has to be built from
   `Finset.card_image_le` and `Finset.exists_mem_notMem_of_card_lt_card` by
   hand. This is the real cost of the problem, and it is not an analysis gap.

7. **Well-definedness of `IsGoodFor`.** Nothing in the statement asserts a
   sequence satisfying it exists; the `IsLeast` clause is a constraint, not a
   definition. An existence lemma (`∃ A, IsGoodFor A 1`, built by `Nat.rec`
   with `Nat.find`) is a prerequisite for the whole file to be non-vacuous, and
   the decidability instance for
   `{m | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ …}` needs the
   `∀ a b` quantifier bounded first (`b ≤ j` from
   `Finset.Icc_subset_Iic_self`-style reasoning, and `Finset.Icc a b` empty for
   `b < a`). Mathlib gives the pieces; the instance itself is not free.

## Sources

- Mathlib at `lean/.lake/packages/mathlib`, pin `v4.33.0-rc2`.
- Statement text: `google-deepmind/formal-conjectures`,
  `FormalConjectures/ErdosProblems/359.lean`, fetched 2026-08-31 from
  `raw.githubusercontent.com`. `erdosproblems.com/359` returned HTTP 403 and
  was not read.
