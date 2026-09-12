/-
# Counting perfect matchings: a `2m`-element set has `(2m-1)‼` pairings

The number of ways to partition a finite set of size `2m` into `m` blocks of
size two, equivalently the number of fixed-point-free involutions of that set,
is the double factorial `(2m-1)‼ = 1·3·5·⋯·(2m-1)`. This is the Wick /
Isserlis pairing count.

Mathlib at the pin used here (`lean/lake-manifest.json`, mathlib `51e6992e`,
toolchain `v4.33.0-rc2`) has `Nat.doubleFactorial` with a full arithmetic API,
and has `SimpleGraph.Subgraph.IsPerfectMatching` as a predicate whose only
cardinality consequence is `IsPerfectMatching.even_card`, a parity statement.
It has nothing named `Isserlis` or `Wick`. So the count itself is not there;
`Probe.lean` in this directory is the compiled evidence, and `LOG.md` records
what it printed.

A pairing is represented as a function `f : α → α` rather than as a set of
blocks or as a subgraph. That is the choice that makes the proof short: the
recursion "pick `x`, choose its partner `y`, recurse on the rest" becomes a
bijection between an explicit fibre and the pairings of a two-element-smaller
`Finset`, with no reindexing of `Fin n` anywhere.

Main results:

* `card_pairings` : `(pairings s).card = if Even s.card then (s.card - 1)‼ else 0`
* `card_pairings_two_mul` : `s.card = 2 * m → (pairings s).card = (2 * m - 1)‼`
* `card_pairings_eq_zero_of_odd` : a set of odd size has no pairing
* `two_pow_mul_factorial_mul_card_pairings` : `2^m · m! · (2m-1)‼ = (2m)!`
* `even_card_of_pairsUp` : a set carrying a pairing has even cardinality
* `card_pairings_univ` : the whole-type form, in terms of `Fintype.card`
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Ring.Parity

open Finset Nat

namespace ZetaLab.Matchings

variable {α : Type*}

/-! ### The predicate -/

/-- `PairsUp s f` says that `f` pairs up `s`: it is an involution of the whole
type which moves every point of `s` to a different point of `s`, and fixes
everything outside `s`. Restricted to `s` this is exactly a fixed-point-free
involution of `s`, that is, a perfect matching of `s`. -/
def PairsUp (s : Finset α) (f : α → α) : Prop :=
  (∀ x, f (f x) = x) ∧ (∀ x ∈ s, f x ≠ x ∧ f x ∈ s) ∧ (∀ x ∉ s, f x = x)

namespace PairsUp

variable {s : Finset α} {f : α → α}

theorem invol (h : PairsUp s f) (x : α) : f (f x) = x := h.1 x

theorem ne_self (h : PairsUp s f) {x : α} (hx : x ∈ s) : f x ≠ x := (h.2.1 x hx).1

theorem mapsTo (h : PairsUp s f) {x : α} (hx : x ∈ s) : f x ∈ s := (h.2.1 x hx).2

theorem eq_self (h : PairsUp s f) {x : α} (hx : x ∉ s) : f x = x := h.2.2 x hx

end PairsUp

/-! ### The two maps of the fibre bijection

`dropPair x y` deletes the pair `{x, y}` from a pairing and `addPair x y`
inserts it. They are mutually inverse on the two sets counted below. -/

section Pair

variable [DecidableEq α]

/-- Remove the pair `{x, y}` from a pairing: `x` and `y` become fixed points. -/
def dropPair (x y : α) (f : α → α) : α → α :=
  fun z => if z = x then x else if z = y then y else f z

/-- Insert the pair `{x, y}` into a pairing: `x` and `y` become partners. -/
def addPair (x y : α) (g : α → α) : α → α :=
  fun z => if z = x then y else if z = y then x else g z

@[simp] theorem dropPair_left (x y : α) (f : α → α) : dropPair x y f x = x := by
  simp [dropPair]

@[simp] theorem addPair_left (x y : α) (g : α → α) : addPair x y g x = y := by
  simp [addPair]

theorem dropPair_right {x y : α} (h : y ≠ x) (f : α → α) : dropPair x y f y = y := by
  simp [dropPair, h]

theorem addPair_right {x y : α} (h : y ≠ x) (g : α → α) : addPair x y g y = x := by
  simp [addPair, h]

theorem dropPair_of_ne {x y z : α} (hzx : z ≠ x) (hzy : z ≠ y) (f : α → α) :
    dropPair x y f z = f z := by
  simp [dropPair, hzx, hzy]

theorem addPair_of_ne {x y z : α} (hzx : z ≠ x) (hzy : z ≠ y) (g : α → α) :
    addPair x y g z = g z := by
  simp [addPair, hzx, hzy]

end Pair

/-! ### The set of pairings, and the count -/

section Count

variable [DecidableEq α] [Fintype α]

instance decidablePairsUp (s : Finset α) (f : α → α) : Decidable (PairsUp s f) :=
  inferInstanceAs
    (Decidable ((∀ x, f (f x) = x) ∧ (∀ x ∈ s, f x ≠ x ∧ f x ∈ s) ∧ (∀ x ∉ s, f x = x)))

/-- The finite set of pairings of `s`. -/
def pairings (s : Finset α) : Finset (α → α) := univ.filter (PairsUp s)

@[simp] theorem mem_pairings {s : Finset α} {f : α → α} :
    f ∈ pairings s ↔ PairsUp s f := by
  simp [pairings]

/-! #### Base cases -/

theorem pairings_empty : pairings (∅ : Finset α) = {id} := by
  ext f
  simp only [mem_pairings, mem_singleton]
  constructor
  · intro h
    funext z
    exact h.eq_self (notMem_empty z)
  · rintro rfl
    refine ⟨fun _ => rfl, ?_, fun _ _ => rfl⟩
    simp

theorem pairings_of_card_eq_one {s : Finset α} (hs : s.card = 1) :
    pairings s = ∅ := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs
  ext f
  simp only [mem_pairings, notMem_empty, iff_false]
  intro h
  exact h.ne_self (mem_singleton_self x) (mem_singleton.mp (h.mapsTo (mem_singleton_self x)))

/-! #### The fibre bijection

Fix `x ∈ s` and a candidate partner `y ∈ s.erase x`. The pairings of `s` that
send `x ↦ y` are in bijection with the pairings of `s` with both `x` and `y`
deleted. -/

theorem card_fiber_pairings (s : Finset α) {x y : α} (hx : x ∈ s) (hy : y ∈ s.erase x) :
    {f ∈ pairings s | f x = y}.card = (pairings ((s.erase x).erase y)).card := by
  obtain ⟨hyx, hys⟩ := Finset.mem_erase.mp hy
  have hmem : ∀ z : α, z ∈ (s.erase x).erase y ↔ (z ≠ y ∧ z ≠ x ∧ z ∈ s) := by
    intro z; simp [Finset.mem_erase]
  have hxt : x ∉ (s.erase x).erase y := by simp [hmem]
  have hyt : y ∉ (s.erase x).erase y := by simp [hmem]
  refine Finset.card_nbij' (dropPair x y) (addPair x y) ?_ ?_ ?_ ?_
  · -- `dropPair` lands in the pairings of the two-element-smaller set
    intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_pairings] at hf ⊢
    obtain ⟨hfp, hfx⟩ := hf
    have hfy : f y = x := by rw [← hfx]; exact hfp.invol x
    have havoid : ∀ z, z ≠ x → z ≠ y → f z ≠ x ∧ f z ≠ y := by
      intro z hzx hzy
      refine ⟨fun h => hzy ?_, fun h => hzx ?_⟩
      · have hz := hfp.invol z; rw [h, hfx] at hz; exact hz.symm
      · have hz := hfp.invol z; rw [h, hfy] at hz; exact hz.symm
    refine ⟨?_, ?_, ?_⟩
    · intro z
      by_cases hzx : z = x
      · rw [hzx]; simp
      by_cases hzy : z = y
      · rw [hzy, dropPair_right hyx, dropPair_right hyx]
      · obtain ⟨h1, h2⟩ := havoid z hzx hzy
        rw [dropPair_of_ne hzx hzy, dropPair_of_ne h1 h2]
        exact hfp.invol z
    · intro z hz
      obtain ⟨hzy, hzx, hzs⟩ := (hmem z).mp hz
      obtain ⟨h1, h2⟩ := havoid z hzx hzy
      rw [dropPair_of_ne hzx hzy]
      exact ⟨hfp.ne_self hzs, (hmem (f z)).mpr ⟨h2, h1, hfp.mapsTo hzs⟩⟩
    · intro z hz
      by_cases hzx : z = x
      · rw [hzx]; simp
      by_cases hzy : z = y
      · rw [hzy]; exact dropPair_right hyx f
      · rw [dropPair_of_ne hzx hzy]
        exact hfp.eq_self (fun hzs => hz ((hmem z).mpr ⟨hzy, hzx, hzs⟩))
  · -- `addPair` lands in the fibre over `y`
    intro g hg
    simp only [Finset.mem_coe, mem_pairings] at hg
    simp only [Finset.mem_coe, Finset.mem_filter, mem_pairings]
    have hgx : g x = x := hg.eq_self hxt
    have hgy : g y = y := hg.eq_self hyt
    have havoid : ∀ z, z ≠ x → z ≠ y → g z ≠ x ∧ g z ≠ y := by
      intro z hzx hzy
      refine ⟨fun h => hzx ?_, fun h => hzy ?_⟩
      · have hz := hg.invol z; rw [h, hgx] at hz; exact hz.symm
      · have hz := hg.invol z; rw [h, hgy] at hz; exact hz.symm
    refine ⟨⟨?_, ?_, ?_⟩, addPair_left x y g⟩
    · intro z
      by_cases hzx : z = x
      · rw [hzx, addPair_left, addPair_right hyx]
      by_cases hzy : z = y
      · rw [hzy, addPair_right hyx, addPair_left]
      · obtain ⟨h1, h2⟩ := havoid z hzx hzy
        rw [addPair_of_ne hzx hzy, addPair_of_ne h1 h2]
        exact hg.invol z
    · intro z hz
      by_cases hzx : z = x
      · rw [hzx, addPair_left]; exact ⟨hyx, hys⟩
      by_cases hzy : z = y
      · rw [hzy, addPair_right hyx]; exact ⟨Ne.symm hyx, hx⟩
      · have hzt : z ∈ (s.erase x).erase y := (hmem z).mpr ⟨hzy, hzx, hz⟩
        obtain ⟨h1, h2⟩ := havoid z hzx hzy
        rw [addPair_of_ne hzx hzy]
        exact ⟨hg.ne_self hzt, ((hmem (g z)).mp (hg.mapsTo hzt)).2.2⟩
    · intro z hz
      have hzx : z ≠ x := by rintro rfl; exact hz hx
      have hzy : z ≠ y := by rintro rfl; exact hz hys
      rw [addPair_of_ne hzx hzy]
      exact hg.eq_self (fun hzt => hz ((hmem z).mp hzt).2.2)
  · -- `addPair ∘ dropPair` is the identity on the fibre
    intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_pairings] at hf
    obtain ⟨hfp, hfx⟩ := hf
    have hfy : f y = x := by rw [← hfx]; exact hfp.invol x
    funext z
    by_cases hzx : z = x
    · rw [hzx, addPair_left, hfx]
    by_cases hzy : z = y
    · rw [hzy, addPair_right hyx, hfy]
    · rw [addPair_of_ne hzx hzy, dropPair_of_ne hzx hzy]
  · -- `dropPair ∘ addPair` is the identity on the smaller pairings
    intro g hg
    simp only [Finset.mem_coe, mem_pairings] at hg
    funext z
    by_cases hzx : z = x
    · rw [hzx, dropPair_left, hg.eq_self hxt]
    by_cases hzy : z = y
    · rw [hzy, dropPair_right hyx, hg.eq_self hyt]
    · rw [dropPair_of_ne hzx hzy, addPair_of_ne hzx hzy]

/-! #### The induction -/

private theorem card_pairings_aux :
    ∀ (n : ℕ) (s : Finset α), s.card = n →
      (pairings s).card = if Even n then (n - 1)‼ else 0 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro s hs
    rw [Finset.card_eq_zero.mp hs, pairings_empty, card_singleton]
    decide
  | one =>
    intro s hs
    rw [pairings_of_card_eq_one hs, card_empty]
    decide
  | more n ih _ =>
    intro s hs
    obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    have hcard_erase : (s.erase x).card = n + 1 := by
      have h := Finset.card_erase_of_mem hx
      omega
    have key : (pairings s).card
        = ∑ y ∈ s.erase x, ({f ∈ pairings s | f x = y}).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro f hf
      simp only [Finset.mem_coe, mem_pairings] at hf ⊢
      exact Finset.mem_erase.mpr ⟨hf.ne_self hx, hf.mapsTo hx⟩
    have fibres : ∀ y ∈ s.erase x,
        ({f ∈ pairings s | f x = y}).card = if Even n then (n - 1)‼ else 0 := by
      intro y hy
      rw [card_fiber_pairings s hx hy]
      refine ih _ ?_
      have h := Finset.card_erase_of_mem hy
      omega
    have heven : Even (n + 2) ↔ Even n := by
      rw [Nat.even_iff, Nat.even_iff]; omega
    calc (pairings s).card
        = ∑ y ∈ s.erase x, ({f ∈ pairings s | f x = y}).card := key
      _ = (s.erase x).card * (if Even n then (n - 1)‼ else 0) :=
          Finset.sum_const_nat fibres
      _ = (n + 1) * (if Even n then (n - 1)‼ else 0) := by rw [hcard_erase]
      _ = if Even (n + 2) then (n + 2 - 1)‼ else 0 := by
          by_cases hn : Even n
          · rw [if_pos hn, if_pos (heven.mpr hn), show n + 2 - 1 = n + 1 by omega,
              Nat.doubleFactorial_add_one]
          · rw [if_neg hn, if_neg (fun h => hn (heven.mp h)), Nat.mul_zero]

/-! #### The results -/

/-- **The number of pairings of a finite set.** The perfect matchings of a
`Finset` `s`, presented as the fixed-point-free involutions of `s` extended by
the identity outside `s`, number `(s.card - 1)‼` when `s.card` is even, and
there are none when `s.card` is odd. -/
theorem card_pairings (s : Finset α) :
    (pairings s).card = if Even s.card then (s.card - 1)‼ else 0 :=
  card_pairings_aux s.card s rfl

/-- The even case, stated the way it is usually quoted: a set of size `2m` has
`(2m-1)‼` perfect matchings. -/
theorem card_pairings_two_mul {s : Finset α} {m : ℕ} (hs : s.card = 2 * m) :
    (pairings s).card = (2 * m - 1)‼ := by
  rw [card_pairings, hs, if_pos ⟨m, by omega⟩]

/-- A set of odd size has no perfect matching. -/
theorem card_pairings_eq_zero_of_odd {s : Finset α} (hs : ¬ Even s.card) :
    (pairings s).card = 0 := by
  rw [card_pairings, if_neg hs]

theorem pairings_eq_empty_of_odd {s : Finset α} (hs : ¬ Even s.card) :
    pairings s = ∅ :=
  Finset.card_eq_zero.mp (card_pairings_eq_zero_of_odd hs)

/-- The closed form `(2m)! = 2^m · m! · (2m-1)‼`, which is the shape the
pairing count usually takes in the Wick / Isserlis literature. Stated as a
product rather than a quotient so that it is an identity in `ℕ`. -/
theorem two_pow_mul_factorial_mul_card_pairings {s : Finset α} {m : ℕ}
    (hs : s.card = 2 * m) :
    2 ^ m * m ! * (pairings s).card = (2 * m)! := by
  rw [card_pairings_two_mul hs]
  cases m with
  | zero => decide
  | succ k =>
    have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h2 : (2 * (k + 1))! = (2 * k + 1 + 1)‼ * (2 * k + 1)‼ := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
      exact Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have h3 : (2 * k + 1 + 1)‼ = 2 ^ (k + 1) * (k + 1)! := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
      exact Nat.doubleFactorial_two_mul (k + 1)
    rw [h1, h2, h3]

/-- A set carrying a pairing has even cardinality. This is the analogue, in
this vocabulary, of Mathlib's `SimpleGraph.Subgraph.IsPerfectMatching.even_card`,
which is the only cardinality fact Mathlib records about perfect matchings. It
falls out of the count rather than being proved separately. -/
theorem even_card_of_pairsUp {s : Finset α} {f : α → α} (h : PairsUp s f) :
    Even s.card := by
  by_contra hodd
  have hf : f ∈ pairings s := mem_pairings.mpr h
  rw [pairings_eq_empty_of_odd hodd] at hf
  exact absurd hf (notMem_empty f)

/-- The whole-type form: the pairings of a `Fintype` `α`. -/
theorem card_pairings_univ :
    (pairings (univ : Finset α)).card =
      if Even (Fintype.card α) then (Fintype.card α - 1)‼ else 0 := by
  rw [card_pairings, Finset.card_univ]

end Count

/-! ### Cross-check against the enumeration oracle

`oracle.py` in this directory enumerates the same count three independent ways
and prints `1, 0, 1, 0, 3, 0, 15, 0, 105, 0, 945` for `n = 0, …, 10`. The
first block below re-derives the small entries inside the kernel by `decide`,
which uses no `native_decide` and makes no appeal to the theorem: it evaluates
the definition. The second block reads the same numbers off the theorem. If
the two blocks ever disagree, the statement is about the wrong objects. -/

section Oracle

example : (pairings (univ : Finset (Fin 0))).card = 1 := by decide
example : (pairings (univ : Finset (Fin 1))).card = 0 := by decide
example : (pairings (univ : Finset (Fin 2))).card = 1 := by decide
example : (pairings (univ : Finset (Fin 3))).card = 0 := by decide
example : (pairings (univ : Finset (Fin 4))).card = 3 := by decide

/- The check that actually bites: a *proper* subset of a strictly larger
ambient type. If the "fixes everything outside `s`" clause were wrong, the
ambient `Fin 5` would contribute extra pairings here and this would not be 3.
This one costs about 17 s of kernel time, which is why it is the only Fin 5
case proved rather than evaluated. -/
set_option maxRecDepth 100000 in
example : (pairings ({0, 1, 2, 3} : Finset (Fin 5))).card = 3 := by decide

example : (pairings (univ : Finset (Fin 0))).card = (2 * 0 - 1)‼ :=
  card_pairings_two_mul (by simp)
example : (pairings (univ : Finset (Fin 2))).card = (2 * 1 - 1)‼ :=
  card_pairings_two_mul (by simp)
example : (pairings (univ : Finset (Fin 4))).card = (2 * 2 - 1)‼ :=
  card_pairings_two_mul (by simp)
example : (pairings (univ : Finset (Fin 6))).card = (2 * 3 - 1)‼ :=
  card_pairings_two_mul (by simp)
example : (pairings (univ : Finset (Fin 8))).card = (2 * 4 - 1)‼ :=
  card_pairings_two_mul (by simp)
example : (pairings (univ : Finset (Fin 10))).card = (2 * 5 - 1)‼ :=
  card_pairings_two_mul (by simp)

example : (2 * 0 - 1)‼ = 1 := by decide
example : (2 * 1 - 1)‼ = 1 := by decide
example : (2 * 2 - 1)‼ = 3 := by decide
example : (2 * 3 - 1)‼ = 15 := by decide
example : (2 * 4 - 1)‼ = 105 := by decide
example : (2 * 5 - 1)‼ = 945 := by decide

example : (pairings (univ : Finset (Fin 5))).card = 0 :=
  card_pairings_eq_zero_of_odd (by decide)
example : (pairings (univ : Finset (Fin 7))).card = 0 :=
  card_pairings_eq_zero_of_odd (by decide)
example : (pairings (univ : Finset (Fin 9))).card = 0 :=
  card_pairings_eq_zero_of_odd (by decide)

/- Compiled evaluation, not kernel reduction, so these are checks and not
proofs. They cover the cases where `decide` is too slow, and they include the
`n = 6` entry of the oracle table and three more proper subsets. Expected, in
order: 1, 0, 1, 0, 3, 0, 15, then 3, 0, 1. -/
#eval (pairings (univ : Finset (Fin 0))).card
#eval (pairings (univ : Finset (Fin 1))).card
#eval (pairings (univ : Finset (Fin 2))).card
#eval (pairings (univ : Finset (Fin 3))).card
#eval (pairings (univ : Finset (Fin 4))).card
#eval (pairings (univ : Finset (Fin 5))).card
#eval (pairings (univ : Finset (Fin 6))).card
#eval (pairings ({0, 1, 2, 3} : Finset (Fin 5))).card
#eval (pairings ({0, 1, 2} : Finset (Fin 5))).card
#eval (pairings ({0, 1} : Finset (Fin 5))).card

end Oracle

end ZetaLab.Matchings

#print axioms ZetaLab.Matchings.card_pairings
#print axioms ZetaLab.Matchings.card_pairings_two_mul
#print axioms ZetaLab.Matchings.card_pairings_eq_zero_of_odd
#print axioms ZetaLab.Matchings.pairings_eq_empty_of_odd
#print axioms ZetaLab.Matchings.two_pow_mul_factorial_mul_card_pairings
#print axioms ZetaLab.Matchings.even_card_of_pairsUp
#print axioms ZetaLab.Matchings.card_pairings_univ
