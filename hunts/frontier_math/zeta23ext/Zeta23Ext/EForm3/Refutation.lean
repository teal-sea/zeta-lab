import Zeta23Ext.EForm3.FarField

/-!
# The second-order far-field bound is false

`PROBLEM.md` asks for a bound `|Qim y s| ≤ C₂ * y / s²`.  No such constant exists.

The window `g u = cos (√2 u) · 1_{|u| ≤ 1/2}` **jumps** at `u = ±1/2`, so its Fourier–Laplace
transform decays exactly like `1/|s|`; two integrations by parts cannot produce `1/s²` because
the boundary term at `u = 1/2` does not vanish (`g (1/2⁻) = cos (1/√2) ≈ 0.76 ≠ 0`).

Quantitatively, the exact identity `far_identity` gives

  `Qim y s * ((y²+s²+2)² - 8 s²) = C_q sin (s/2) + C_p cos (s/2)`,

and along the sequence `s = 4πN` (where `sin (s/2) = 0`, `cos (s/2) = 1`) only `C_p` survives.
Since `C_p ≤ -2 sinh (y/2) · s · cos (1/√2) · (s² + y² - 2)`, this forces
`|Qim y s| ≥ (7/10) y / s`, which beats `C y / s²` as soon as `s > (10/7) C`.

The correct far-field statement, and the one the counting argument uses, is
`Qim_far_first_order` / `Qim_far_sq`.
-/

open scoped BigOperators Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Retention

/-- Along `s` with `sin (s/2) = 0` and `cos (s/2) = 1` (i.e. `s ∈ 4πℤ`), the interference term
is bounded **below** by `(7/10) y / s`: the decay is genuinely first order. -/
theorem Qim_lower_at_even_multiple {y s : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1/2) (hs : 10 ≤ s)
    (hq : Real.sin (s/2) = 0) (hp : Real.cos (s/2) = 1) :
    (7/10) * y / s ≤ |Qim y s| := by
  have hr : (Real.sqrt 2)^2 = 2 := sqrt2_sq
  have hrpos : (0:ℝ) < Real.sqrt 2 := sqrt2_pos
  have hrub : Real.sqrt 2 ≤ 1.4142136 := sqrt2_ub
  have hs0 : (0:ℝ) < s := by linarith
  have hs2 : (100:ℝ) ≤ s^2 := by nlinarith
  have hy2 : y^2 ≤ 1/4 := by nlinarith
  have hy20 : (0:ℝ) ≤ y^2 := sq_nonneg y
  set r := Real.sqrt 2 with hrdef
  set c0 := Real.cos (1 / r) with hc0def
  set s0 := Real.sin (1 / r) with hs0def
  set P := y * Real.cosh (y/2) with hPdef
  set S := Real.sinh (y/2) with hSdef
  have hhalf : r / 2 = 1 / r := sqrt2_half
  have hDp : y^2+(s+r)^2 ≠ 0 := by positivity
  have hDm : y^2+(s-r)^2 ≠ 0 := by
    have h : (0:ℝ) < (s - r)^2 := by nlinarith
    positivity
  have hQ : Qim y s = (P*(c0*Real.sin (s/2)+s0*Real.cos (s/2))
        - (s+r)*S*(c0*Real.cos (s/2)-s0*Real.sin (s/2)))/(y^2+(s+r)^2)
      + (P*(c0*Real.sin (s/2)-s0*Real.cos (s/2))
        - (s-r)*S*(c0*Real.cos (s/2)+s0*Real.sin (s/2)))/(y^2+(s-r)^2) := by
    rw [Qim_closed y s hDp hDm]
    have ep : (s + r)/2 = s/2 + 1/r := by rw [← hhalf]; ring
    have em : (s - r)/2 = s/2 - 1/r := by rw [← hhalf]; ring
    rw [ep, em, Real.sin_add, Real.cos_add, Real.sin_sub, Real.cos_sub]
    rw [← hc0def, ← hs0def, hPdef, hSdef]
    ring
  have hid : Qim y s * ((y^2+s^2+2)^2 - 8*s^2)
      = (2*P*c0*(y^2+s^2+2) + 2*S*(r*s0)*(y^2+2-s^2)) * Real.sin (s/2)
        + (-4*s*P*(r*s0) - 2*S*s*c0*(y^2+s^2-2)) * Real.cos (s/2) := by
    rw [hQ]
    exact far_identity y s r c0 s0 P S _ _ hr hDp hDm
  rw [hq, hp] at hid
  -- ingredients
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hS0 : y/2 ≤ S := by rw [hSdef]; exact Real.self_le_sinh_iff.2 (by linarith)
  have hc0 : (0.760243 : ℝ) ≤ c0 := by
    rw [hc0def, hrdef]; exact cos_inv_sqrt2_lb
  have hAeq : r * s0 = Aconst := by rw [hs0def, Aconst, hrdef]
  have hA0 : 0 ≤ r * s0 := by rw [hAeq]; exact le_of_lt Aconst_pos
  set D : ℝ := (y^2+s^2+2)^2 - 8*s^2 with hDdef
  have hD0 : (0:ℝ) < D := by
    rw [hDdef]; nlinarith [hs2, hy20, hy2]
  have hDu : D ≤ (s^2 + 9/4)^2 := by
    rw [hDdef]; nlinarith [hs2, hy20, hy2, sq_nonneg s]
  set c : ℝ := 0.760243 * y * s * (s^2 - 2) with hcdef
  have hc0' : 0 ≤ c := by
    rw [hcdef]; have : (0:ℝ) ≤ s^2 - 2 := by linarith
    positivity
  -- `C_p ≤ -c`
  have hCp : Qim y s * D ≤ -c := by
    rw [hid, hcdef]
    have t1 : (0:ℝ) ≤ 4*s*P*(r*s0) := by positivity
    have t2 : 0.760243 * y * s * (s^2 - 2) ≤ 2*S*s*c0*(y^2+s^2-2) := by
      have h1 : (0:ℝ) ≤ s * (s^2 - 2) := by nlinarith
      have hB0 : (0:ℝ) ≤ s*(s^2+y^2-2) := by nlinarith [hs2, hy20, hs0]
      have h2 : y * (s * (s^2-2)) * 0.760243 ≤ (2*S) * (s*(s^2+y^2-2)) * c0 := by
        have hE : y * (s*(s^2-2)) ≤ y * (s*(s^2+y^2-2)) := by
          nlinarith [mul_nonneg (mul_nonneg hy0 hs0.le) hy20]
        have hF : y * (s*(s^2+y^2-2)) ≤ (2*S) * (s*(s^2+y^2-2)) :=
          mul_le_mul_of_nonneg_right (by linarith [hS0]) hB0
        have hA : y * (s*(s^2-2)) ≤ (2*S) * (s*(s^2+y^2-2)) := le_trans hE hF
        have hB : (0:ℝ) ≤ (2*S) * (s*(s^2+y^2-2)) :=
          mul_nonneg (by linarith [hS0]) hB0
        have hA0' : (0:ℝ) ≤ y * (s*(s^2-2)) := mul_nonneg hy0 h1
        nlinarith [hA, hB, hc0, hA0']
      nlinarith [h2]
    linarith [t1, t2]
  have habs : c ≤ |Qim y s| * D := by
    have h1 : -(Qim y s) ≤ |Qim y s| := neg_le_abs _
    nlinarith [hCp, h1, hD0]
  have hcs : (7/10) * y * D ≤ c * s := by
    have h1 : (7/10) * y * D ≤ (7/10) * y * (s^2+9/4)^2 := by
      have : (0:ℝ) ≤ (7/10) * y := by linarith
      nlinarith [hDu, this]
    have h2 : (7/10) * y * (s^2+9/4)^2 ≤ c * s := by
      rw [hcdef]
      nlinarith [hs2, hy0, sq_nonneg (s^2 - 100)]
    linarith
  rw [div_le_iff₀ hs0]
  nlinarith [habs, hcs, hD0, hs0, abs_nonneg (Qim y s)]

/-- **There is no second-order far-field bound.**  No constant `C` satisfies
`|Qim y s| ≤ C y / s²` for all `0 ≤ y ≤ 1/2` and `s ≠ 0`: the true decay is first order. -/
theorem no_second_order_far_field :
    ¬ ∃ C : ℝ, ∀ y s : ℝ, 0 ≤ y → y ≤ 1/2 → s ≠ 0 → |Qim y s| ≤ C * y / s^2 := by
  rintro ⟨C, hC⟩
  set N : ℕ := ⌈C⌉₊ + 3 with hNdef
  have hNC : C + 3 ≤ (N:ℝ) := by
    have h := Nat.le_ceil C
    rw [hNdef]; push_cast; linarith
  have hN3 : (3:ℝ) ≤ (N:ℝ) := by
    rw [hNdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈C⌉₊]
  have hpi : (3.14:ℝ) ≤ Real.pi := by
    have := Real.pi_gt_d6
    norm_num at this ⊢
    linarith
  set s : ℝ := (N:ℝ) * (4 * Real.pi) with hsdef
  have hslb : 12.56 * (N:ℝ) ≤ s := by
    rw [hsdef]; nlinarith [hN3, hpi]
  have hs10 : (10:ℝ) ≤ s := by nlinarith [hslb, hN3]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs10; norm_num at hs10
  have hhalf : s / 2 = (N:ℝ) * (2 * Real.pi) := by rw [hsdef]; ring
  have hq : Real.sin (s/2) = 0 := by
    rw [hhalf]
    have h := Real.sin_nat_mul_pi (2*N)
    push_cast at h
    rw [show (N:ℝ) * (2*Real.pi) = 2*(N:ℝ)*Real.pi by ring]
    exact h
  have hp : Real.cos (s/2) = 1 := by
    rw [hhalf]; exact Real.cos_nat_mul_two_pi N
  have hlow := Qim_lower_at_even_multiple (y := 1/2) (s := s) (by norm_num) le_rfl hs10 hq hp
  have hup := hC (1/2) s (by norm_num) le_rfl hs0
  -- `0.35 / s ≤ |Qim| ≤ C/(2 s²)` forces `C ≥ 0.7 s`
  have hsq : (0:ℝ) < s^2 := by positivity
  have hkey : (7/10) * s ≤ C := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s)] at hlow
    rw [le_div_iff₀ hsq] at hup
    nlinarith [hlow, hup, hs10]
  nlinarith [hkey, hslb, hNC, hN3]

end Retention

#print axioms Retention.Qim_lower_at_even_multiple
#print axioms Retention.no_second_order_far_field
