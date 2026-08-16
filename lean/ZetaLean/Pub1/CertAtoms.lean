/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.CertDefs
import ZetaLean.Pub1.Aristotle.O

/-!
# Pub 1 strong closure: the 132 atomic integrals, in closed form

Each lemma evaluates one `∫_I |x-t|^m t^n dt` as an exact rational polynomial in
`x`, by instantiating `AristotleO.integral_abs_pow_mul_pow` and expanding the
resulting binomial sum.  These are the only integrals the truncated operator
`A₀` needs: `m = 2` for the `-4x²` term and `m = 2k+1` for `0 ≤ k ≤ 20`, against
`t^(2j)` for `0 ≤ j ≤ 5`.

Machine-generated from the evidence scripts; the statements are exact.
-/

set_option maxRecDepth 40000

namespace ZetaLean.Pub1

set_option maxHeartbeats 1000000 in
theorem atom_2_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 0 x = (1)*x^2 + (1/12) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_2_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 2 x = (1/12)*x^2 + (1/80) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_2_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 4 x = (1/80)*x^2 + (1/448) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_2_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 6 x = (1/448)*x^2 + (1/2304) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_2_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 8 x = (1/2304)*x^2 + (1/11264) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_2_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 2 10 x = (1/11264)*x^2 + (1/53248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 2 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 0 x = (1)*x^2 + (1/4) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 2 x = (1/6)*x^4 + (1/32) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 4 x = (1/15)*x^6 + (1/192) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 6 x = (1/28)*x^8 + (1/1024) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 8 x = (1/45)*x^10 + (1/5120) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_1_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 1 10 x = (1/66)*x^12 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 1 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 0 x = (1/2)*x^4 + (3/4)*x^2 + (1/32) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 2 x = (1/30)*x^6 + (3/32)*x^2 + (1/192) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 4 x = (1/140)*x^8 + (1/64)*x^2 + (1/1024) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 6 x = (1/420)*x^10 + (3/1024)*x^2 + (1/5120) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 8 x = (1/990)*x^12 + (3/5120)*x^2 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_3_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 3 10 x = (1/2002)*x^14 + (1/8192)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 3 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 0 x = (1/3)*x^6 + (5/4)*x^4 + (5/16)*x^2 + (1/192) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 2 x = (1/84)*x^8 + (5/32)*x^4 + (5/96)*x^2 + (1/1024) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 4 x = (1/630)*x^10 + (5/192)*x^4 + (5/512)*x^2 + (1/5120) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 6 x = (1/2772)*x^12 + (5/1024)*x^4 + (1/512)*x^2 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 8 x = (1/9009)*x^14 + (1/1024)*x^4 + (5/12288)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_5_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 5 10 x = (1/24024)*x^16 + (5/24576)*x^4 + (5/57344)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 5 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 0 x = (1/4)*x^8 + (7/4)*x^6 + (35/32)*x^4 + (7/64)*x^2 + (1/1024) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 2 x = (1/180)*x^10 + (7/32)*x^6 + (35/192)*x^4 + (21/1024)*x^2 + (1/5120) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 4 x = (1/1980)*x^12 + (7/192)*x^6 + (35/1024)*x^4 + (21/5120)*x^2 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 6 x = (1/12012)*x^14 + (7/1024)*x^6 + (7/1024)*x^4 + (7/8192)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 8 x = (1/51480)*x^16 + (7/5120)*x^6 + (35/24576)*x^4 + (3/16384)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_7_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 7 10 x = (1/175032)*x^18 + (7/24576)*x^6 + (5/16384)*x^4 + (21/524288)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 7 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 0 x = (1/5)*x^10 + (9/4)*x^8 + (21/8)*x^6 + (21/32)*x^4 + (9/256)*x^2 + (1/5120) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 2 x = (1/330)*x^12 + (9/32)*x^8 + (7/16)*x^6 + (63/512)*x^4 + (9/1280)*x^2 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 4 x = (1/5005)*x^14 + (3/64)*x^8 + (21/256)*x^6 + (63/2560)*x^4 + (3/2048)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 6 x = (1/40040)*x^16 + (9/1024)*x^8 + (21/1280)*x^6 + (21/4096)*x^4 + (9/28672)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 8 x = (1/218790)*x^18 + (9/5120)*x^8 + (7/2048)*x^6 + (9/8192)*x^4 + (9/131072)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_9_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 9 10 x = (1/923780)*x^20 + (3/8192)*x^8 + (3/4096)*x^6 + (63/262144)*x^4 + (1/65536)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 9 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 0 x = (1/6)*x^12 + (11/4)*x^10 + (165/32)*x^8 + (77/32)*x^6 + (165/512)*x^4 + (11/1024)*x^2 + (1/24576) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 2 x = (1/546)*x^14 + (11/32)*x^10 + (55/64)*x^8 + (231/512)*x^6 + (33/512)*x^4 + (55/24576)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 4 x = (1/10920)*x^16 + (11/192)*x^10 + (165/1024)*x^8 + (231/2560)*x^6 + (55/4096)*x^4 + (55/114688)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 6 x = (1/111384)*x^18 + (11/1024)*x^10 + (33/1024)*x^8 + (77/4096)*x^6 + (165/57344)*x^4 + (55/524288)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 8 x = (1/755820)*x^20 + (11/5120)*x^10 + (55/8192)*x^8 + (33/8192)*x^6 + (165/262144)*x^4 + (55/2359296)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_11_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 11 10 x = (1/3879876)*x^22 + (11/24576)*x^10 + (165/114688)*x^8 + (231/262144)*x^6 + (55/393216)*x^4 + (11/2097152)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 11 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 0 x = (1/7)*x^14 + (13/4)*x^12 + (143/16)*x^10 + (429/64)*x^8 + (429/256)*x^6 + (143/1024)*x^4 + (13/4096)*x^2 + (1/114688) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 2 x = (1/840)*x^16 + (13/32)*x^12 + (143/96)*x^10 + (1287/1024)*x^8 + (429/1280)*x^6 + (715/24576)*x^4 + (39/57344)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 4 x = (1/21420)*x^18 + (13/192)*x^12 + (143/512)*x^10 + (1287/5120)*x^8 + (143/2048)*x^6 + (715/114688)*x^4 + (39/262144)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 6 x = (1/271320)*x^20 + (13/1024)*x^12 + (143/2560)*x^10 + (429/8192)*x^8 + (429/28672)*x^6 + (715/524288)*x^4 + (13/393216)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 8 x = (1/2238390)*x^22 + (13/5120)*x^12 + (143/12288)*x^10 + (1287/114688)*x^8 + (429/131072)*x^6 + (715/2359296)*x^4 + (39/5242880)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_13_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 13 10 x = (1/13728792)*x^24 + (13/24576)*x^12 + (143/57344)*x^10 + (1287/524288)*x^8 + (143/196608)*x^6 + (143/2097152)*x^4 + (39/23068672)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 13 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 0 x = (1/8)*x^16 + (15/4)*x^14 + (455/32)*x^12 + (1001/64)*x^10 + (6435/1024)*x^8 + (1001/1024)*x^6 + (455/8192)*x^4 + (15/16384)*x^2 + (1/524288) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 2 x = (1/1224)*x^18 + (15/32)*x^14 + (455/192)*x^12 + (3003/1024)*x^10 + (1287/1024)*x^8 + (5005/24576)*x^6 + (195/16384)*x^4 + (105/524288)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 4 x = (1/38760)*x^20 + (5/64)*x^14 + (455/1024)*x^12 + (3003/5120)*x^10 + (2145/8192)*x^8 + (715/16384)*x^6 + (1365/524288)*x^4 + (35/786432)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 6 x = (1/596904)*x^22 + (15/1024)*x^14 + (91/1024)*x^12 + (1001/8192)*x^10 + (6435/114688)*x^8 + (5005/524288)*x^6 + (455/786432)*x^4 + (21/2097152)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 8 x = (1/5883768)*x^24 + (3/1024)*x^14 + (455/24576)*x^12 + (429/16384)*x^10 + (6435/524288)*x^8 + (5005/2359296)*x^6 + (273/2097152)*x^4 + (105/46137344)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_15_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 15 10 x = (1/42493880)*x^26 + (5/8192)*x^14 + (65/16384)*x^12 + (3003/524288)*x^10 + (715/262144)*x^8 + (1001/2097152)*x^6 + (1365/46137344)*x^4 + (35/67108864)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 15 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 0 x = (1/9)*x^18 + (17/4)*x^16 + (85/4)*x^14 + (1547/48)*x^12 + (2431/128)*x^10 + (2431/512)*x^8 + (1547/3072)*x^6 + (85/4096)*x^4 + (17/65536)*x^2 + (1/2359296) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 2 x = (1/1710)*x^20 + (17/32)*x^16 + (85/24)*x^14 + (1547/256)*x^12 + (2431/640)*x^10 + (12155/12288)*x^8 + (221/2048)*x^6 + (595/131072)*x^4 + (17/294912)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 4 x = (1/65835)*x^22 + (17/192)*x^16 + (85/128)*x^14 + (1547/1280)*x^12 + (2431/3072)*x^10 + (12155/57344)*x^8 + (1547/65536)*x^6 + (595/589824)*x^4 + (17/1310720)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 6 x = (1/1211364)*x^24 + (17/1024)*x^16 + (17/128)*x^14 + (1547/6144)*x^12 + (2431/14336)*x^10 + (12155/262144)*x^8 + (1547/294912)*x^6 + (119/524288)*x^4 + (17/5767168)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 8 x = (1/14060475)*x^26 + (17/5120)*x^16 + (85/3072)*x^14 + (221/4096)*x^12 + (2431/65536)*x^10 + (12155/1179648)*x^8 + (1547/1310720)*x^6 + (595/11534336)*x^4 + (17/25165824)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_17_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 17 10 x = (1/118107990)*x^28 + (17/24576)*x^16 + (85/14336)*x^14 + (1547/131072)*x^12 + (2431/294912)*x^10 + (2431/1048576)*x^8 + (1547/5767168)*x^6 + (595/50331648)*x^4 + (17/109051904)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 17 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 0 x = (1/10)*x^20 + (19/4)*x^18 + (969/32)*x^16 + (969/16)*x^14 + (12597/256)*x^12 + (46189/2560)*x^10 + (12597/4096)*x^8 + (969/4096)*x^6 + (969/131072)*x^4 + (19/262144)*x^2 + (1/10485760) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 2 x = (1/2310)*x^22 + (19/32)*x^18 + (323/64)*x^16 + (2907/256)*x^14 + (12597/1280)*x^12 + (46189/12288)*x^10 + (37791/57344)*x^8 + (6783/131072)*x^6 + (323/196608)*x^4 + (171/10485760)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 4 x = (1/106260)*x^24 + (19/192)*x^18 + (969/1024)*x^16 + (2907/1280)*x^14 + (4199/2048)*x^12 + (46189/57344)*x^10 + (37791/262144)*x^8 + (2261/196608)*x^6 + (969/2621440)*x^4 + (171/46137344)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 6 x = (1/2302300)*x^26 + (19/1024)*x^18 + (969/5120)*x^16 + (969/2048)*x^14 + (12597/28672)*x^12 + (46189/262144)*x^10 + (4199/131072)*x^8 + (6783/2621440)*x^6 + (969/11534336)*x^4 + (57/67108864)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 8 x = (1/31081050)*x^28 + (19/5120)*x^18 + (323/8192)*x^16 + (2907/28672)*x^14 + (12597/131072)*x^12 + (46189/1179648)*x^10 + (37791/5242880)*x^8 + (6783/11534336)*x^6 + (323/16777216)*x^4 + (171/872415232)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_19_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 19 10 x = (1/300450150)*x^30 + (19/24576)*x^18 + (969/114688)*x^16 + (2907/131072)*x^14 + (4199/196608)*x^12 + (46189/5242880)*x^10 + (37791/23068672)*x^8 + (2261/16777216)*x^6 + (969/218103808)*x^4 + (171/3758096384)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 19 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 0 x = (1/11)*x^22 + (21/4)*x^20 + (665/16)*x^18 + (6783/64)*x^16 + (14535/128)*x^14 + (29393/512)*x^12 + (29393/2048)*x^10 + (14535/8192)*x^8 + (6783/65536)*x^6 + (665/262144)*x^4 + (21/1048576)*x^2 + (1/46137344) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 2 x = (1/3036)*x^24 + (21/32)*x^20 + (665/96)*x^18 + (20349/1024)*x^16 + (2907/128)*x^14 + (146965/12288)*x^12 + (12597/4096)*x^10 + (101745/262144)*x^8 + (2261/98304)*x^6 + (1197/2097152)*x^4 + (105/23068672)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 4 x = (1/164450)*x^26 + (7/64)*x^20 + (665/512)*x^18 + (20349/5120)*x^16 + (4845/1024)*x^14 + (20995/8192)*x^12 + (88179/131072)*x^10 + (11305/131072)*x^8 + (6783/1310720)*x^6 + (5985/46137344)*x^4 + (35/33554432)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 6 x = (1/4144140)*x^28 + (21/1024)*x^20 + (133/512)*x^18 + (6783/8192)*x^16 + (14535/14336)*x^14 + (146965/262144)*x^12 + (29393/196608)*x^10 + (20349/1048576)*x^8 + (6783/5767168)*x^6 + (1995/67108864)*x^4 + (105/436207616)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 8 x = (1/64382175)*x^30 + (21/5120)*x^20 + (665/12288)*x^18 + (2907/16384)*x^16 + (14535/65536)*x^14 + (146965/1179648)*x^12 + (88179/2621440)*x^10 + (101745/23068672)*x^8 + (2261/8388608)*x^6 + (5985/872415232)*x^4 + (15/268435456)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_21_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 21 10 x = (1/709634640)*x^32 + (7/8192)*x^20 + (95/8192)*x^18 + (20349/524288)*x^16 + (1615/32768)*x^14 + (29393/1048576)*x^12 + (88179/11534336)*x^10 + (33915/33554432)*x^8 + (6783/109051904)*x^6 + (855/536870912)*x^4 + (7/536870912)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 21 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 0 x = (1/12)*x^24 + (23/4)*x^22 + (1771/32)*x^20 + (33649/192)*x^18 + (245157/1024)*x^16 + (81719/512)*x^14 + (676039/12288)*x^12 + (81719/8192)*x^10 + (245157/262144)*x^8 + (33649/786432)*x^6 + (1771/2097152)*x^4 + (23/4194304)*x^2 + (1/201326592) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 2 x = (1/3900)*x^26 + (23/32)*x^22 + (1771/192)*x^20 + (33649/1024)*x^18 + (245157/5120)*x^16 + (408595/12288)*x^14 + (96577/8192)*x^12 + (572033/262144)*x^10 + (81719/393216)*x^8 + (100947/10485760)*x^6 + (805/4194304)*x^4 + (253/201326592)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 4 x = (1/245700)*x^28 + (23/192)*x^22 + (1771/1024)*x^20 + (33649/5120)*x^18 + (81719/8192)*x^16 + (408595/57344)*x^14 + (676039/262144)*x^12 + (572033/1179648)*x^10 + (245157/5242880)*x^8 + (9177/4194304)*x^6 + (8855/201326592)*x^4 + (253/872415232)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 6 x = (1/7125300)*x^30 + (23/1024)*x^22 + (1771/5120)*x^20 + (33649/24576)*x^18 + (245157/114688)*x^16 + (408595/262144)*x^14 + (676039/1179648)*x^12 + (572033/5242880)*x^10 + (22287/2097152)*x^8 + (33649/67108864)*x^6 + (8855/872415232)*x^4 + (253/3758096384)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 8 x = (1/126219600)*x^32 + (23/5120)*x^22 + (1771/24576)*x^20 + (4807/16384)*x^18 + (245157/524288)*x^16 + (408595/1179648)*x^14 + (676039/5242880)*x^12 + (52003/2097152)*x^10 + (81719/33554432)*x^8 + (100947/872415232)*x^6 + (1265/536870912)*x^4 + (253/16106127360)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_23_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 23 10 x = (1/1573537680)*x^34 + (23/24576)*x^22 + (253/16384)*x^20 + (33649/524288)*x^18 + (81719/786432)*x^16 + (81719/1048576)*x^14 + (676039/23068672)*x^12 + (572033/100663296)*x^10 + (245157/436207616)*x^8 + (14421/536870912)*x^6 + (1771/3221225472)*x^4 + (253/68719476736)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 23 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 0 x = (1/13)*x^26 + (25/4)*x^24 + (575/8)*x^22 + (8855/32)*x^20 + (120175/256)*x^18 + (408595/1024)*x^16 + (185725/1024)*x^14 + (185725/4096)*x^12 + (408595/65536)*x^10 + (120175/262144)*x^8 + (8855/524288)*x^6 + (575/2097152)*x^4 + (25/16777216)*x^2 + (1/872415232) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 2 x = (1/4914)*x^28 + (25/32)*x^24 + (575/48)*x^22 + (26565/512)*x^20 + (24035/256)*x^18 + (2042975/24576)*x^16 + (557175/14336)*x^14 + (1300075/131072)*x^12 + (408595/294912)*x^10 + (216315/2097152)*x^8 + (4025/1048576)*x^6 + (6325/100663296)*x^4 + (75/218103808)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 4 x = (1/356265)*x^30 + (25/192)*x^24 + (575/256)*x^22 + (5313/512)*x^20 + (120175/6144)*x^18 + (2042975/114688)*x^16 + (557175/65536)*x^14 + (1300075/589824)*x^12 + (81719/262144)*x^10 + (98325/4194304)*x^8 + (44275/50331648)*x^6 + (6325/436207616)*x^4 + (75/939524096)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 6 x = (1/11780496)*x^32 + (25/1024)*x^24 + (115/256)*x^22 + (8855/4096)*x^20 + (120175/28672)*x^18 + (2042975/524288)*x^16 + (185725/98304)*x^14 + (260015/524288)*x^12 + (37145/524288)*x^10 + (360525/67108864)*x^8 + (44275/218103808)*x^6 + (6325/1879048192)*x^4 + (5/268435456)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 8 x = (1/236030652)*x^34 + (5/1024)*x^24 + (575/6144)*x^22 + (3795/8192)*x^20 + (120175/131072)*x^18 + (2042975/2359296)*x^16 + (111435/262144)*x^14 + (1300075/11534336)*x^12 + (408595/25165824)*x^10 + (1081575/872415232)*x^8 + (6325/134217728)*x^6 + (1265/1610612736)*x^4 + (75/17179869184)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_25_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 25 10 x = (1/3304429128)*x^36 + (25/24576)*x^24 + (575/28672)*x^22 + (26565/262144)*x^20 + (120175/589824)*x^18 + (408595/2097152)*x^16 + (557175/5767168)*x^14 + (1300075/50331648)*x^12 + (408595/109051904)*x^10 + (1081575/3758096384)*x^8 + (8855/805306368)*x^6 + (6325/34359738368)*x^4 + (75/73014444032)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 25 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 0 x = (1/14)*x^28 + (27/4)*x^26 + (2925/32)*x^24 + (13455/32)*x^22 + (444015/512)*x^20 + (937365/1024)*x^18 + (4345965/8192)*x^16 + (5014575/28672)*x^14 + (4345965/131072)*x^12 + (937365/262144)*x^10 + (444015/2097152)*x^8 + (13455/2097152)*x^6 + (2925/33554432)*x^4 + (27/67108864)*x^2 + (1/3758096384) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 2 x = (1/6090)*x^30 + (27/32)*x^26 + (975/64)*x^24 + (40365/512)*x^22 + (88803/512)*x^20 + (1562275/8192)*x^18 + (13037895/114688)*x^16 + (5014575/131072)*x^14 + (482885/65536)*x^12 + (1687257/2097152)*x^10 + (201825/4194304)*x^8 + (49335/33554432)*x^6 + (675/33554432)*x^4 + (351/3758096384)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 4 x = (1/503440)*x^32 + (9/64)*x^26 + (2925/1024)*x^24 + (8073/512)*x^22 + (148005/4096)*x^20 + (4686825/114688)*x^18 + (13037895/524288)*x^16 + (557175/65536)*x^14 + (869193/524288)*x^12 + (766935/4194304)*x^10 + (740025/67108864)*x^8 + (11385/33554432)*x^6 + (8775/1879048192)*x^4 + (117/5368709120)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 6 x = (1/18828656)*x^34 + (27/1024)*x^26 + (585/1024)*x^24 + (13455/4096)*x^22 + (444015/57344)*x^20 + (4686825/524288)*x^18 + (1448655/262144)*x^16 + (1002915/524288)*x^14 + (4345965/11534336)*x^12 + (2812095/67108864)*x^10 + (170775/67108864)*x^8 + (148005/1879048192)*x^6 + (585/536870912)*x^4 + (351/68719476736)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 8 x = (1/423644760)*x^36 + (27/5120)*x^26 + (975/8192)*x^24 + (40365/57344)*x^22 + (444015/262144)*x^20 + (1562275/786432)*x^18 + (2607579/2097152)*x^16 + (5014575/11534336)*x^14 + (1448655/16777216)*x^12 + (648945/67108864)*x^10 + (2220075/3758096384)*x^8 + (9867/536870912)*x^6 + (8775/34359738368)*x^4 + (351/292057776128)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_27_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 27 10 x = (1/6618272584)*x^38 + (9/8192)*x^26 + (2925/114688)*x^24 + (40365/262144)*x^22 + (49335/131072)*x^20 + (937365/2097152)*x^18 + (13037895/46137344)*x^16 + (1671525/16777216)*x^14 + (334305/16777216)*x^12 + (8436285/3758096384)*x^10 + (148005/1073741824)*x^8 + (148005/34359738368)*x^6 + (8775/146028888064)*x^4 + (39/137438953472)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 27 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 0 x = (1/15)*x^30 + (29/4)*x^28 + (1827/16)*x^26 + (39585/64)*x^24 + (390195/256)*x^22 + (2003001/1024)*x^20 + (5766215/4096)*x^18 + (9694845/16384)*x^16 + (9694845/65536)*x^14 + (5766215/262144)*x^12 + (2003001/1048576)*x^10 + (390195/4194304)*x^8 + (39585/16777216)*x^6 + (1827/67108864)*x^4 + (29/268435456)*x^2 + (1/16106127360) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 2 x = (1/7440)*x^32 + (29/32)*x^28 + (609/32)*x^26 + (118755/1024)*x^24 + (78039/256)*x^22 + (3338335/8192)*x^20 + (2471235/8192)*x^18 + (67863915/524288)*x^16 + (1077205/32768)*x^14 + (10379187/2097152)*x^12 + (910455/2097152)*x^10 + (1430715/67108864)*x^8 + (9135/16777216)*x^6 + (3393/536870912)*x^4 + (203/8053063680)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 4 x = (1/695640)*x^34 + (29/192)*x^28 + (1827/512)*x^26 + (23751/1024)*x^24 + (130065/2048)*x^22 + (1430715/16384)*x^20 + (17298645/262144)*x^18 + (7540435/262144)*x^16 + (1938969/262144)*x^14 + (51895935/46137344)*x^12 + (3338335/33554432)*x^10 + (330165/67108864)*x^8 + (16965/134217728)*x^6 + (7917/5368709120)*x^4 + (203/34359738368)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 6 x = (1/29216880)*x^36 + (29/1024)*x^28 + (1827/2560)*x^26 + (39585/8192)*x^24 + (390195/28672)*x^22 + (10015005/524288)*x^20 + (5766215/393216)*x^18 + (13572783/2097152)*x^16 + (9694845/5767168)*x^14 + (17298645/67108864)*x^12 + (770385/33554432)*x^10 + (4292145/3758096384)*x^8 + (7917/268435456)*x^6 + (23751/68719476736)*x^4 + (203/146028888064)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 8 x = (1/733552380)*x^38 + (29/5120)*x^28 + (609/4096)*x^26 + (16965/16384)*x^24 + (390195/131072)*x^22 + (3338335/786432)*x^20 + (3459729/1048576)*x^18 + (67863915/46137344)*x^16 + (3231615/8388608)*x^14 + (3991995/67108864)*x^12 + (1430715/268435456)*x^10 + (286143/1073741824)*x^8 + (118755/17179869184)*x^6 + (23751/292057776128)*x^4 + (203/618475290624)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_29_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 29 10 x = (1/12714907920)*x^40 + (29/24576)*x^28 + (261/8192)*x^26 + (118755/524288)*x^24 + (43355/65536)*x^22 + (2003001/2097152)*x^20 + (17298645/23068672)*x^18 + (22621305/67108864)*x^16 + (9694845/109051904)*x^14 + (7413705/536870912)*x^12 + (667667/536870912)*x^10 + (4292145/68719476736)*x^8 + (118755/73014444032)*x^6 + (2639/137438953472)*x^4 + (203/2611340115968)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 29 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 0 x = (1/16)*x^32 + (31/4)*x^30 + (4495/32)*x^28 + (56637/64)*x^26 + (2629575/1024)*x^24 + (4032015/1024)*x^22 + (28224105/8192)*x^20 + (29464725/16384)*x^18 + (300540195/524288)*x^16 + (29464725/262144)*x^14 + (28224105/2097152)*x^12 + (4032015/4194304)*x^10 + (2629575/67108864)*x^8 + (56637/67108864)*x^6 + (4495/536870912)*x^4 + (31/1073741824)*x^2 + (1/68719476736) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 2 x = (1/8976)*x^34 + (31/32)*x^30 + (4495/192)*x^28 + (169911/1024)*x^26 + (525915/1024)*x^24 + (6720025/8192)*x^22 + (12096045/16384)*x^20 + (206253075/524288)*x^18 + (33393355/262144)*x^16 + (53036505/2097152)*x^14 + (141120525/46137344)*x^12 + (14784055/67108864)*x^10 + (606825/67108864)*x^8 + (105183/536870912)*x^6 + (6293/3221225472)*x^4 + (465/68719476736)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 4 x = (1/942480)*x^36 + (31/192)*x^30 + (4495/1024)*x^28 + (169911/5120)*x^26 + (876525/8192)*x^24 + (20160075/114688)*x^22 + (84672315/524288)*x^20 + (68751025/786432)*x^18 + (60108039/2097152)*x^16 + (265182525/46137344)*x^14 + (47040175/67108864)*x^12 + (3411705/67108864)*x^10 + (7888725/3758096384)*x^8 + (245427/5368709120)*x^6 + (31465/68719476736)*x^4 + (465/292057776128)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 6 x = (1/44170896)*x^38 + (31/1024)*x^30 + (899/1024)*x^28 + (56637/8192)*x^26 + (2629575/114688)*x^24 + (20160075/524288)*x^22 + (9408035/262144)*x^20 + (41250615/2097152)*x^18 + (300540195/46137344)*x^16 + (88394175/67108864)*x^14 + (10855425/67108864)*x^12 + (44352165/3758096384)*x^10 + (525915/1073741824)*x^8 + (736281/68719476736)*x^6 + (31465/292057776128)*x^4 + (155/412316860416)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 8 x = (1/1230474960)*x^40 + (31/5120)*x^30 + (4495/24576)*x^28 + (24273/16384)*x^26 + (2629575/524288)*x^24 + (6720025/786432)*x^22 + (16934463/2097152)*x^20 + (206253075/46137344)*x^18 + (100180065/67108864)*x^16 + (265182525/872415232)*x^14 + (20160075/536870912)*x^12 + (2956811/1073741824)*x^10 + (7888725/68719476736)*x^8 + (736281/292057776128)*x^6 + (31465/1236950581248)*x^4 + (465/5222680231936)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_31_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 31 10 x = (1/23543087568)*x^42 + (31/24576)*x^30 + (4495/114688)*x^28 + (169911/524288)*x^26 + (292175/262144)*x^24 + (4032015/2097152)*x^22 + (84672315/46137344)*x^20 + (68751025/67108864)*x^18 + (300540195/872415232)*x^16 + (265182525/3758096384)*x^14 + (9408035/1073741824)*x^12 + (44352165/68719476736)*x^10 + (7888725/292057776128)*x^8 + (81809/137438953472)*x^6 + (31465/5222680231936)*x^4 + (93/4398046511104)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 31 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 0 x = (1/17)*x^34 + (33/4)*x^32 + (341/2)*x^30 + (9889/8)*x^28 + (267003/64)*x^26 + (1928355/256)*x^24 + (4032015/512)*x^22 + (10235115/2048)*x^20 + (64822395/32768)*x^18 + (64822395/131072)*x^16 + (10235115/131072)*x^14 + (4032015/524288)*x^12 + (1928355/4194304)*x^10 + (267003/16777216)*x^8 + (9889/33554432)*x^6 + (341/134217728)*x^4 + (33/4294967296)*x^2 + (1/292057776128) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 2 x = (1/10710)*x^36 + (33/32)*x^32 + (341/12)*x^30 + (29667/128)*x^28 + (267003/320)*x^26 + (3213925/2048)*x^24 + (12096045/7168)*x^22 + (71645805/65536)*x^20 + (21607465/49152)*x^18 + (116680311/1048576)*x^16 + (4652325/262144)*x^14 + (14784055/8388608)*x^12 + (445005/4194304)*x^10 + (3471039/939524096)*x^8 + (69223/1006632960)*x^6 + (5115/8589934592)*x^4 + (33/18253611008)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 4 x = (1/1254855)*x^38 + (11/64)*x^32 + (341/64)*x^30 + (29667/640)*x^28 + (89001/512)*x^26 + (9641775/28672)*x^24 + (12096045/32768)*x^22 + (7960645/32768)*x^20 + (12964479/131072)*x^18 + (53036505/2097152)*x^16 + (17058525/4194304)*x^14 + (3411705/8388608)*x^12 + (5785065/234881024)*x^10 + (1157013/1342177280)*x^8 + (69223/4294967296)*x^6 + (5115/36507222016)*x^4 + (11/25769803776)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 6 x = (1/65252460)*x^40 + (33/1024)*x^32 + (341/320)*x^30 + (9889/1024)*x^28 + (267003/7168)*x^26 + (9641775/131072)*x^24 + (1344005/16384)*x^22 + (14329161/262144)*x^20 + (5892945/262144)*x^18 + (194467185/33554432)*x^16 + (51175575/54525952)*x^14 + (44352165/469762048)*x^12 + (385671/67108864)*x^10 + (3471039/17179869184)*x^8 + (69223/18253611008)*x^6 + (1705/51539607552)*x^4 + (33/326417514496)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 8 x = (1/2006513145)*x^42 + (33/5120)*x^32 + (341/1536)*x^30 + (29667/14336)*x^28 + (267003/32768)*x^26 + (3213925/196608)*x^24 + (2419209/131072)*x^22 + (6513255/524288)*x^20 + (21607465/4194304)*x^18 + (583401555/436207616)*x^16 + (51175575/234881024)*x^14 + (2956811/134217728)*x^12 + (5785065/4294967296)*x^10 + (3471039/73014444032)*x^8 + (69223/77309411328)*x^6 + (5115/652835028992)*x^4 + (33/1374389534720)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_33_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 33 10 x = (1/42181365226)*x^44 + (11/8192)*x^32 + (341/7168)*x^30 + (29667/65536)*x^28 + (29667/16384)*x^26 + (1928355/524288)*x^24 + (12096045/2883584)*x^22 + (23881935/8388608)*x^20 + (64822395/54525952)*x^18 + (583401555/1879048192)*x^16 + (3411705/67108864)*x^14 + (44352165/8589934592)*x^12 + (5785065/18253611008)*x^10 + (385671/34359738368)*x^8 + (69223/326417514496)*x^6 + (1023/549755813888)*x^4 + (11/1924145348608)*x^2 + (1/387028092977152) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 33 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 0 x = (1/18)*x^36 + (35/4)*x^34 + (6545/32)*x^32 + (40579/24)*x^30 + (840565/128)*x^28 + (3530373/256)*x^26 + (34768825/2048)*x^24 + (26363175/2048)*x^22 + (405992895/65536)*x^20 + (756261275/393216)*x^18 + (405992895/1048576)*x^16 + (26363175/524288)*x^14 + (34768825/8388608)*x^12 + (3530373/16777216)*x^10 + (840565/134217728)*x^8 + (40579/402653184)*x^6 + (6545/8589934592)*x^4 + (35/17179869184)*x^2 + (1/1236950581248) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 2 x = (1/12654)*x^38 + (35/32)*x^34 + (6545/192)*x^32 + (40579/128)*x^30 + (168113/128)*x^28 + (5883955/2048)*x^26 + (14900925/4096)*x^24 + (184542225/65536)*x^22 + (135330965/98304)*x^20 + (453756765/1048576)*x^18 + (184542225/2097152)*x^16 + (96664975/8388608)*x^14 + (8023575/8388608)*x^12 + (6556407/134217728)*x^10 + (1176791/805306368)*x^8 + (202895/8589934592)*x^6 + (385/2147483648)*x^4 + (595/1236950581248)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 4 x = (1/1645020)*x^40 + (35/192)*x^34 + (6545/1024)*x^32 + (40579/640)*x^30 + (840565/3072)*x^28 + (2521695/4096)*x^26 + (104306475/131072)*x^24 + (61514075/98304)*x^22 + (81198579/262144)*x^20 + (206253075/2097152)*x^18 + (676654825/33554432)*x^16 + (289994925/109051904)*x^14 + (14900925/67108864)*x^12 + (15298283/1342177280)*x^10 + (5883955/17179869184)*x^8 + (11935/2147483648)*x^6 + (6545/154618822656)*x^4 + (595/5222680231936)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 6 x = (1/94424148)*x^42 + (35/1024)*x^34 + (1309/1024)*x^32 + (40579/3072)*x^30 + (840565/14336)*x^28 + (17651865/131072)*x^26 + (34768825/196608)*x^24 + (36908445/262144)*x^22 + (36908445/524288)*x^20 + (756261275/33554432)*x^18 + (2029964475/436207616)*x^16 + (289994925/469762048)*x^14 + (6953765/134217728)*x^12 + (45894849/17179869184)*x^10 + (346115/4294967296)*x^8 + (202895/154618822656)*x^6 + (6545/652835028992)*x^4 + (119/4398046511104)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 8 x = (1/3190187286)*x^44 + (7/1024)*x^34 + (6545/24576)*x^32 + (5797/2048)*x^30 + (840565/65536)*x^28 + (5883955/196608)*x^26 + (20861295/524288)*x^24 + (184542225/5767168)*x^22 + (135330965/8388608)*x^20 + (2268783825/436207616)*x^18 + (289994925/268435456)*x^16 + (19332995/134217728)*x^14 + (104306475/8589934592)*x^12 + (2699697/4294967296)*x^10 + (5883955/309237645312)*x^8 + (202895/652835028992)*x^6 + (1309/549755813888)*x^4 + (85/13194139533312)*x^2 + (1/387028092977152) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_35_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 35 10 x = (1/73374307578)*x^46 + (35/24576)*x^34 + (935/16384)*x^32 + (40579/65536)*x^30 + (840565/294912)*x^28 + (3530373/524288)*x^26 + (104306475/11534336)*x^24 + (61514075/8388608)*x^22 + (405992895/109051904)*x^20 + (324111975/268435456)*x^18 + (135330965/536870912)*x^16 + (289994925/8589934592)*x^14 + (6135675/2147483648)*x^12 + (15298283/103079215104)*x^10 + (5883955/1305670057984)*x^8 + (40579/549755813888)*x^6 + (935/1649267441664)*x^4 + (595/387028092977152)*x^2 + (1/1618481116086272) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 35 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 0 x = (1/19)*x^38 + (37/4)*x^36 + (3885/16)*x^34 + (145299/64)*x^32 + (643467/64)*x^30 + (6220181/256)*x^28 + (35624673/1024)*x^26 + (127230975/4096)*x^24 + (585262485/32768)*x^22 + (883631595/131072)*x^20 + (883631595/524288)*x^18 + (585262485/2097152)*x^16 + (127230975/4194304)*x^14 + (35624673/16777216)*x^12 + (6220181/67108864)*x^10 + (643467/268435456)*x^8 + (145299/4294967296)*x^6 + (3885/17179869184)*x^4 + (37/68719476736)*x^2 + (1/5222680231936) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 2 x = (1/14820)*x^40 + (37/32)*x^36 + (1295/32)*x^34 + (435897/1024)*x^32 + (643467/320)*x^30 + (31100905/6144)*x^28 + (15267717/2048)*x^26 + (890616825/131072)*x^24 + (65029165/16384)*x^22 + (1590536871/1048576)*x^20 + (401650725/1048576)*x^18 + (2145962445/33554432)*x^16 + (381692925/54525952)*x^14 + (66160107/134217728)*x^12 + (43541267/2013265920)*x^10 + (9652005/17179869184)*x^8 + (8547/1073741824)*x^6 + (22015/412316860416)*x^4 + (333/2611340115968)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 4 x = (1/2126670)*x^42 + (37/192)*x^36 + (3885/512)*x^34 + (435897/5120)*x^32 + (214489/512)*x^30 + (31100905/28672)*x^28 + (106874019/65536)*x^26 + (98957425/65536)*x^24 + (117052497/131072)*x^22 + (722971305/2097152)*x^20 + (1472719325/16777216)*x^18 + (6437887335/436207616)*x^16 + (381692925/234881024)*x^14 + (154373583/1342177280)*x^12 + (43541267/8589934592)*x^10 + (567765/4294967296)*x^8 + (48433/25769803776)*x^6 + (66045/5222680231936)*x^4 + (333/10995116277760)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 6 x = (1/134121988)*x^44 + (37/1024)*x^36 + (777/512)*x^34 + (145299/8192)*x^32 + (643467/7168)*x^30 + (31100905/131072)*x^28 + (11874891/32768)*x^26 + (178123365/524288)*x^24 + (585262485/2883584)*x^22 + (2650894785/33554432)*x^20 + (4418157975/218103808)*x^18 + (6437887335/1879048192)*x^16 + (25446195/67108864)*x^14 + (463120749/17179869184)*x^12 + (2561251/2147483648)*x^10 + (1072445/34359738368)*x^8 + (145299/326417514496)*x^6 + (13209/4398046511104)*x^4 + (111/15393162788864)*x^2 + (1/387028092977152) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 8 x = (1/4957723485)*x^46 + (37/5120)*x^36 + (1295/4096)*x^34 + (62271/16384)*x^32 + (643467/32768)*x^30 + (31100905/589824)*x^28 + (106874019/1310720)*x^26 + (890616825/11534336)*x^24 + (195087495/4194304)*x^22 + (7952684355/436207616)*x^20 + (631165425/134217728)*x^18 + (429192489/536870912)*x^16 + (381692925/4294967296)*x^14 + (27242397/4294967296)*x^12 + (43541267/154618822656)*x^10 + (9652005/1305670057984)*x^8 + (145299/1374389534720)*x^6 + (3145/4398046511104)*x^4 + (333/193514046488576)*x^2 + (1/1618481116086272) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_37_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 37 10 x = (1/124273602024)*x^48 + (37/24576)*x^36 + (555/8192)*x^34 + (435897/524288)*x^32 + (214489/49152)*x^30 + (6220181/524288)*x^28 + (106874019/5767168)*x^26 + (296872275/16777216)*x^24 + (585262485/54525952)*x^22 + (1136097765/268435456)*x^20 + (294543865/268435456)*x^18 + (6437887335/34359738368)*x^16 + (22452525/1073741824)*x^14 + (51457861/34359738368)*x^12 + (43541267/652835028992)*x^10 + (1930401/1099511627776)*x^8 + (6919/274877906944)*x^6 + (66045/387028092977152)*x^4 + (333/809240558043136)*x^2 + (1/6755399441055744) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 37 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 0 x = (1/20)*x^40 + (39/4)*x^38 + (9139/32)*x^36 + (191919/64)*x^34 + (15380937/1024)*x^32 + (52978783/1280)*x^30 + (139671337/2048)*x^28 + (290086623/4096)*x^26 + (6285210165/131072)*x^24 + (2834506545/131072)*x^22 + (6892326441/1048576)*x^20 + (2834506545/2097152)*x^18 + (6285210165/33554432)*x^16 + (290086623/16777216)*x^14 + (139671337/134217728)*x^12 + (52978783/1342177280)*x^10 + (15380937/17179869184)*x^8 + (191919/17179869184)*x^6 + (9139/137438953472)*x^4 + (39/274877906944)*x^2 + (1/21990232555520) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 2 x = (1/17220)*x^42 + (39/32)*x^38 + (9139/192)*x^36 + (575757/1024)*x^34 + (15380937/5120)*x^32 + (52978783/6144)*x^30 + (419014011/28672)*x^28 + (2030606361/131072)*x^26 + (698356685/65536)*x^24 + (5102111781/1048576)*x^22 + (3132875655/2097152)*x^20 + (10393190665/33554432)*x^18 + (1450433115/33554432)*x^16 + (3771126099/939524096)*x^14 + (977699359/4026531840)*x^12 + (158936349/17179869184)*x^10 + (904761/4294967296)*x^8 + (1087541/412316860416)*x^6 + (4329/274877906944)*x^4 + (741/21990232555520)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 4 x = (1/2715020)*x^44 + (13/64)*x^38 + (9139/1024)*x^36 + (575757/5120)*x^34 + (5126979/8192)*x^32 + (52978783/28672)*x^30 + (419014011/131072)*x^28 + (225622929/65536)*x^26 + (1257042033/524288)*x^24 + (25510558905/23068672)*x^22 + (11487210735/33554432)*x^20 + (2398428615/33554432)*x^18 + (18855630495/1879048192)*x^16 + (1257042033/1342177280)*x^14 + (977699359/17179869184)*x^12 + (9349197/4294967296)*x^10 + (1708993/34359738368)*x^8 + (171717/274877906944)*x^6 + (82251/21990232555520)*x^4 + (247/30786325577728)*x^2 + (1/387028092977152) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 6 x = (1/187336380)*x^46 + (39/1024)*x^38 + (9139/5120)*x^36 + (191919/8192)*x^34 + (15380937/114688)*x^32 + (52978783/131072)*x^30 + (139671337/196608)*x^28 + (2030606361/2621440)*x^26 + (6285210165/11534336)*x^24 + (8503519635/33554432)*x^22 + (2650894785/33554432)*x^20 + (31179571995/1879048192)*x^18 + (1257042033/536870912)*x^16 + (3771126099/17179869184)*x^14 + (57511727/4294967296)*x^12 + (52978783/103079215104)*x^10 + (809523/68719476736)*x^8 + (3262623/21990232555520)*x^6 + (27417/30786325577728)*x^4 + (741/387028092977152)*x^2 + (1/1618481116086272) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 8 x = (1/7546979880)*x^48 + (39/5120)*x^38 + (9139/24576)*x^36 + (82251/16384)*x^34 + (15380937/524288)*x^32 + (52978783/589824)*x^30 + (419014011/2621440)*x^28 + (2030606361/11534336)*x^26 + (2095070055/16777216)*x^24 + (1962350685/33554432)*x^22 + (4923090315/268435456)*x^20 + (2078638133/536870912)*x^18 + (18855630495/34359738368)*x^16 + (221830947/4294967296)*x^14 + (977699359/309237645312)*x^12 + (8365071/68719476736)*x^10 + (15380937/5497558138880)*x^8 + (155363/4398046511104)*x^6 + (82251/387028092977152)*x^4 + (741/1618481116086272)*x^2 + (1/6755399441055744) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_39_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 39 10 x = (1/205445563400)*x^50 + (13/8192)*x^38 + (9139/114688)*x^36 + (575757/524288)*x^34 + (1708993/262144)*x^32 + (52978783/2621440)*x^30 + (419014011/11534336)*x^28 + (676868787/16777216)*x^26 + (483477705/16777216)*x^24 + (25510558905/1879048192)*x^22 + (2297442147/536870912)*x^20 + (31179571995/34359738368)*x^18 + (1109154735/8589934592)*x^16 + (419014011/34359738368)*x^14 + (51457861/68719476736)*x^12 + (158936349/5497558138880)*x^10 + (5126979/7696581394432)*x^8 + (3262623/387028092977152)*x^6 + (82251/1618481116086272)*x^4 + (247/2251799813685248)*x^2 + (1/28147497671065600) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 39 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_0 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 0 x = (1/21)*x^42 + (41/4)*x^40 + (2665/8)*x^38 + (374699/96)*x^36 + (5620485/256)*x^34 + (70068713/1024)*x^32 + (197466373/1536)*x^30 + (2202509545/14336)*x^28 + (3964517181/32768)*x^26 + (8421360025/131072)*x^24 + (6116566755/262144)*x^22 + (6116566755/1048576)*x^20 + (8421360025/8388608)*x^18 + (3964517181/33554432)*x^16 + (2202509545/234881024)*x^14 + (197466373/402653184)*x^12 + (70068713/4294967296)*x^10 + (5620485/17179869184)*x^8 + (374699/103079215104)*x^6 + (2665/137438953472)*x^4 + (41/1099511627776)*x^2 + (1/92358976733184) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 0 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_2 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 2 x = (1/19866)*x^44 + (41/32)*x^40 + (2665/48)*x^38 + (374699/512)*x^36 + (1124097/256)*x^34 + (350343565/24576)*x^32 + (197466373/7168)*x^30 + (2202509545/65536)*x^28 + (440501909/16384)*x^26 + (15158448045/1048576)*x^24 + (30582833775/5767168)*x^22 + (22427411435/16777216)*x^20 + (1943390775/8388608)*x^18 + (51538723353/1879048192)*x^16 + (440501909/201326592)*x^14 + (987331865/8589934592)*x^12 + (4121689/1073741824)*x^10 + (31849415/412316860416)*x^8 + (59163/68719476736)*x^6 + (10127/2199023255552)*x^4 + (205/23089744183296)*x^2 + (1/387028092977152) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 2 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_4 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 4 x = (1/3426885)*x^46 + (41/192)*x^40 + (2665/256)*x^38 + (374699/2560)*x^36 + (1873495/2048)*x^34 + (350343565/114688)*x^32 + (197466373/32768)*x^30 + (2202509545/294912)*x^28 + (3964517181/655360)*x^26 + (75792240225/23068672)*x^24 + (10194277925/8388608)*x^22 + (5175556485/16777216)*x^20 + (25264080075/469762048)*x^18 + (17179574451/2684354560)*x^16 + (2202509545/4294967296)*x^14 + (58078345/2147483648)*x^12 + (70068713/77309411328)*x^10 + (5028855/274877906944)*x^8 + (1124097/5497558138880)*x^6 + (50635/46179488366592)*x^4 + (205/96757023244288)*x^2 + (1/1618481116086272) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 4 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_6 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 6 x = (1/257701752)*x^48 + (41/1024)*x^40 + (533/256)*x^38 + (374699/12288)*x^36 + (5620485/28672)*x^34 + (350343565/524288)*x^32 + (197466373/147456)*x^30 + (440501909/262144)*x^28 + (3964517181/2883584)*x^26 + (25264080075/33554432)*x^24 + (2352525675/8388608)*x^22 + (67282234305/939524096)*x^20 + (1684272005/134217728)*x^18 + (51538723353/34359738368)*x^16 + (129559385/1073741824)*x^14 + (987331865/154618822656)*x^12 + (3687827/17179869184)*x^10 + (19109649/4398046511104)*x^8 + (374699/7696581394432)*x^6 + (50635/193514046488576)*x^4 + (205/404620279021568)*x^2 + (1/6755399441055744) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 6 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_8 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 8 x = (1/11274451650)*x^50 + (41/5120)*x^40 + (2665/6144)*x^38 + (374699/57344)*x^36 + (5620485/131072)*x^34 + (350343565/2359296)*x^32 + (197466373/655360)*x^30 + (2202509545/5767168)*x^28 + (1321505727/4194304)*x^26 + (5830172325/33554432)*x^24 + (30582833775/469762048)*x^22 + (4485482287/268435456)*x^20 + (25264080075/8589934592)*x^18 + (3031689609/8589934592)*x^16 + (2202509545/77309411328)*x^14 + (51964835/34359738368)*x^12 + (70068713/1374389534720)*x^10 + (31849415/30786325577728)*x^8 + (1124097/96757023244288)*x^6 + (50635/809240558043136)*x^4 + (205/1688849860263936)*x^2 + (1/28147497671065600) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 8 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
theorem atom_41_10 (x : ℝ) (hx : |x| ≤ 1/2) :
    atomInt 41 10 x = (1/332220508620)*x^52 + (41/24576)*x^40 + (2665/28672)*x^38 + (374699/262144)*x^36 + (1873495/196608)*x^34 + (70068713/2097152)*x^32 + (197466373/2883584)*x^30 + (2202509545/25165824)*x^28 + (3964517181/54525952)*x^26 + (75792240225/1879048192)*x^24 + (2038855585/134217728)*x^22 + (67282234305/17179869184)*x^20 + (25264080075/36507222016)*x^18 + (5726524817/68719476736)*x^16 + (115921555/17179869184)*x^14 + (197466373/549755813888)*x^12 + (70068713/5772436045824)*x^10 + (95548245/387028092977152)*x^8 + (1124097/404620279021568)*x^6 + (50635/3377699720527872)*x^4 + (41/1407374883553280)*x^2 + (1/117093590311632896) := by
  rw [atomInt, AristotleO.integral_abs_pow_mul_pow 41 10 x hx]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

end ZetaLean.Pub1