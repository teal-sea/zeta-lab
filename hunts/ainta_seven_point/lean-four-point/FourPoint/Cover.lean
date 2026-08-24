import FourPoint.Cells

/-!
# The one-dimensional cover, at the level the adjacent-pair coefficient can pay for

The pair `(i, i+1)` of `F 4 p` carries `2/(4-1) = 2/3`, so a gap `x` closes the whole
certificate on its own exactly when `(2/3) w x ≥ c`, i.e. `w x ≥ 3c/2`.  This cover is
therefore run at `3c/2 = (693/200000:ℝ)`, not at `c`.
-/

noncomputable section
namespace Zeta23Ext.Bridge.FourPoint

/-- **The one-dimensional cover.**  Outside 4 short intervals around the low zeros of
the kernel, `w ≥ 3c/2` outright.  `[0,1/2]` is the window of `wfun_window`; the rest is
the table. -/
lemma cover1 (x : ℝ) (h0 : 0 ≤ x) (hS : x ≤ (231/40:ℝ)) :
    (693/200000:ℝ) ≤ wfun x ∨ ((63/64:ℝ) ≤ x ∧ x ≤ (73/64:ℝ)) ∨ ((121/64:ℝ) ≤ x ∧ x ≤ (141/64:ℝ)) ∨ ((179/64:ℝ) ≤ x ∧ x ≤ (105/32:ℝ)) ∨ ((237/64:ℝ) ≤ x ∧ x ≤ (231/40:ℝ)) := by
  rcases le_total x (1/2 : ℝ) with hw | hw
  · exact Or.inl (le_trans (by norm_num) (wfun_window x h0 hw))
  rcases le_total x (3/4:ℝ) with hz1 | hz1
  · exact Or.inl (le_trans (by norm_num) (wc_0 x (by linarith) (by linarith)))
  rcases le_total x (7/8:ℝ) with hz2 | hz2
  · exact Or.inl (le_trans (by norm_num) (wc_1 x (by linarith) (by linarith)))
  rcases le_total x (15/16:ℝ) with hz3 | hz3
  · exact Or.inl (le_trans (by norm_num) (wc_2 x (by linarith) (by linarith)))
  rcases le_total x (31/32:ℝ) with hz4 | hz4
  · exact Or.inl (le_trans (by norm_num) (wc_3 x (by linarith) (by linarith)))
  rcases le_total x (63/64:ℝ) with hz5 | hz5
  · exact Or.inl (le_trans (by norm_num) (wc_4 x (by linarith) (by linarith)))
  rcases le_total x (73/64:ℝ) with hz6 | hz6
  · exact Or.inr ((Or.inl ⟨by linarith, by linarith⟩))
  rcases le_total x (37/32:ℝ) with hz7 | hz7
  · exact Or.inl (le_trans (by norm_num) (wc_68 x (by linarith) (by linarith)))
  rcases le_total x (19/16:ℝ) with hz8 | hz8
  · exact Or.inl (le_trans (by norm_num) (wc_69 x (by linarith) (by linarith)))
  rcases le_total x (5/4:ℝ) with hz9 | hz9
  · exact Or.inl (le_trans (by norm_num) (wc_70 x (by linarith) (by linarith)))
  rcases le_total x (3/2:ℝ) with hz10 | hz10
  · exact Or.inl (le_trans (by norm_num) (wc_71 x (by linarith) (by linarith)))
  rcases le_total x (7/4:ℝ) with hz11 | hz11
  · exact Or.inl (le_trans (by norm_num) (wc_72 x (by linarith) (by linarith)))
  rcases le_total x (15/8:ℝ) with hz12 | hz12
  · exact Or.inl (le_trans (by norm_num) (wc_73 x (by linarith) (by linarith)))
  rcases le_total x (121/64:ℝ) with hz13 | hz13
  · exact Or.inl (le_trans (by norm_num) (wc_74 x (by linarith) (by linarith)))
  rcases le_total x (141/64:ℝ) with hz14 | hz14
  · exact Or.inr (Or.inr ((Or.inl ⟨by linarith, by linarith⟩)))
  rcases le_total x (71/32:ℝ) with hz15 | hz15
  · exact Or.inl (le_trans (by norm_num) (wc_180 x (by linarith) (by linarith)))
  rcases le_total x (9/4:ℝ) with hz16 | hz16
  · exact Or.inl (le_trans (by norm_num) (wc_181 x (by linarith) (by linarith)))
  rcases le_total x (5/2:ℝ) with hz17 | hz17
  · exact Or.inl (le_trans (by norm_num) (wc_183 x (by linarith) (by linarith)))
  rcases le_total x (11/4:ℝ) with hz18 | hz18
  · exact Or.inl (le_trans (by norm_num) (wc_184 x (by linarith) (by linarith)))
  rcases le_total x (89/32:ℝ) with hz19 | hz19
  · exact Or.inl (le_trans (by norm_num) (wc_185 x (by linarith) (by linarith)))
  rcases le_total x (179/64:ℝ) with hz20 | hz20
  · exact Or.inl (le_trans (by norm_num) (wc_186 x (by linarith) (by linarith)))
  rcases le_total x (105/32:ℝ) with hz21 | hz21
  · exact Or.inr (Or.inr (Or.inr ((Or.inl ⟨by linarith, by linarith⟩))))
  rcases le_total x (421/128:ℝ) with hz22 | hz22
  · exact Or.inl (le_trans (by norm_num) (wc_394 x (by linarith) (by linarith)))
  rcases le_total x (211/64:ℝ) with hz23 | hz23
  · exact Or.inl (le_trans (by norm_num) (wc_395 x (by linarith) (by linarith)))
  rcases le_total x (53/16:ℝ) with hz24 | hz24
  · exact Or.inl (le_trans (by norm_num) (wc_396 x (by linarith) (by linarith)))
  rcases le_total x (27/8:ℝ) with hz25 | hz25
  · exact Or.inl (le_trans (by norm_num) (wc_397 x (by linarith) (by linarith)))
  rcases le_total x (7/2:ℝ) with hz26 | hz26
  · exact Or.inl (le_trans (by norm_num) (wc_398 x (by linarith) (by linarith)))
  rcases le_total x (29/8:ℝ) with hz27 | hz27
  · exact Or.inl (le_trans (by norm_num) (wc_399 x (by linarith) (by linarith)))
  rcases le_total x (59/16:ℝ) with hz28 | hz28
  · exact Or.inl (le_trans (by norm_num) (wc_400 x (by linarith) (by linarith)))
  rcases le_total x (237/64:ℝ) with hz29 | hz29
  · exact Or.inl (le_trans (by norm_num) (wc_401 x (by linarith) (by linarith)))
  have hz30 : x ≤ (231/40:ℝ) := hS
  exact Or.inr (Or.inr (Or.inr (Or.inr (⟨by linarith, by linarith⟩))))

end Zeta23Ext.Bridge.FourPoint
