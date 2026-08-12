import RequestProject.Data

/-!
# Running the checker on the recorded certificate

Each depth is discharged in three kernel chunks: the walk over `(0, G]`
(negativity cells and band cells), the `ω`-cover, and the scalar arithmetic.
-/

namespace BandDual

set_option maxRecDepth 100000

theorem dep0_chain : chainOK dep0 0 dep0.segs dep0.bands = true := by decide +kernel
theorem dep0_omg : omgOK dep0.K 0 dep0.ocells dep0.w = true := by decide +kernel
theorem dep0_rest : (basicOK dep0 && bandsOK dep0 && arithOK dep0) = true := by decide +kernel

theorem dep1_chain : chainOK dep1 0 dep1.segs dep1.bands = true := by decide +kernel
theorem dep1_omg : omgOK dep1.K 0 dep1.ocells dep1.w = true := by decide +kernel
theorem dep1_rest : (basicOK dep1 && bandsOK dep1 && arithOK dep1) = true := by decide +kernel

theorem dep2_chain : chainOK dep2 0 dep2.segs dep2.bands = true := by decide +kernel
theorem dep2_omg : omgOK dep2.K 0 dep2.ocells dep2.w = true := by decide +kernel
theorem dep2_rest : (basicOK dep2 && bandsOK dep2 && arithOK dep2) = true := by decide +kernel

theorem dep3_chain : chainOK dep3 0 dep3.segs dep3.bands = true := by decide +kernel
theorem dep3_omg : omgOK dep3.K 0 dep3.ocells dep3.w = true := by decide +kernel
theorem dep3_rest : (basicOK dep3 && bandsOK dep3 && arithOK dep3) = true := by decide +kernel

theorem depOK_of_parts {d : Dep}
    (h1 : chainOK d 0 d.segs d.bands = true) (h2 : omgOK d.K 0 d.ocells d.w = true)
    (h3 : (basicOK d && bandsOK d && arithOK d) = true) : depOK d = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true] at h3
  simp [depOK, h1, h2, h3.1.1, h3.1.2, h3.2]

theorem dep0_ok : depOK dep0 = true := depOK_of_parts dep0_chain dep0_omg dep0_rest
theorem dep1_ok : depOK dep1 = true := depOK_of_parts dep1_chain dep1_omg dep1_rest
theorem dep2_ok : depOK dep2 = true := depOK_of_parts dep2_chain dep2_omg dep2_rest
theorem dep3_ok : depOK dep3 = true := depOK_of_parts dep3_chain dep3_omg dep3_rest

/-- The certificate checks at every recorded depth. -/
theorem band_dual_closes : ∀ d ∈ cert, depOK d = true := by
  intro d hd
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact dep0_ok
  · exact dep1_ok
  · exact dep2_ok
  · exact dep3_ok

end BandDual
