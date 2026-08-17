import Zeta23Ext.EForm3.O9Sound
import Zeta23Ext.EForm3.O9Shc
import Zeta23Ext.EForm3.O9Real
import Zeta23Ext.EForm3.O9Parts
import Zeta23Ext.EForm3.O9Num
import Zeta23Ext.EForm3.O9Assemble
import Zeta23Ext.EForm3.O9Comp
import Zeta23Ext.EForm3.O9CompEval
import Zeta23Ext.EForm3.O9RoundTrip
import Zeta23Ext.EForm3.O9PhiCmp
import Zeta23Ext.EForm3.ShcTaylor
import Zeta23Ext.EForm3.ShcBranch

/-!
# O9 axiom audit, and the reason this file exists at all

`TruncEst/Axioms.lean` is the model: one module that imports every file of a
chain, so `lake build` reaches all of them, and runs `#print axioms` over the
results.

**Why O9 needed one.** On 2026-08-13 the O9 development was built for the first
time, and `tests/test_zeta23ext_imports.py` reported **thirteen** modules that
nothing imported from `Zeta23Ext.lean`, the whole soundness chain among them.
`EForm3/Main.lean` imported `O9Check2`, so the *table* was re-decided by a
plain `lake build`, but every lemma establishing that the table says anything
about `Dam` was invisible to it. Those files had been built by hand, once, and
nothing afterwards would have noticed them rotting.

That is the same defect, in the same directory, that the morning's build found
in the 1-D route: `O9Check.lean` was orphaned *and* did not compile, and both
facts had gone unnoticed because no target reached it. The guard exists
because an orphan is worse than a build error, the package still reports
success.

The refuted 1-D route (`O9Data`, `O9Check`, `O9Damage`) is deleted rather than
wired in: the kernel refuted its table on 7 of 9 chunks, `O9Check2` supersedes
it, and a known-false artifact left in the tree is exactly what a later reader
mistakes for staged work.
-/

namespace Retention

-- The seams: what the table says about `Dam`.
#print axioms Retention.dam_zero_le
#print axioms Retention.dam_le_of_branch
#print axioms Retention.dam_le_of_mode1
#print axioms Retention.dam_le_of_mode2

-- The new leaf and its truncation bound.
#print axioms Retention.hornerR_sinhL_eq
#print axioms Retention.shc_trunc_le
#print axioms Retention.shcSmall_mem
#print axioms ShcTaylor.shc_taylor
#print axioms ShcBranch.shc_eq_tsum

-- The compositions and their enclosure lemmas.
#print axioms O9Real.re_div_eq
#print axioms O9Real.im_div_eq
#print axioms O9Real.im_div_over_y
#print axioms O9Seam.qre_comp_mem
#print axioms O9Seam.r_comp_mem
#print axioms O9Seam.qre_comp_mem'
#print axioms O9Seam.r_comp_mem'
#print axioms O9Seam.denAbs2_mem

-- The interval-level parts.
#print axioms Retention.reDen_mem
#print axioms Retention.imDenOverY_mem
#print axioms Retention.imDen_mem
#print axioms Retention.X_mem
#print axioms Retention.leaves_mem
#print axioms Retention.reNum_mem
#print axioms Retention.imNumOverY_mem
#print axioms Retention.imNum_mem
#print axioms Retention.denAbs2_mem

-- The compositions joined to the parts: the last structural step.
#print axioms Retention.qreIv_mem
#print axioms Retention.rIv_mem

-- The same two with every field hypothesis discharged. `rIv_mem_box` goes
-- through `r_comp_mem'`, not `r_comp_mem`: see its docstring.
#print axioms Retention.qreIv_mem_box
#print axioms Retention.rIv_mem_box

end Retention
