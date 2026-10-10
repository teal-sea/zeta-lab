module

public import Zeta23Ext.EForm.Basic
public import Zeta23Ext.EForm2.Defs
public import Zeta23Ext.EForm3.Defs

@[expose] public section

/-!
# The three retention arms define the same window, constant and autocorrelation

`EForm/`, `EForm2/` and `EForm3/` each define the window, `Aconst` and `c2`.
They once all did so in the bare namespace `Retention`, so the root could load
at most one of them (issue #24). The two legacy arms now live in
`Retention.EForm` and `Retention.EForm2`; `EForm3`, the live arm, keeps
`Retention`.

Scoping removes the collision, not the duplication. What this file adds is the
check that the duplication is not divergence: the three windows are the same
function, the three constants are the same number, and the three
autocorrelations are the same function, even though `EForm` writes
`∫ g u * g (u - w)` where the other two write `∫ g u * g (u + w)`. All but the
last hold by unfolding; the last needs the substitution `u ↦ u + w`.

Every statement names both sides by their full name. A declaration called
`EForm.foo` would open `Retention.EForm` inside its own statement, so a bare
`c2` there would mean `Retention.EForm.c2` and the statement would compare the
legacy definition with itself.

Nothing here is new mathematics, and the duplicated definitions are left as
they are: merging them would change the definitional form that the `unfold c2`
and `simp [c2]` steps in each arm were written against.
-/

open MeasureTheory

namespace Retention.ArmAgreement

theorem gker_eq : Retention.EForm.gker = Retention.g := rfl

theorem gwin_eq : Retention.EForm2.gwin = Retention.g := rfl

theorem aconst_eform_eq : Retention.EForm.Aconst = Retention.Aconst := rfl

theorem aconst_eform2_eq : Retention.EForm2.Aconst = Retention.Aconst := rfl

theorem c2_eform2_eq : Retention.EForm2.c2 = Retention.c2 := rfl

theorem c2_eform_eq : Retention.EForm.c2 = Retention.c2 := by
  funext w
  change (∫ u : ℝ, Retention.g u * Retention.g (u - w))
    = ∫ u : ℝ, Retention.g u * Retention.g (u + w)
  rw [← integral_add_right_eq_self (fun u : ℝ => Retention.g u * Retention.g (u - w)) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [add_sub_cancel_right]
  exact mul_comm _ _

end Retention.ArmAgreement

#print axioms Retention.ArmAgreement.gker_eq
#print axioms Retention.ArmAgreement.gwin_eq
#print axioms Retention.ArmAgreement.aconst_eform_eq
#print axioms Retention.ArmAgreement.aconst_eform2_eq
#print axioms Retention.ArmAgreement.c2_eform2_eq
#print axioms Retention.ArmAgreement.c2_eform_eq
