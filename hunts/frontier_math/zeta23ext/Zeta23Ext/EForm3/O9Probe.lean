import Zeta23Ext.EForm3.O9Field
import Zeta23Ext.EForm3.O9Data2

/-! Scratch: compare the kernel's leaves with the Python prediction. -/

namespace Retention
open BandDual

/-- Width of an `EIv`, in ulp, or `-1` for `none`. -/
def wid : EIv → Int
  | none => -1
  | some a => a.hi - a.lo

def c0 : O9Cell2 := (o9cells2.take 1).headD ⟨0,0,0,0,0⟩

#eval (c0.slo, c0.shi, c0.ylo, c0.yhi, c0.cap)

-- the individual leaves on that cell
#eval let X : EIv := some ⟨c0.slo, c0.shi⟩
      wid (sinCosIv (EIv.divInt X 2)).1
#eval let X : EIv := some ⟨c0.slo, c0.shi⟩
      wid (sinCosIv (EIv.divInt X 2)).2
#eval let Y : EIv := some ⟨c0.ylo, c0.yhi⟩
      wid (sinhCoshSmall (EIv.divInt Y 2)).1
#eval let Y : EIv := some ⟨c0.ylo, c0.yhi⟩
      wid (shfnIv Y)
#eval let Y : EIv := some ⟨c0.ylo, c0.yhi⟩
      (shfnIv Y)

-- the field itself
#eval match o9Field c0.slo c0.shi c0.ylo c0.yhi with
      | none => "FIELD IS NONE"
      | some f => s!"R={wid f.R} Qre={wid f.Qre}"

#eval match o9Field c0.slo c0.shi c0.ylo c0.yhi with
      | none => (0, 0)
      | some f => match f.R with | none => (0,0) | some a => (a.lo, a.hi)

end Retention
