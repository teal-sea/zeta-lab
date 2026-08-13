import Zeta23Ext.EForm3.O9Data
import Zeta23Ext.EForm3.O9Damage

/-!
# Running the O9 checker

`o9Walk` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Re-evaluate `phiC` on a cell and compare with its recorded target. -/
def o9Cell (c : O9Cell) : Bool :=
  match damageIv c.lo c.hi with
  | none => false
  | some d => decide (d.hi ≤ c.target)

def o9Walk : List O9Cell → Bool
  | [] => true
  | c :: cs => o9Cell c && o9Walk cs

theorem o9_chunk0 : o9Walk (o9cells.drop 0 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk1 : o9Walk (o9cells.drop 40 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk2 : o9Walk (o9cells.drop 80 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk3 : o9Walk (o9cells.drop 120 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk4 : o9Walk (o9cells.drop 160 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk5 : o9Walk (o9cells.drop 200 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk6 : o9Walk (o9cells.drop 240 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk7 : o9Walk (o9cells.drop 280 |>.take 40) = true := by
  decide +kernel
theorem o9_chunk8 : o9Walk (o9cells.drop 320 |>.take 40) = true := by
  decide +kernel

end Retention
