import Zeta23Ext.EForm3.O9Data2

/-!
# Running the two-variable O9 checker

`o9Walk2` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Check one leaf: `y^2 (R^2 - cap) <= Qre^2`. -/
def o9Cell2 (c : O9Cell2) : Bool :=
  match o9Field c.slo c.shi c.ylo c.yhi with
  | none => false
  | some f =>
      match EIv.mul (EIv.sub (EIv.sqr f.R) (some ⟨c.cap, c.cap⟩)) (EIv.sqr f.Y),
            EIv.sqr f.Qre with
      | some l, some r => decide (l.hi ≤ r.lo)
      | _, _ => false

def o9Walk2 : List O9Cell2 → Bool
  | [] => true
  | c :: cs => o9Cell2 c && o9Walk2 cs

theorem o9_2_chunk0 : o9Walk2 (o9cells2.drop 0 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk1 : o9Walk2 (o9cells2.drop 40 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk2 : o9Walk2 (o9cells2.drop 80 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk3 : o9Walk2 (o9cells2.drop 120 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk4 : o9Walk2 (o9cells2.drop 160 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk5 : o9Walk2 (o9cells2.drop 200 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk6 : o9Walk2 (o9cells2.drop 240 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk7 : o9Walk2 (o9cells2.drop 280 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk8 : o9Walk2 (o9cells2.drop 320 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk9 : o9Walk2 (o9cells2.drop 360 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk10 : o9Walk2 (o9cells2.drop 400 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk11 : o9Walk2 (o9cells2.drop 440 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk12 : o9Walk2 (o9cells2.drop 480 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk13 : o9Walk2 (o9cells2.drop 520 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk14 : o9Walk2 (o9cells2.drop 560 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk15 : o9Walk2 (o9cells2.drop 600 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk16 : o9Walk2 (o9cells2.drop 640 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk17 : o9Walk2 (o9cells2.drop 680 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk18 : o9Walk2 (o9cells2.drop 720 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk19 : o9Walk2 (o9cells2.drop 760 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk20 : o9Walk2 (o9cells2.drop 800 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk21 : o9Walk2 (o9cells2.drop 840 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk22 : o9Walk2 (o9cells2.drop 880 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk23 : o9Walk2 (o9cells2.drop 920 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk24 : o9Walk2 (o9cells2.drop 960 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk25 : o9Walk2 (o9cells2.drop 1000 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk26 : o9Walk2 (o9cells2.drop 1040 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk27 : o9Walk2 (o9cells2.drop 1080 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk28 : o9Walk2 (o9cells2.drop 1120 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk29 : o9Walk2 (o9cells2.drop 1160 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk30 : o9Walk2 (o9cells2.drop 1200 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk31 : o9Walk2 (o9cells2.drop 1240 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk32 : o9Walk2 (o9cells2.drop 1280 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk33 : o9Walk2 (o9cells2.drop 1320 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk34 : o9Walk2 (o9cells2.drop 1360 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk35 : o9Walk2 (o9cells2.drop 1400 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk36 : o9Walk2 (o9cells2.drop 1440 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk37 : o9Walk2 (o9cells2.drop 1480 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk38 : o9Walk2 (o9cells2.drop 1520 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk39 : o9Walk2 (o9cells2.drop 1560 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk40 : o9Walk2 (o9cells2.drop 1600 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk41 : o9Walk2 (o9cells2.drop 1640 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk42 : o9Walk2 (o9cells2.drop 1680 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk43 : o9Walk2 (o9cells2.drop 1720 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk44 : o9Walk2 (o9cells2.drop 1760 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk45 : o9Walk2 (o9cells2.drop 1800 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk46 : o9Walk2 (o9cells2.drop 1840 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk47 : o9Walk2 (o9cells2.drop 1880 |>.take 40) = true := by
  decide +kernel
theorem o9_2_chunk48 : o9Walk2 (o9cells2.drop 1920 |>.take 40) = true := by
  decide +kernel

end Retention
