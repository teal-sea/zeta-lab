import Zeta23Ext.EForm3.O9Data2
import Zeta23Ext.EForm3.O9Comp

/-!
# Running the two-dimensional O9 checker

`o9Walk2` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.

`rIv`, `qreIv` and `sqrScaled` come from `O9Comp.lean`, whose integers are
pinned against this generator's own composition by
`tests/test_o9_leaves_kernel.py`.  A green `decide +kernel` here says the
recorded table is consistent with the kernel's arithmetic; it does **not** yet
say anything about `Dam`, because the `_mem` seam lemmas are not written.  The
two claims are different and the difference is the point.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Re-evaluate the box and check whichever test it claims. -/
def o9Box (b : O9Box) : Bool :=
  match rIv b.sLo b.sHi b.yLo b.yHi, qreIv b.sLo b.sHi b.yLo b.yHi with
  | some r, some q =>
      let excess := (EIv.sqr (some r)).sub (some ⟨b.cap, b.cap⟩)
      match excess with
      | none => false
      | some e =>
        if b.mode = 1 then decide (e.hi ≤ 0)
        else
          match EIv.mul (EIv.sqrScaled b.yHi) (some ⟨e.hi, e.hi⟩),
                EIv.sqr (some q) with
          | some l, some q2 => decide (l.hi ≤ q2.lo)
          | _, _ => false
  | _, _ => false

def o9Walk2 : List O9Box → Bool
  | [] => true
  | b :: bs => o9Box b && o9Walk2 bs

theorem o9_box_chunk0 : o9Walk2 (o9boxes.drop 0 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk1 : o9Walk2 (o9boxes.drop 40 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk2 : o9Walk2 (o9boxes.drop 80 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk3 : o9Walk2 (o9boxes.drop 120 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk4 : o9Walk2 (o9boxes.drop 160 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk5 : o9Walk2 (o9boxes.drop 200 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk6 : o9Walk2 (o9boxes.drop 240 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk7 : o9Walk2 (o9boxes.drop 280 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk8 : o9Walk2 (o9boxes.drop 320 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk9 : o9Walk2 (o9boxes.drop 360 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk10 : o9Walk2 (o9boxes.drop 400 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk11 : o9Walk2 (o9boxes.drop 440 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk12 : o9Walk2 (o9boxes.drop 480 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk13 : o9Walk2 (o9boxes.drop 520 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk14 : o9Walk2 (o9boxes.drop 560 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk15 : o9Walk2 (o9boxes.drop 600 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk16 : o9Walk2 (o9boxes.drop 640 |>.take 40) = true := by
  decide +kernel
theorem o9_box_chunk17 : o9Walk2 (o9boxes.drop 680 |>.take 40) = true := by
  decide +kernel

end Retention
