import Zeta23Ext.EForm3.O9Check2

/-!
# From eighteen decided chunks to the whole list

`O9Check2` proves `o9Walk2 (o9boxes.drop k |>.take 40) = true` for the eighteen
offsets `k = 0, 40, …, 680`. The per-box soundness statement quantifies over
`b ∈ o9boxes`, so the chunks have to be reassembled.

`BandCert/Verify.lean` does not help here: its `cert` has four entries and it
enumerates them with `List.mem_cons` and `rcases`. That is exactly why the O9
table is chunked instead — 699 boxes cannot be enumerated that way — so this
step is written rather than copied.

The route avoids a membership cover. `o9Walk2` distributes over `++`, and
`l.take n ++ l.drop n = l`, so a chunk pair reassembles by rewriting rather than
by locating each box in some chunk.
-/

namespace Retention

/-- `o9Walk2` distributes over append. -/
theorem o9Walk2_append (a b : List O9Box) :
    o9Walk2 (a ++ b) = (o9Walk2 a && o9Walk2 b) := by
  induction a with
  | nil => simp [o9Walk2]
  | cons x xs ih => simp [o9Walk2, ih, Bool.and_assoc]

/-- A list is decided as soon as a `take` and the matching `drop` are. -/
theorem o9Walk2_of_split {l : List O9Box} {n : ℕ}
    (h1 : o9Walk2 (l.take n) = true) (h2 : o9Walk2 (l.drop n) = true) :
    o9Walk2 l = true := by
  have := o9Walk2_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at this
  rw [this, h1, h2]
  rfl

/-- Deciding a list decides every box in it. -/
theorem o9Box_of_walk : ∀ {l : List O9Box}, o9Walk2 l = true → ∀ b ∈ l, o9Box b = true
  | [], _, _, hb => absurd hb (List.not_mem_nil)
  | x :: xs, h, b, hb => by
      rw [o9Walk2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact h.1
      · exact o9Box_of_walk h.2 b hmem

end Retention

#print axioms Retention.o9Walk2_append
#print axioms Retention.o9Walk2_of_split
#print axioms Retention.o9Box_of_walk
