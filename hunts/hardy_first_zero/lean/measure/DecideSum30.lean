import ZetaLean.IntervalCExp

/-! Measurement, not part of the proof (`RUNS.md`, run `decide-sum30`): one `decide +kernel`
over the recursive 29-term box sum at both endpoints. Stopped unfinished after 30 minutes
(29 min of CPU). `Boxes.lean` replaces it with 60 per-term literal checks, 2 min 48 s in all.
The recursion's `Nat.log2` and the unshared sum are the suspects; neither was isolated. -/
open ZetaLean ZetaLean.ComplexInterval

def Sa : ComplexInterval := ComplexInterval.exact (1/2) (1413/100)
def Sb : ComplexInterval := ComplexInterval.exact (1/2) (707/50)

/-- sum of m^{-s} boxes for m = 2 .. N-1, plus 1 -/
def sumBox (S : ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | 1 => ComplexInterval.exact 1 0
  | m + 1 => (sumBox S m).add (dirichletTermBox2 40 24 96 (Nat.log2 m + 1) 8 m S)

#eval ((sumBox Sa 30).re.lo : Float)
#eval ((sumBox Sa 30).re.hi : Float)

set_option maxRecDepth 100000 in
theorem tsum30 : (sumBox Sa 30).re.hi < 10 ∧ (sumBox Sb 30).re.hi < 10 := by decide +kernel
