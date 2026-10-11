import ZetaLean.IntervalCExp

/-! Measurement, not part of the proof (`RUNS.md`, run `decide-one-term`): can the kernel
read one term box `m^(-s)` at `s = 1/2 + 14.13i` by `decide +kernel`? It can, in seconds. -/
open ZetaLean ZetaLean.ComplexInterval

def Sa : ComplexInterval := ComplexInterval.exact (1/2) (1413/100)

-- mirror value: m = 29 box at nLog 40, nExp 24, p 96, kE 8 has re within [-0.18, -0.17]?
#eval ((dirichletTermBox2 40 24 96 5 8 29 Sa).re.lo : Float)
#eval ((dirichletTermBox2 40 24 96 5 8 29 Sa).re.hi : Float)

set_option maxRecDepth 100000 in
theorem t29 : (dirichletTermBox2 40 24 96 5 8 29 Sa).re.hi < 1 := by decide +kernel
#print axioms t29
