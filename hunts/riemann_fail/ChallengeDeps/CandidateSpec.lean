/-
  Faithful local copy of the file riemannzeta.fun generates per submission from
  challenge/templates/CandidateSpec.lean.tmpl (josusanmartin/riemann), with
  CURRENT_EXPRESSION = "2 - 1 / cMT" per challenge/contract.json and this
  submission's numerator and denominator.

  It is placed at comparator/ChallengeDeps/CandidateSpec.lean inside the pinned
  Zeta23 checkout, which is where scripts/prepare-candidate.ts writes it and
  where Zeta23's own `ChallengeDeps` lean_lib (srcDir = "comparator") resolves
  the module. `cMT` is the dependency's comparator constant, not ours.
-/
import ChallengeDeps

noncomputable section

/-- The currently accepted exact lower bound. -/
def currentRecordKappa : ℝ := 2 - 1 / cMT

/-- The candidate's exact rational lower bound. -/
def candidateKappa : ℝ := (672737 : ℝ) / 1000000

end
