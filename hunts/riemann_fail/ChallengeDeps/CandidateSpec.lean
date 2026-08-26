/-
  Local mirror of the file riemannzeta.fun generates per submission from
  challenge/templates/CandidateSpec.lean.tmpl, with CURRENT_EXPRESSION
  "2 - 1 / cMT" (challenge/contract.json) and this submission's p and q.

  `cMT` is defined inside their ChallengeDeps and appears nowhere in the pinned
  zeta-23-lean tree, so it cannot be mirrored faithfully. Their expression
  2 - 1/cMT is the Montgomery-Taylor constant, which upstream is
  `Zeta23.ThmD.HD 1 = 2 - 1 / cStar 1` by the definition of `HD`. This mirror
  therefore writes `HD 1` directly: it tests everything in the submission
  except the identity of `cMT`, which no local build can settle.
-/
import Zeta23.ThmD.Mult

noncomputable section

/-- The currently accepted exact lower bound. -/
def currentRecordKappa : ℝ := Zeta23.ThmD.HD 1

/-- The candidate's exact rational lower bound. -/
def candidateKappa : ℝ := (672737 : ℝ) / 1000000

end
