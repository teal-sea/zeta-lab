/-
  Local mirror of the file riemannzeta.fun GENERATES for a submission, from
  challenge/templates/CandidateSpec.lean.tmpl in josusanmartin/riemann:

      import ChallengeDeps
      def currentRecordKappa : ℝ := {{CURRENT_EXPRESSION}}
      def candidateKappa : ℝ := ({{NUMERATOR}} : ℝ) / {{DENOMINATOR}}

  with CURRENT_EXPRESSION = "2 - 1 / cMT" per challenge/contract.json.

  ASSUMPTION UNDER TEST, and the one thing this mirror cannot verify: that the
  site's `cMT` is the Montgomery-Taylor constant `Zeta23.ThmD.cStar 1`. No `cMT`
  exists anywhere in the pinned zeta-23-lean tree, so it is defined inside their
  ChallengeDeps and is not readable from outside. If their `cMT` is something
  else, `candidate_strict_improvement` is the only theorem affected.
-/
import Zeta23.ThmD.Mult

noncomputable section
open Zeta23 Zeta23.ThmD

/-- The Montgomery-Taylor constant, as this mirror assumes the site defines it. -/
def cMT : ℝ := Zeta23.ThmD.cStar 1

/-- The currently accepted exact lower bound. -/
def currentRecordKappa : ℝ := 2 - 1 / cMT

/-- The candidate's exact rational lower bound. -/
def candidateKappa : ℝ := (672737 : ℝ) / 1000000

end
