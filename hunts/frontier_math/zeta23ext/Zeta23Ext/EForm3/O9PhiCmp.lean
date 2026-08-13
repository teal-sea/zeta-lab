import Zeta23Ext.EForm3.O9Comp
import Zeta23Ext.EForm3.O9Damage

/-!
# Does `phiC`'s real part already equal `qreIv`?

The seam `qreIv_mem` is only worth proving if `qreIv` is the composition O9 must
use. `BandDual.phiC` already has a proved `_mem` lemma, so if its real part
produces the *same integers* as `qreIv`, the seam collapses to one line and no
new soundness proof is needed at all.

That is the question these `#eval`s answer. `phiC` is evaluated on the same
boxes as `O9CompEval.lean`, with the same `sinh`/`cosh` leaves the O9
composition builds internally, so the only difference under test is
component-wise real division against `CIv.div`.

Nothing here is a proof. It is an experiment to decide which arithmetic O9
should be built on, before any lemma is written against either.
-/

open BandDual Retention

/-- `phiC` over a box, with the hyperbolic leaves taken the way `boxParts`
takes them, so the comparison isolates the division. -/
def phiCBox (sLo sHi yLo yHi : ℤ) : CIv :=
  let X : EIv := some ⟨sLo, sHi⟩
  let Y : EIv := some ⟨yLo, yHi⟩
  let hc := sinhCoshSmall (EIv.divInt Y 2)
  phiC X Y hc.1 hc.2

-- s in [5.6, 5.83], y in [0, 0.25]
#eval (phiCBox 103275952565021900800 107517428211175260160 0 4611686018427387904).1
#eval qreIv 103275952565021900800 107517428211175260160 0 4611686018427387904

-- s in [6.1, 6.2], y in [0.375, 0.5]
#eval (phiCBox 112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808).1
#eval qreIv 112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808

-- s in [30, 30.1], y in [0, 0.125]
#eval (phiCBox 553402322211286548480 555246933107921076224 0 2305843009213693952).1
#eval qreIv 553402322211286548480 555246933107921076224 0 2305843009213693952

-- and the imaginary parts, which is where R would come from
#eval (phiCBox 112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808).2
#eval rIv 112533895920948609024 114378506817583136768 6917529027641081856 9223372036854775808
