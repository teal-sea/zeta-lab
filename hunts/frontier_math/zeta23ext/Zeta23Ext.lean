import Zeta23Ext.Composition
import Zeta23Ext.GridIncidence
import Zeta23Ext.Bridge
import Zeta23Ext.RetentionAlgebra
import Zeta23Ext.RetentionWired
import Zeta23Ext.FloorCert
import Zeta23Ext.BandCert.Main
import Zeta23Ext.PairEnergy
import Zeta23Ext.EForm.Main
import Zeta23Ext.EForm2.Main
import Zeta23Ext.EForm3.Main
import Zeta23Ext.EForm3.Refutation
-- `TruncEst.Axioms` is that chain's audit aggregator: it imports every
-- TruncEst module and runs `#print axioms` over the development. Importing it
-- (rather than `TruncEst.Sums` alone) is what makes the audit actually run.
import Zeta23Ext.TruncEst.Axioms

-- O9 as a two-variable table: the field and its `sinh(u/2)/u` leaf
-- (`O9Field`), the soundness identities tying it to `Phi2` (`O9Sound`), and
-- the recorded leaves with their `decide +kernel` walk (`O9Check2`, which
-- imports `O9Data2`).  `O9Check2` costs ~210 s of kernel reduction; it is
-- imported rather than left orphaned because a table nothing builds is a
-- table that rots, which is what `test_zeta23ext_imports` exists to catch.
import Zeta23Ext.EForm3.O9Sound
import Zeta23Ext.EForm3.O9Check2
