module

public import Zeta23Ext.Composition
public import Zeta23Ext.GridIncidence
public import Zeta23Ext.Bridge
public import Zeta23Ext.RetentionAlgebra
public import Zeta23Ext.RetentionWired
public import Zeta23Ext.FloorCert
public import Zeta23Ext.BandCert.Main
public import Zeta23Ext.PairEnergy
-- `StableRankTrace` (S2) and `Bridge/` (S6-S16 and Ainta's seven-point
-- simple-zero bound, Hunt #79) moved to `lean/bridge/` on 2026-08-23: the
-- Palomar Registry replays the selected project, and this package does not
-- assemble at its root (#101), so the submitted theorem was split into a
-- package of its own that does. Nothing here imports them any more.
public import Zeta23Ext.EForm.Main
public import Zeta23Ext.EForm2.Main
public import Zeta23Ext.EForm3.Main
public import Zeta23Ext.EForm3.Refutation
-- `TruncEst.Axioms` is that chain's audit aggregator: it imports every
-- TruncEst module and runs `#print axioms` over the development. Importing it
-- (rather than `TruncEst.Sums` alone) is what makes the audit actually run.
public import Zeta23Ext.TruncEst.Axioms

@[expose] public section
