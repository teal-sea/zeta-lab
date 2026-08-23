/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
SPDX-License-Identifier: MIT
-/
import Zeta23Ext.StableRankTrace
import Zeta23Ext.Bridge.Main

/-!
# The bridge package root

Every module of this package's development is imported above, so `lake build`
at the package root builds the whole thing.  That is the point of the package:
the theorem and its import closure have to assemble at a root, because the
Palomar Registry replays the *selected project*, not a module named by hand.

The two imports are the whole development:

* `Zeta23Ext.StableRankTrace` — S2, the stability rank-trace inequality, in
  both the trust map's form and the sharp form with no hypothesis on `V`.
* `Zeta23Ext.Bridge.Main` — S6 to S16 and the assembled theorem
  `Zeta23Ext.Bridge.n_point_bound`, parametric in the number of points `n`,
  with `seven_point_bound` (`n = 7`, the statement the Palomar surface
  advertises) and `eight_point_bound` (`n = 8`) as corollaries.  It imports
  every other module under `Zeta23Ext/Bridge/`.

Zero `sorry` in either.  The Palomar surface itself is the separate pair of
libraries `BridgeChallenge` and `BridgeSolution`; the Challenge carries the
four deliberate `sorry`s the format requires and is not part of this root.
-/
