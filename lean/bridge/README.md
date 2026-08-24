# Zeta23Bridge

Ainta's simple-zero bound, assembled in Lean 4 as a theorem about Mathlib's
`riemannZeta`, **parametric in the number of points `n`** and **conditional on
the `n`-point inequality**, which is a named hypothesis of every statement here
and is not a Lean fact.

`Zeta23Ext.Bridge.n_point_bound` is the general theorem;
`seven_point_bound` (Ainta's Theorem 1.1, the statement the Palomar surface
advertises, unchanged) and `eight_point_bound` are its `n = 7` and `n = 8`
corollaries.

This is a Lake package of its own because the theorem depends on
`anthropics/zeta-23-lean` (pinned in `lake-manifest.json`), which the
laboratory's `lean/` package does not require, and because the Palomar Registry
replays the *selected project*: the theorem and its whole import closure have to
build at a package root, which they do here.

| Path | What it is |
| --- | --- |
| `Zeta23Ext.lean` | The root. Imports the whole development. Zero `sorry`. |
| `Zeta23Ext/StableRankTrace.lean` | S2, the stability rank-trace inequality. |
| `Zeta23Ext/Bridge/` | S6 to S16 and the assembled theorem, sixteen modules, parametric in `n`. |
| `ThreePoint/`, `ThreePoint.lean` | The three-point certificate: the finite inequality at `n = 3` proved in Lean, and the unconditional bound that follows. Zero `sorry`. |
| `BridgeChallenge.lean` | V1's advertised statements, over Mathlib alone. Four deliberate `sorry`s. |
| `BridgeSolution.lean` | The same four, proved from `Zeta23Ext.Bridge.Main`. |
| `V2Challenge.lean` | V2's advertised statements, over Mathlib alone. Five deliberate `sorry`s. |
| `V2Solution.lean` | The same five, proved from `Zeta23Ext.Bridge.Main` and `ThreePoint.Main`. |
| `NOTICE` | Licence attribution for the one adapted file. |
| `assemble.sh` | `lake build` with the prebuilt Mathlib and `Zeta23` stores symlinked in. |

The mathematics, the step table, the hypotheses and what each is believed on are
in `hunts/ainta_seven_point/BRIDGE.md`; the three-point certificate is in
`hunts/ainta_seven_point/THREE-POINT.md`. The registry surfaces are described in
`lean/PALOMAR.md`. The nine `sorry`s in `BridgeChallenge.lean` and
`V2Challenge.lean` are what the Palomar format requires of a statement-only
module, one per advertised statement; **do not "fix" them.**

```bash
bash lean/bridge/assemble.sh
# Build completed successfully (8860 jobs)
```
