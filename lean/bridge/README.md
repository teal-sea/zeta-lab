# Zeta23Bridge

Ainta's simple-zero argument, assembled in Lean 4 as a theorem about Mathlib's
`riemannZeta` and generalized to `n` points. The general theorem and the
eight-point instance retain a named certificate hypothesis. The three- and
four-point instances discharge their certificates inside Lean and are
unconditional.

The intended Palomar surface selects seven declarations through
`comparator-v2.json`: the general theorem, the conditional eight-point bound
and ratio, the unconditional three-point bound and ratio, and the unconditional
four-point bound and ratio.

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
| `FourPoint/`, `FourPoint.lean` | The four-point certificate: the finite inequality at `n = 4` proved in Lean, and the unconditional bound that follows. Zero `sorry`. |
| `BridgeChallenge.lean` | The earlier unregistered surface, over Mathlib alone. Four deliberate `sorry`s. |
| `BridgeSolution.lean` | The same four statements, proved from `Zeta23Ext.Bridge.Main`. |
| `V2Challenge.lean` | The intended surface's statements, over Mathlib alone. Seven deliberate `sorry`s. |
| `V2Solution.lean` | The same seven statements, proved from the bridge plus the three- and four-point certificate libraries. |
| `NOTICE` | Licence attribution for the one adapted file. |
| `assemble.sh` | `lake build` with the prebuilt Mathlib and `Zeta23` stores symlinked in. |

The mathematics, the step table, the hypotheses and what each is believed on are
in `hunts/ainta_seven_point/BRIDGE.md`; the three-point certificate is in
`hunts/ainta_seven_point/THREE-POINT.md`, and the four-point certificate is in
`hunts/ainta_seven_point/FOUR-POINT.md`. The registry surfaces are described in
`lean/PALOMAR.md`. The eleven `sorry`s in `BridgeChallenge.lean` and
`V2Challenge.lean` are what the Palomar format requires of a statement-only
module, one per advertised statement; **do not "fix" them.**

```bash
bash lean/bridge/assemble.sh
# Build completed successfully (8860 jobs)
```
