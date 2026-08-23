# Zeta23Bridge

Ainta's seven-point simple-zero bound, assembled in Lean 4 as a theorem about
Mathlib's `riemannZeta` and **conditional on the seven-point inequality**, which
is a named hypothesis of every statement here and is not a Lean fact.

This is a Lake package of its own because the theorem depends on
`anthropics/zeta-23-lean` (pinned in `lake-manifest.json`), which the
laboratory's `lean/` package does not require, and because the Palomar Registry
replays the *selected project*: the theorem and its whole import closure have to
build at a package root, which they do here.

| Path | What it is |
| --- | --- |
| `Zeta23Ext.lean` | The root. Imports the whole development. Zero `sorry`. |
| `Zeta23Ext/StableRankTrace.lean` | S2, the stability rank-trace inequality. |
| `Zeta23Ext/Bridge/` | S6 to S16 and the assembled theorem, sixteen modules. |
| `BridgeChallenge.lean` | The advertised statements, over Mathlib alone. Four deliberate `sorry`s. |
| `BridgeSolution.lean` | The same four, proved from `Zeta23Ext.Bridge.Main`. |
| `NOTICE` | Licence attribution for the one adapted file. |
| `assemble.sh` | `lake build` with the prebuilt Mathlib and `Zeta23` stores symlinked in. |

The mathematics, the step table, the hypotheses and what each is believed on are
in `hunts/ainta_seven_point/BRIDGE.md`. The registry surface is described in
`lean/PALOMAR.md`. The four `sorry`s in `BridgeChallenge.lean` are what the
Palomar format requires of a statement-only module; **do not "fix" them.**

```bash
bash lean/bridge/assemble.sh
# Build completed successfully (8860 jobs)
```
