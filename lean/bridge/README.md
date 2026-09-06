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

## Relation to the public field

Two published constants for this quantity are larger than either unconditional
instance proved here. That is not an oversight, it is the point of the
submission, so the comparison is set out in full.

| Source | `c` | `m` | `p` | Constant | The finite inequality | The passage to a proportion of zeros |
| --- | --- | --- | --- | --- | --- | --- |
| Anthropic, Theorem D (`arXiv:2608.13637`) |, |, |, | `0.67250070367941164573…` | not used | Lean |
| Ainta, Theorem 1.1 | `19/5000` | 269 | 3000 | `0.6730085279277797613…` | interval search | informal |
| Gohms, [issue #1](https://github.com/ainta/zeta-simple-zeros/issues/1) | `191/50000` | 267 | 3000 | `0.6730213619501665…` | interval search | informal |
| here, `three_point_bound` | `1345/10^6` | 745 | 3000 | `0.67273733450380945032…` | **proved in Lean** | **Lean** |
| here, `four_point_bound` | `2310/10^6` | 435 | 2500 | `0.67284701976668882760…` | **proved in Lean** | **Lean** |
| here, `eight_point_bound` | `41763/10^7` | 246 | 3200 | `0.67305298298962888…` | interval search, *carried as the hypothesis `hCert`* | **Lean** |

Read the last two columns rather than the constant. Ainta's and Gohms's figures
rest on an interval-arithmetic program accepting a finite inequality, and on an
informal argument carrying that inequality to a statement about zeros; the Gohms
issue describes its own result as provisional, not peer-reviewed and not
formally verified. Neither step is a theorem about `riemannZeta`. This package
machine-checks the second step for every `n`, and at `n = 3` and `n = 4` proves
the first step too, which is why those two instances need no certificate and no
hypothesis, and why their constants are smaller. The largest constant in the
table is `eight_point_bound`, and it is the one deliberately left conditional,
with `hCert` and its numbers written into the statement.

Both outside runs were reproduced at the pinned commit `040c5e8`, a defect in
the shared verifier's compactification prune was found and reported, and both
targets were re-run with the cutoff derived from the target; every published
claim survived. That report, the family's measured ceiling of `0.673029553` at
`p = 3400`, and the eight-point figure were posted publicly on 2026-08-23 on the
issue linked above. The audit is in `hunts/ainta_seven_point/TRUST-MAP.md`,
section 5.1 for the defect.

No novelty is claimed for the `n`-point generalization: no prior formalization
of it is known here, and no systematic search has been done that would establish
that none exists.

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
