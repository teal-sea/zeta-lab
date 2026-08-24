# Mission: what the public field actually holds, and whether it collides with our barrier

> A field audit, not a search for a better constant. Two questions, in order:
> (1) where does this laboratory actually stand against the public claims for
> `liminf N0s(T,2T)/N(T,2T)`, and (2) does any of that public work live inside
> the `n`-point pressure family whose ceiling `family_wall` (Hunt #82) fixed at
> `0.675142509660254`, in which case one of the two results is wrong.

Occasioned by discovering, on 2026-08-24, a wave of public repositories created
2026-08-11 and 2026-08-12 — a week before this laboratory's own seven- and
eight-point work — carrying constants above ours. Our prior-art search had
found `ainta/zeta-simple-zeros` and `anthropics/zeta-23-lean` and stopped.

The audit is adversarial in both directions. If the public claims are sound we
must say we are behind, in plain words, and say by how much. If their verifiers
have the defect pattern we found in Ainta's, we must show it. And if any of
their constructions is a point of *our* family, the `family_wall` barrier and
their numbers cannot both stand.

```huntspec
id: field_audit
question: What is the true public state of the art for the simple-zero proportion, and does any public construction sit inside the n-point pressure family whose ceiling Hunt #82 fixed at 0.675142509660254?
frontier: this laboratory holds 0.6730529829896288 (eight-point, p=3200, c=41763/10^7, bridge proved in Lean) and 0.6730295534796928 (seven-point, p=3400, c=34697/10^7); the family ceiling is 0.675142509660254; the configuration ceiling is 0.6818286874638
proposed_attack: read the competing constructions against lean/bridge/Zeta23Ext/Bridge/Defs.lean definition by definition, then replay whichever finite inequality is cheap enough to replay on this host
dead_routes:
  - improving the constant by raising n inside the fixed Montgomery-Taylor window, which Hunt #82 showed turns over and returns to H
  - reading a claimed constant off a README and treating it as a result
required_oracles:
  - Arb interval arithmetic through python-flint, run on this host against the competitor's own source
  - exact rational arithmetic over the published weight and pressure data
  - repository metadata from the GitHub REST API, for dates and precedence
  - the vendored Lean definitions in lean/bridge/Zeta23Ext/Bridge/Defs.lean, for what our family is
kill_conditions:
  - a competitor construction is shown to be a point of our family and exceeds 0.675142509660254, in which case this audit withdraws nothing and Hunt #82 is withdrawn instead
  - a competitor's published candidate fails its own stated inequality when replayed here
  - the claimed ranking changes under a recount of the published digits
agents_may:
  - search
  - derive
  - code
  - attack
  - replay a competitor verifier on its own published data
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - post, comment, fork, star or open an issue on any repository not owned by this laboratory
```

## Scope, and what was deliberately not done

Read-only against every external repository. Nothing was posted, opened,
commented, starred or forked anywhere. One competitor repository was replayed
from a scratch clone using its own pinned dependency; the others were read.

No Lean was built (host constraint). No cloud compute was used.
