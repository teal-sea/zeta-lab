# Hunt #77: where the seven-point simple-zero certificate ends

Two outside groups are hill-climbing the same finite certificate for the proportion of
simple zeros on the critical line: Ainta (`ainta/zeta-simple-zeros`, a GPT-5.6 Sol
research draft with an Arb verifier, 2026-08-11) at `F6 >= 19/5000`, and Gohms (issue #1
on that repository, a ChatGPT campaign, 2026-08-19) at `F6 >= 191/50000`. Neither has a
human reviewer and neither has a Lean line. This hunt does not join the climb. It
reproduces both certificates independently, locates the apparent floor of the functional
they are pushing against, and states how much of the room under Anthropic's configuration
ceiling this certificate family can ever extract.

The analytic bridge from `F6 >= c` to the asymptotic proportion is a separate trust
boundary and is NOT audited here. A companion session maps it (`TRUST-MAP.md`, pending).

```huntspec
id: ainta_seven_point
question: What is the largest value the seven-point certificate F6 >= c can reach, what configuration of six consecutive gaps attains the floor, and how much of the room between the 0.6725 window ceiling and the 0.68185 configuration ceiling does this certificate family leave unreachable?
frontier: window ceiling 0.6725007 (Anthropic Theorem D, Pub 1 strong closure); lab gap-census transplant 0.6725106958 (prior art, superseded); Ainta 19/5000 giving 0.6730085279 (reproduced here); Gohms 191/50000 giving 0.6730213620 (reported, reproduction in this hunt); configuration ceiling 0.68185 (Anthropic Remark 1.1)
proposed_attack: reproduce both certificates on the pinned commit; minimise F6 numerically to find the apparent floor and its argmin; probe certifiability of rational targets between the last claim and the floor with the published verifier at its published grid; reconstruct the map c -> bound from the two published data points
dead_routes:
  - pushing the seven-point target one decimal at a time, the remaining purse is of order 4e-6 in the bound
  - re-proposing the Cheer-Goldston gap-census floor transplant, prior art in hunts/rogue_frontier/FRONTIER_MAP.md
  - reaching past 0.68185 with any certificate reading only bandwidth-one data, excluded by Anthropic Remark 1.1
required_oracles:
  - the published Arb interval verifier at commit 040c5e899e658aed7b56a2a87f501798fe10761d, run locally, compared field by field against its committed certificates
  - the published verifier run at modified rational targets, which fails loudly at a terminal cell when a target is not certifiable at its grid
  - exact rational arithmetic on the published bound formula checked against both published constants to the last binary64 digit
kill_conditions:
  - a published certificate does not reproduce field for field on the pinned commit
  - a rational target strictly above the apparent float floor is accepted by the verifier, which would mean the float minimiser missed the true minimum
  - the reconstructed map c -> bound fails to reproduce a published constant exactly
  - the bridge map finds the bound formula depends on the certificate in a way that changes the ceiling by more than the headroom
agents_may:
  - run the published verifier and record every field
  - minimise the functional numerically and report the result as apparent, not rigorous
  - reconstruct the bound formula from published data and label it inferred
  - draft a reproducibility report to the upstream author for the owner to post
agents_may_not:
  - declare the seven-point theorem verified, only its finite certificates are
  - declare novelty for the ceiling, Anthropic Remark 1.1 already bounds the family from above
  - promote the apparent floor to a rigorous one without an interval certificate of the minimum
  - post to the upstream repository
  - touch the analytic bridge, which belongs to TRUST-MAP.md
```

Related: `hunts/rogue_frontier/FRONTIER_MAP.md` (Ainta first recorded at commit `bb8fa70`),
`lean/ZetaLean/Pub1/` (the window ceiling), `release-candidates/pub1-arxiv/arxiv_note.tex`
line 379 in the publication workspace (the note's own disclaimer that it says nothing
about configuration-coupled information, which is exactly what Ainta and Gohms use).
