# The axiom audit, pinned

`audit-v2-frozen.log` in this directory is the `#print axioms` output for the Palomar V2
surface, committed so that the claim does not rest on a log that expires.

## Why this file exists

Until 2026-08-31 the only evidence that the seven advertised declarations are kernel-checked
under standard axioms was the output of a GitHub Actions run. Actions logs age out of retention
in roughly ninety days. A paper whose central claim is faithfulness cannot cite an artifact that
is scheduled to be deleted, so the output is now in the commit record and a reader can check it
against the source without credentials and without a rebuild.

This does not replace rebuilding. It records what one build printed, and a build is the only
thing that can establish the claim afresh. What the file buys is that the claim stays
*checkable against a stated source* after the log is gone.

## Provenance

| Field | Value |
| --- | --- |
| Workflow run | `32803748017`, `three-point.yml`, conclusion `success` |
| Run URL | https://github.com/teal-sea/zeta-lab/actions/runs/32803748017 |
| Run date | 2026-08-25T03:03:58Z |
| Head commit | `d6ebb816393342e0e8f9d4b776b5e2507be9d2a8` |
| `lean/bridge` tree at that commit | `858418471411ab49f26e463968eeb67ab6b92b00` |

That tree hash is the point of choosing this run over a later one. It is byte-identical to the
tree at `84312e4477dfeb7e0d8a91c38897f225f5a52f19`, the frozen commit the Palomar Registry
fetched and replayed and the reproducibility boundary for every Lean claim in the Pub 2
manuscript. Confirm with:

```bash
git rev-parse 84312e44:lean/bridge d6ebb816:lean/bridge   # same hash
```

A later successful run, `33217377329` of 2026-08-28, audits the same seven declarations to the
same axioms over a moved tree (`692dd279…`). It is the more recent evidence and the weaker
citation, because its tree is not the frozen one.

## What the log contains

109 distinct declarations across the Bridge, ThreePoint, FourPoint and PalomarV2 modules, one
line each, deduplicated and sorted from the run's `audit.log`. Two facts are mechanical from the
file itself:

```bash
grep -c sorryAx audit-v2-frozen.log                          # 0
sed 's/.*depends on axioms: //' audit-v2-frozen.log | sort -u
# [propext, choice, Quot.sound]
# [propext, Classical.choice, Quot.sound]
```

Nothing depends on `sorryAx`, so no `sorry` in `V2Challenge.lean` reached a proved statement.
The two axiom sets are the same three axioms; Lean prints `Classical.choice` short as `choice`
in some contexts. They are exactly the `permitted_axioms` of `comparator-v2.json`.

The seven advertised declarations are the ones named in `comparator-v2.json`:
`n_point_bound`, `eight_point_bound`, `eight_point_bound_ratio`, `three_point_bound`,
`three_point_bound_ratio`, `four_point_bound`, `four_point_bound_ratio`.

## What this does not establish

A clean axiom audit says the kernel accepted the proofs under standard axioms. It says nothing
about whether a statement means what its name suggests, which is the faithfulness question that
Appendix A of the manuscript addresses by printing the statements. And it does not make
`eight_point_bound` unconditional: that declaration carries its certificate as a named
hypothesis, and a hypothesis costs no axiom. Its grade is unchanged by anything in this file.

Regenerate for a newer run with:

```bash
gh run view <run-id> --log | grep "depends on axioms" | sed 's/^.*info: //' \
  | grep -v "^three- and four" | sort -u > lean/bridge/audit-v2-frozen.log
```
