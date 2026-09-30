# Stronger four-point Palomar submission packet

Staged September 29, 2026. Not submitted or registered.

## Fixed source snapshot

The proof, metadata and raw laboratory verification logs are already on
GitHub through [PR #262](https://github.com/teal-sea/zeta-lab/pull/262).
Use the fixed source commit below, not whichever commit is latest when this
packet is read. Adding this document does not change the selected snapshot.

```json
{
  "repository": "teal-sea/zeta-lab",
  "commit": "783307c8be59317375ae6675622b4d3019222875",
  "project_path": "hunts/ainta_seven_point/lean-four-point",
  "comparator_config_path": "hunts/ainta_seven_point/lean-four-point/comparator.json",
  "formalization_metadata_path": "hunts/ainta_seven_point/lean-four-point/formalization.yaml",
  "authorization_relationship": "maintainer"
}
```

This is a staged intake body, not a request already sent. The proposed
maintainer declaration refers to Thomas Lince as responsible maintainer of
the substantive Zeta Lab development. Confirm that declaration with the
owner before sending it.

Omit `existing_id`. The public repository index checked at staging lists
three registered surfaces, none at this project/comparator identity.
Recheck that identity before intake to avoid a duplicate submission.
Do not replace or revise the older registered four-point surface.

## Result and evidence

The selected declarations are
`Zeta23Ext.PalomarFourPoint.four_point_bound` and
`Zeta23Ext.PalomarFourPoint.four_point_bound_ratio`.
Their unconditional asymptotic coefficient is
`(14400000 H - 17240)/14366681`, with
`H = 3/2 - cot(1/sqrt(2))/sqrt(2)`, at parameters
`(n,c,m,p) = (4,2330/1000000,432,2500)`.
This is not RH or a claim to the largest published bound.
See [the preparation record](PALOMAR-READINESS.md) for the numerical
evaluation, provenance and exact scope.

- [Final assembly and interfaces](https://github.com/teal-sea/zeta-lab/actions/runs/36633942493): builds passed; the first comparator setup failed and is retained in the record.
- [Successful comparison](https://github.com/teal-sea/zeta-lab/actions/runs/36637271632): both statements matched; Lean, NanoDa and con-ron accepted the solution; matching and mismatch controls behaved as intended; all 645 source headers parsed as modules.
- [Numerical fast tier](https://github.com/teal-sea/zeta-lab/actions/runs/36641227947): 3179 passed, 3 skipped, 6 expected failures.
- Selected local preparation checks at the staged snapshot: 68 passed, 0 warnings, 0 failures.
- Raw build and comparison logs: [port-evidence](port-evidence/).

The selected snapshot has the same tree as PR head
`822a2aee59a0a8f8a7338a7795e730e4941af779`.
Lean sources, toolchain pins, manifests and comparator configuration are
unchanged from successful comparison source
`3ee65788397d0eed8c4743704492dae159cde521`.

The committed metadata preserves Ainta's argument, the Alpoge/Furman
foundation and anthropics/zeta-23-lean attribution. SamiYaya's separate
candidate is credited separately, not incorporated or claimed rebuilt.

## Next: full mechanical preflight

Palomar's [agent protocol](https://submit.palomar-registry.org/llms.txt)
requires its complete reusable workflow in `mode: full`, with a mechanical
report saying `status: pass`, before intake. The incremental laboratory
build and three-kernel comparison do not satisfy this separate gate.
**No full preflight was launched by staging this packet.**

The pinned workflow is
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@65f0154ed776cd26c224254aa57b379137f28b0d`.
Its `workflow_call` inputs are:

```json
{
  "repository": "teal-sea/zeta-lab",
  "commit": "783307c8be59317375ae6675622b4d3019222875",
  "pipeline_commit": "65f0154ed776cd26c224254aa57b379137f28b0d",
  "request_id": "zeta-four-point-2330-20260929",
  "mode": "full",
  "execution_profile": "palomar-standard-v1",
  "options": "{\"project_path\":\"hunts/ainta_seven_point/lean-four-point\",\"comparator_config_path\":\"hunts/ainta_seven_point/lean-four-point/comparator.json\",\"formalization_metadata_path\":\"hunts/ainta_seven_point/lean-four-point/formalization.yaml\",\"authorization_relationship\":\"maintainer\"}"
}
```

That upstream revision was current at staging. Recheck the protocol before
launching. Use a small caller workflow on an isolated branch, with the
workflow reference and `pipeline_commit` pinned identically. This packet
does not install that caller or schedule a job.

Run the expensive work on GitHub Actions, never a local Mac. Once dispatched,
the GitHub-hosted job continues without the launching computer. A local
agent or local polling command does not: record the public run URL so another
session can inspect it. Assign ownership of completion, retain the mechanical
report and resource results, and make any failure visible. Do not interpret
an OOM or timeout as a theorem failure or blindly repeat it.

## Intake and registration boundaries

After the full preflight passes, show the owner the exact intake body and
obtain agreement to send the proposed maintainer declaration. Follow the
documented tag-and-secret-gist API route, not automated browser sign-in.
Complete intake and verification in one sitting, then remove the temporary
ownership-proof tag and gist. No pending intake or access token exists for
this staged packet. Keep any subsequently returned access token private and
outside Git; it is needed to resume status and review access.

Registration requires a separate decision after the review is available.
Show the review and publication consequences before requesting authorization
to register. Do not turn a request to finish verification into permission to
publish an unread review permanently.

The final paragraphs of `scripts/palomar_stage.sh` still describe the old
V1/V2 bridge and an older capacity rule. Its selected paths and 68 local
checks were used here, not those generic paragraphs. Current intake rules
come from the protocol linked above.
