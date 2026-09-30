# Stronger four-point Palomar submission packet

Updated September 30, 2026. Resource repair awaiting full preflight; not submitted or registered.

## Fixed source snapshot

The proof, metadata and raw laboratory verification logs are already on
GitHub through [PR #262](https://github.com/teal-sea/zeta-lab/pull/262).
Use the fixed source commit below, not whichever commit is latest when this
packet is read. Adding this document does not change the selected snapshot.

```json
{
  "repository": "teal-sea/zeta-lab",
  "commit": "020a974f2c7153314f9dac8c0fe8a0f9d2dbd53b",
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

The original baseline `783307c8be59317375ae6675622b4d3019222875` has the same tree as PR head
`822a2aee59a0a8f8a7338a7795e730e4941af779`.
At that baseline, Lean sources, toolchain pins, manifests and comparator configuration are
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
The original full [run 36668540666](https://github.com/teal-sea/zeta-lab/actions/runs/36668540666)
ended with `provider.resource_exhausted` during `solution-build`: exit 137
and cgroup `oom-kill`, with peak memory 15,844,528,128 bytes. It did not pass.
Its [report, raw workflow log, and proof-body preservation check](port-evidence/full-preflight-36668540666/)
are retained.

The newly selected source adds ordinary import dependencies so at most two
cell modules and one heavy chunk module build concurrently; the cover finishes
before the chunk chain begins. All 40 changed Lean files preserve every byte
after their `noncomputable section` marker. The generator emits the same
dependencies, and a graph test checks the concurrency bound and absence of cycles.
The statement, coefficient, proof bodies, comparator and toolchain are unchanged.
A new full preflight is required for this exact repaired source. Do not submit
until its mechanical report says `status: pass`.

The pinned workflow is
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@65f0154ed776cd26c224254aa57b379137f28b0d`.
Its `workflow_call` inputs are:

```json
{
  "repository": "teal-sea/zeta-lab",
  "commit": "020a974f2c7153314f9dac8c0fe8a0f9d2dbd53b",
  "pipeline_commit": "65f0154ed776cd26c224254aa57b379137f28b0d",
  "request_id": "f42330260930",
  "mode": "full",
  "execution_profile": "palomar-standard-v1",
  "options": "{\"project_path\":\"hunts/ainta_seven_point/lean-four-point\",\"comparator_config_path\":\"hunts/ainta_seven_point/lean-four-point/comparator.json\",\"formalization_metadata_path\":\"hunts/ainta_seven_point/lean-four-point/formalization.yaml\",\"authorization_relationship\":\"I am a responsible author or maintainer\"}"
}
```

The protocol and upstream revision were rechecked on September 29, 2026
(America/Bogota). The pinned caller is
[palomar-full-preflight.yml](../../.github/workflows/palomar-full-preflight.yml)
on `codex/palomar-full-preflight`. It targets the fixed source above,
independently of the caller branch's own commit.

The first [run 36668179464](https://github.com/teal-sea/zeta-lab/actions/runs/36668179464)
stopped before source preparation and proof execution. Its final report says
`palomar.reporting_failed`. Inspection of the pinned verifier's
`submission_contract.submission_request` found that the original descriptive
request ID fails its exact twelve-character lowercase alphanumeric rule.
The caller now uses `f42330260929`; no mathematical source was changed.
The original [report and workflow log](port-evidence/full-preflight-36668179464/)
are retained. No resource-exhaustion or theorem-failure conclusion follows
from that run.

The second [run 36668379988](https://github.com/teal-sea/zeta-lab/actions/runs/36668379988)
also stopped before source preparation. The workflow requires the full
relationship sentence shown above; the HTTPS API instead takes `maintainer`.
The corrected caller was checked against the pinned upstream
`submission_request` parser and `AUTHORIZATION_RELATIONSHIPS` mapping before
the third run. The second [report and workflow log](port-evidence/full-preflight-36668379988/)
are retained. Both failed reports replaced the specific intake error with
the generic reporting error because intake had not yet bound the source.

The previously filled browser form used the original baseline and must be
replaced with the repaired source above after its full preflight passes. The registry index was
rechecked and the form identifies this as a new submission. The agent has performed no intake or authentication. The owner reported a
stalled browser authentication attempt; no successful submission was confirmed. The owner performs the final
authentication and submission after the full preflight passes.

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

The first resource-repair run [36733676572](https://github.com/teal-sea/zeta-lab/actions/runs/36733676572)
was canceled during setup so the selected source could also include the
historical-proof guard update. It is not a completed verification attempt.
