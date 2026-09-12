# Hunt AIMO-2 Results

**Status: report-ready (reframed 2026-08-22); Main-track entry is a legal model-identity prior;
Small-track entry is the always-non-robust constant; leaderboard learned-method arm stays killed;
no GPU spent.** Nothing here rehabilitates the withdrawn R-662B12 +25pp claim: the structural
interpretation stays dead, the cross-validation there was not cross-validation, and the number it
produced is re-measured here out of fold as what the audit said it was, a model-identity base rate.

## What was established (all from public data, graded "measured on public data")

1. **The clear-cut protocol is reconstructible.** The 9 robust rows of `val-sample` are exactly the 9
   `sample-full` pairs with base accuracy 1.0 on every row and zero detrimental perturbations; the 19
   non-robust rows are single-type rows with relative decay >= 0.5, present in `sample-full` with
   identical numbers (30 such rows exist on the same 8 problems). The organizers' proposal (§1.4) says
   the test set drops non-clear-cut cases, so the hidden set is built this way, not like the natural
   distribution. Applied to all 10 public problems: 22.0% robust (strict, 9/41) to 42.9% (loose, 24/56).
   The organizers' MATH releases say the same: DeepSeek-R1-8B 11/54 = 20.4% robust, Llama-3.1-8B 0/156.
   **The 89-97% "natural" robust rate in the first version of this hunt is irrelevant to the
   evaluation distribution; the always-robust constants prepared on it were the wrong bet.**
2. **The label is mostly a property of the model.** A per-model majority prior fitted only on the
   official `val-sample` labels scores, leave-one-problem-out, 26/28 on `val-sample`, 39/41 on the strict
   reconstruction, 43/56 on the loose one (constant: 19/28, 32/41, 32/56). Fit on one set, scored on the
   other: 39/41 and 26/28; the two fits agree on all 7 models. Leave-one-model-out it equals the
   constant, which is its fallback. The site and proposal both state the validation set covers all
   model types in the test set, so leave-one-problem-out is the binding split (preregistration
   amendment below).
3. **Structural facts about the label.** (a) The importer keys cases by (model, problem, perturbation
   type): two `val-sample` pairs appear 3x each and supply 6/19 non-robust rows. (b) `expert_no_solution`
   rows carry one variant sampled 10 times (n_detrimental in {0,1} on all 49 rows): 10/19 non-robust
   rows in `val-sample` and 12/32 in the reconstruction rest on a single human-written variant.
4. **Self-consistency adds nothing under the protocol** (38/41 vs 39/41): robust rows have base 1.0 by
   construction; 8/19 `val-sample` non-robust rows and 52/54 MATH rows do too.
5. **Cross-type failure transfer is absent for the 8B.** On the 69-problem MATH release, 28 problems fail
   under no generic type, 40 under exactly one, 1 under three; `domain` is 32/43 failing rows. No
   single-type predictor of "fails under another type" beats the majority (acc 0.33-0.43 vs majority
   0.56-0.92). This is the free gate failing on a 7x larger set than before; the Small-track GPU route
   stays killed.
6. **Official container path replayed** at starter `e46be92` (HEAD): always-false 0.6786, always-true
   0.3214, identity prior 0.9286 (in-sample), all coverage 1.0, 0 invalid. The importer/ingestion
   schema mismatch (`import_hf_dataset.py` writes `problem` as an object, `ingestion.py:45` requires a
   string) is at HEAD, not a stale pin. Server-side input is organizer-made, so it does not affect
   scoring; it is a starter-kit defect worth one GitHub issue.

## Public competition facts verified 2026-08-22

- Prizes (site): Main $3,000 / $1,000 / $600; Small $2,000 / $600 / $300; writeups $5,000 for
  "selected technical reports, regardless of their ranking, judged on their scientific contribution";
  stated interests: generalization, actionable interpretability, negative results, efficient methods.
- Ties broken by average runtime over three trials (a constant-time submission wins every tie).
- Codabench: 10 submissions/day, 100 per person; warmup phase ends 2026-08-28T22:00Z; main phase to
  2026-11-01; reports due 2026-11-15; review 11-15 to 11-30; 59 participants, 133 submissions.
  The organizers re-uploaded ingestion/scoring/input/reference on 2026-08-21 (task "Validation v8").
- Rules: "teams may not use extra labeled data for the same perturbation types as in our final
  validation set"; model identity is an input and nothing restricts its use; same bundle may go to
  both tracks; report required from teams considered for awards.
- Public leaderboard on the current warmup task: five identical scores at 7/17 = 0.4118 (one from
  organizer `pmmon`), one 11/17, one 8/17. Read as competitor intelligence only; no submission of ours
  was used to infer anything, and the constant choice above rests on the public datasets.

## What was chosen and why

- **Main track: `submissions/identity_prior_main`** (bundle `artifacts/aimo2-identity_prior_main.zip`,
  table generated by `protocol_reconstruction.py`, fallback non-robust). Legal, zero compute, beats the
  constant by 17-25 points out of fold on every public set; bounded downside (= constant on unseen models).
- **Small track: `submissions/official_reference`** (always-non-robust). The 8B is 20% robust on the
  organizers' MATH release and 0/1 in `val-sample`; no public signal beats that constant.
- **Control: `official_reference`** may also be uploaded to the Main track once to read the hidden
  balance from our own single score; that is one legal submission, not probing.
- **Superseded, kept for the record:** `natural_prior_main`, `natural_prior_small` (always-robust).
  They score 0.32 on `val-sample` and would score 1 minus the hidden robust rate. Do not upload.
- **Report thesis reframed** from "the development sample is curated to inflate signals" (which reads
  the organizers' documented design as a defect and they are the judges) to "here is what the protocol
  produces, here is the zero-compute floor, here is what the floor implies for the final analysis".

## What could not be settled

- Whether the hidden set's model identifiers are the 7 public ones. Both organizer statements say the
  validation set covers the test set's model types; if an unseen identifier appears, the prior answers
  non-robust for it.
- The hidden robust fraction. The public protocol puts it at 20-43%; the warmup leaderboard cluster is
  consistent with ~41%. Always-non-robust is the better constant under every public reading.

## Reproduce

```
.venv/bin/python hunts/aimo2/protocol_reconstruction.py   # artifacts/protocol.json, identity_prior.json
.venv/bin/python hunts/aimo2/free_gate.py                  # artifacts/free_gate.json
.venv/bin/python hunts/aimo2/reconstruct_curation.py       # artifacts/curation.json
# official path (starter at e46be92, val-sample written as string problems):
#   python3 scripts/run_local.py <bundle>  -> identity prior 0.9286, always-false 0.6786, always-true 0.3214
```

## Loose threads

1. **Starter round-trip issue upstream.** *What:* `import_hf_dataset.py` / `ingestion.py:45` mismatch at
   HEAD `e46be92`. *Why:* cheap goodwill with the judges; the FAQ invites issues. *First step:* operator
   opens a one-paragraph issue on `aimo-interp/getting-started` (text in the job report).
2. **Main-phase calibration.** *What:* after the main phase opens (2026-08-28), upload the identity
   prior and once the constant; record both scores. *Why:* our own two scores bound the hidden balance
   and whether the identity assumption held; both facts belong in the final report. *First step:* the
   operator's upload session; no further agent work before then.
3. **Report finalization, late October.** *What:* add the main-phase scores and any organizer
   clarification to `REPORT.md`, keep it to the 1-2 page norm the proposal mentions. *Why:* the $5,000
   writeup pool is the largest ranking-independent item. *First step:* one short pass after 2026-10-20.

Nothing in this hunt bears on the Riemann Hypothesis (docs/08).
