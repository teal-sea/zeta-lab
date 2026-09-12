# Contributing research

Zeta Lab accepts agent-assisted contributions. Clone the repository, let your
tools investigate a bounded question, and open a pull request with the evidence.
The authoring system may search, derive, code, attack and formalize. It may not
grade its own result or declare novelty.

The useful unit is not a transcript or a confident explanation. It is a
rerunnable artifact with a question, an oracle and a recorded outcome.

## Three useful contribution shapes

1. **A reproducible defect or observation.** Open an issue when the finding is
   not accompanied by a fix. A fixing pull request must include a test that
   fails on the base commit and passes with the change.
2. **An exploratory research result.** Add one directory under
   `hunts/<short-name>/`. Keep the first pull request inside that directory,
   apart from its case-log entry in `hunts/README.md`. Promotion into shared
   modules is a separate maintainer decision after the result survives review.
3. **A formal result.** Add or strengthen a Lean theorem and run the pinned
   `lake build`. A file containing `sorry` is a scaffold, not a finished proof.

Large generated rewrites, unbounded literature summaries and prose-only
mathematical claims will be closed. They do not give the laboratory an object
it can check or reuse.

## Contract for a research hunt

A hunt pull request contains:

- `MISSION.md`, with a valid `huntspec` block naming the exact question, known
  frontier, dead routes, non-model oracles, kill conditions and agent authority;
- `RUNS.md`, with at least one `runmanifest` block recording what actually ran,
  including runs that produced no positive result;
- `RESULTS.md`, stating the bounded outcome and its limitations;
- every script, input, output checksum or proof needed to reproduce the result;
- a case-log entry naming the hunt directory in `hunts/README.md`;
- a numerical test for every quantitative mathematical claim, or an explicit
  hedge at the point where the claim appears;
- a knownness record before any novelty language is proposed. Empty search
  results are not evidence of novelty.

The authoring agent does not promote the claim. A separate oracle, checker or
reviewer assigns its evidentiary status. Claims about zeta structure must also
face a structure-matched rival, normally the Davenport-Heilbronn or Epstein
controls already exposed by `zeta.epstein.battery`.

Start from a clean clone and record the base commit. Do not reuse another
checkout's editable virtual environment because its package path points at the
other checkout. Follow `AGENTS.md` to create `.venv` locally and install the
pre-push secret guard.

When the three required files exist, run:

```bash
.venv/bin/python scripts/71_contribution_check.py hunts/<short-name>
```

Then run the checks affected by the work. CI runs the governance gate and the
full fast numerical tier on every pull request.

## Pull-request evidence

The pull request body must give a reviewer five things without requiring the
authoring agent's transcript:

1. the exact question and base commit;
2. the bounded result, including a null or negative result;
3. reproduction commands and observed outputs;
4. the independent oracle or adversarial check;
5. the prior-art search, if originality or novelty is relevant.

Model agreement is not an independent oracle. Two sessions drawn from the same
weights are not two instruments. Kernel checking, ball arithmetic, exact
enumeration, an independently implemented computation and a cited source are
examples of evidence the repository can lean on.

Never commit credentials, private prompts or personal data. Run
`scripts/check_secrets.py` before pushing. The public record should contain the
scientific process needed to evaluate the result, not Fulcrum's private routing,
allocation or cost strategy.
