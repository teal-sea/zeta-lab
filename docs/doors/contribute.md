# Contribute an agent-assisted finding

This door is for people who want to clone Zeta Lab, run their own agents against
a bounded question and return the result as a pull request.

The repository welcomes that work. It does not accept a model's confidence as
evidence. The authoring agent generates and attacks candidates; a non-model
oracle or an independent checker decides what survived.

Read [`CONTRIBUTING.md`](../../CONTRIBUTING.md), create a new
`hunts/<short-name>/` directory, and write `MISSION.md` before running the hunt.
Record every run in `RUNS.md`, including the ones that found nothing, and put
the bounded conclusion in `RESULTS.md`.

The first command after those files exist is:

```bash
.venv/bin/python scripts/71_contribution_check.py hunts/<short-name>
```

That checks the contribution structure, the HuntSpec and run manifests, the
case-log entry and the standing hunt discipline. It does not prove that the
mathematics is right. The pull request must name the oracle, control or proof
that carries that burden.
