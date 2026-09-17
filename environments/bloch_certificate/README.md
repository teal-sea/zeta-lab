# Bloch certificate environment

A model gets read-only access to Frank Wikström's published Bloch certificate
verifier. It must reproduce two archived certificate values, reproduce the
published near-branch target, and calibrate the highest decimal target accepted
by the shipped near branch. Reward comes from the archive's own Arb verifier,
not an LLM judge.

This is a public seed environment from Zeta Lab Hunt #80. It is deliberately
small: four public calibration rows, no hidden test claim, no Lean rung, and no
24-sector away replay. The full environment product is the method across
multiple targets and graders, not this free sample.

## Trust boundary

- Archive: Zenodo `10.5281/zenodo.21975862`, version 1.0.0, MIT.
- SHA-256 pinned: `bdaa1ff347043a00733ca40d5db46c5418810d1f4e5c472d0bcb9de48ef408e7`.
- The same downloaded bytes are hashed and extracted into a fresh temporary
  directory before every uncached verifier mode.
- Model inputs are exact JSON decimal strings. They are never passed to a shell,
  path lookup, Python evaluation, or upstream program.
- Near-target queries have a 24-call episode budget. That is enough for the
  advertised `1e-10` bisection and prevents runaway tool/audit output.
- Upstream code runs in a subprocess with a 90-second timeout and a minimal
  environment. This is process isolation, not a hostile-code sandbox. The code
  is hash-pinned and trusted as the grader.
- Oracle failures raise an environment error. They never become a zero reward.
- Each score records mode, digest, verifier log, elapsed time, target, verdict,
  and the exact scope of the check.

## Tasks

| Task | Acceptance |
|---|---|
| `fine-reproduce` | Exact (C) gain printed by the fine fixed-radius certificate |
| `coarse-reproduce` | Exact (C) gain printed by the coarse fixed-radius certificate |
| `near-reproduce` | A shipped near-branch target from `0.0153` up to its strict cutoff |
| `near-branch-cutoff` | An accepted target within `1e-10` below the near-branch cutoff |

The near tasks do not replay the 24 away sectors. Hunt #80 previously replayed
all sectors at `0.0153040536`. That result is evidence behind
the task calibration, not a computation this lightweight environment pretends
to rerun.

For `check_near_target`, use `goal="published"` on `near-reproduce` and
`goal="cutoff"` on `near-branch-cutoff`. The tool and final reward share the
same positivity check, lower floor, and strict upper cutoff.

## Run

```bash
python3 -m venv .venv
.venv/bin/pip install -e environments/bloch_certificate
.venv/bin/bloch-prepare
.venv/bin/bloch-smoke
.venv/bin/vf-eval bloch-certificate   --env-dir-path environments   --model <provider/model> -n 4 -r 1
```

`bloch-prepare` downloads once into `~/.cache/bloch-certificate/` and verifies
the digest. `load_environment()` also prepares a missing default archive.
`bloch-smoke` runs four positive and four negative controls without a model.

## What the evidence means

The fixed-radius rows check the finite certificate arithmetic. The near rows
check the shipped near branch. They do not audit Bonk's theorem, the moment
inequality, the three-atom reduction, or the centre-placement lemma. Acceptance
is not by itself a theorem about Bloch's constant.

Sources: the upstream archive, its paper `arXiv:2608.17660`, and Zeta Lab's
`hunts/bloch_ceiling/RESULTS.md`.
