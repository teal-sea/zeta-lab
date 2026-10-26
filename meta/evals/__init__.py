"""Runners for the experiments `meta/` designs, on Inspect (`inspect_ai`, UK AI
Security Institute).

* :mod:`meta.evals.asymmetry` is E0 of `meta/asymmetry-experiment.md`, a
  pre-registered factorial whose *Factor B = probabilistic* cells need a model in
  the loop at check time, plus per-artifact cost accounting and a log a stranger
  can audit.  Run on 2026-08-20; the disposition is
  `docs/28-asymmetry-e0-disposition.md`.
* :mod:`meta.evals.self_report` and :mod:`meta.evals.self_report_tooled` ask
  whether a proving agent's own report that its proof compiles predicts the
  kernel.  Pre-registered and reported in `meta/SELF-REPORT-PROTOCOL.md`, run on
  2026-08-20, with the corrections in its section 12.

The run logs are in `meta/evals/logs/`.  Importing a module runs nothing.
Nothing here is a mathematical result and nothing here trades against one, per
`meta/README.md`.
"""
