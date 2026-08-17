# REPRODUCE — exact steps for every promoted or delivered claim

All commands run from the repo root with the project venv
(`.venv/bin/python`). The Arb backend must be live:
`.venv/bin/python -c "from zeta import rigor; print(rigor.BACKEND)"`
should print `python-flint`.

## RF-C001 / RF-C002 — sine-Gram moments (m_4 check; m_5, m_6 new)

    .venv/bin/python hunts/rogue_frontier/sine_gram/exact_finite_N.py
    .venv/bin/python hunts/rogue_frontier/sine_gram/fast_moments.py
    .venv/bin/python hunts/rogue_frontier/sine_gram/lambda_structure.py
    .venv/bin/python hunts/rogue_frontier/sine_gram/mc_moments.py

The first two are exact integer arithmetic (no floats in any claimed
value); the JSON checkpoints they write are committed alongside. The
Monte Carlo is the statistical control.

## RF-C003 — the improved window (PROMOTED, RH-conditional)

First arm (derivation, optimization, enclosures):

    .venv/bin/python hunts/rogue_frontier/window_opt/functional.py
    .venv/bin/python hunts/rogue_frontier/window_opt/optimize.py
    .venv/bin/python hunts/rogue_frontier/window_opt/crosscheck_finiteN.py
    .venv/bin/python hunts/rogue_frontier/window_opt/enclose.py

Headline check in one line (exact rationals; sympy):

    .venv/bin/python -c "import sys; sys.path.insert(0,'hunts/rogue_frontier/window_opt'); from functional import exact_F_quartic; print(exact_F_quartic(1467,1159))"

Expected: 2245228120295149280/3276332462159207451, and the final constant
1/2 + F/18 + (4/9)(19/27) = 50176758585216887915/58973984318865734118.
The blinded verifier's independent scripts (structurally different
derivation, same rationals) are preserved in the session scratchpad and
its key outputs are quoted in RESULTS_LEDGER.md; an outside reader
re-derives independently from the source paper's SS7.1 and SS7.5(g), which
is the point.

## RF-C004 — truncated Weil form replication + enclosures + DH control

    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_replication.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_enclosures.py
    .venv/bin/python hunts/rogue_frontier/weil_trunc/run_dh_control.py

(See `weil_trunc/RESULTS.md` for the exact driver names and the JSON
gates; `replication.json` must report 8/8, `enclosures.json` 27/27
conclusive-positive cells.) Sources and equation-level citations:
`weil_trunc/SOURCE.md`.

## RF-C006 — Bian audit

    .venv/bin/python hunts/rogue_frontier/fkappa/bian_engine.py --selftest
    .venv/bin/python hunts/rogue_frontier/fkappa/validate_pairs.py
    .venv/bin/python hunts/rogue_frontier/fkappa/validate_numeric.py
    .venv/bin/python hunts/rogue_frontier/fkappa/closed_form.py

The thesis itself: University of Rochester repository, institutional item
5500 (URL in `fkappa/RESULTS.md`); the transcribed Mathematica source is
`fkappa/bian_mathematica.txt`, and the three defect witnesses are each a
single exact rational computation printed by the validators.

## RF-C005 — Baez-Duarte distances

    .venv/bin/python hunts/rogue_frontier/nyman_beurling/validate.py
    .venv/bin/python hunts/rogue_frontier/nyman_beurling/run_ladder.py
    .venv/bin/python hunts/rogue_frontier/nyman_beurling/analyze.py

Checkpointed coefficients and analysis are under
`nyman_beurling/results/`.
