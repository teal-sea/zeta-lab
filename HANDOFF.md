# Session handoff — zeta moments programme

**Snapshot:** 2026-08-04  
**Branch:** `main`  
**Remote state before this handoff commit:** `origin/main` at `40d27ff`  
**Detailed sources of truth:** `ROADMAP.md` and `docs/13-moments.md`

## Where the work landed

The moments programme now has a full finite-height comparison instrument for
the 2nd, 4th, 6th, and 8th critical-line moments:

- `zeta.moments.moment_polynomial(k)` returns the full degree-`k²` polynomial
  in the convention `P_k(log(t/(2*pi)))` for `k=1,…,4`.
- `moment_polynomial_mean` integrates every polynomial term over the actual
  window; it does not use a midpoint or leading-only approximation.
- `moment_scorecard` calibrates on the theorem cases `k=1,2` before releasing
  the conjectural `k=3,4` rows.
- `scripts/14_moment_experiment.py` computes local critical-line values and now
  supports convergence, disjoint-block, peak-concentration, multi-height, and
  pre-registered multi-offset studies.

The `k=1,2` full polynomials are theorem-backed. The `k=3,4` polynomials are
CFKRS conjectures. Published decimal coefficients have reported stable digits
but no interval enclosure; the code never calls them certified.

## Main numerical finding

The candidate empirical pattern is:

> With increasing height and moment order, moment mass becomes increasingly
> concentrated in rare large-value intervals, while pooling enough disjoint
> windows recovers the full CFKRS polynomial aggregate.

This is not claimed as novel, proven, probabilistic, or related evidence for
RH. It is a replicated finite-height numerical observation that still needs a
literature audit and further attacks.

### Pinned results

One width-4000 window at `t=10^5`, spacing `0.005`:

| moment | full-polynomial ratio | block-ratio CV | top 1% integral share |
| ---: | ---: | ---: | ---: |
| 2nd | `0.9982` | `1.28%` | `25.81%` |
| 4th | `0.9893` | `7.43%` | `67.06%` |
| 6th | `0.9653` | `19.20%` | `88.67%` |
| 8th | `0.9229` | `34.63%` | `96.49%` |

The nested-grid audit changed every moment by less than `1.1e-6` relatively,
so grid resolution was not the observed limitation. Window-ratio drift reached
`18.05%` for the 8th moment.

Height-normalized single-window replication used 6,000 nominal mean zero gaps,
128 points/gap, and 768,001 samples per height:

| height | 2nd | 4th | 6th | 8th | 8th-moment top 1% share |
| ---: | ---: | ---: | ---: | ---: | ---: |
| `10^4` | `1.0004` | `1.0014` | `1.0052` | `1.0199` | `90.25%` |
| `10^5` | `0.9996` | `0.9947` | `0.9755` | `0.9368` | `96.52%` |
| `10^6` | `1.0061` | `1.0154` | `1.0084` | `0.9677` | `98.96%` |

## Strongest attack completed

Before the multi-offset run, three gates were fixed in code:

1. pooled 2nd/4th theorem controls within `5%` of one;
2. pooled 6th/8th conjectural ratios within `15%` of one;
3. median top-one-percent concentration strictly increasing with height for
   both the 6th and 8th moments.

Four consecutive disjoint whole windows were then evaluated at each height
band: 12 windows, about 9.2 million finest-grid points. Mutation tests force all
three gate paths to fail. The real run passed all three without changing the
thresholds.

| height | pooled 2nd | pooled 4th | pooled 6th | pooled 8th |
| ---: | ---: | ---: | ---: | ---: |
| `10^4` | `1.0000` | `1.0002` | `1.0006` | `1.0001` |
| `10^5` | `1.0003` | `0.9986` | `0.9866` | `0.9633` |
| `10^6` | `1.0001` | `1.0075` | `1.0301` | `1.0628` |

At `10^6`, individual 8th-moment whole-window ratios ranged from `0.5831` to
`1.4362`, yet pooling returned `1.0628`; median top-one-percent concentration
was `99.12%`.

## Reproduction commands

Always run from the repository root with the project venv:

```bash
.venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 --spacing 5e-3 --convergence
.venv/bin/python scripts/14_moment_experiment.py --start 1e5 --length 4e3 --spacing 5e-3 --blocks 8
.venv/bin/python scripts/14_moment_experiment.py --replicate
.venv/bin/python scripts/14_moment_experiment.py --attack
.venv/bin/python -m pytest -q -o addopts='' tests/test_script_14_moment_experiment.py
```

The last command collects 25 tests, including pinned real numerical runs and
mutation tests for the attack gates.

## Commits in this build sequence

```text
6814f9d Add locally generated moment experiment
f6ffadc Add full CFKRS moment polynomials
e0f5d98 Add nested moment convergence study
3dbac1e Measure moment peak concentration
fcc0c3a Replicate moments across heights
40d27ff Attack moment pattern across offsets
```

## What not to infer

- Deterministic disjoint blocks are not asserted to be independent samples.
- Block CV, nested-grid drift, and peak shares are not confidence intervals or
  rigorous error bounds.
- “Top 1%” means ranked uniform-grid trapezoidal interval contributions, not
  one percent of independent peaks.
- The mean-zero-gap normalization is asymptotic and fixes nominal exposure; it
  is not an exact count of zeros inside each window.
- Agreement does not prove CFKRS, establish novelty, support RH, or weaken RH.
- Any apparent RH consequence should be treated as a bug.

## Next session: do this first

1. Read `ROADMAP.md`, then `docs/13-moments.md`, then this snapshot.
2. Perform a primary-literature novelty audit on finite-height high-moment
   concentration, block/window variance, and the relation between CFKRS moment
   polynomials and extreme-value tails. Do not name a new conjecture first.
3. Before computing, pre-register an **exposure-scaling attack** using several
   nominal window sizes. The open question is whether pooled-ratio error
   stabilizes as exposure grows while peak concentration persists.
4. Hold back a set of untouched windows for out-of-sample predictions. Record
   exact gates before evaluation and add mutation tests for every gate.
5. Only after the audit and out-of-sample test decide whether the observation
   merits an entry in the private `conjectures/` ledger.

External high-height critical-line value data remains desirable, but no public
dense row table was found in the 2026-08-04 source audit. Never substitute zero
ordinates for independently evaluated `|zeta|` samples.

## Test-run caveat

The focused moments and script suites pass. The repository's parallel pytest
runner has a pre-existing teardown/worker hang near completion; the last broad
fast run reported 1,370 passes and 4 skips before manual interruption. Do not
misreport that interrupted run as a clean full-suite exit. Use the focused
single-process command above for this work, and investigate the unrelated
runner hang separately if a clean repository-wide exit is required.
