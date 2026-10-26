# MISSION: where Li's criterion first fails for Davenport-Heilbronn, enclosure-carrying

**Opened 2026-10-26, hunt #151, branch `hunt/li-dh-onset-hardened`.** Part of the
owner's 2026-10-26 compute sweep: walls the record calls cost walls rather than
mathematical ceilings, to be knocked down with *hardened* results (ball
arithmetic carrying every step, plus a second route). Nothing in this directory
is a result until `RESULTS.md` says so, and the strongest grade any number here
can reach is *hardened*. The reserved enclosure word of `zeta/rigor.py` is not
used anywhere under `hunts/`.

Scope, stated once: **nothing here is evidence about the Riemann Hypothesis**
(`docs/08`). The Davenport-Heilbronn function f is not zeta, has no Euler
product, and already has zeros off its critical line. Every number is about f.

## The question

Bombieri and Lagarias (1999, Theorem 1): for a multiset of zeros closed under
rho -> 1 - rho (with their convergence condition), lambda_n >= 0 for all n
if and only if every zero has real part 1/2. f has the off-line pair
rho_1 = 0.80851718... + 85.69934848...i, so some lambda_n(DH) is negative.

> **Find an explicit n\* with lambda_{n\*}(DH) < 0 and lambda_n(DH) > 0 for every
> 1 <= n < n\*, every step enclosure-carrying.**

`hunts/li_dh_onset` (#128) measured lambda_n(DH) > 0 for n <= 5000 (float grade;
the zero side agrees to 1e-8 at n <= 12), and extrapolated a background fit
66 times past its last coefficient to n\* near 328997. Its own cost model priced
reaching that index by its contour plan at about 20,000 core-hours, at r = 0.95
or 0.99 with about 1490 working digits (`hunts/li_dh_onset/RESULTS.md`, the
doors; `ceiling.py`).

## The repricing under test

The 20,000 core-hours come from the r^{-n} amplification at r <= 0.99: the
precision is n log10(1/r) digits, so the cost grows like n^3. That radius was
the top of the old scan, not a limit. The analyticity radius of
g(z) = log F(1/(1-z)) is R_a = min |1 - 1/rho| over the zeros with Re rho > 1/2,
and if rho_1 is the minimiser then R_a = 0.999958 (1 - R_a = 4.2e-5). Moving to

    r = sqrt(1 - 1/c),  c = 5000,   so 1 - r = 1.0e-4 and r^{-n} = e^{33} at n = 3.3e5,

makes the precision cost about 50 bits instead of about 5000 digits, and moves
the whole difficulty into two things the old plan never needed:

1. **an admissibility certificate**: every zero with Re rho > 1/2 has
   |1 - 1/rho| >= R_a > r', for an aliasing circle r' between r and R_a; and
2. **rigorous trapezoid bookkeeping**: the aliasing bound on r', and the branch
   of log F tracked node to node with a ball argument step.

A judge's check carried in the brief: at c = 1e4 the aliasing circle
r' = (1 + r)/2 lies beyond |1 - 1/rho_1| = 0.999958, so the trapezoid needs about
1.3e7 nodes. This hunt rechecks that (`trapezoid.py`).

## Inputs and their grades

| input | grade as found | used for |
|---|---|---|
| rho_1, rho_2 locations (`hunts/flow_repair/results.json`) | measured | starting points only; re-located in balls here |
| lambda_n(DH), n <= 5000 (`hunts/li_dh_onset/artifacts/`) | measured | a cross-check, never an input |
| n\* near 328997 (`hunts/li_dh_onset/artifacts/onset.json`) | extrapolated | sizing the production run only |
| kappa (`hunts/lambda_dh_bounds/instrument.kappa_ball`) | enclosure (Arb linear solve) | the evaluator's constant |
| committed xi Li tables `data/li_lambda_*.json` | measured (float, two routes) | the positive control target |
| Arb (python-flint 0.9.0) Hurwitz zeta, lgamma, DFT | ball arithmetic | every enclosure here |
| mpmath.iv (Euler-Maclaurin Hurwitz written here, iv.loggamma) | interval arithmetic | the independent second route at sample points |

## Rivals and the gate

Two routes that share no evaluator code: Arb (`acb.zeta`, `acb.lgamma`) and an
mpmath.iv Euler-Maclaurin Hurwitz sum with its own kappa solve. Every Arb ball
checked against the iv route must intersect it. The coefficient pipeline has
two positive controls: pointed at xi it must contain the committed tables, and
at two radii its DH balls must intersect each other and contain the #128 float
table. A planted fault must break each control.

The admissibility gate is the exact integer equality

    N_box = N_line + 2q

on [1 - sigma_h, sigma_h] x [0, T]: N_box the argument-principle count, N_line the
number of ball-decided sign changes of the real function F(1/2 + it) on (0, T),
and q the number of off-line zeros with Re > 1/2 located in small boxes with a
ball count of exactly one. Dropping a quadruple must break it.

## Kill conditions

- The completeness equality cannot be closed in balls at any c >= 2000. Then only
  the r = 0.99 plan remains, to be re-estimated before any spend.
- Two radii (or the Arb and iv routes) disagree beyond their enclosures. That is a
  defect, investigated before any number is reported.
- The xi control fails to contain the committed tables, or a planted fault does
  not flip it.

## Write scope and compute rules

May write: `hunts/li_dh_onset_hardened/` and this hunt's case-log entry in
`hunts/README.md`. May not edit `zeta/`, `ontology/`, `harness/`, `lean/`,
`scripts/` or any other hunt (reading and importing them is fine). Box rules:
at most 4 processes, `nice -n 10` for long jobs, wait while the 1-minute load
exceeds 64, stop the newest job if MemAvailable < 20 GiB, no file over 100 MB,
under 300 MB added. Every estimate goes in `RUNS.md` before the spend; anything
over one core-hour goes to the coordinator first.

## Novelty record

See the section "Prior work searched" at the end of `RESULTS.md` once written;
until then nothing here claims novelty.

```huntspec
id: li_dh_onset_hardened
question: Is there an explicit n* with lambda_{n*}(DH) < 0 and lambda_n(DH) > 0 for all 1 <= n < n*, every step enclosure-carrying, reachable at a contour radius r = sqrt(1 - 1/c) with c near 5000?
frontier: lambda_n(DH) > 0 measured for n <= 5000 and hardened (two routes) only for n <= 12 (hunt 128); n* near 328997 by a 66x extrapolation; the r <= 0.99 contour plan priced at about 20000 core-hours
proposed_attack: an admissibility certificate (argument-principle box count equal to line sign changes plus the located off-line quadruples) licensing r = sqrt(1 - 1/c), then an Arb trapezoid with a rigorous aliasing bound on an intermediate circle and ball-tracked branch of log F
dead_routes:
  - the r <= 0.99 contour plan of hunt 128, whose precision grows like n log10(1/r) digits and whose cost grows like n^3; not refunded unless this hunt's kill fires
  - reading lambda_n off a zero list as the primary route, which imports every completeness assumption above the ball-checked box height
  - the envelope-crossing indicator of hunts/jensen_clock phase 3, which fires at n = 1
required_oracles:
  - Arb ball arithmetic (python-flint acb.zeta, acb.lgamma, acb.dft) with every truncation bounded
  - an mpmath.iv Euler-Maclaurin route sharing no evaluator code, whose intervals must intersect every Arb ball checked
  - the committed xi Li tables in data/, contained in the balls of the same pipeline pointed at xi
  - the exact integer equality N_box = N_line + 2q, broken by a planted dropped quadruple
kill_conditions:
  - the completeness equality cannot be closed in balls at any c >= 2000
  - two radii or the two routes disagree beyond their enclosures
  - the xi control fails, or a planted fault leaves it passing
agents_may:
  - derive
  - code
  - measure
  - attack their own pipeline
  - state a grade on the certainty ladder
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - write any sentence implying a computation bears on the Riemann Hypothesis
```

## Pre-registration of the production runs (2026-10-26, committed before run A starts)

Written and committed alone, before any production coefficient exists.

**The prediction under test.** Hunt #128 (`li_dh_onset/artifacts/onset.json`)
extrapolated the first negative index to **n\* = 328997** under four background
variants (325229 under a zeta-shaped one). Its recorded sensitivity is about
530: a shift of the background constant b by -0.05 moves the index to 328469,
one period 2 pi/psi of the dominant quadruple's oscillation. The background is
about 1.98e6 there and the dip is about 0.11 per cent of it, so lambda_{n\*} is
predicted near -2e3. The prediction counts as **confirmed** if the first
ball-decided negative index lies in [328997 - 600, 328997 + 600], and as
**located elsewhere** otherwise. Either outcome is reported.

**The statement a positive outcome hardens.** An explicit n\* <= 500,000 with
the Arb ball of lambda_{n\*}(DH) entirely below 0 and the ball of lambda_n(DH)
entirely above 0 for every 1 <= n < n\*. Every step is enclosure-carrying:
- the admissibility certificate (`artifacts/admissibility.json`);
- M(rho) from the ball arc cover;
- node samples in Arb, with the branch tracked by ball steps and closing;
- `acb.dft`;
- the aliasing bound (A) added as a ball to every coefficient.
The grade is *hardened*, not kernel-checked.

**Runs, in order, one process each.**
- **Run A:** c = 5000, rho = 1 - 4.6e-5, N = 2^21, 192 bits, n <= 500,000.
- **Run B:** c = 2500, rho = 1 - 4.6e-5, N = 2^19, 256 bits, n <= 500,000.
- **Both runs** carry the xi positive control (all 48 committed values
  contained, both planted faults flipping it) and the 20-node mpmath.iv
  subsample on their own circle, and their outcome is void if either fails.

**The two-radii rule (kill condition 2).** At every n <= 500,000 the A and B
balls must intersect. One disjoint pair is a defect. It is investigated before
any n\* is reported, and no n\* is reported from a run that fails it.

**What "undecided" means.** If some ball for n < n\* contains 0, the statement
above is not established. The report then gives the undecided indices and the
radius, and does not claim n\*.

**The stop rule.** If no ball-decided negative coefficient appears for
n <= 500,000, stop. Record the positivity range actually hardened and
re-estimate (a larger n_max changes N and the bits) before any further spend.

## Pre-registration of the independent-evaluator rerun of run B (2026-10-26, committed before it starts)

Committed before `ivpipe.py` runs. **Why:** RESULTS.md names a shared failure
mode, that both production radii evaluate f with the same Arb code (four
`acb.zeta` calls). The rerun repeats run B (c = 2500, N = 2^19, 256 bits,
rho = 1 - 4.6e-5, n <= 500,000) with every evaluation of f, log G and S(3/2)
taken from mpmath.iv instead (`iv_fast.py`: Euler-Maclaurin, its own kappa
solve, `mpmath.iv.loggamma`). That covers the node samples, the branch-cover arc
balls and the M(rho) cover. The node geometry, the tracking logic, `acb.dft` and
the aliasing arithmetic are shared with run B on purpose ("run the same DFT").

**The comparison sample.** `sorted(random.Random(1512026).sample(range(1, 500001), 1000))`,
`ivpipe.sample_indices()`. It begins 312, 546, 986, 1390, 1759, ends 498499,
499466, 499616, and does not contain 328996 or 328997.

**The rules.**
1. The iv run's first ball-negative index must be 328997, with no undecided
   index before it. Undecided iv balls are reported as undecided, not as a
   disagreement.
2. At every n <= 500,000 where both runs decide the sign, the signs must agree.
3. The iv ball and run B's ball must intersect at n = 328996, at n = 328997 and
   at all 1000 sampled indices.

**Verdict.** If all three hold, the named shared failure mode is excluded for
run B's table, at the grade the iv route carries: interval arithmetic, with
every evaluation enclosed. Any failure is a defect between the two evaluators.
It is investigated before anything else is reported, and the headline is not
withdrawn or changed until that investigation says so. Neither outcome changes
the headline grade (hardened, pending external verification).

## Pre-registration of the iv replay of the admissibility certificate (2026-10-26, committed before it runs)

**Why.** The certificate (`admissibility.py`, `artifacts/admissibility.json`) is
the remaining Arb-only link in the chain RESULTS.md describes. It is replayed
with every evaluation of f, log G and S taken from mpmath.iv (`iv_fast.py`,
`iv_route.py`). Arb is used only to hold converted boxes and for the argument
arithmetic on them, exactly as in `ivpipe.py`.

**Where iv must differ.** Near s = 1, Arb computed f(1) through `dirichlet_l`.
The iv Euler-Maclaurin sum cannot evaluate at the removable pole. The replay
therefore bounds |f(sigma) - f(s0)| at an exact point s0 near 1 by a Cauchy
estimate on a circle around 1. That is a different route to the same
statement.

**The rule.** The replay at T = 160, 128 bits must reproduce the certificate's
admissibility conclusion:
- S(3/2) < 1 and S(7/4) < 1;
- f > 0 on [1/2, 7/4];
- N_box = 98, N_line = 94, both pair1 and pair2 squares counting exactly 1;
- the equality N_box = N_line + 2q closing;
- R_a's lower bound above r for c = 5000.

Its balls must intersect Arb's wherever both evaluate: S(3/2), S(7/4), the
N_box ball, the value of Z at every line grid point, and |1 - 1/s| over each
square. The planted faults must break it as before: drop a quadruple, displace
a square. Any failure is a defect between the evaluators, investigated before
anything else, with the headline grade unchanged either way.
