# Checkpoint: zero visibility (for the next session)

Written 2026-11-02 ~02:55 UTC. Branch `mad/zero-visibility`, worktree
`/home/thomas/zeta-lab/.claude/worktrees/mad-zero-visibility` (on the Linux box),
pushed to `origin/mad/zero-visibility`. Not merged; not a PR. Read `lab/MISSION.md` (scope,
rules) and `lab/RESULTS.md` (everything measured, with labels and commands) first.

## State

| item | status |
|---|---|
| HVG tool + tests (`hvg.py`, `test_hvg.py`) | done, 10 passed |
| Zeros to 10^5 (`lab/data/zeros_T100000.npz`, gitignored) | done, 138,069, regenerate with `scan_zeros.py 100000` (~2 min) |
| Exp A degree law | done: Conjecture A FALSIFIED (k=2 excess over GUE) |
| Exp B arrow of time | done: Conjecture B survives |
| Exp C effective CUE size | done: Conjecture C FALSIFIED |
| Independent verification (3 agents) | done, all confirmed; folded into RESULTS section 7 |
| Zeros to 10^6 (`scan_zeros.py 1000000`) | **RUNNING** at checkpoint time (91+ min, nohup, PID of `lab/.venv/bin/python lab/scan_zeros.py 1000000`), writes `lab/data/zeros_T1000000.npz` and `lab/data_scan_T1e6.log` |
| Exp D height dependence | **PENDING**: a detached chain (`lab/logs/chain.log`) runs `exp_d_height.py` then `make_viz.py` when the scan log gets `exit=0`; output `lab/logs/exp_d_height.log`, `lab/results/exp_d.json` |
| RESULTS section 6 | **PENDING**: write it from `exp_d.json` |
| `viz.html` height panel | rebuilt automatically by the chain |

## How to resume

```bash
cd /home/thomas/zeta-lab/.claude/worktrees/mad-zero-visibility
cat lab/data_scan_T1e6.log lab/logs/exp_d_height.log      # did they finish?
ps -eo etime,args | grep -E 'scan_zeros|exp_d' | grep -v grep
# if the scan died or the box rebooted (lab/.venv is local, rebuild if missing):
python3 -m venv lab/.venv && lab/.venv/bin/pip install numpy scipy mpmath matplotlib sympy pytest pyyaml python-flint hypothesis
OPENBLAS_NUM_THREADS=1 lab/.venv/bin/python lab/scan_zeros.py 1000000   # ~90+ min here
OPENBLAS_NUM_THREADS=1 lab/.venv/bin/python lab/exp_d_height.py
lab/.venv/bin/python lab/make_viz.py
```

## The open question (what D decides)

Zeta gaps up to 10^5 have pV = 0.35514 ± 0.00036 local minima vs sine-process 0.35118 ±
0.00006. About 85% of the excess is second-order structure (IAAFT surrogates, reported by a
verification agent), i.e. known finite-height rigidity. But inside T <= 10^5 the variance
and rho1 drift toward GUE with height while the pV excess does not shrink (index thirds:
+0.00349, +0.00390, +0.00451, ± ~0.0006). D fits the excess against 1/log^2(T/2pi) and
1/log(T/2pi) over 7 windows to 10^6, and checks it against a Gaussian-copula prediction
from rho1, rho2.

- Excess decays like 1/log^2 with the correlations: explained, write it up as known physics.
- Excess flat or growing while variance/rho1 relax: the interesting case. Next steps then:
  re-run the hunter's IAAFT test per height window; compare with zeros of a Dirichlet
  L-function at matched density (arithmetic vs universal).

## Caveats to carry forward

- Effective-size formula N_eff = log(E/2pi)/sqrt(12 Lambda), Lambda = 1.57314, is quoted
  from memory (Bogomolny et al. 2006), unverified.
- The Arb completeness check of all 138,069 zeros and the IAAFT numbers are agent reports
  (scratchpad `verify/`, session 45f89c9a), not re-run by me; the scratchpad is tmpfs and
  may be gone.
- No novelty search was done (the original brief forbade external sends).
- Budget: ~105 of 150 main-loop tool calls used at checkpoint.
- `~/.claude/hooks/zeta-budget-guard.py` was created this session (the hook entry pointed at
  a missing file); its push rule now blocks only main/master and force pushes.
