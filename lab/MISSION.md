# lab/: the zero-visibility obsession

Branch `mad/zero-visibility`, worktree `.claude/worktrees/mad-zero-visibility`, from
`origin/main` at `b278389f3`. Opened 2026-11-02 by an unsupervised session ("mad
mathematician" brief).

## Scope and rules

- Writes go to `lab/` only. No existing file is modified or deleted. Nothing is pushed,
  merged or sent anywhere. The one external fetch is PyPI, for `lab/.venv` (numpy,
  scipy, mpmath, matplotlib, python-flint, hypothesis, pytest), after the operator
  cleared external compute on 2026-11-02.
- Budget: about 150 main-loop tool calls, or stop after three experiments in a row that
  go nowhere.
- Every result is labelled **PROVEN** (a proof written here and checked exhaustively on
  small cases, or a theorem cited from the literature), **OBSERVED** (measured, float
  grade unless stated), or **GUESS**. Failed experiments are logged, not dropped.
- Novelty: not searched. The brief forbids sending anything out, and a literature search
  sends queries. "Original" below means produced here, nothing more.

## The object

The horizontal visibility graph (HVG) of a real sequence x_1, ..., x_n joins i < j when
every value strictly between them is lower than both: x_k < min(x_i, x_j) for i < k < j
(Luque, Lacasa, Ballesteros and Luque, Phys. Rev. E 80, 046103, 2009). For any i.i.d.
sequence with a continuous law, the degree distribution of the bi-infinite HVG is
exactly P(k) = (1/3)(2/3)^(k-2), k >= 2, whatever the law (their theorem). HVG
statistics see only the order pattern of the data, so every i.i.d. sequence, including
Poisson spacings, gives the same graph statistics.

Here the sequence is the unfolded gaps between consecutive zeta zeros,
s_n = theta(gamma_{n+1})/pi - theta(gamma_n)/pi.

## Conjecture A (one line)

**The HVG degree law of unfolded zeta-zero gaps breaks the i.i.d. theorem and agrees with
the GUE gap process at every degree k = 2..12, within 3 sigma of sampling error, for all
zeros up to T = 10^5.**

How it can fail: the zeta law matches i.i.d. (no visible repulsion), or it differs from
GUE at some k by more than sampling error (a finite-height or arithmetic effect).

## Conjecture B (one line, run after A)

**The zeta-zero gap sequence has no arrow of time: the out-degree and in-degree laws of
its directed HVG agree within sampling error.**

How it can fail: a significant Kullback-Leibler gap between the two, larger than for
random block reversals of the same data.
