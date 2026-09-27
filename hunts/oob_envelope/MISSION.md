# MISSION: out-of-band envelopes for Weil window positivity

Opened 2026-09-27 on branch `teal-sea/oob-cert` from `origin/main` (8941a80).
Scope: `hunts/oob_envelope/` only, plus this hunt's case-log entry in
`hunts/README.md`. Everything else in the repo is a read-only input.

## The gate

Every deliverable must be a statement **strictly weaker than RH**: a
fixed-window positivity theorem, a lemma with a proof, or a measured cost law.
A reformulation of RH is recorded as a reformulation, never as progress.

## The observation this hunt tests

Weil's form on the window `supp f ⊆ [-L, L]` (arXiv:2608.24827, Zhu, eq. (2)):

    Q(f) = 2 F(i/2)^2 + (1/2π) ∫ |F(t)|^2 Ψ_L(t) dt,
    Ψ_L(t) = Re ψ(1/4 + it/2) − log π − P_L(t),
    P_L(t) = Σ_{log n < 2L} (2Λ(n)/√n) cos(t log n).

`|F|^2` is the Fourier transform of `f ⋆ f~`, which is supported in
`[-2L, 2L]`. So for **any** bounded almost-periodic `H` whose frequencies all
satisfy `|λ| ≥ 2L`, `∫ |F|^2 H dt = 0`, and `Ψ_L` may be replaced by
`Ψ_L + H` without changing `Q` on the window. Zhu's one-stroke reduction
(Theorem 1.1) then runs with the envelope constant

    S_L(H) = sup_t (P_L − H)(t)    in place of    A_L = sup_t P_L(t).

Zhu's barrier (Lemma 3.2, Theorem 1.4) is about bounding `P_L` itself: its
sup is `A_L`, so `T_1 = 2π e^{A_L}` is optimal *for pointwise envelopes of
P_L*. Remark 1.6 there says beating it needs Diophantine information about
`{log p}`. The out-of-band freedom uses none: it is a band-limitation fact.

Weak duality (easy): `S_L(H) ≥ λ_max` of the windowed comb operator
`(Pφ)(x) = Σ_n (Λ(n)/√n)[φ(x − log n) + φ(x + log n)]` on `L^2[-L, L]`.
Per prime `p`, the best out-of-band correction of
`φ_p(θ) = Σ_{k log p < 2L} (2 log p / p^{k/2}) cos kθ` has constant
`λ_max` of the Toeplitz matrix with first row `(0, t_1, ..., t_m)`,
`t_k = log p / p^{k/2}` (Carathéodory–Toeplitz), realised to within a Fejér
loss by a nonnegative kernel sum.

## Seed numbers (Scholar's probes, float64, one route: **measured**)

Probes: `probes/comb_operator.py`, `probes/separable.py`. `S_sep` is the
per-prime construction (Fejér degree 64), `S_opt` the comb-operator floor.
`N ≈ e·L·T#/2` is the matrix size with `T# = 2π e^{S + 0.5}`.

| L | A_L | S_sep | S_opt | T_1 (Zhu) | T_1 sep | T_1 opt | N Zhu | N sep | N opt |
|---|---|---|---|---|---|---|---|---|---|
| 0.8 | 2.942 | 1.549 | 1.219 | 119 | 30 | 21 | 213 | 58 | 38 |
| 1.19 | 7.075 | 3.839 | 2.668 | 7.4e3 | 292 | 91 | 2.0e4 | 970 | 241 |
| 1.4 | 10.29 | 5.575 | 3.708 | 1.9e5 | 1.7e3 | 256 | 5.8e5 | 7.2e3 | 804 |
| 2.0 | 24.38 | 13.32 | 7.974 | 2.4e11 | 3.8e6 | 1.8e4 | | | |

Calibration: `N Zhu` at L = 0.8 reproduces the N = 200 of Zhu's run.
Zhu's valid-certificate estimate at L = 1.19 (support 2.38, the claim he
retracted) was N ≈ 1.4–2 × 10^4; the separable correction brings it to the
size of his retracted 950-mode run.

**What this does not do:** `S_opt` still grows like `c·e^L` (measured
c ≈ 1.1 at L = 2), so the threshold stays doubly exponential. The gain is in
the exponent's constant (roughly 4 → 1.1), not the shape. It cannot reach RH,
and the Landau–Widom precision wall (Zhu §12) is untouched.

## Records to beat (to be verified by the theory worker, one normalization)

- Yoshida 1992 / Connes–Consani (arXiv:2006.13771): support log 2.
- Zhu, arXiv:2608.24827v2: half-width 0.8 (support 1.6), computer-assisted.
- Liu, alphaXiv preprint dated 2026-09-14, unrefereed: half-width 1 and 17/16.
- Burnol 2000 and Bombieri 2000 are cited elsewhere with other ranges; pin
  down their normalization.

A valid, enclosure-carrying positivity bound at half-width 1.19 (support
2.38) would be a new record under any of the above.

## Workers and ownership

- `theory/`, branch `teal-sea/oob-cert-theory`: the lemma, its proof, duality,
  asymptotics of `S_opt`, prior art. Brief: `theory/BRIEF.md`.
- `numerics/`, branch `teal-sea/oob-cert`: construction of `H` with
  enclosures, the modified reduction, the L = 0.8 replication, the L = 1.19
  attempt. Brief: `numerics/BRIEF.md`.

- `referee/`, branch `teal-sea/oob-cert-referee`: adversarial review and an
  independent reimplementation, on a different model family. Started only
  once the lemma and the L = 0.8 replication exist. Brief: `referee/BRIEF.md`.

Team (chosen by the supervisor, 2026-09-27):

| lane | harness | model / effort | why |
|---|---|---|---|
| theory | Claude Code | Opus, effort max | proofs and duality are long careful reasoning; few tool calls |
| numerics | Claude Code | Opus, effort high | many tool calls with ball arithmetic; high is enough, max would burn quota on loops |
| referee | Codex | gpt-6-astra, xhigh | a different model family, so it does not share the authors' blind spots |

Method reference for all lanes (read, do not copy into this repo):
`/Users/thomas/.hermes/profiles/scholar/skills/research/computational-math-research/SKILL.md`.

Each worker writes only in its own subdirectory. Supervisor: Scholar (Hermes
cron, every 5 minutes). Questions go at the top of your `PROGRESS.md` under a
`QUESTION:` line; then end your turn and wait.

## Kill-controls

- **K1 (upper-bound consistency).** Zhu's interval-arithmetic variational
  bound gives `λ*(0.8) ≤ 2.27e-17`. Any lower bound this hunt produces at
  L = 0.8 above that is a bug.
- **K2 (unsound pipeline).** Run the same reduction on a function whose Weil
  form is known negative on the window (Epstein (1,1,6) past c ≈ 28 to 29.5,
  or Davenport–Heilbronn past c ≈ 30.6; data in
  `hunts/rogue_frontier/weil_trunc/` and the `weil_propagation` hunt). The
  pipeline must fail to produce a positive bound there. Note these have no
  Euler product, so use a valid joint `H` or `H = 0`, not the per-prime one.
- **K3 (orthogonality).** Check `∫|F|^2 H = 0` numerically on random window
  functions, and check that a deliberately in-band term breaks the identity.

## Rules

- No claim about RH. The certainty ladder in `AGENTS.md` governs every
  statement; a composite claim takes the grade of its weakest step.
- The reserved word banned under `hunts/` stays banned
  (`tests/test_hunt_probe_discipline.py`). Do not quote paper titles that
  contain it.
- **Compute.** This machine is Ghost: 8 GB, and it hosts the Hermes gateway.
  Local runs stay under 10 minutes and 2 GB. Heavy runs go to **Modal**
  (`modal` CLI, profile `teal-sea`), one unit per container, results written
  per unit. **Never GitHub Actions**: this overrides `AGENTS.md` compute rule
  2 for this hunt. Write the estimate in `numerics/RUNS.md` and ask the
  supervisor before any Modal run.
- No push, no PR, no publication, no edits outside `hunts/oob_envelope/`
  (and the one case-log entry). Commit small, often, to your own branch.
