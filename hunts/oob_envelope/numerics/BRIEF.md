# Brief: numerics worker (out-of-band envelopes)

Read first: `hunts/oob_envelope/MISSION.md`, then `AGENTS.md` (certainty
ladder, compute discipline, reserved words), then arXiv:2608.24827v2 (Zhu)
§1–5 and §7. Seed probes: `hunts/oob_envelope/probes/`. Your worktree:
`/Users/thomas/orca/workspaces/zeta-lab/oob-cert` (branch
`teal-sea/oob-cert`). Write only in `hunts/oob_envelope/numerics/`. Python:
`/Users/thomas/zeta-lab/.venv/bin/python` (numpy, scipy, mpmath,
python-flint 0.9 are installed; the worktree has no venv of its own).

## Phases, in order

1. **H with enclosures.** For L ∈ {0.8, 1.0, 1.19}, build the per-prime
   out-of-band correction (Fejér-smoothed Carathéodory–Toeplitz, as in
   `probes/separable.py`) with rational or ball coefficients, and bound
   `S = sup_t (P_L − H)(t)` rigorously. Per prime the claim is
   `Φ_p = M_p − φ_p + h_p ≥ 0` as a trigonometric polynomial in θ; prove it by
   exhibiting `Φ_p` as a nonnegative combination of Fejér kernels (exact
   arithmetic) or by an arb enclosure of its minimum. Then `S ≤ Σ_p M_p`.
   Report both the separable constant and, as a stretch, a joint LP/SDP
   constant on the first few primes' torus.
2. **K3**, then **L = 0.8 replication with H**: assemble Zhu's reduced form
   (eq. (4)) with `Ψ_L + H`, the threshold now `T# > 2π e^{S}`, and compute
   `λ_min` of the leading block. Expect a much smaller matrix than Zhu's
   N = 200. Check K1: your lower bound must not exceed 2.27e-17. Float first
   (measured), then with mpmath / arb enclosures and Zhu's two-block bound
   (13) with explicit `ε_D`, `ε_B` (hardened). Remember `H` adds
   out-of-band terms to the symbol, so the frequency-cut matrix entries must
   include them: they are not zero inside `[0, T#]`.
3. **L = 1.19 (support 2.38).** Estimate cost from phase 2 (N, precision near
   the Landau–Widom floor ~1e-47 per Zhu §7/§12), write the estimate in
   `numerics/RUNS.md`, put `QUESTION: approve Modal run` at the top of
   `PROGRESS.md`, and stop. Do not launch it yourself before the supervisor
   answers.
4. **K2** on Epstein (1,1,6) or Davenport–Heilbronn at a window where the
   form is known negative (see MISSION.md). The reduction must not return a
   positive bound there.

## Output

`hunts/oob_envelope/numerics/RESULTS.md`, opening with a **5-line graded
summary** (each line with its ladder grade and the commit/JSON it rests on),
raw numbers in JSON beside it, reproduction commands at the end.
`PROGRESS.md` updated at each phase. Small commits; do not push.

## Limits

Local runs under 10 minutes and 2 GB (Ghost has 8 GB and hosts the chat
gateway; an out-of-memory hangs it). Anything heavier: Modal, after the
supervisor approves. Never GitHub Actions. When blocked, write
`QUESTION: ...` at the top of `PROGRESS.md` and end your turn.
