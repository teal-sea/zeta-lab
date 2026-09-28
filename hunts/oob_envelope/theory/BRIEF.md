# Brief: theory worker (out-of-band envelopes)

Read first: `hunts/oob_envelope/MISSION.md`, then `AGENTS.md` (certainty
ladder, reserved words, original vs novel), then arXiv:2608.24827v2 (Zhu)
§1–4 and §14–16. Your worktree: `/Users/thomas/orca/workspaces/zeta-lab/oob-cert-theory`
(branch `teal-sea/oob-cert-theory`). Write only in `hunts/oob_envelope/theory/`.

## Tasks, in order

1. **The lemma, proved.** State and prove: for `f ∈ L^2`, `supp f ⊆ [-L, L]`,
   and a real almost-periodic `H(t) = Σ_w b_w cos(λ_w t)` with
   `Σ|b_w| < ∞` and every `|λ_w| ≥ 2L`, `∫ |F(t)|^2 H(t) dt = 0`. Handle the
   boundary case `|λ_w| = 2L` explicitly (it is a measure-zero issue for L^2
   f, but say why). Then restate Zhu's Theorem 1.1 with `A_L` replaced by
   `S_L(H) = sup_t (P_L − H)(t)` and check line by line that his proof (§4,
   eq. (13) and the tail/coupling bounds) goes through unchanged. Flag every
   place where it does not.
2. **Optimal constant.** Prove weak duality `S_L(H) ≥ λ_max(P_L on L^2[-L,L])`
   for every admissible `H`. Then decide whether equality (strong duality)
   holds, for instance via Perron–Frobenius on the positive-coefficient comb,
   characters of the Bohr compactification, or a finite-dimensional
   Carathéodory–Fejér argument after truncating to finitely many primes. A
   proof, a counterexample, or an honest "unresolved" are all acceptable.
3. **Asymptotics.** Upper and lower bounds on `S*_L = inf_H S_L(H)` as
   `L → ∞`. The measured data suggests `S*_L ≍ e^L` with constant near 1.1 at
   L = 2 (Zhu's `A_L ~ 4 e^L`). Derive the constant if you can (hint: a
   positive test function on `[-L, L]` against the comb gives lower bounds;
   the per-prime Toeplitz construction gives upper bounds). This decides
   whether the doubly-exponential barrier keeps its shape (expected: yes).
4. **Prior art.** Has anyone used out-of-band freedom in Weil positivity or
   in the explicit formula? Check at least: Yoshida 1992, Bombieri 2000
   (Rend. Lincei, and "Remarks on Weil's quadratic functional"), Burnol,
   Connes–Consani arXiv:2006.13771, Connes–Consani–Moscovici arXiv:2511.22755,
   Connes–van Suijlekom arXiv:2511.23257, Suzuki arXiv:2606.09096, Liu
   (alphaXiv, 2026-09-14, "Source-exact block-Schur and tail-compensation
   bounds"), and the Beurling–Selberg majorant literature (Carneiro and
   coauthors, which uses band-limited majorants on the *zero* side).
   Record exact citations with arXiv IDs and section numbers. Also pin down
   the true current record for unconditional window positivity, in one
   normalization (half-width L of `supp f`).
5. **Liu's obstruction.** Liu proves a tail-dropping localization has a
   negative high-frequency limit past half-width log 8 / 2 and that no fixed
   compact correction repairs it. Does that obstruction touch the
   out-of-band route? Answer from the paper's actual statement.

## Output

`hunts/oob_envelope/theory/RESULTS.md`, opening with a **5-line graded
summary** (one line per task finding, each with its ladder grade), then the
statements and proofs. `PROGRESS.md` updated at each step. Small commits to
your branch; do not push. No heavy computation: anything over a minute of
CPU belongs to the numerics worker (write the request in `PROGRESS.md`).

When blocked, write `QUESTION: ...` at the top of `PROGRESS.md` and end your
turn. The supervisor answers there and in your terminal.
