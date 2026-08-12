# PIPELINE — the formalization endgame, arranged so nothing waits on anything it does not need

**Written 2026-08-12.** The plan for finishing the Lean arm of the transplant
chain (and the one adjacent higher_xi batch), arranged as four independent
lanes plus a standing collection loop. The organising fact is latency:
Aristotle turnaround is hours (the calibration batch measured ~8 h for a hard
lemma), local drafting is minutes-to-hours, and the two overlap completely if
submissions go out first. So the rule is **submit early, draft during the
round-trip, collect late, and never let a session idle waiting on a project
id it could have polled**.

House rules that bind every lane: an artifact counts only after the static
refusal scan and a zero-`sorry` `lake build` on this repository's toolchain
(`lean/proof_adapter.py`; Aristotle's own claims are input, not evidence).
Every submission gets a row in `lean/ARISTOTLE-RUNS.md` **appended by the
submitting session in its own worktree** — that file is the serialization
point; never rewrite existing rows, only append and update your own. Do not
resubmit an unchanged statement. A collected artifact's *statement* must be
read against what the chain needs before its module lands — the kernel
guarantees the proof, not the relevance — and that reading is a
frontier-model task, not a formality.

Machine constraint: the collection poller may run anywhere; the kernel-check
half (`proof_adapter.py check`) must run on a machine with elan and the
pinned toolchain.

---

## Lane 0 — the collection loop (standing, cheap)

A recurring session every 2–3 h: for each open project id in
`lean/ARISTOTLE-RUNS.md`, attempt `collect_from_aristotle`, run
`proof_adapter.py check` on anything returned, and append the outcome
(`collected — accepted`, `collected — refused (<reason>)`, `no output`) to
the ledger row. It never lands modules and never judges statements; it turns
"came back" into a recorded fact so the owning lane's next session starts
from state instead of polling.

**Model: Haiku 4.5** (mechanical; judgment is explicitly withheld from this
lane). Set up with `/loop` or `/schedule` in Claude Code.

## Lane 1 — the transplant chain to its conditional endgame

The only lane with internal sequencing. Steps, each a submission wave with
drafting done during the previous wave's round-trip:

1. **Pin port (submit first, zero drafting).** Resubmit the existing
   `Composition.lean` and `GridIncidence.lean` statements verbatim under
   Mathlib v4.33.0-rc2 (upstream `zeta-23-lean`'s pin). This retires the
   v4.28.0 mismatch without a local Mathlib compile.
   *Prep model: Sonnet 5* (~30 min, then hours of service time).
2. **Bridge spec (draft during wave 1).** Restate the composition on the
   upstream repo's types — `Matrix (Fin (P.d T)) _ ℂ`,
   `RHLinalg.rtrace`/`frobSq`/`posIndex`, `ZeroBlockData` — forking at
   `rank_trace_mult` where upstream discards `tr(PQ)`. Type fidelity is the
   whole game; a wrong statement wastes an 8 h round-trip.
   *Model: Opus 5.* Submit as its own batch when wave 1 returns.
3. **Census spec.** The gap-census counting function on `ZeroConfig`, seamed
   one-sidedly to `N0simple` via the floor's monotonicity in ν.
   *Model: Opus 5.* Drafts during wave 2's round-trip.
4. **`RetentionHypothesis.lean` + `Main.lean` (no Aristotle needed for the
   skeleton).** θ = 995/1000 as a named hypothesis; the endgame clones
   upstream `thmD_mult2_abstract` carrying the census term through the full
   error ledger, concluding `(H + 2·θ·c_u − ε)·N ≤ N0simple` **given the
   retention hypothesis**. This is writable now and stays honest whatever
   Lane 2 does; glue obligations it surfaces become the final batch.
   *Model: Opus 5.*
5. **Single assembly build.** One local `lake build` of `zeta23ext` at the
   end (per its README: service-side per module, one assembly build, never a
   partial `.lake/` in the tree), plus the suite, `make_context --check`,
   land and push. *Model: Sonnet 5.*

## Lane 2 — the H3 attack (the critical unknown; start now, in parallel)

H3 is not an engineering gap: it is the reduction of the retention to the
band certificate, equivalently (after the per-pair refutation) one
bandlimited nonnegative-kernel inequality in two exponential sums. Three
moves, concurrent:

- **Statement drafting.** Produce 2–3 candidate formal statements of the
  inequality (with `c₂ = φ²∗φ²`, `E[G] = A⁻²∫c₂|G|²`, `F_on`, `F_p` as in
  `PROOF-LEDGER.md`), each with its reduction chain written next to it, so a
  service run attacks the statement we actually need. Half a day.
  *Model: Fable 5* — this is the run where model quality buys the most,
  because a subtly wrong statement burns the longest round-trips.
- **Submit prove-or-refute.** The service has already produced a
  counterexample against one of our hypotheses (evenness) and a stronger
  proof than requested (polarised Parseval); all three outcomes of this
  batch are wins — the chain upgrades, blocker 2 dies honestly into the
  graveyard, or we learn the obligation's price.
- **Paper attack, racing the service.** A frontier-model session working the
  inequality directly, and feeding any sub-lemma it isolates into the next
  batch. *Model: Fable 5.*

Submittable **today**, before the main statement is ready: the `c₂` support
and nonnegativity lemmas (needed under every outcome) and the
coincident-stack excess closed form `[2Σ_{i<j}F_iF_j − (k−1)(cK)²]/(4cK)` as
exact algebra (cheap, calibrating). *Prep: Sonnet 5.*

## Lane 3 — depth-cell hardening (independent, start now)

The 18-cell tiling of (0, ½] is double-precision. Skip the arb rung and go
straight to the kernel the way `BandCert/` did: generate rational interval
covers per cell locally (python-flint), then submit BandCert-style per-cell
certificates. Local data generation *Model: Sonnet 5*; cover-spec review
before submission *Model: Opus 5*.

## Lane 4 — higher_xi route A (independent, one batch only)

From `hunts/higher_xi/LEAN-FRONTIER.md`'s dependency boundary, submit **only
item 4** — reconstruction of the exact downstream rational from the
40-coefficient data and its tail bound inside Lean — which is
FloorCert-shaped and cheap. **Do not spend Aristotle runs on items 1–3**
(the RAMS2 square-density asymptotic with uniformity, the marked-cluster
derivative estimate, the smoothed contour transfer): those are deep analytic
theorems outside what the calibration batch showed the service buys, and a
predictable `no output` there is time and ledger noise. They stay on the
paper-mathematics queue. *Spec model: Opus 5.*

## Day-0 checklist (what goes out before anything is drafted)

| submission | lane | drafting needed | prep model |
| --- | --- | --- | --- |
| Composition + GridIncidence @ v4.33.0-rc2 | 1 | none (verbatim) | Sonnet 5 |
| c₂ support + nonnegativity lemmas | 2 | minutes | Sonnet 5 |
| coincident-stack excess, exact algebra | 2 | minutes | Sonnet 5 |
| 18-cell cover data generation (local, no service) | 3 | — | Sonnet 5 |
| H3 statement drafting (local, no service) | 2 | half day | Fable 5 |
| Bridge spec drafting (local, no service) | 1 | during wave 1 | Opus 5 |

Every Claude Code session takes its own worktree; `lean/ARISTOTLE-RUNS.md`
rows are append-only per session; merges to main go through the usual gates.

## The honest shape

Lanes 1, 3 and 4 are bounded work: specs, round-trips, kernel checks. Lane 2
is the only unknown, and the pipeline is arranged so its outcome changes the
*grade* of the endgame, never its *existence*: if H3 falls, `Main.lean`
drops its named hypothesis; if it resists, the endgame lands conditional
with `RetentionHypothesis` in its statement, said plainly. Wall-clock is
dominated by service round-trips, and under this arrangement every
round-trip has a local drafting task scheduled inside it.
