# INTERVENTIONS: where the system needed a human, measured honestly

The metric the operator named is **legitimate research output per unit of scarce
human judgment**. That needs a denominator, and the denominator is only useful
if it is not gamed. This file records every point where the run believed it
needed the operator, whether the need was real, and what was substituted.

The run was instructed **not** to optimise for zero interventions. Two were
genuinely deferred; the rest were substituted, and the substitutions are named
so they can be scored later.

---

## I-1: Which research programs to fund (SUBSTITUTED)

**Decision required:** the operator explicitly declined to assign a direction.
**Why the system could not resolve it from the repository:** `ROADMAP.md` states
a next build, but the mandate was that the current agenda might be wrong.
**Substitution attempted:** five competing programs were constructed with
theses, objections, cheap falsification tests and a scoring rule fixed *before*
any result returned (`PROGRAMS.md`), so the allocation is auditable after the
fact instead of being a matter of taste.
**Outcome:** the scoring rule fired as designed, the candidate-generation
programme (P4) failed its own pre-registered test (fewer than three survivors
of a five-minute attack) and did not get renewed; the audit programme (P1)
returned six defects and was extended.
**Capability that would remove this intervention:** none needed. This is the
kind of judgment the system can make provided it commits to the criteria first.

## I-2: Whether to spend the run's wall clock installing a Lean toolchain (SUBSTITUTED)

**Decision required:** several gigabytes and an unknown fraction of the run, for
a capability the environment did not have.
**Why it looked like a human call:** the operator warned specifically against
building infrastructure because infrastructure is satisfying to build.
**Substitution:** it was made reversible and cheap to abandon, the install ran
in the background against a fixed falsification test ("does the repository's own
zero-`sorry` claim reproduce?"), so its cost was wall clock the run was spending
anyway and its value was a replication rather than a capability.
**Outcome:** replicated (8715 jobs, zero `sorry`s). Justified.

## I-3: Whether to modify `zeta/` at all (SUBSTITUTED, with a rule)

**Decision required:** `hunts/README.md` forbids a hunt from modifying `zeta/`
without explicit permission, and the operator's mandate explicitly allowed
modifying the lab.
**Substitution:** a rule fixed in advance, a change to `zeta/` is allowed only
where a defect was *reproduced by the director independently of the agent that
reported it*, and only with a regression test or an explicitly corrected
contract. Six changes met it. Nothing was changed because it looked better.

## I-4: Whether `hunts/local_positivity/` could be repaired by this run (SUBSTITUTED)

Its `MISSION.md` scopes that hunt to itself. The run's justification for editing
it is that `provenance_report()` was publishing a **false statement about its own
module's theorem** in machine-readable output; leaving a known-false field in
returned data because of a scope rule would be the rule defeating its purpose.
Recorded here so the exception is visible rather than silent.

## I-5: Adjudicating the shift result (SUBSTITUTED, the load-bearing one)

**Decision required:** an explorer produced a five-part refutation of a
repository claim, some of which was right and some of which was not. Adjudicating
that is exactly the "severity calibration" and "skepticism routing" that
`meta/operator-functions.md` identifies as the operator's residual role.
**Substitution:** two further agents, each blind to the other, one paid to
destroy the result and one paid to find prior art. They converged: the numbers
survived, the inferences did not, the mathematics turned out to be known, and
the skeptic found a defect the original had missed.
**What this measures:** the substitution worked *because the parties were
independent and had opposed incentives*, which is the same condition
`meta/ledger.py` records as the guard on self-adjudication. It is not evidence
that a single agent could have done it.
**Residual human need:** the *decision to accept the skeptic over the explorer*
was made by the director, which is a party to the dispute. That is the one
structural weakness in this run's adjudication, and it is recorded rather than
resolved.

---

## Genuinely deferred to the operator

**D-1: Nothing here should be published outside this repository.** The run
produced no new mathematics (the knownness gate says so explicitly, at ~0.9
confidence). No external review is warranted and none is requested.

**D-2: The rung-3 re-plan is a build decision, not a measurement.** The run
measured that a feasible configuration exists and priced it at ~130k terms
against 79.5k. Whether to spend that compute, and whether to instead do the
architectural fix (a polar or mean-value enclosure of `m^{-s}`, worth ~2× on the
whole certificate), is a resource call with no reversible experiment that
substitutes for it. It is the one place this run stops and asks.

---

## Honest accounting

| quantity | value |
| --- | --- |
| interventions believed necessary | 7 |
| substituted by an independent agent or a pre-committed rule | 5 |
| genuinely deferred | 2 |
| interventions the substitution demonstrably failed | 0 *(no substitution was later found to have been wrong, but the run has no independent check on that, which is itself the limit of this table)* |

The last row is the one to distrust. A ledger kept by the system whose autonomy
it measures cannot certify its own substitutions, and this one does not claim to.
