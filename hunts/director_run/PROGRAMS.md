# PROGRAMS — the competing research programs and the initial allocation

Written **before** the first result came back, so the allocation can be scored
against what actually happened. Amendments are appended with a timestamp, never
edited in place.

The unit of budget is one **agent-unit**: one investigator working in parallel
with an isolated context, roughly bounded by "keep every single computation
under a few minutes on four cores". The run's hard resources: 4 cores, 15 GB,
no external mathematical database, mpmath/numpy/sympy/python-flint, and a Lean
toolchain that had to be installed from scratch (it was absent).

---

## P1 — AUDIT: the repository is an untrusted artifact

**Thesis.** In a tree with ~2 200 tests, 25 documents and a large verification
superstructure, the densest source of new *true* statements is not new
mathematics — it is the gap between what the prose claims and what the code
establishes.

**Why it might succeed.** Several strategic conclusions are carried by prose
rather than by a test. The reserved-word discipline is lexical (a grep), not
semantic. Every prior audit was run by the same process that wrote the claims,
so correlated blind spots are expected rather than surprising.

**Strongest objection.** Three audits already ran and are recorded as complete;
the tree is unusually careful; expected yield could genuinely be zero.

**Cheap falsification.** Two bounded skeptic sweeps (ball arithmetic; numerics).
If both return only CLEARED verdicts, the program is over-funded and loses its
budget to P4.

**Potentially decisive experiment.** Mutation testing (P5) — planting defects
and measuring what the suite catches — converts "the audit found nothing" from
a reassurance into a measurement.

**Dependencies.** A green baseline suite; otherwise every verdict is confounded.
**Expected information gain.** HIGH. **Cost.** LOW. **Initial allocation: 2.**

---

## P2 — SHIFT: the blindness argument, made precise or destroyed

**Thesis.** The repository has recorded three times, and used once to *close an
avenue*, the claim that a statistic computed from arithmetic (coefficients)
alone is "blind to the position of the critical line by construction", on the
grounds that `f(s−δ)` carries the same arithmetic with its zeros somewhere else.
That claim is either a theorem with unstated hypotheses or it is false. The
laboratory does not currently know which, and it has already spent the claim.

**Why it might succeed.** It is elementary, cheap, and decidable. Every object
it needs — `factorization.D`, the local instrument of hunt #5, the Mertens and
Baez–Duarte faces in `criteria.py` — is already in the tree.

**Strongest objection.** It may terminate in a wording fix, which is
housekeeping, not information. It may also be so obvious once stated that the
"hidden hypothesis" was never really hidden.

**Cheap falsification.** Exhibit a single coefficient-only statistic that does
detect the shift. If none can be found in an hour, the claim gains support.

**Potentially decisive experiment.** A proposition with explicit hypotheses, a
proof sketch, and an explicit counterexample showing the hypotheses cannot be
dropped — plus the list of which recorded uses survive.

**Dependencies.** None beyond the installed package.
**Expected information gain.** HIGH if false (it reopens a closed avenue and
retargets the requirement that closed it), MED if it survives with a wording
fix. **Cost.** LOW. **Initial allocation: 1.**

---

## P3 — RUNG3: is the formal arm's flagship target reachable at all?

**Thesis.** The laboratory's largest formalization target (rung 3, the
Davenport–Heilbronn statement in Lean) is blocked on a question that needs *no
Lean at all*: `scripts/61_rung3_mirror.py` is a bit-exact rational mirror of the
whole interval layer, so feasibility is a Python measurement. The previous
session left one genuinely unresolved trade — the centre cell fails by 37% and
the fix inflates the literals that already blew a tactic's step limit.

**Why it might succeed.** The mirror exists, the parameter space is small
(orders, precisions, geometry, budget split), and the previous session's own
data says the grid is a *headroom* problem, not a geometry problem: 59 of 59
sampled sites landed within ±2% of their own threshold.

**Strongest objection.** This is engineering, not mathematics; and a
configuration with 10% width headroom but ten times the literal size can be
worse than no configuration at all.

**Cheap falsification.** Reproduce the previous session's site numbers first. If
they do not reproduce, that *is* the finding, and it is a large one.

**Potentially decisive experiment.** A plan v3 with ≥10% margin everywhere and a
priced literal budget — or a sharp inequality showing the architecture cannot
carry the centre.

**Dependencies.** The mirror; no Lean toolchain required.
**Expected information gain.** HIGH — it either unblocks or kills the flagship.
**Cost.** MED. **Initial allocation: 1.**

---

## P4 — CANDIDATES: generate far more than can be afforded, then murder cheaply

**Thesis.** The recorded funnel yield is approximately zero *by design*. The
only way to get a survivor is to raise the input rate and lower the cost of
killing, not to think harder about the first plausible idea.

**Why it might succeed.** The tree contains an unusual asset: the
Davenport–Heilbronn function and curves over finite fields are places where
*ground truth exists*, so a candidate can be decided rather than argued.

**Strongest objection.** Volume generation produces mostly already-known or
malformed items, and the murder step is where all the cost lands.

**Cheap falsification.** If fewer than ~3 of 60 candidates survive a
five-minute attack, this channel does not deserve further budget this run.

**Expected information gain.** MED. **Cost.** LOW. **Initial allocation: 1.**

---

## P5 — LESION: does the apparatus catch faults that are actually planted?

**Thesis.** A suite's power is unmeasured until faults are planted in it. The
tree plants faults at the *battery* level (`harness/shams.py`) and at the
*detector* level, but the mathematical core has never had defects planted in it
with the detection rate measured. Until that number exists, "the suite is green"
is a statement about the suite, not about the mathematics.

**Why it might succeed.** Mutation testing is mechanical and the preregistration
is easy: state the mutation set and the scoring rule before running it.

**Strongest objection.** Mutation testing measures test *coverage of the code*,
not correctness of the mathematics, and a high catch rate can be produced by
tests that pin outputs to themselves.

**Cheap falsification / decisive experiment.** They are the same thing here: the
catch rate. A survivor mutation — a wrong function that the whole suite passes —
is the highest-value single object this program can produce.

**Dependencies.** An isolated worktree (mutations must never touch the main
tree) and a green baseline.
**Expected information gain.** HIGH. **Cost.** MED. **Initial allocation: 1
(wave 2, after the baseline is green).**

---

## P6 — FORMALIZE: kernel-check something, or name what blocks it

**Thesis.** Of everything in this laboratory, only the Lean arm produces claims
that survive an adversary by construction. A survivor that can be stated in Lean
should be.

**Strongest objection.** The toolchain was absent at run start; a Mathlib cache
is several gigabytes and a cold build is expensive. Spending a large fraction of
the run's wall clock to kernel-check a triviality would be exactly the failure
mode the operator warned about ("beautiful machinery that produces no science").

**Cheap falsification.** Install the toolchain and try to reproduce the repo's
own claim that `lean/` builds with zero `sorry`s. If the cache cannot be
fetched, the program is dead on resources and says so.

**Expected information gain.** MED (it independently checks the repo's loudest
verification claim). **Cost.** MED–HIGH, mostly wall clock, little attention.
**Initial allocation: 0.5, contingent.**

---

## P7 — KNOWNNESS: a gate, not a program

Every survivor from any program must pass a prior-art search before it is
written down as a finding, on the standing assumption that it is already known.
Not separately budgeted; charged to whichever program produced the survivor.

---

## Deliberately not funded, and why

- **Raw computational reach** (large zero computations, deep scans). `AGENTS.md`
  names this an explicit non-goal, the tables are not in the tree, and four
  cores are not where that work belongs.
- **More meta-infrastructure.** The tree already carries a conjecture funnel, a
  validation harness with six departments, a research-dossier probe, an
  intervention ledger and a promotion gate. The marginal value of a seventh
  layer is low, and the operator's instruction was explicit: infrastructure must
  earn its existence by enabling an experiment.
- **Anything needing an outside team.** The repo names outside adoption as the
  experiment most likely to hurt it, and it cannot be run from inside.
- **New departments.** Admission costs a battery with rivals, decoys,
  surrogates, lesions and reference claims. Nothing this run generated is close
  to paying that.

---

## Scoring rule, fixed in advance

A program keeps its budget if it produces, per agent-unit, at least one of:
a **defect** in a recorded claim, a **negative result** that changes what
another program should do, a **replication failure**, or a **survivor** that
passes the knownness gate. A program that produces only reassurance loses its
budget to the program with the highest realized information per unit — and
"nobody has attacked it yet" is scored as a *penalty*, not as a survival.

---

## Amendments

*(appended as the run proceeds)*
