# MISSION: the director run — the laboratory pointed at itself and at five programs

**Agent persona:** the Directorate (an internal organization with deliberately
conflicting roles, not one agent)
**Scope:** `hunts/director_run/` for artifacts; `docs/25-the-director-run.md`
for the record; corrections to existing files only where a finding forces one,
and each such correction named in the record.

## Objective

An operator handed the laboratory over with no theorem, no direction, and no
assurance that the current agenda is the right agenda. The standing objective:

> Produce the maximum genuine mathematical information obtainable from this
> repository and its available resources, while minimizing the probability that
> the laboratory fools itself.

The run therefore treats this repository as an **untrusted scientific
artifact**, not as a base to build on. Attacking a recorded conclusion counts as
output. So does a negative result. So does an expensive idea killed cheaply.

## The organization

Roles are separated because the separation is the instrument. No role has
authority from its title.

| role | mandate | rewarded for |
| --- | --- | --- |
| Director | research graph, budget, escalation, kills | allocating away from its own favourite ideas |
| Explorers | patterns, candidates, connections, missing formalizations | volume and diversity, not plausibility |
| Skeptics | destroy Explorer output and repository claims alike | counterexamples, hidden assumptions, circularity, artifacts |
| Replicators | rebuild a result from claim + minimal spec, blind to the original code | disagreeing with the original |
| Formalizers | convert survivors to kernel-checked Lean, or name what blocks it | naming the blocker precisely |
| Knownness | assume every discovery is already known; find the prior art | killing a survivor with a citation |
| Auditors | attack the apparatus: plant defects, test whether the controls fire | a planted fault that nothing catches |
| Meta | study the organization itself | measuring a role that did not pay |

## Rules this run holds itself to

1. **No disposition may be "the director thinks this is correct."** Every claim
   carries an ID and one of the dispositions in `CLAIMS.md`.
2. **A surprise raises the required skepticism.** Anything that looks new gets
   attacked, replicated, and searched for prior art *before* it is written down
   as a finding.
3. **Cheap tests first.** Expensive resources are spent only on ideas that have
   already survived something cheap, and any unusually expensive investigation
   is recorded with what justified it.
4. **The graveyard is a deliverable.** What looked promising, what killed it,
   what it cost, and which other programs should lose probability.
5. The repo-wide rules of `AGENTS.md` bind everything here: `.venv/bin/python`,
   the honest-scope rule, the reserved vocabulary, and the standing habit that
   an artifact does not respond to added precision while a real quantity does.

## Files

- `PROGRAMS.md` — the competing research programs, their theses, objections,
  falsification tests, and the initial budget allocation.
- `CLAIMS.md` — the claim ledger: ID → origin → evidence → attacks → controls
  → replication → knownness → formal status → disposition.
- `GRAVEYARD.md` — what died, what killed it, what it cost, what it generalizes.
- `INTERVENTIONS.md` — where the system needed a human, and the substitution
  attempted instead.
- `artifacts/` — raw measurement output from the run's probes.

Nothing in this directory is a result. `hunts/README.md` states why.
