# MISSION: `wide_search`

## Persona

A breadth-first search for one externally checkable mathematical contribution
adjacent to the Riemann zeta function, run under the laboratory's standing
controls. The operator's instruction was explicit: generate approaches in
volume, allocate independent programmes, kill aggressively, search prior art,
reproduce survivors independently, attempt formalization where feasible, and
call nothing new without passing a novelty gate. A negative result is an
acceptable outcome. A rediscovery is an acceptable outcome, provided it is
labelled as one.

## Scope

**This hunt may write**: `hunts/wide_search/` and, if the run earns one, a
single new `docs/NN-*.md` taken from the next free number, plus `figures/`.

**This hunt may not write**: `zeta/`, `ontology/`, `harness/`, `lean/` without
explicit permission, and may not write a verdict into `README.md`,
`ROADMAP.md` or `HANDOFF.md` as an established finding. It may not promote its
own claim. The routes that can say "yes" are the battery
(`docs/doors/refute.md`) and the funnel (`docs/doors/discover.md`), and neither
of them is this hunt.

## Objective

Not RH. RH is allowed but deliberately not privileged, and every direct route
to it carries a standing no-go result (`docs/08`). The target is *adjacent*: a
precise statement about zeta or its neighbours, an identity, an inequality, a
counterexample, an asymptotic, a bound, a negative result, or a machine-checked
formalization, that is

1. **precisely stateable**, so it is either true or false;
2. **externally checkable**, so that somebody outside this tree can settle it
   without trusting this tree; and
3. **not already in the literature**, established by an operator-level search,
   because the offline knownness gate structurally cannot say that anything is
   new (`ontology/knownness.py`: `Knownness` has exactly two values, and
   `establishes_novelty` is hard-coded `False`).

## Method

Breadth first, then adversarial narrowing. The generator of a claim never
judges it, the rule the director run was built on.

1. **Generate.** Independent programmes across disjoint territories, each
   emitting candidate propositions in a fixed schema, each candidate carrying
   its own refutation condition and an honest prior-art risk.
2. **Triage.** A referee that did not generate the candidates kills against the
   standing walls (`docs/08`), the in-tree graveyard, and the rule that raw
   computational reach is a non-goal.
3. **Prior art.** A networked search on survivors. This is the step the
   offline gate refuses to fake.
4. **Attempt.** Compute. Most survivors are expected to die here.
5. **Reproduce.** Anything still standing is rebuilt by a replicator given the
   statement only and forbidden the first implementation, because a
   cross-check bounds only what is actually duplicated.
6. **Formalize** where the statement is small enough to be worth a kernel.

## The standing checklist, answered in advance

1. **Rival.** Any structural claim about zeta goes through
   `zeta.epstein.battery`: zeta against Davenport–Heilbronn and both
   discriminant −23 Epstein forms. A claim a rival also satisfies distinguishes
   nothing. The trap is recorded: if the test set *is* the rival set, the
   measurement is of this laboratory's own admission criterion.
2. **Decoy / surrogate.** Any claimed effect is run against a matched null
   with no arithmetic in it. Davenport–Heilbronn sits at the 27th percentile
   of the random non-factoring null, so "it is unusual" has a denominator here.
3. **Lesion.** Any detector is shown a violation planted on purpose, and must
   distinguish the plant from the claimed signal.
4. **Precision response.** An artifact does not respond to added precision; a
   real quantity does. Every numerical survivor is re-run at strictly higher
   working precision before it is written down.

## What would make this hunt a failure worth recording

Finding nothing is the expected outcome and is not a failure. The failure modes
that would matter are: a claim recorded without its prior-art search; a
numerical effect written down without a precision response; a structural claim
written down without the battery; or a survivor whose generator also judged it.
Each of those is a defect in this hunt, not a weak result.

## Vocabulary

This directory says *measured*, *observed*, *consistent with*. It does not say
*verified*, *confirmed*, *definitively* or *proves*, and it never uses the
reserved word that `zeta/rigor.py` owns for enclosure-carrying quantities,
a ban `tests/test_hunt_probe_discipline.py` enforces on the bytes of every
file here.
