# Doors

One page per way in. A repository with several purposes does not get several
repositories; it gets **one spine and several doors**. The spine is the
verified core — `zeta/` and its tests, `ontology/` and its seam, `harness/` and
its protocol. A door is a short page that names an audience, states what they
can do here, and gives the first command to run.

The cost of a purpose is a door plus a test that the door still works. A
purpose that will not pay that cost stays a document, not a directory.

## The doors

| Door | For you if you want to… | First command |
|---|---|---|
| [learn.md](learn.md) | see the classical machinery happen, at arbitrary precision | `.venv/bin/python scripts/06_tour.py` |
| [refute.md](refute.md) | **bring a claim about the zeros and have it attacked** | `.venv/bin/python scripts/23_gate_3_battery.py` |
| [certify.md](certify.md) | work in a regime where nothing is measured | `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` |
| [discover.md](discover.md) | run the conjecture funnel and see its hit rate | `.venv/bin/python scripts/13_discovery_run.py --dry-run` |
| [adopt.md](adopt.md) | take the referee for a subject that is not ζ | `.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_protocol.py tests/test_department_conformance.py` |

If you are new and do not know which you want: **[refute.md](refute.md)**. It is
the only door to the mathematics that does something no textbook, notebook or
literature survey does for you. If you are here for the refereeing pattern
rather than for ζ, that is a distinct audience and it has its own door:
**[adopt.md](adopt.md)**.

## Departments

A *door* is for a reader. A **department** is for the code: a subject, plus the
battery of instruments entitled to kill claims made in that subject's name,
plus the door above. Departments are declared in `harness/departments/` and
audited by `tests/test_department_conformance.py`, which is parametrized over
all of them — so adding a department adds its audit automatically.

The admission rule is short: **no department without a battery.** A body of
work whose claims nothing in this tree can falsify is not a department, it is a
probe, and probes live where nobody will mistake one for a result.

That is also the *only* thing the spine asks. A department keeps its own
doors, its own reading course, its own gallery — [learn.md](learn.md) and the
heat-equation chain in `README.md` are department #1 enjoying itself, and the
next department is entitled to the same room.

| Department | Subject | Battery |
|---|---|---|
| [`zeta`](zeta.md) | the Riemann zeta function and RH | 3 rivals, 2 decoys, 3 surrogates, 3 lesions |
| [`finitefield`](finitefield.md) | curves over F_p, where RH is a theorem | 2 rivals, 2 decoys, 2 surrogates, 3 lesions |
| [`compiler`](compiler.md) | LLVM IR rewrites — belief in a transformation, separated from its size | 3 rivals, 2 decoys, 3 surrogates, 4 lesions |

See `harness/README.md` for what those four words mean and how to add the
second department.

## Probes

The other side of the admission rule. A probe is work whose claims nothing in
this tree can yet falsify — which is a normal and useful state, not a
criticism. Probes are kept where nobody will mistake one for a result, they
appear in no department table, and they get no door.

| Probe | What it is |
|---|---|
| [`dossier/`](../19-research-dossiers.md) | representing research state — intent, definitions, rejected alternatives, obligations, evidence — so an agent can *resume*. Four independent support axes, no aggregate |
| [`hunts/`](../../hunts/README.md) | scoped exploratory attacks, with permission to be wrong in public |

Neither becomes a department by growing. Their rivals are the *zeta*
department's rivals, and **a department whose battery is another department's
battery is not a department** — the reason is recorded in
[`docs/19`](../19-research-dossiers.md) §6.
