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

If you are new and do not know which you want: **[refute.md](refute.md)**. It is
the only one of the four that does something no textbook, notebook or
literature survey does for you.

## Departments

A *door* is for a reader. A **department** is for the code: a subject, plus the
battery of instruments entitled to kill claims made in that subject's name,
plus the door above. Departments are declared in `harness/departments/` and
audited by `tests/test_department_conformance.py`, which is parametrized over
all of them — so adding a department adds its audit automatically.

The admission rule is short: **no department without a battery.** A body of
work whose claims nothing in this tree can falsify is not a department, it is a
probe, and probes live where nobody will mistake one for a result.

| Department | Subject | Battery |
|---|---|---|
| `zeta` | the Riemann zeta function and RH | 3 rivals, 2 decoys, 3 surrogates, 3 lesions |

See `harness/README.md` for what those four words mean and how to add the
second department.
