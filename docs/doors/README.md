# Entry-point guides

One page per way into the repository. A repository with several purposes
does not get several repositories; it gets one verified core and several
short entry points. The core is `zeta/` and its tests, `ontology/` and its
seam. Each guide names an audience, states what they can do here, and gives
the first command to run.

`harness/` was a third; it was **demoted on 2026-08-13** after being tested
against the practice it was meant to improve. Its guide is kept and banners
the verdict, because deleting the guide to a thing you decided against is how
a lab forgets what it learned (`harness/VERDICT.md`).

The cost of adding a purpose is a guide page plus a test that the page's
command still works. A purpose that will not pay that cost stays a
document, not a directory.

(The directory is named `doors/` for historical reasons; department code
references these paths, so the name stays.)

## The guides

| Guide | For you if you want to… | First command |
|---|---|---|
| [learn.md](learn.md) | see the classical machinery run at arbitrary precision | `.venv/bin/python scripts/06_tour.py` |
| [refute.md](refute.md) | test a claim about the zeros against the control battery | `.venv/bin/python scripts/23_gate_3_battery.py` |
| [certify.md](certify.md) | work in a regime where nothing is measured, Lean proofs and interval enclosures | `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` |
| [discover.md](discover.md) | run the conjecture funnel and see its measured hit rate | `.venv/bin/python scripts/13_discovery_run.py --dry-run` |
| [contribute.md](contribute.md) | return an agent-assisted finding as a checkable research pull request | `.venv/bin/python scripts/71_contribution_check.py hunts/<short-name>` |
| [adopt.md](adopt.md) | *(demoted)* the validation framework, and why it was frozen | `.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_protocol.py tests/test_department_conformance.py` |

If you are new and unsure: **[refute.md](refute.md)**, it is the one thing
this repository does that a textbook, a notebook or a literature survey
does not. If you are here for the validation pattern rather than for ζ:
**[adopt.md](adopt.md)**.

## Departments

A *guide* is for a reader. A **department** is a registered subject: the
subject itself, plus the battery of controls that can refute claims made in
that subject's name, plus a guide page. Departments are declared in
`harness/departments/` and audited by
`tests/test_department_conformance.py`, which is parametrized over all of
them, adding a department adds its audit automatically.

The admission rule: **no department without a battery.** Work whose claims
nothing in this tree can falsify is not a department; it is exploratory,
and exploratory work lives where nobody will mistake it for a result.

That is also the *only* thing the core asks. A department keeps its own
guides, its own reading course, its own gallery, [learn.md](learn.md) and
the heat-equation chain in `README.md` belong to the zeta department, and
the next department is entitled to the same room.

| Department | Subject | Battery |
|---|---|---|
| [`zeta`](zeta.md) | the Riemann zeta function and RH | 3 rivals, 2 decoys, 3 surrogates, 3 lesions |
| [`finitefield`](finitefield.md) | curves over F_p, where RH is a theorem | 2 rivals, 2 decoys, 2 surrogates, 3 lesions |
| [`compiler`](compiler.md) | LLVM IR rewrites, belief in a transformation, separated from its size | 3 rivals, 2 decoys, 3 surrogates, 4 lesions |
| [`croniter`](croniter.md) | cron schedule union semantics under `#`/`W`, the first foreign-domain subject, battery content authored independently | 2 rivals, 2 decoys, 2 surrogates, 3 lesions |
| [`referee`](referee.md) | the verification machinery itself, hollow batteries detected, the audit's power measured, blind spots pinned | 3 rivals, 2 decoys, 3 surrogates, 4 lesions |
| [`stateval`](stateval.md) | statistical model evaluation, whether a reported improvement is skill or protocol | 3 rivals, 2 decoys, 2 surrogates, 3 lesions |

Every department also carries **declared detectors** (power and specificity
measured, floors stated), a **scope** (what a pass licenses), and a
**provenance record** (who authored the battery content, and blind or not).
Every claim outcome is paired with the battery's integrity grade, see
[`docs/20`](../20-verification-integrity.md), and run the whole thing:

```bash
.venv/bin/python -m harness.demo
```

See `harness/README.md` for what the four control roles mean;
`python -m harness.new_department <name>` scaffolds the next one.

## Exploratory areas

The other side of the admission rule. Exploratory work is work whose claims
nothing in this tree can yet falsify, a normal and useful state, not a
criticism. It is kept where nobody will mistake it for a result, appears in
no department table, and gets no guide page.

| Area | What it is |
|---|---|
| [`dossier/`](../19-research-dossiers.md) | representing research state, intent, definitions, rejected alternatives, obligations, evidence, so an agent can *resume*. Four independent support axes, no aggregate |
| [`hunts/`](../../hunts/README.md) | scoped exploratory studies; most fail, and the failures are recorded |

Neither becomes a department by growing. Their negative controls are the
*zeta* department's, and a department whose battery belongs to another
department is not a department, the reason is recorded in
[`docs/19`](../19-research-dossiers.md) §6.
