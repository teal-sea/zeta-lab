# Zeta Lab

A computational and formal workbench around the Riemann zeta function.

Its purpose is that you can **check it yourself**: clone it, run it, and
re-derive the numbers rather than take them. Every number claimed in a
docstring is pinned by a test, identities are exposed as measured *defect*
functions rather than assumed, and the Lean arm is checked by a proof kernel.

**Nothing here is evidence for the Riemann Hypothesis, and no computation
could be.** That is a theorem, not modesty: `docs/08-why-it-is-hard.md` has
Littlewood's, and the failure catalogue for every obvious route.

The public reading surface is <https://zeta.teal-sea.com>: what has been
established, what is still a candidate, and what was withdrawn. Every figure on
it is derived from this tree at build time rather than typed in, so it cannot
quietly disagree with the repository it describes. Its generator lives in a
separate repository; this one holds the record, not the presentation of it.

## Where to start

| Guide | For you if you want to… | First command |
|---|---|---|
| [learn](docs/doors/learn.md) | see the classical machinery run at arbitrary precision | `.venv/bin/python scripts/06_tour.py` |
| [refute](docs/doors/refute.md) | test a claim about the zeros against the control battery | `.venv/bin/python scripts/23_gate_3_battery.py` |
| [certify](docs/doors/certify.md) | Lean proofs and interval enclosures | `cd lean && PATH="$HOME/.elan/bin:$PATH" lake build` |
| [discover](docs/doors/discover.md) | run the conjecture funnel and see its measured hit rate | `.venv/bin/python scripts/13_discovery_run.py --dry-run` |
| [contribute](docs/doors/contribute.md) | clone the lab, run a bounded agent hunt and return checkable findings | `.venv/bin/python scripts/71_contribution_check.py hunts/<short-name>` |
| [adopt](docs/doors/adopt.md) | *(demoted, read `harness/VERDICT.md` first)* the validation framework and why it was frozen | `.venv/bin/python -m pytest -q -o addopts='' tests/test_harness_protocol.py` |

Twelve worked demonstrations, the figure gallery, the repository map and the
standing list of limitations are in
[`docs/36-what-you-can-run.md`](docs/36-what-you-can-run.md). The docs are a
single course and `00 → 01 → 02 → 03 → 04` is one argument: start at
[`docs/00-orientation.md`](docs/00-orientation.md), and
[`docs/README.md`](docs/README.md) lists all thirty-seven with one line each.

## Quickstart

```bash
git clone https://github.com/teal-sea/zeta-lab && cd zeta-lab
python3 -m venv .venv                # Python >= 3.11
.venv/bin/pip install -r requirements.txt
.venv/bin/pip install -e .
.venv/bin/python scripts/06_tour.py  # the whole story in ~90 seconds, six acts
```

Dependencies are ordinary: `mpmath`, `numpy`, `scipy`, `matplotlib`, `sympy`,
plus `python-flint` for the ball-arithmetic backend. Expensive computations
cache under `data/`, so second runs are fast.

## Registered

Three results here have been rebuilt and kernel-checked by someone other than their
author. Each was submitted to the [Palomar Registry](https://palomar-registry.org/),
the Lean FRO / ICARM registry of Lean-verified mathematics, which fetched a pinned
commit, rebuilt the development from scratch on its own hardware inside a sandbox,
and replayed the proofs through Lean's kernel *and* the independent NanoDa kernel.

**[PALOMAR-2026-08-25-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-08-25-000005&version=1)**, the n-point
simple-zero bound (`lean/bridge/`). The parametric theorem and four instances. The
three- and four-point instances are **unconditional**: their finite certificates are
proved *inside Lean*, by interval cell lemmas over rationals rather than accepted from
an external program, so the theorems carry no certificate hypothesis.

> Φ₄ = (906250·H − 1085)/904171 = 0.6728470197…
> Φ₃ = (149000000·H − 99200)/148800133 = 0.6727373345…

built on `anthropics/zeta-23-lean` (arXiv:2608.13637), whose Theorem D gives
H = 0.6725007036… unconditionally; the step from 41.6% to H is theirs and is much the
larger piece of work. `#print axioms` reports exactly `[propext, Classical.choice,
Quot.sound]`. The eight-point instance keeps its certificate as a named hypothesis and
is registered as conditional.

**[PALOMAR-2026-08-21-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000004&version=1)**, the
source-admissible strong closure (`lean/`). With `A = I + T` the Fredholm operator
whose kernel is the Farmer–Gonek–Lee form factor `F1` on `I = [-1/2, 1/2]`,
`w = A^-1 1` and `c* = <1, w>`, over the compactly supported monotone admissible class
`v(s) = phi(Ls)^2`:

> sup <1,v>^2 / <Av,v> = c*, and inf <Av,v> / <1,v>^2 = 1/c*.

The upper bound is energy Cauchy–Schwarz and is classical. The content is the reverse
inequality: the class constraints do not lower the supremum, proved by exhibiting an
explicit endpoint-tapered family whose quotient converges to `c*`. **Scope:** a
statement about a Fredholm operator on an interval and a class of test profiles. It
says nothing about the zeros of ζ, nothing about RH, and asserts no numerical value
for `c*`.

**[PALOMAR-2026-08-21-000012](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000012&version=1)**, the analytic half
of Davenport–Heilbronn (`lean/palomar-dh/`). The registry classifies it *source-based*:
it formalizes an existing theorem rather than establishing a new one.

None of this is peer review. No person read any of them.

Check any of them yourself:

```bash
cd lean/bridge && PATH="$HOME/.elan/bin:$PATH" lake build V2Challenge V2Solution
# Solution builds sorry-free; Challenge carries one deliberate sorry per advertised
# statement, which is what the Palomar format requires.
bash scripts/palomar_stage.sh              # from the repo root, checks all four paths
```

## Conditional results, and where the method stops

Certificate-based figures above H exist, here and elsewhere, and every one of them
assumes a finite certificate that has not been proved. They are claims, not theorems.
This tree's best is an eight-point certificate at 0.6730529829…; the highest published
anywhere is 0.6734164909… (`AMTOPA/zeta-exact-pressure`), whose artifact returns
`INCONCLUSIVE` 1.19e-07 short of its own target when run at its own pinned tip, with
all six of its interval tables reproducing byte for byte (`hunts/amtopa_ceiling/`).
`trmdy`'s full 2,168,370-box interval run was reproduced here node for node with no
soundness defect found.

Every conditional figure above H, including this tree's, rests on an analytic bridge
that no person has reviewed. Φ₃ and Φ₄ do not.

The pressure-certificate family built on the Montgomery–Taylor window saturates at
sup Φₙ ≤ 0.675142509660254, against a configuration ceiling of 0.6818286874638
(`hunts/family_wall/`). Adding points cannot close that gap. The argument was audited
adversarially by an independent model working from a blank directory, which found two
repairable defects in the write-up and could not break the result.

A separate artifact with its own ledger: the gap-census transplant in
`hunts/frontier_math/` carries a candidate reading of record of 0.6725106958, graded
step by step in its `PROOF-LEDGER.md`. It is a candidate on a different chain, not one
of the certificate figures above, and it moves only when its ledger does.

## Negative controls, and one framework that did not earn its keep

The practice is load-bearing and stays: a claim is worth something only if a
**rival**, an object sharing the structure the claim leans on but lacking the
property, fails it. For ζ that rival is the Davenport–Heilbronn function, which
has the functional equation, real coefficients and a real Hardy Z, **and violates
RH**. `zeta.epstein.battery` runs a claimed property against it and two Epstein
zetas; `docs/09` gate #3 is the rule, and it needs no framework.

`harness/` generalized that into a subject-independent framework with pluggable
departments. In August 2026 it was tested against the practice it was meant to
improve: four preregistered experiments, two subjects, 74 agent runs. The
harness arm never outperformed the control, the control was 37/37, and at
identical correctness the harness cost 1.1–1.7× the tokens and 2.4–5.0× the tool
calls. Live hunts had meanwhile reimplemented the same four control roles by hand
rather than import them.

It is therefore **demoted, not deleted**: the ledgers under `harness/` (dead
ends, guards, reviews) have a live consumer in `scripts/70_lab_state.py` and stay
as ordinary bookkeeping; the framework is frozen. The full record, including the
protocols frozen before each run, is `harness/VERDICT.md` and
`harness/gate-evidence/`.

The negative result is kept because it is the more useful artifact. It also
supplies the rule in `AGENTS.md`: **do not build an abstraction without naming
the live thing that will consume it.**

## Checking the whole thing

Continuous integration runs on every push, in three tiers cut by measured cost:

| tier | when | what | cost |
|---|---|---|---|
| `checks` | every push and PR | 342 tests, **stdlib + pytest only**, no numpy, scipy, mpmath, no editable install, plus `make_context.py --check` | ~7 s |
| `tests` | PRs and pushes to `main` | the fast tier with the real dependency set; asserts `rigor.BACKEND` is genuinely Arb before running, because the mpmath fallback silently drops the cross-check that licenses the word *certified* | ~20 min |
| `full` | nightly, and on demand | the complete suite including slow, plus the Lean arm as its own job with a zero-`sorry` scan | up to an hour |

That CI is young and has already earned its place: its first complete run found
a `PROVED` formal record citing a kernel build older than the file it certified,
stale for six days, because until then nothing ran the suite unless a human
remembered to ([#20](https://github.com/teal-sea/zeta-lab/issues/20)).

Locally, `.venv/bin/python -m pytest -q -m "not slow"` is the fast tier.

**Open observations live as issues.** Something measured, noticed, broken or
bounded is a fact about the subject or about this tree, and it is true whether
or not anyone is pursuing it. Those are filed openly rather than kept in a
backlog file, see the [open issues](https://github.com/teal-sea/zeta-lab/issues).

## What this is (and is not)

This is an instrument for building intuition and numerics about RH: for
seeing the theorems happen, checking that formulas mean what you think they
mean, and calibrating what "evidence" is worth in this subject. Zeta Lab
reconstructs, tests, connects, and falsifies ideas around RH, without claiming
to advance RH. House rule, from `docs/00-orientation.md`: *if a computation
here appears to settle something, the correct inference is that there is a
bug.*

There are two certainty regimes, and they are not the same claim. The numerical
machinery in `zeta/` is *accurate*, and `zeta/rigor.py` alone may say
*certified*, for quantities whose every step carried an enclosure. `lean/` is
the second: a Lean 4 + Mathlib project whose theorems are checked by a proof
kernel rather than measured, and nothing there counts until it compiles with
zero `sorry`s.

## Pointers

- [`ROADMAP.md`](ROADMAP.md) records the *decisions*: why the work went this
  way, what is deliberately not being attempted, the known gaps, and the next
  build. Read it before planning anything.
- [`AGENTS.md`](AGENTS.md) is the operating context for a coding agent (Claude
  Code, Codex, Cursor, …): setup, house rules, the naming traps, and how to run
  the suite. `CLAUDE.md` is a symlink to it.
- [`ALIGNMENT.md`](ALIGNMENT.md) covers what an agent here is expected to do
  when it disagrees, and which decisions are not an agent's to make.
- [`CONTEXT.md`](CONTEXT.md) is the generated index of the public API, the
  document list, the script list and test counts. Regenerate it with
  `.venv/bin/python scripts/make_context.py`; never edit it by hand.
- `.venv/bin/python scripts/make_figures.py --quick` regenerates `figures/`.

## License

MIT, see `LICENSE`.
