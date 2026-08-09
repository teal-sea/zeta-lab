# `dossier/` — research state as data. **A probe, not a department.**

An experiment: can intent, definitions, provenance, evidence, failed attempts,
proof obligations and verification status be represented so that an agent can
perform and **resume** rigorous mathematical work?

One schema, one worked example (Hardy's Z), one CLI. Read
[`docs/19-research-dossiers.md`](../docs/19-research-dossiers.md) for the
design and for §6, which explains why this is deliberately *not* a department.

```bash
.venv/bin/python scripts/50_dossier.py                # list
.venv/bin/python scripts/50_dossier.py hardy_Z        # the full report
.venv/bin/python scripts/50_dossier.py --validate     # non-zero exit if malformed
```

## Why it is a probe

`harness/README.md`'s admission rule is **no department without a battery**,
and a battery needs rivals — things that share the claimed structure and lack
the property. A dossier has no rivals of its own: refuting the `|ζ(½+it)|`
candidate is a claim about ζ, adjudicated by the *zeta* department's subject
matter. **A department whose battery is another department's battery is not a
department.**

So this registers nowhere, has no door, and appears in no department table.
The rule was not weakened to let it in. §6 of doc 19 records what would have to
change.

## The two ideas being tested

**Intent is data.** `Intent.purpose` says what the object is *for*, in prose,
before any formula; `distinguishes_from` lists what it is most likely to be
confused with. The Hardy Z dossier lists five, four of them name collisions
already documented in `AGENTS.md`. A definition can be checked against a
formula — an intent can only be stated, and stating it is what makes a later
mismatch visible.

**"Verified" is four things.** `status.py` carries four independent axes:

| axis | fails by |
| --- | --- |
| `numeric` | agreeing to forty digits and still being false (`docs/08`) |
| `certified` | proving something about a finite computation only |
| `literature` | citing a paper that is about a different object |
| `formal` | proving the statement as formalised, not the one meant |

There is no aggregate. `Support.__bool__` **raises**, so `if support:` is an
error rather than a silent collapse. That is the module's whole job.

## What the schema refuses

- no intent — a formula with no way to tell if it is the right formula;
- no *discriminating* obligation — a check nothing plausible fails is a tautology;
- an axis asserting support with no artifact — decoration;
- a rejected alternative with no reason, or an open question with no `what_would_settle_it`.

## The seam

`schema.py`, `status.py`, `report.py` and `__init__.py` name no quantity any
laboratory computes and import nothing from one — AST scan,
clean-interpreter `sys.modules` check, and a lexical scan, the same three the
other seams use. Subject matter lives in `subjects/`.

The lexical scan caught the first draft of these very modules, which cited
`zeta/rigor.py` by name in a docstring. That is the seam working.

## Reuse, not reinvention

`Provenance` comes from `ontology.schema`. No ledger, no verdict vocabulary,
and no second notion of provenance is defined here — a dossier describes one
object's research state; it is not a candidate observation with a hit rate, and
`ontology/` already owns that.

Identity is the one thing *not* reused: `ontology.schema.content_hash`
canonicalises a claim, demands a candidate kind and prefixes ids with `cand-`.
A dossier is not a candidate, and an id reading `cand-` would be read as one —
so `dossier_id` hashes its own three fields under `doss-`.

No certificate is ever issued here. "Certified" is reserved (`AGENTS.md`); a
dossier records *that* one was obtained and points at it.

## Scope

Bookkeeping about a textbook function. Nothing here is evidence for RH.
