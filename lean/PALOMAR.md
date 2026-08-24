# The Palomar submission surface

[Palomar](https://palomar-registry.org/) is a registry of Lean-verified
mathematics, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18. It is the analogue of a preprint server for Lean proofs: it records
a claim from a fixed commit of a public repository, replays the proof through
Lean's kernel *and* the independent NanoDa kernel, applies an editorial floor
for research interest, and publishes the exact statement together with the
review's findings.

Pub 1 and Davenport-Heilbronn are registered. The earlier bridge submission
attempt closed without registration. The sole intended bridge submission is
the surface called V2 in this repository: the unconditional three- and
four-point theorems together with the explicitly conditional general and
eight-point statements.

| File | Surface | Role |
| --- | --- | --- |
| `Challenge.lean` | Pub 1 | The advertised statements. Imports Mathlib alone. |
| `Solution.lean` | Pub 1 | The same statements, proved from `ZetaLean.Pub1`. |
| `comparator.json` | Pub 1 | Which declarations are compared, and under which axioms. |
| `formalization.yaml` | Pub 1 | Provenance, scope, automation and review metadata. |
| `DHChallenge.lean` | DH | The advertised statement. Imports Mathlib alone. |
| `DHSolution.lean` | DH | The same statement, proved from `ZetaLean.DHAnalytic`. |
| `comparator-dh.json` | DH | Which declaration is compared, and under which axioms. |
| `palomar-dh/formalization.yaml` | DH | Provenance, scope, automation and review metadata. |
| `bridge/BridgeChallenge.lean` | Earlier bridge attempt | The earlier statement surface. Imports Mathlib alone. |
| `bridge/BridgeSolution.lean` | Earlier bridge attempt | The same statements, proved from `Zeta23Ext.Bridge.Main`. |
| `bridge/comparator.json` | Earlier bridge attempt | The earlier Comparator configuration. |
| `bridge/formalization.yaml` | Earlier bridge attempt | The pinned V1 metadata; V2 does not modify it. |
| `bridge/V2Challenge.lean` | Intended bridge submission | The advertised statements. Imports Mathlib alone. |
| `bridge/V2Solution.lean` | Intended bridge submission | The same statements, proved from the bridge plus the three- and four-point certificate libraries. |
| `bridge/comparator-v2.json` | Intended bridge submission | Which declarations are compared, and under which axioms. |
| `bridge/palomar-v2/formalization.yaml` | Intended bridge submission | Canonical provenance, scope, automation and review metadata. |
| `bridge/formalization-v2.yaml` | Intended bridge submission | Compatibility copy; not the submission path. |
| `PALOMAR.md` | all of them | This file. |

The surfaces carry **fifteen** deliberate `sorry`s between them, three in
`Challenge.lean`, one in `DHChallenge.lean`, four in `BridgeChallenge.lean` and
seven in `V2Challenge.lean`, one per advertised statement.
Any claim about this tree being sorry-free has to say *which* object it means:
the developments and every Solution module are sorry-free, the Challenge
modules are not, and a submission whose metadata blurs the two gets that pointed
out. One did.

**The bridge surface is a separate Lake project, and has to be.** Pub 1 and DH
are built by the `lean/` package, whose only dependency is Mathlib. The bridge
theorem depends on `anthropics/zeta-23-lean`, which `lean/` does not require, so
its surface lives in a package of its own at `lean/bridge/` — the **selected
project** for that submission, in the sense of CONTRIBUTING.md section 6.1. Its
metadata and Comparator files stay beside the other two entries', because that is
where a reader looks for them; the submission form takes both paths explicitly.

## The Challenge modules contain deliberate `sorry`s. Do not "fix" them.

Three in `Challenge.lean`, one in `DHChallenge.lean`, four in
`BridgeChallenge.lean`, seven in `V2Challenge.lean`. They are what the Palomar format requires of an
advertised statement: the Challenge module is the small, trusted surface a
mathematical reader audits, and it states each claim without proving it. The
matching Solution module proves the same statements, and Comparator checks that
the two match. The repository rule that the Lean arm counts nothing with a
`sorry` is untouched: every proof development is sorry-free, and every Solution
module builds with no `sorry` warning.

## Why the definitions are duplicated

`Challenge.lean` may import only Lean core, Mathlib and Tau Ceti, so it cannot
import `ZetaLean`. It therefore restates the definitions the statements need,
verbatim, in a fresh `ZetaLean.Palomar` namespace. `Solution.lean` does **not**
import `Challenge`: under the Palomar layout the two modules independently
declare the same names, and importing one into the other would collide. Its
definition block is byte-identical to the one in `Challenge.lean`, and the
bridge lemmas to `ZetaLean.Pub1` are all `rfl`, except that `SourceWindow` is a
structure and therefore two distinct inductive types, so `sourceAdmissible_eq`
transports its ten fields in both directions.

If you edit a definition in `ZetaLean/Pub1/Setting.lean`, `Window.lean`,
`Main.lean` or `Aristotle/E1.lean` that an advertised statement mentions, the
`rfl` bridges in `Solution.lean` will break. That is the intended alarm: the
registry entry pins a commit, and the statements it advertises must keep
matching the development.

## What is submitted

The three declarations the companion note names in its formal-verification
section, mirrored into `ZetaLean.Palomar`:

- `pub1_strong_closure`: the supremum orientation,
  `sup ⟨1,v⟩²/⟨Av,v⟩ = c*` over the compactly supported monotone admissible
  class.
- `pub1_strong_closure_reciprocal`: the matching infimum, `1/c*`.
- `pub1_strong_closure_exists`: the same identity with the profile and both
  uniform constants existentially quantified, so it carries no hypothesis and
  cannot be vacuous.

These are statements about a Fredholm operator on `[-1/2, 1/2]` and about a
class of test profiles. They say nothing about the zeros of ζ and nothing about
the Riemann Hypothesis, and `formalization.yaml` says so in `status.scope`.

## Relation to the companion note

The informal note pins this repository at tag `xi-prime-ceiling-support-v1`,
commit `197cee922270a3ceba7c21de0a21dd816a29adad`. Between that commit and this
one the only file changed under `lean/` is `ZetaLean/HardyRamanujantheorem.lean`,
which is in the import closure of no advertised declaration. The mathematics
being advertised is therefore the same tree the note describes.

## Re-verifying before a resubmission

```bash
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build Challenge Solution
# expect: three `sorry` warnings from Challenge.lean, none from Solution.lean
cat > /tmp/Ax.lean <<'EOF'
import Solution
#print axioms ZetaLean.Palomar.pub1_strong_closure
#print axioms ZetaLean.Palomar.pub1_strong_closure_reciprocal
#print axioms ZetaLean.Palomar.pub1_strong_closure_exists
EOF
PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/Ax.lean
# expect each: [propext, Classical.choice, Quot.sound]
```

Both were run on 2026-08-21 against Mathlib `v4.33.0-rc2` and passed.

## The Davenport-Heilbronn surface, and why it advertises one declaration

Submitted 2026-08-21 as `m135pipw9ldb` at commit `e474535` advertising three
declarations, it cleared the mechanical gate clean and was then refused by the
editorial review. Two findings, both recorded in full in
`docs/32-the-palomar-arm.md` §8:

1. `review.notes` claimed "the tree is sorry-free", which the Challenge modules
   make false. The table above now states the split explicitly.
2. The two minimum-modulus criteria were a **separate selected result group**,
   and an elementary consequence of the maximum-modulus principle does not
   clear the notability floor on its own account. Usefulness to a later
   certified search is not research interest.

So the surface now advertises `ZetaLean.PalomarDH.dh_analytic_half` alone.
`ZetaLean.DH.exists_zero_of_norm_lt_on_sphere` and
`..._on_frontier` remain in the development, where `DHZeroCriterion.lean` uses
them; they are simply no longer offered to an editor to score. **Do not add
them back to `DHChallenge.lean` without a reason that answers finding 2.**

Palomar does not re-review a refused submission, and permits one submission in
progress per repository, so `m135pipw9ldb` was abandoned and the corrected
commit `097215a` went in as a new one. That one returned **no problems were
identified** and registration was requested on 2026-08-21. A submission's review
is private and reachable only through its own access link, which is a
credential: it does not belong in this repository.

```bash
cd lean && PATH="$HOME/.elan/bin:$PATH" lake build DHChallenge DHSolution
# expect: one `sorry` warning from DHChallenge.lean, none from DHSolution.lean
.venv/bin/python scripts/palomar_precheck.py . lean \
  lean/comparator-dh.json lean/palomar-dh/formalization.yaml
```


## The bridge registration

The V1 submission attempt at commit
`58bd44cadb5881540af744a152492d2c25420008` passed mechanical verification
and later closed without registration. It is not a public Palomar entry. The
owner reports that Palomar's page currently says its API credits are exhausted,
which is consistent with the four failed V1 review attempts. V2 must not be
submitted until V1 is withdrawn and Palomar reports that those credits have
been restored.

The sole intended bridge submission is the surface called V2 in this
repository. It advertises the selected declarations:

- the parametric `n`-point theorem, conditional on its named certificate;
- the eight-point bound and ratio, conditional on the same named certificate;
- the three-point bound and ratio, unconditional because their certificate is
  proved inside Lean;
- the four-point bound and ratio, unconditional because their certificate is
  proved inside Lean.

The unconditional constants are `0.67273733450380945875` at three points and
`0.67284701976668870316` at four points. The proved declarations use exactly
`propext`, `Classical.choice`, and `Quot.sound`. The
Challenge module contains one deliberate statement placeholder per advertised
declaration; `V2Solution` proves the advertised declarations without
`sorry`.

The submission coordinates are:

- repository: `teal-sea/zeta-lab`;
- project directory: `lean/bridge`;
- Comparator configuration: `lean/bridge/comparator-v2.json`;
- metadata: `lean/bridge/palomar-v2/formalization.yaml`.

Palomar requires the metadata basename to be exactly `formalization.yaml`;
the V2 copy therefore lives in its own `palomar-v2/` directory. The suffixed
compatibility file is not a valid submission path, and V1's
`bridge/formalization.yaml` and `bridge/comparator.json` remain pinned and
unchanged. Because V1 never registered,
the existing Palomar ID must be left blank: this is the initial bridge
registration, not a new version of a registered entry.

The four-point certificate has a green whole-package build in its source
package. The combined seven-statement V2 surface still requires its own hosted
whole-package build and axiom audit before submission, followed by Palomar's
official preparation against the exact public commit. Submission, withdrawal
and registration remain the owner's actions.
