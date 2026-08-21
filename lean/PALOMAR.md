# The Palomar submission surface

[Palomar](https://palomar-registry.org/) is a registry of Lean-verified
mathematics, incubated by the Lean FRO and ICARM and opened for submissions on
2026-08-18. It is the analogue of a preprint server for Lean proofs: it records
a claim from a fixed commit of a public repository, replays the proof through
Lean's kernel *and* the independent NanoDa kernel, applies an editorial floor
for research interest, and publishes the exact statement together with the
review's findings.

Five files in this directory exist for that registry and for nothing else.

| File | Role |
| --- | --- |
| `Challenge.lean` | The advertised statements. Imports Mathlib alone. |
| `Solution.lean` | The same statements, proved from `ZetaLean.Pub1`. |
| `comparator.json` | Which declarations are compared, and under which axioms. |
| `formalization.yaml` | Provenance, scope, automation and review metadata. |
| `PALOMAR.md` | This file. |

## `Challenge.lean` contains three deliberate `sorry`s. Do not "fix" them.

They are what the Palomar format requires of an advertised statement: the
Challenge module is the small, trusted surface a mathematical reader audits,
and it states each claim without proving it. `Solution.lean` proves the same
statements, and Comparator checks that the two match. The repository rule that
the Lean arm counts nothing with a `sorry` is untouched: the proof development
is sorry-free, and `Solution.lean` builds with no `sorry` warning.

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
